from __future__ import annotations
import itertools
import json
import pglast
from pglast.visitors import Visitor
from pglast.enums.parsenodes import SetOperation, A_Expr_Kind
from pglast.enums.primnodes import BoolExprType
from pglast.stream import RawStream
from pglast.enums.nodes import JoinType
from copy import deepcopy
from typing import Any, Dict, Optional, Set, Tuple, List

from sqlalchemy import false
from common import HOLE_AGG_NAME, AGGREGATE_NAMES, SELECT_EMPTY, SELECT_SUM_ZERO, TOP, Column, Counter, FullContext, ast_BoolExpr, find_involved_columns, find_involved_tables, TranslationPayload, translate
from full_analyzer import FullAnalyzer
from top_level_analyzer import TopLevelAnalyzer
from branch_builder import Branch, BranchBuilder


class InstantiatedBranch:
    def __init__(
        self, 
        root: pglast.ast.SelectStmt, 
        free: bool, 
        target_names: List[str],
        link_target_map: Dict[str, str], 
        value_map: Dict[Tuple[str, str], pglast.ast.Node], 
        value_target_map: Dict[Tuple[str, str], str],
        ):
        self.root = root
        self.free = free
        self.target_names = target_names
        # map from text form of outermost key to name of inner target column that corresonds to the key
        self.link_target_map = link_target_map
        self.value_map = value_map
        # map from outermost (table, column) to name of inner target column that corresonds to it
        self.value_target_map = value_target_map
        
    def empty_instbranch():
        return InstantiatedBranch(SELECT_EMPTY, True, [], {}, {})
    
    def zero_instbranch():
        return InstantiatedBranch(SELECT_SUM_ZERO, True, [HOLE_AGG_NAME], {}, {})

    @staticmethod
    def check_empty_instbranch(branch: InstantiatedBranch):
        return RawStream()(branch.root) == RawStream()(SELECT_EMPTY)
    
    @staticmethod
    def check_zero_instbranch(branch: InstantiatedBranch):
        return RawStream()(branch.root) == RawStream()(SELECT_SUM_ZERO)
    
    @staticmethod
    def parse_link_orign_str(origin_str: str):
        """parse the keys of link_target_map in to pglast.ast.Node"""
        return pglast.parse_sql(f"SELECT {origin_str}")[0].stmt.targetList[0].val
    
    
class Instantiator:
    
    def __init__(self, id_to_branch, context: FullContext):
        self.context = context
        self.id_to_branch: Dict[int, List[Branch]] = id_to_branch
        self.id_to_instbranch: Dict[int, List[InstantiatedBranch]] = {}
        
    def instantiate(self):
        self.instantiate_id_dfs(1)
        return self.id_to_instbranch[1]
    
    def instantiate_id_dfs(self, id: int):
        """instantiate all possibilities for this id, cache in id_to_instbranch"""
        instantiated = self.id_to_instbranch[id] = []
        seen_text_form = set()
        for branch in self.id_to_branch[id]:
            text_form = RawStream()(branch.root)
            if text_form in seen_text_form:
                continue
            seen_text_form.add(text_form)
            if branch.children_type is None and branch.zoom_in_payload is None:
                # leaf branch
                instantiated.append(self.instantiate_branch(branch))
                continue
            children_components = []
            for child_id in branch.children:
                if child_id not in self.id_to_instbranch:
                    self.instantiate_id_dfs(child_id)
                children_components.append(self.id_to_instbranch[child_id])
            if branch.children_type is SetOperation.SETOP_NONE:
                # "hole" children type
                for children in itertools.product(*children_components):
                    merged = self.instantiate_merge_hole(branch, children)
                    instantiated.extend(merged)
            else:
                # "set operation" children type
                for children in itertools.product(*children_components):
                    merged = self.instantiate_merge_set_op(branch, children)
                    instantiated.append(merged)
                
        
    def instantiate_branch(self, branch: Branch):
        """instantiate a branch, i.e. add nodes in translation_payload to SELECT clause"""
        link_target_map = {}
        value_target_map = {}
        key_targets = []
        other_targets = []
        root = deepcopy(branch.root)
        links = branch.translation_payload.links if branch.translation_payload.links is not None else {}
        value_map = branch.translation_payload.value_map if branch.translation_payload.value_map else {}
        reverse_link = {RawStream()(node): origin_str for origin_str, node in links.items()}
        # process existing targets
        for resTarget in root.targetList:
            text_form = RawStream()(resTarget.val)
            if text_form in reverse_link:
                key_targets.append(resTarget)
                link_target_map[reverse_link[text_form]] = resTarget.name
                del reverse_link[text_form]
            else:
                other_targets.append(resTarget)
        link_counter = Counter()
        value_counter = Counter()
        # add keys not already present
        for origin_str in reverse_link.values():
            column_name = "key" + str(link_counter.count())
            key_targets.append(pglast.ast.ResTarget(name=column_name, val=links[origin_str]))
            link_target_map[origin_str] = column_name
        # add values
        for column, node in value_map.items():
            column_name = "value" + str(value_counter.count())
            other_targets.append(pglast.ast.ResTarget(name=column_name, val=node))
            value_target_map[column] = column_name
        root.targetList = [*key_targets, *other_targets]
        target_names = [target.name for target in root.targetList]
        return InstantiatedBranch(root, branch.free, target_names, link_target_map, value_map, value_target_map)
    
    
    def keyify_free_instbranch(self, branch: InstantiatedBranch, links: Dict[str, pglast.ast.Node]):
        """make a free instantiated branch non-free by providing external link nodes"""
        assert(branch.free)
        if links is None or len(links) == 0:
            return branch
        new_tables = set()
        for node in links.values():
            new_tables |= find_involved_tables(node, self.context.sublink_exterior_columns)
        root = deepcopy(branch.root)
        top_level_analyzer = TopLevelAnalyzer(root)
        top_level_analyzer()
        existing_tables = set(top_level_analyzer.tables)
        new_tables -= existing_tables
        # construct from node
        range_var = lambda table_name: pglast.ast.RangeVar(relname=table_name, inh=True, relpersistence="p")
        cross_join = lambda left, right: pglast.ast.JoinExpr(jointype=JoinType.JOIN_INNER, larg=left, rarg=right)
        from_node = None
        for table in new_tables:
            if from_node is None:
                from_node = range_var(table)
            else:
                from_node = cross_join(from_node, range_var(table))
        if root.fromClause is not None:
            root.fromClause = (cross_join(from_node, root.fromClause[0]),)
        else:
            root.fromClause = (from_node,)
        # construct target list
        link_counter = Counter()
        link_target_map = {}
        target_list = []
        for origin_str, node in links.items():
            column_name = "key" + str(link_counter.count())
            link_target_map[origin_str] = column_name
            target_list.append(pglast.ast.ResTarget(name=column_name, val=node))
        root.targetList = [*target_list, *root.targetList]
        target_names = [target.name for target in root.targetList]
        return InstantiatedBranch(root, false, target_names, link_target_map, branch.value_map, branch.value_target_map)
    
    ### merge "set operation" children type
            
    def instantiate_merge_set_op(self, parent: Branch, children: List[InstantiatedBranch]):
        """merge children when the split type is set operation
           for simplicity, for now do not support value_map across set operation
        """
        assert(parent.children_type in (SetOperation.SETOP_UNION, SetOperation.SETOP_INTERSECT, SetOperation.SETOP_EXCEPT))
        assert(len(children) > 0)
        non_empty_children = [child for child in children if not InstantiatedBranch.check_empty_instbranch(child)]
        # handle case of empty children
        if parent.children_type is SetOperation.SETOP_INTERSECT and len(non_empty_children) < len(children):
            return InstantiatedBranch.empty_instbranch()
        elif parent.children_type is SetOperation.SETOP_EXCEPT and InstantiatedBranch.check_empty_instbranch(children[0]):
            assert(len(children) == 2)
            return InstantiatedBranch.empty_instbranch()
        elif len(non_empty_children) == 0:
            return InstantiatedBranch.empty_instbranch()
        elif len(non_empty_children) == 1:
            return children[0]
        children = non_empty_children
        # check aggregate
        zoom_in_payload = parent.zoom_in_payload
        aggregate_func = None
        if zoom_in_payload is not None:
            top_level = zoom_in_payload.top_level
        elif parent.root.op is SetOperation.SETOP_NONE:
            top_level = TopLevelAnalyzer(parent.root)
            top_level()
        else:
            top_level = None
        if top_level is not None:
            holes = top_level.find_holes()
            if len(holes) > 0:
                # if more than one hole/one column, would have been isolated earlier
                assert(len(holes) == 1)
                assert(len(top_level.target_columns) == 1)
                aggregate_func = holes[0].funcname[0].val
        # start instantiating root
        if aggregate_func is None:
            # no aggregation, simply do set operation
            return self.instantiate_merge_set_op_non_agg(parent, children)
        else:
            # special case of zoom in
            return self.instantiate_merge_set_op_agg(parent, children, aggregate_func)
            
    def instantiate_merge_set_op_non_agg(self, parent: Branch, children: List[InstantiatedBranch]):
        """helper function of instantiate_merge_set_op, non aggregate case
           for simplicity, for now do not support value_map across set operation
        """
        # if all children free, then result is free
        if all(child.free for child in children):
            free = True
        else:
            free = False
            children = [self.keyify_free_instbranch(child, parent.translation_payload.links) if child.free else child for child in children]
        # construct root
        root = Instantiator.polyadic_set_op(parent.children_type, [child.root for child in children])
        # special information assigned in zoom-in
        if parent.root.op is not SetOperation.SETOP_NONE and parent.root.whereClause is not None:
            root = pglast.ast.SelectStmt(
                targetList=[pglast.ast.ResTarget(name=name, val=pglast.ast.ColumnRef(
                    fields=(pglast.ast.String(name),))) for name in children[0].target_names],
                fromClause=(pglast.ast.RangeSubselect(lateral=False, subquery=root, alias=pglast.ast.Alias("setop")),),
                whereClause=deepcopy(parent.root.whereClause),
                limitOption=pglast.enums.nodes.LimitOption,
                op=SetOperation.SETOP_NONE
            )
        return InstantiatedBranch(root, free, children[0].target_names, children[0].link_target_map, {}, {})
    
    def instantiate_merge_set_op_agg(self, parent: Branch, children: List[InstantiatedBranch], aggregate_func: str):
        """helper function of instantiate_merge_set_op, aggregate case
           for simplicity, for now do not support value_map across set operation
        """
        # special case of summing 0
        if aggregate_func == "sum":
            non_zero_children = [child for child in children if not InstantiatedBranch.check_zero_instbranch(child)]
            if len(non_zero_children) == 0:
                return InstantiatedBranch.zero_instbranch()
            children = non_zero_children
        # if all children free, then result is free
        if all(child.free for child in children):
            free = True
        else:
            free = False
            children = [self.keyify_free_instbranch(child, parent.translation_payload.links) if child.free else child for child in children]
        _, agg_target_name = Instantiator.extract_set_op_without_aggregate(children[0].root)
        key_names = children[0].link_target_map.values()
        root_args = [Instantiator.extract_set_op_without_aggregate(child.root)[0] for child in children]
        subquery = Instantiator.polyadic_set_op(parent.children_type, root_args)
        # construct root
        subselect_alias = "setop"
        target_list = []
        for target_name in children[0].target_names:
            node = pglast.ast.ColumnRef(fields=(pglast.ast.String(target_name),))
            if target_name not in (*key_names, agg_target_name):
                continue
            if target_name == agg_target_name:
                # add back aggregate function
                node = pglast.ast.FuncCall(funcname=(pglast.ast.String(aggregate_func),), args=(
                    node,), agg_within_group=False, agg_star=False, agg_distinct=False, func_variadic=False)
            target_list.append(pglast.ast.ResTarget(name=target_name, val=node))
        group_clause = [pglast.ast.ColumnRef(fields=(pglast.ast.String(key_name),)) for key_name in children[0].link_target_map.values()] 
        if len(group_clause) == 0:
            group_clause = None
        root = pglast.ast.SelectStmt(
            targetList=target_list,
            fromClause=(pglast.ast.RangeSubselect(lateral=False, subquery=subquery, alias=pglast.ast.Alias(subselect_alias)),),
            whereClause=deepcopy(parent.root.whereClause),
            groupClause=group_clause,
            op=SetOperation.SETOP_NONE
        )
        return InstantiatedBranch(root, free, [target.name for target in target_list], children[0].link_target_map, {}, {})
    
    @staticmethod
    def polyadic_set_op(set_op: SetOperation, args: List[pglast.ast.SelectStmt]):
        """return the result of applying set operation to combine multiple roots"""
        assert(len(args) > 0)
        if len(args) == 1:
            return args[0]
        root = deepcopy(args[0])
        for arg in args[1:]:
            root = pglast.ast.SelectStmt(
                op = set_op,
                larg = root,
                rarg = deepcopy(arg)
            )
        return root
    
    @staticmethod 
    def extract_set_op_without_aggregate(root: pglast.ast.SelectStmt):
        """Replace aggregate target by content and remove group by clause"""
        root = deepcopy(root)
        top_level = TopLevelAnalyzer(root)
        top_level()
        holes = top_level.find_holes()
        assert(len(holes) == 1)
        agg_target_name = None
        for res_target in root.targetList:
            func_node = res_target.val
            if not (isinstance(func_node, pglast.ast.FuncCall) and func_node.funcname[0].val in AGGREGATE_NAMES):
                continue
            agg_target_name = res_target.name
            res_target.val = func_node.args[0]
        root.groupClause = None
        # in case of nested set operation, try to use inner subquery directly
        if len(top_level.tables) == 1 and root.whereClause is None:
            table_node = root.fromClause[0]
            if isinstance(table_node, pglast.ast.RangeSubselect) and table_node.subquery.op is not SetOperation.SETOP_NONE:
                root = table_node.subquery
        return root, agg_target_name
    
    ### merge "hole" children type
    
    def instantiate_merge_hole(self, parent: Branch, children: List[InstantiatedBranch]):
        assert(parent.children_type is SetOperation.SETOP_NONE)
        root = deepcopy(parent.root)
        top_level = TopLevelAnalyzer(root)
        top_level()
        center_tables = top_level.find_center_tables()
        # remove side tables
        for table in top_level.tables:
            if table not in center_tables:
                top_level.remove_table_from_join(table)
        # join children tables
        children_names = [f"b{parent.id}t{count}" for count in range(1, len(children) + 1)]
        root_using_inner, root_using_left = Instantiator.join_children(root, children, children_names)
        top_level = TopLevelAnalyzer(root_using_inner)
        top_level()
        # find translation_map from children
        translate_map_from_children = self.find_translate_map_from_children(children, children_names)
        # find center switch plan and corresponding translate_maps from center
        switch_plans, center_translations = self.find_switch_plans(top_level, center_tables, children, children_names)
        # switch center, add chlidren, and translate predicates
        instantiated_branches = []
        for switch_plan in switch_plans:
            translate_maps = Instantiator.translate_maps_of_switch_plan(
                top_level, switch_plan, center_translations, translate_map_from_children)
            for translate_map in translate_maps:
                new_branch = deepcopy(parent)
                new_branch.translation_payload.update(translate_map)
                # todo: add root_using_inner
                for root in [root_using_inner, root_using_left]:
                    root = deepcopy(root)
                    result_root = self.switch_center_and_translate(
                        root, center_tables, switch_plan, children_names, translate_map)
                    new_branch.root = result_root
                    instantiated_branches.append(self.instantiate_branch(new_branch))
        return instantiated_branches
    
    @staticmethod
    def join_children(root: pglast.ast.SelectStmt, children: List[InstantiatedBranch], children_names: List[str]):
        """join children tables, translate holes to use columns of children tables"""
        class ReplaceHoleVisitor(Visitor):
            def __init__(self, children_names: List[str], left_join: bool):
                self.children_names = children_names
                self.left_join = left_join
            def visit_FuncCall(self, _, node):
                if node.funcname[0].val in AGGREGATE_NAMES:
                    # location set in TopLevelAnalyzer.find_holes
                    assert(node.location >= 0 and node.location < len(children))
                    child_table_name = self.children_names[node.location]
                    replacement = Column.create(child_table_name, HOLE_AGG_NAME).val
                    if self.left_join:
                        # default value is 0
                        replacement = pglast.ast.CoalesceExpr(args=(replacement, pglast.ast.A_Const(pglast.ast.Integer(0))))
                    return replacement
                return None
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()
        root_using_inner = deepcopy(root)
        root_using_left = deepcopy(root)
        # replace hole with reference to children columns
        ReplaceHoleVisitor(children_names, False)(root_using_inner)
        ReplaceHoleVisitor(children_names, True)(root_using_left)
        # join non-free children tables
        assert(root_using_inner.fromClause is not None)
        from_using_inner = root_using_inner.fromClause[0]
        from_using_left = root_using_left.fromClause[0]
        def join_expr(larg: pglast.ast.Node, rarg: pglast.ast.Node, quals: pglast.ast.Node, left_join: bool):
            join_type = JoinType.JOIN_LEFT if left_join else JoinType.JOIN_INNER
            return pglast.ast.JoinExpr(jointype=join_type, isNatural=False, larg=larg, rarg=rarg, quals=quals)
        for child_name, child in zip(children_names, children):
            if child.free:
                continue
            subselect = pglast.ast.RangeSubselect(lateral=False, subquery=child.root, alias=pglast.ast.Alias(child_name))
            on_predicates = []
            # gather on-conditions
            for origin_str, target_name in child.link_target_map.items():
                if BranchBuilder.check_dummy_origin_str(origin_str):
                    continue
                link_node = InstantiatedBranch.parse_link_orign_str(origin_str)
                inner_target = Column.create(child_name, target_name).val
                on_predicates.append(
                    pglast.ast.A_Expr(kind=A_Expr_Kind.AEXPR_OP, name=(
                        pglast.ast.String("="),), lexpr=link_node, rexpr=inner_target)
                )
            # join child table
            from_using_inner = join_expr(from_using_inner, subselect, ast_BoolExpr(
                BoolExprType.AND_EXPR, on_predicates), False)
            from_using_left = join_expr(from_using_left, subselect, ast_BoolExpr(
                BoolExprType.AND_EXPR, on_predicates), True)
        root_using_inner.fromClause = (from_using_inner,)
        root_using_left.fromClause = (from_using_left,)
        return [root_using_inner, root_using_left]
    
    def find_translate_map_from_children(self, children: List[InstantiatedBranch], children_names: List[str]):
        """find translate_map mapping from columns in parent to columns in children"""
        named_children = dict(zip(children_names, children))
        translate_map = {}
        for table_name, branch in named_children.items():
            for column, target_name in branch.value_target_map.items():
                translate_map.setdefault(column, [])
                translate_map[column].append((table_name, target_name))
        return translate_map
    
    def find_switch_plans(self, top_level: TopLevelAnalyzer, center_tables: List[str], children: List[InstantiatedBranch], children_names: List[str]):
        """find center switch plan and corresponding translate_maps from center"""
        context_columns = {table: list(columns.keys()) for table, columns in self.context.columns.items()}
        children_context_columns = {child_name: child.target_names for child_name, child in zip(children_names, children)}
        top_level.construct_equality_graph({**context_columns, **children_context_columns}, conjunct_only=False)
        must_switch_columns = self.find_must_switch_columns(top_level, center_tables, children)
        center_translations = []
        for center_table in center_tables:
            center_translations.append(self.find_center_translations(top_level, center_table, must_switch_columns))
        switch_plans = list(itertools.product(*[translations.keys() for translations in center_translations]))
        return switch_plans, center_translations
    
    def find_must_switch_columns(self, top_level: TopLevelAnalyzer, center_tables: List[str], children: List[InstantiatedBranch]):
        """find all columns of centers tables that must be translated if we are to switch center tables"""
        must_switch_columns = set()
        for column in top_level.target_columns.values():
            invovled_columns = find_involved_columns(column.val, self.context.sublink_exterior_columns)
            must_switch_columns |= {(table, column) for (table, column) in invovled_columns if table in center_tables}
        for column in top_level.group_columns:
            invovled_columns = find_involved_columns(column.val, self.context.sublink_exterior_columns)
            must_switch_columns |= {(table, column) for (table, column) in invovled_columns if table in center_tables}
        for child in children:
            if child.link_target_map is None:
                continue
            for origin_str in child.link_target_map:
                if BranchBuilder.check_dummy_origin_str(origin_str):
                    continue
                link_node = InstantiatedBranch.parse_link_orign_str(origin_str)
                invovled_columns = find_involved_columns(link_node, self.context.sublink_exterior_columns)
                must_switch_columns |= {(table, column) for (table, column) in invovled_columns if table in center_tables}
        return must_switch_columns
    
    def find_center_translations(self, top_level: TopLevelAnalyzer, center_table: str, must_switch_columns: Set[Tuple[str, str]]):
        """return a dict: other_table -> (dict: (center_table, column_name) -> (other_table, column_name))
           where the translation from center_table to other_table is in dict if all must_swtich_columns can be translated 
           assume top_level.equality_cluster_of has been constructed
        """
        translation_map_by_table = {}
        for center_column_name in self.context.columns[center_table]:
            # translate to itself is always valid
            column = (center_table, center_column_name)
            for other_table, other_column_name in top_level.equality_cluster_of[column]:
                translation_map_by_table.setdefault(other_table, {})
                translation_map_by_table[other_table].setdefault(column, [])
                translation_map_by_table[other_table][column].append((other_table, other_column_name))
        # filter out translations that can't translate must_switch_columns
        valid_translations = {}
        must_switch_columns = {(table, column) for (table, column) in must_switch_columns if table == center_table}
        for other_table, translation in translation_map_by_table.items():
            if set(translation.keys()) >= must_switch_columns:
                valid_translations[other_table] = translation
        # process translation map to make explicit cases we can't translate
        for other_table, translation in valid_translations.items():
            for center_column_name in self.context.columns[center_table]:
                column = (center_table, center_column_name)
                if column not in translation:
                    translation[column] = None
        return valid_translations
    
    @staticmethod
    def translate_maps_of_switch_plan(
        top_level: TopLevelAnalyzer,
        switch_plan: List[str], 
        center_translations: List[Dict[Tuple[str, str], List[Tuple[str, str]]]],
        translate_map_from_children: Dict[Tuple[str, str], List[Tuple[str, str]]]
        ):
        """find possible translate maps corresponding to a switch plan"""
        # helper function to extend dictionary by keys in extension, merging lists when a key exists in both
        def extend_dict(dictionary: Dict[Any, list], extension: Dict[Any, list]):
            for key, value_list in extension.items():
                if key in dictionary:
                    dictionary[key].extend(value_list)
                else:
                    dictionary[key] = value_list
        # merge translate map obtained with the switch plan choice
        translate_map_from_center = {}
        for translate_map_by_table, switch_to_table in zip(center_translations, switch_plan):
            extend_dict(translate_map_from_center, translate_map_by_table[switch_to_table])
        return Instantiator.concretize_and_merge_translate_maps(
            top_level, translate_map_from_center, translate_map_from_children)
    
    @staticmethod
    def concretize_and_merge_translate_maps(
        top_level: TopLevelAnalyzer, 
        translate_map_from_center: Dict[Tuple[str, str], List[Tuple[str, str]]], 
        translate_map_from_children: Dict[Tuple[str, str], List[Tuple[str, str]]]
    ):
        """identify all possibilities for translate_maps and transform them to format translate() can use"""
        exact_group_by_columns = []
        for column in top_level.group_columns:
            if isinstance(column.exact_inner, Tuple):
                exact_group_by_columns.append(column.exact_inner)
        concrete_center_maps = Instantiator.concretize_translate_map(translate_map_from_center, exact_group_by_columns)
        concrete_children_maps = Instantiator.concretize_translate_map(translate_map_from_children, [])
        concrete_maps = []
        for concrete_center_map in concrete_center_maps:
            for concrete_children_map in concrete_children_maps:
                concrete_maps.append({**concrete_center_map, **concrete_children_map})
        cleaned_up_concrete_maps = []
        for concrete_map in concrete_maps:
            cleaned_map_concreate_map = {}
            for column, translated in concrete_map.items():
                if translated is None:
                    cleaned_map_concreate_map[column] = None
                elif column != concrete_map[column]:
                    cleaned_map_concreate_map[column] = Column.create(*translated).val
                else:
                    pass
            cleaned_up_concrete_maps.append(cleaned_map_concreate_map)
        return cleaned_up_concrete_maps
                

    @staticmethod
    def concretize_translate_map(translate_map: Dict[Tuple[str, str], List[Tuple[str, str]]], distinct_columns: List[Tuple[str, str]]):
        """return all possible translate map, where distinct_columns are translated to distinct columns"""
        # process as much as we can first (None/single option)
        partial_result = {}
        translate_map = deepcopy(translate_map)
        for column, candidates in deepcopy(translate_map).items():
            if candidates is None:
                partial_result[column] = None
                del translate_map[column]
            elif len(candidates) == 1:
                partial_result[column] = candidates[0]
                del translate_map[column]
            else:
                pass
        supposedly_distinct = list(partial_result[column] for column in distinct_columns if column in partial_result)
        if len(supposedly_distinct) != len(set(supposedly_distinct)):
            return []
        return Instantiator.concretize_translate_map_dfs(partial_result, translate_map, distinct_columns)
    
    @staticmethod
    def concretize_translate_map_dfs(
        partial_result: Dict[Tuple[str, str], Tuple[str, str]], 
        remaining: Dict[Tuple[str, str], List[Tuple[str, str]]], 
        distinct_columns: List[Tuple[str, str]]
    ):
        """helper function for concretize_translate_map"""
        if len(remaining) == 0:
            return [deepcopy(partial_result)]
        center_column = next(iter(remaining))
        candidates = deepcopy(remaining[center_column])
        # backtracking
        del remaining[center_column]
        assert(len(candidates) > 1)
        supposedly_distinct = set()
        if center_column in distinct_columns:
            supposedly_distinct = set(partial_result[column] for column in distinct_columns if column in partial_result)
        results = []
        for candidate in candidates:
            if candidate in supposedly_distinct:
                continue
            partial_result[center_column] = candidate
            results += Instantiator.concretize_translate_map_dfs(partial_result, remaining, distinct_columns)
            del partial_result[center_column]
        remaining[center_column] = candidates
        return results
    
    @staticmethod
    def switch_center_and_translate(
        root: pglast.ast.SelectStmt, 
        center_tables: List[str], 
        switch_plan: List[str],
        children_names: List[str],
        translate_map: Dict[Tuple[str, str], Tuple[str, str]]
    ):
        """replace/remove center tables in join and translate everything accordingly"""
        # calculate replacement relationship
        existing_centers = set()
        replace_center = {}
        for old_table, new_table in zip(center_tables, switch_plan):
            replace_center[old_table] = new_table if new_table not in existing_centers else None
            existing_centers.add(new_table)
        Instantiator.switch_center(root, replace_center, children_names)
        top_level = TopLevelAnalyzer(root)
        top_level()
        top_level.translate_targets(translate_map)
        top_level.translate_where_predicates(translate_map)
        top_level.translate_join_on_dfs(root.fromClause[0], translate_map)
        # translate group by
        top_level.node.groupClause = [translate(node, translate_map) for node in top_level.node.groupClause]
        # best effort translate order by
        top_level.translate_order_by(translate_map)
        return top_level.node
    
    @staticmethod
    def switch_center(root: pglast.ast.SelectStmt, replace_center: Dict[str, Optional[str]], children_names: List[str]):
        """replace/remove center tables in join"""
        top_level = TopLevelAnalyzer(root)
        for table, replace_table in replace_center.items():
            if replace_table is None or replace_table in children_names:
                top_level.remove_table_from_join(table)
        class ReplaceTableVisitor(Visitor):
            def __init__(self, replace_center: Dict[str, Optional[str]], children_names: List[str]):
                self.replace_center = replace_center
                self.children_names = children_names
            def visit_RangeVar(self, _, node):
                return self.replace_table(node)
            def visit_RangeSubselect(self, _, node):
                return self.replace_table(node)
            def replace_table(self, node):
                table_name = node.alias.aliasname if node.alias else node.relname
                if table_name in self.children_names:
                    return pglast.visitors.Skip()
                assert(table_name in self.replace_center)
                replace_table = self.replace_center[table_name]
                if replace_table is not None:
                    alias = alias=pglast.ast.Alias(replace_table)
                    return pglast.ast.RangeVar(relname=replace_table, inh=True, relpersistence="p", alias=alias)
                return node
        replace_table_visitor = ReplaceTableVisitor(replace_center, children_names)
        replace_table_visitor(root)

schema_file="testschema.json"
with open(schema_file) as file:
    schema = json.load(file)

# sql="""
#     SELECT  t.team_id
#        ,t.team_name
#        ,(SUM(CASE WHEN ((t.team_id = m.host_team) AND (m.host_goals > m.guest_goals)) OR ((t.team_id = m.guest_team) AND (m.host_goals < m.guest_goals)) THEN 3 ELSE 0 END)) AS num_points
# FROM Teams AS t
# CROSS JOIN Matches AS m
# GROUP BY  t.team_id
#          ,t.team_name
# ORDER BY num_points DESC
#          ,t.team_id ASC"""
# sql = """SELECT a.id, SUM(b0.b1) su FROM a INNER JOIN (SELECT id1, b1 FROM b) b0 ON a.id = b0.id1 GROUP BY a.id"""
# sql = """SELECT SUM(c1) su FROM (SELECT a.id c0, a.a1 c1 FROM a UNION SELECT b.id1 c0, b.b1 c1 FROM b) tt GROUP BY c0"""
# sql = """SELECT  t1.contest_id
#        ,round(cast(div((COUNT(t2.user_id)) * 100,COUNT(t1.user_id)) AS numeric),2) AS percentage
# FROM
# (
# 	SELECT  *
# 	FROM
# 	(
# 		SELECT  distinct register.contest_id
# 		FROM register
# 	) AS co
# 	CROSS JOIN
# 	(
# 		SELECT  distinct users.user_id
# 		FROM users
# 	) AS us
# ) AS t1
# LEFT JOIN register AS t2
# ON (t1.contest_id = t2.contest_id) AND (t1.user_id = t2.user_id)
# GROUP BY  t1.contest_id
# ORDER BY percentage desc
#          ,t1.contest_id asc"""
# sql = """WITH all_users AS
# (
#        SELECT  distinct calls.from_id AS id
#        FROM calls union
#        SELECT  distinct calls.to_id AS id
#        FROM calls
# )
# SELECT  a.id            AS person1
#        ,b.id            AS person2
#        ,COUNT(c.duration) AS call_count
#        ,SUM(c.duration)   AS total_duration
# FROM      all_users a
#      JOIN all_users b ON a.id<b.id
#      JOIN calls c ON (a.id = c.from_id AND b.id = c.to_id ) or (a.id = c.to_id AND b.id = c.from_id )
# GROUP BY  a.id
#          ,b.id"""
# sql = "SELECT COUNT(bb.b1) col FROM a INNER JOIN (SELECT * FROM b) bb ON a.a1 = bb.b1 WHERE (CASE WHEN a.id < bb.id2 THEN 1 ELSE 20 END) < 10 GROUP BY a.a1"
# sql = "SELECT COUNT(bb.b1) col FROM a INNER JOIN (SELECT * FROM b b11 UNION SELECT * FROM b b12) bb ON a.a1 = bb.b1 WHERE (CASE WHEN a.id < bb.id2 THEN 1 ELSE 20 END) < 10 GROUP BY a.a1"
# sql = "SELECT COUNT(z.z1) col1 FROM c INNER JOIN (SELECT c.c1 z1, SUM(b.b1) z2 FROM c CROSS JOIN b GROUP BY c.id) z ON c.id = z.z1 WHERE z.z2 > 1 GROUP BY c.id"
# sql = "SELECT z.z1 col1 FROM (SELECT SUM(a.a1) z1, a.id z2 FROM a UNION SELECT SUM(b.b1) z1, b.id2 z2 FROM b) z"
# sql = "SELECT a.id id, a.a1 fr FROM a UNION SELECT c.id id, c.c1 fr"
# sql = "SELECT a.id id FROM a UNION SELECT b.id1 id FROM b UNION SELECT c.id id FROM c"
# sql = "SELECT a.id FROM a CROSS JOIN b WHERE a.a1 = b.b1 OR a.a1 = b.id2"
# sql = "SELECT SUM(z.fr) col1 FROM c INNER JOIN (SELECT a.id id, a.a1 fr FROM a UNION SELECT b.id1 id, b.b1 fr FROM b) z ON c.id = z.id GROUP BY c.id"
# sql = "SELECT SUM(z.z1) col FROM ((SELECT b.b1 z1 FROM a CROSS JOIN b GROUP BY a.a1) UNION (SELECT c.c1 z1 FROM a CROSS JOIN c GROUP BY a.a1) UNION (SELECT c.c1 z1 FROM a CROSS JOIN c GROUP BY a.a1)) z"
# sql = "SELECT SUM(z.z1) col1 FROM c INNER JOIN (SELECT y.a1 z1, SUM(y.a2) z2 FROM (SELECT a.a1 a1, SUM(a.a1) a2 FROM a) y) z ON c.id = z.z1 WHERE z.z2 < 1 GROUP BY c.id"
# sql = "SELECT SUM(z.z1) col1 FROM c INNER JOIN (SELECT a.a1 z1, ABS(SUM(a.a1)) z2 FROM a) z ON c.id = z.z1 WHERE z.z2 < 1 GROUP BY c.id"
# sql = "SELECT a.id, SUM(b.b1) col FROM a INNER JOIN b ON a.id = b.id1 GROUP BY a.id"


def main(sql, schema):
    # analyze incoming sql
    full_analyzer=FullAnalyzer(sql, schema)
    context=full_analyzer()
    root = context.table_node[TOP] 
    branch_builder = BranchBuilder(root, context)
    id_to_branch = branch_builder.build()
    instantiator = Instantiator(id_to_branch, context)
    return id_to_branch, instantiator.instantiate()

if __name__ == "__main__":
    id_to_branch, instbranches = main(sql, schema)
    for id, branches in id_to_branch.items():
        print(id)
        for branch in branches:
            print(RawStream()(branch.root))
            print(
                f"children ({branch.children_type}):", branch.children, 
                "free:", branch.free,
                "links:", branch.translation_payload.links, 
                "value_map:", branch.translation_payload.value_map
            )
    print("instantiated results:")
    for instbranch in instbranches:
        print(RawStream()(instbranch.root))
