from __future__ import annotations
from copy import deepcopy
import json
import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
from top_level_analyzer import TopLevelAnalyzer
from common import Column, TranslationPayload, deduplicate_nodes_by_stream, find_involved_tables, connected_component_dfs, ast_BoolExpr, FullContext, AGGREGATE_NAMES, TOP
from full_analyzer import FullAnalyzer
from pglast.stream import RawStream
from typing import Dict, List, Tuple
import itertools
from pglast.enums.parsenodes import SetOperation


class Phase1:
    def __init__(self, node: pglast.ast.Node, context: FullContext, translation_payload: TranslationPayload):
        if not isinstance(node, pglast.ast.Node):
            raise Exception("ToplevelAnalyzer accepts ast.Node, not node.Node")
        self.node: pglast.ast.Node = node
        self.context: FullContext = context
        self.top_level: TopLevelAnalyzer = TopLevelAnalyzer(self.node)
        self.center_tables: list[str] = None
        self.clusters: list[list[str]] = None
        self.relevant_clusters: list[list[str]] = None
        self.translation_payload = translation_payload
        # init
        self.top_level()
        self.top_level.replace_column_alias_usage()

    def find_center_tables(self):
        """fill in center_tables"""
        self.center_tables = self.top_level.find_center_tables()

    def find_clusters(self):
        """find clusters
           two side tables are in the same cluster iff there is a predicate that involve both
           assume center columns is filled
        """
        center_tables = set(self.center_tables)
        side_tables = set(self.top_level.tables) - center_tables
        edges = {side_table: [] for side_table in side_tables}
        predicates = self.top_level.fetch_all_predicates()
        # construct edges
        for predicate in predicates:
            involved_tables = find_involved_tables(predicate, self.context.sublink_exterior_columns)
            involved_tables -= center_tables
            for table in involved_tables:
                edges[table].extend(involved_tables - set([table]))
        # find connected components
        visited = set()
        clusters = []
        for table in side_tables:
            if table not in visited:
                cluster = []
                connected_component_dfs(table, edges, visited, cluster)
                clusters.append(cluster)
        self.clusters = clusters

    def remove_irrelevant_clusters(self):
        """remove tables in irrelevant clusters from Join clause and all related predicates
           calculate self.relevant_clusters
           return True if any cluster is removed
        """
        involved_tables = set()
        for column in self.top_level.target_columns.values():
            involved_tables |= find_involved_tables(column.val, self.context.sublink_exterior_columns)
        if self.translation_payload.links is not None:
            for node in self.translation_payload.links.values():
                involved_tables |= find_involved_tables(node, self.context.sublink_exterior_columns)
        modified = False
        self.relevant_clusters = []
        for cluster in self.clusters:
            if any(table in involved_tables for table in cluster):
                self.relevant_clusters.append(cluster)
                continue
            modified = True
            for table_name in cluster:
                self.top_level.remove_table_from_join(table_name)
                updated_where_clause = self.predicates_without_table_dfs(
                    pglast.node.Node(self.node).whereClause, table_name)
                self.node.whereClause = updated_where_clause
        self.remove_untranslatable_from_value_map()
        return modified

    def predicates_without_table_dfs(self, node: pglast.node.Node, table_name: str):
        """return a modified version of node that eliminates all predicates involving table_name"""
        if node is Missing:
            return None
        if isinstance(node, pglast.node.Scalar):
            return node.value
        if node.node_tag != "BoolExpr":
            involved_tables = find_involved_tables(node.ast_node, self.context.sublink_exterior_columns)
            return None if table_name in involved_tables else node.ast_node
        # node is BoolExpr
        args = [self.predicates_without_table_dfs(
            arg, table_name) for arg in node.args]
        args = [arg for arg in args if arg is not None]
        return ast_BoolExpr(node.boolop.value, args)
    
    def remove_untranslatable_from_value_map(self):
        """remove nodes translation_payload that involve removed clusters"""
        if self.translation_payload.value_map is None:
            return
        self.top_level()
        value_map = {}
        for column, node in self.translation_payload.value_map.items():
            involved_tables = find_involved_tables(node, self.context.sublink_exterior_columns)
            if all(table in self.top_level.tables for table in involved_tables):
                value_map[column] = node
        self.translation_payload.value_map = value_map
    
    def try_zoom_in(self):
        """returns zoom_in_finished, zoom_in_successful
           sets self.node, self.translation_payload on success
           see apply_zoom_in for more info
           """
        if len(self.top_level.tables) != 1 or len(self.top_level.target_columns) != 1:
            return True, False
        if isinstance(self.node.fromClause[0], pglast.ast.RangeVar):
            inner_root = deepcopy(self.context.table_node[self.top_level.tables[0]])
        else:
            assert(isinstance(self.node.fromClause[0], pglast.ast.RangeSubselect))
            inner_root = deepcopy(self.node.fromClause[0].subquery)
        if not isinstance(inner_root, pglast.ast.SelectStmt):
            return True, False
        self.translation_payload = deepcopy(self.translation_payload)
        if inner_root.op is SetOperation.SETOP_NONE:
            child_top_level = TopLevelAnalyzer(inner_root)
            child_top_level()
            zoom_in_successful = Phase1.apply_zoom_in(self, self.translation_payload, child_top_level)
            if zoom_in_successful:
                self.node = child_top_level.node
            return True, zoom_in_successful
        return False, None
        
    def set_op_inner_root_with_where(self):
        """when zooming into the single top-level table, the inner root has set operation (e.g. UNION)
           we push the where conditions into the inner root by removing table-qualifications for each column reference
           this is not legal SQL, but it does the job of storing where info
           return inner root with where clause
        """
        assert(len(self.top_level.tables) == 1)
        class RemoveQualificationVisitor(Visitor):
            def visit_ColumnRef(self, _, node):
                assert(len(node.fields) == 2)
                return pglast.ast.ColumnRef(fields=(node.fields[0],))
            # do not consider sublink yet
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()
            def visit_SortBy(self, _, node):
                return pglast.visitors.Skip()
        new_where = None
        if self.node.whereClause is not None:
            new_where = deepcopy(self.node.whereClause)
            visitor = RemoveQualificationVisitor()
            visitor(new_where)
        inner_root = deepcopy(self.context.table_node[self.top_level.tables[0]])
        inner_root.whereClause = new_where
        return inner_root

            
    @staticmethod
    def apply_zoom_in(parent: Phase1, translation_payload: TranslationPayload, child_top_level: TopLevelAnalyzer):
        """if all side tables are irrelevant and have been removed and there is only one center table,
           then we zoom in to the center table
           returns successful, new keys
           assume center_tables and relevant_clusters have been calculated
        """
        assert(len(parent.top_level.tables) == 1)
        assert(len(parent.top_level.target_columns) == 1)
        target_column = list(parent.top_level.target_columns.values())[0]
        # replace each columnRef in the selected field with actual content in inner table
        # if the columnRef to be replaced is in agg function and the replacement contains another aggregate function, we can't proceed
        TARGET = "%target%"
        must_translate_nodes = {TARGET: deepcopy(target_column.val)}
        if translation_payload.links is not None:
            must_translate_nodes = {**must_translate_nodes, **translation_payload.links}
        for origin_str, node_outer in must_translate_nodes.items():
            node_inner, inner_has_aggregate, outer_has_aggregate = parent.interpret_column_in_inner_scope(
                node_outer, child_top_level.target_columns)
            if inner_has_aggregate and outer_has_aggregate:
                return False
            must_translate_nodes[origin_str] = node_inner
        select_column_node = must_translate_nodes[TARGET]
        if translation_payload.links is not None:
            translation_payload.links = {
                origin_str: node for origin_str, node in must_translate_nodes.items() if origin_str != TARGET}
        # construct new branch's select
        new_root = deepcopy(child_top_level.node)
        if outer_has_aggregate and new_root.distinctClause is not None:
            parent.make_aggregate_distinct(select_column_node)
            new_root.distinctClause = None
        new_root.targetList = [pglast.ast.ResTarget(
            name=target_column.name, val=select_column_node)]
        # construct new branch's group by
        group_clause = []
        if new_root.groupClause is not None:
            group_clause.extend(new_root.groupClause)
        if len(parent.top_level.group_columns) > 0:
            for column in parent.top_level.group_columns:
                group_column_node, _, _ = parent.interpret_column_in_inner_scope(
                    deepcopy(column.val), child_top_level.target_columns)
                group_clause.append(group_column_node)
        # deduplicate group by columns
        new_group_column_nodes = deduplicate_nodes_by_stream(group_clause)
        if len(new_group_column_nodes) > 0:
            new_root.groupClause = new_group_column_nodes
        child_top_level.node = new_root
        # update translation payload value_map
        if translation_payload.value_map is not None:
            value_map = {}
            for column, node_outer in translation_payload.value_map.items():
                node_inner, inner_has_aggregate, outer_has_aggregate = parent.interpret_column_in_inner_scope(
                    node_outer, child_top_level.target_columns)
                if not (inner_has_aggregate and outer_has_aggregate):
                    value_map[column] = node_inner
            translation_payload.value_map = value_map
        return True

    @staticmethod
    def interpret_column_in_inner_scope(ast_node: pglast.ast.Node, columns: Dict[str, Column]):
        class IsAggregateVisitor(Visitor):
            def __init__(self):
                self.is_aggregate = False

            def visit_FuncCall(self, _, node):
                if node.funcname[0].val in AGGREGATE_NAMES:
                    self.is_aggregate = True

            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()

        class InterpretVisitor(Visitor):
            def __init__(self, columns: Dict[str, Column]):
                self.inner_has_aggregate = False
                self.columns = columns

            def visit_ColumnRef(self, _, node):
                assert(len(node.fields) == 2)
                column_name = node.fields[1].val
                replacement = self.columns[column_name].val
                is_aggregate_visitor = IsAggregateVisitor()
                is_aggregate_visitor(replacement)
                self.inner_has_aggregate = self.inner_has_aggregate or is_aggregate_visitor.is_aggregate
                return replacement
            # do not go into sublink

            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()
        # dummy node needed to be able to replace itself entirely
        dummy_node = pglast.ast.ResTarget(val=ast_node)
        is_aggregate_visitor = IsAggregateVisitor()
        is_aggregate_visitor(dummy_node)
        interpret_visitor = InterpretVisitor(columns)
        interpret_visitor(dummy_node)
        return dummy_node.val, interpret_visitor.inner_has_aggregate, is_aggregate_visitor.is_aggregate
    
    @staticmethod
    def enforce_zoom_in(parent: Phase1, translation_payload: TranslationPayload, child_top_level: TopLevelAnalyzer, subselect_alias: str):
        """after zooming in a select node with set operation, if some of the must-push-in columns can't be pushed in
           because the translation result would have nested aggregate functions, then we add a layer of select
        """
        class RenameTableVisitor(Visitor):
            def __init__(self, table_name_map: Dict[str, str]):
                self.table_name_map = table_name_map
            def visit_ColumnRef(self, _, node):
                if len(node.fields) == 2:
                    table, column = node.fields[0].val, node.fields[1].val
                    if table in self.table_name_map:
                        return Column.create(self.table_name_map[table], column).val
        def rename(ast_node: pglast.ast.Node, table_name_map):
            dummy_node = pglast.ast.ResTarget(val=ast_node)
            rename_table_visitor = RenameTableVisitor(table_name_map)
            rename_table_visitor(dummy_node)
            return dummy_node.val
        table_node = root.fromClause[0]
        table_name = table_node.alias.aliasname if table_node.alias else table_node.relname
        root = deepcopy(parent.node)
        subquery = deepcopy(child_top_level.node)
        alias = pglast.ast.Alias(subselect_alias)
        root = rename(root, {table_name: subselect_alias})
        if translation_payload.links is not None:
            translation_payload.links = {origin_str: rename(node) for origin_str, node in translation_payload.links.items()}
        if translation_payload.value_map is not None:
            translation_payload.links = {column: rename(node) for column, node in translation_payload.links.items()}
        root.fromClause = (pglast.ast.RangeSubselect(lateral=False, subquery=subquery, alias=alias),)
        child_top_level.node = root

    @staticmethod
    def make_aggregate_distinct(ast_node: pglast.ast.Node):
        class AggregateDistinctVisitor(Visitor):
            def visit_FuncCall(self, _, node):
                if node.funcname[0].val in AGGREGATE_NAMES:
                    node.agg_distinct = True

            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()
        aggregate_distinct_visitor = AggregateDistinctVisitor()
        aggregate_distinct_visitor(ast_node)
    
    def check_free_from_center(self):
        """if the selected column does not involve center tables, and the center tables are totally unrelated to
           the relevant cluster(s), then we remove the center table and GROUP BY altogether
           assume center tables and relevant clusters have been calculated
        """
        relevant_side_tables = list(itertools.chain(*self.relevant_clusters))
        if len(self.center_tables) == 0 or len(relevant_side_tables) == 0:
            return False
        remaining_tables = self.center_tables + relevant_side_tables
        edges = {table: [] for table in remaining_tables}
        nodes_to_be_checked = self.top_level.fetch_all_predicates()
        nodes_to_be_checked.extend(column.val for column in self.top_level.target_columns.values())
        # construct edges
        for node in nodes_to_be_checked:
            involved_tables = find_involved_tables(node, self.context.sublink_exterior_columns)
            for table in involved_tables:
                edges[table].extend(involved_tables - set([table]))
        # find connected components
        visited = set()
        clusters = []
        for table in remaining_tables:
            if table not in visited:
                cluster = []
                connected_component_dfs(table, edges, visited, cluster)
                clusters.append(cluster)
        # check if center tables share no clusters with relevant side tables
        for cluster in clusters:
            contains_center, contains_side = False, False
            if any(table in self.center_tables for table in cluster):
                contains_center = True
            if any(table in relevant_side_tables for table in cluster):
                contains_side = True
            if contains_center and contains_side:
                return False
        # remove center tables if they are indeed irrelevant
        for table_name in self.center_tables:
            self.top_level.remove_table_from_join(table_name)
            updated_where_clause = self.predicates_without_table_dfs(
                pglast.node.Node(self.node).whereClause, table_name)
            self.node.whereClause = updated_where_clause
        self.node.groupClause = None
        self.node.sortClause = None
        return True

    def check_idempotent(self):
        """check if the hole is idempotent, i.e. return same thing regardless of whether there is only one
           or more than one rows with same value in the fields it involves
        """
        holes = self.top_level.find_holes()
        if len(holes) == 0:
            return True
        assert(len(holes) == 1)
        funcCall = holes[0]
        assert(funcCall.funcname[0].val in AGGREGATE_NAMES)
        if funcCall.agg_distinct:
            return True
        involved_tables = find_involved_tables(funcCall, self.context.sublink_exterior_columns)
        irrelevant_cluster = 0
        for cluster in self.clusters:
            if all(table not in involved_tables for table in cluster):
                irrelevant_cluster += 1
        return irrelevant_cluster == 0


if __name__ == "__main__":
    schema_file = "phase1schema.json"
    # sql = """WITH cte AS (SELECT 1 as cst1, a.a1 as a1 FROM a) SELECT (SELECT 3 FROM d) k2, a2.a + 1 k2 FROM c c2 CROSS JOIN (SELECT * FROM a) as a2 WHERE EXISTS (SELECT 3 FROM d)"""
    # sql = """SELECT
    #     COUNT(DISTINCT A.id, B.id) ab
    # FROM I
    #     LEFT JOIN A
    #     ON I.x1 < A.a1
    #     INNER JOIN (
    #     B
    #     LEFT JOIN C
    #     ON I.x2 < C.c1
    #     CROSS JOIN E)
    #     ON B.b1 > A.a2
    #     LEFT JOIN D
    #     ON D.d1 = C.c2
    #     WHERE B.b1 >= A.a2 AND (A.a1 < A.a1 OR I.x2 < C.c1) OR NOT(D.d1 = C.c2 AND 1 AND B.id < 1 AND E.id = D.id)
    # GROUP BY I.x"""
    # sql = """SELECT COUNT(aa.a1) c1 FROM (SELECT a.a1 FROM a GROUP BY a.a1) aa CROSS JOIN b GROUP BY aa.a1"""
    # sql = """SELECT COUNT(c.id) c1 FROM a LEFT JOIN b ON a.id = b.id1 CROSS JOIN c GROUP BY a.a1 ORDER BY a.a1, b.id1"""
    # sql = """SELECT COUNT(a.id) c1 FROM a CROSS JOIN b CROSS JOIN c WHERE (SELECT id FROM c c2 WHERE c.id < c2.id) < 10"""
    sql = """SELECT a.id, a.a1 FROM a INNER JOIN b ON a.id = b.id1"""
    with open(schema_file) as file:
        schema = json.load(file)

    full_analyzer = FullAnalyzer(sql, schema)
    context = full_analyzer()
    node = context.table_node[TOP]
    # print(RawStream()(node))
    phase1 = Phase1(node, context)
    phase1.find_center_tables()
    phase1.find_clusters()
    print(phase1.center_tables, phase1.clusters)
    print("before:", RawStream()(phase1.node))
    phase1.remove_irrelevant_clusters()
    print("after remove:", RawStream()(phase1.node))
    zoom = phase1.zoom_in_if_center_one_only()
    if zoom:
        print("after zoom:", RawStream()(phase1.node))
    free = phase1.check_free_from_center()
    if free:
        print("after free:", RawStream()(phase1.node))
