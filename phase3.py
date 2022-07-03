from copy import deepcopy
import itertools
import json
from numpy import inner
import pglast
from pglast import parser, parse_sql
from pglast.visitors import Visitor
from phase2 import Phase2
from top_level_analyzer import TopLevelAnalyzer
from common import TOP, Column, TranslationPayload, find_involved_columns, find_involved_tables, translate
from full_analyzer import FullAnalyzer, FullContext
from pglast.stream import RawStream
from typing import Dict, Set, List, Tuple
from pglast.enums.nodes import JoinType

class Phase3:
    def __init__(self, node: pglast.ast.Node, context: FullContext, outer_tables: List[str], translation_payload: TranslationPayload):
        if not isinstance(node, pglast.ast.Node):
            raise Exception("ToplevelAnalyzer accepts ast.Node, not node.Node")
        self.node: pglast.ast.Node = node
        self.context: FullContext = context
        self.top_level: TopLevelAnalyzer = TopLevelAnalyzer(self.node)
        self.translate_map: Dict[Tuple[str, str], pglast.ast.Node] = None
        self.translation_payload: TranslationPayload = translation_payload
        # init
        self.top_level()
        self.outer_tables = [table for table in outer_tables if table in self.top_level.tables]
        
    def construct_equality_graph(self):
        """construct equality graph, equality clusters, equalities and save it in top_level"""
        self.top_level.construct_equality_graph(self.context.columns)
    
    def find_functionally_dependent_columns(self, columns: Set[Tuple[str, str]]):
        """find all (top_level_table, column) that are functionally dependent on columns, taken equalities into account
           assume top_level.equality_graph has been constructed
        """
        columns = self.expand_columns_by_equal_graph(columns)
        columns = self.expand_columns_by_unique_tuple(columns)
        while True:
            equal_expanded = self.expand_columns_by_equal_graph(columns)
            if (len(columns) == len(equal_expanded)):
                break
            columns = equal_expanded
            unique_expanded = self.expand_columns_by_unique_tuple(columns)
            if (len(columns) == len(unique_expanded)):
                break
            columns = unique_expanded
        return columns
        
    def expand_columns_by_equal_graph(self, columns: Set[Tuple[str, str]]):
        """find all (top_level_table, column) that are the same as at least one column in columns
           assume top_level.equality_graph, top_level.equality_clusters has been constructed
        """
        result = set()
        for vertex in columns:
            result |= self.top_level.equality_cluster_of[vertex]
        return result
    
    def expand_columns_by_unique_tuple(self, columns: Set[Tuple[str, str]]):
        """find all (top_level_table, column) that are functionally dependent on columns"""
        result = set()
        by_table = itertools.groupby(sorted(columns), lambda table_column: table_column[0])
        for table, group in by_table:
            group = set(group)
            column_name_set = set(column for _, column in group)
            has_ucc = False
            for unique_tuple in self.context.unique_column_tuples[table]:
                if set(unique_tuple) <= column_name_set:
                    has_ucc = True
                    break
            if has_ucc:
                # if we have unique column combination, then we can determine every column
                result |= set((table, column_name) for column_name in self.context.columns[table])
            else:
                result |= group
        return result
    
    def construct_translate_map(self, keys_outer: List[pglast.ast.Node]):
        """find all outer columns we must translate into inner scope and construct
           a mapping: outer_column -> inner_column
        """
        self.translate_map = {}
        if self.node.fromClause is None:
            return True
        # columns we must translate
        obliged_columns = set()
        for column in self.top_level.target_columns.values():
            obliged_columns |= find_involved_columns(column.val, self.context.sublink_exterior_columns)
        for key_outer in keys_outer:
            obliged_columns |= find_involved_columns(key_outer, self.context.sublink_exterior_columns)
        if self.translation_payload.links is not None:
            for _, key_outer in self.translation_payload.links.items():
                obliged_columns |= find_involved_columns(key_outer, self.context.sublink_exterior_columns)
        # construct mapping
        for table in self.outer_tables:
            for column in self.context.columns[table]:
                cluster = self.top_level.equality_cluster_of[(table, column)]
                try:
                    mapped_to = next((table, column) for table, column in cluster if table not in self.outer_tables)
                    self.translate_map[(table, column)] = Column.create(*mapped_to).val
                except StopIteration:
                    self.translate_map[(table, column)] = None
                    if (table, column) in obliged_columns:
                        # Cannot translate table.column, which we must translate
                        return False
        return True
    
    def update_translation_payload(self):
        """update translate_payload.links if it's not null
           update translate_payload.value_map: translate existing values and new values found in where/join on condition
        """
        self.translation_payload.update(self.translate_map)
        if self.translation_payload.value_map is not None:
            return
        involved_columns = set()
        if self.node.fromClause is not None:
            involved_columns |= find_involved_columns(self.node.fromClause[0], self.context.sublink_exterior_columns)
        if self.node.whereClause is not None:
            involved_columns |= find_involved_columns(self.node.whereClause, self.context.sublink_exterior_columns)
        self.translation_payload.value_map = {
            (table, column): Column.create(table, column).val for (table, column) in involved_columns
            if table not in self.outer_tables
        } 
    
    def check_center_is_unique(self):
        """check if the tuple of group-by columns functionally determines all outer table fields
           assume top_level.equality_graph has been constructed
        """
        # all group-by columns of the form top_level_table.column
        exact_center_columns = set()
        for column in self.top_level.group_columns:
            if isinstance(column.exact_inner, tuple):
                exact_center_columns.add(column.exact_inner)
        outer_table_columns = set()
        for table in self.top_level.tables:
            if table not in self.outer_tables:
                continue
            for column_name in self.context.columns[table]:
                outer_table_columns.add((table, column_name))
        functionally_dependent_columns = self.find_functionally_dependent_columns(exact_center_columns)
        return functionally_dependent_columns >= outer_table_columns
    
    def check_all_one_to_one(self):
        """check if all joins are one-to-one joins
           assume top_level.equalities, top_level.equality_graph has been constructed
        """
        equality_columns = set()
        for column1, column2 in self.top_level.equalities:
            equality_columns.add(column1)
            equality_columns.add(column2)
        all_columns_count = sum(len(self.context.columns[table]) for table in self.top_level.tables)
        functionally_dependent_columns = self.find_functionally_dependent_columns(equality_columns)
        return len(functionally_dependent_columns) == all_columns_count
    
    def outer_columns_in_equalities(self):
        """get all column ast_nodes in the outer table that participate in at least one equality,
           and then find a minimal subset of it that does not affect functional dependency
           assume top_level.equality_graph has been construcuted
        """
        inner_keys = []
        for table in self.outer_tables:
            for column in self.context.columns[table]:
                if len(self.top_level.equality_graph[(table, column)]) > 0:
                    inner_keys.append(Column.create(table, column).val)
        minimal_subset = FullAnalyzer.minimal_equidependent_subset(self.node, inner_keys, self.context.unique_column_tuples)
        assert(len(minimal_subset) > 0)
        return minimal_subset[0]
    
    def untranslated_inner_keys_from_center(self):
        """get what will be the group-by column ast_nodes in the inner scope after they are translated, if
           we are to to move the group-clause inside
           and then find a minimal subset of it that does not affect functional dependency
        """
        # all group-by columns of the form top_level_table.column
        inner_keys = []
        exact_outer_center_columns = set()
        for column in self.top_level.group_columns:
            if isinstance(column.exact_inner, tuple) and column.exact_inner[0] in self.outer_tables:
                exact_outer_center_columns.add(column.exact_inner)
            else:
                inner_keys.add(column.val)
        all_outer_columns_count = sum(len(self.context.columns[table]) for table in self.top_level.tables if table in self.outer_tables)
        dependent_columns = self.find_functionally_dependent_columns(exact_outer_center_columns)
        dependent_outer_columns = [(table, column) for (table, column) in dependent_columns if table in self.outer_tables]
        if len(dependent_outer_columns) == all_outer_columns_count:
            # group-by columns of the form outer_table.column is UCC for outer table
            inner_keys.extend(self.outer_columns_in_equalities())
        else:
            inner_keys.extend(Column.create(table, column).val for (table, column) in exact_outer_center_columns)
        minimal_subset = FullAnalyzer.minimal_equidependent_subset(self.node, inner_keys, self.context.unique_column_tuples)
        assert(len(minimal_subset) > 0)
        return minimal_subset[0]
    
    def prepare_for_push_in(self):
        """translate outer table columns to inner table columns, returns penalty (incurred when we can't translate some predicate)"""
        self.top_level.translate_targets(self.translate_map)
        penalty = self.top_level.translate_where_predicates(self.translate_map)
        penalty += self.remove_outer_table()
        return penalty
    
    
    def remove_outer_table(self):
        """remove outer table in FROM clause, return penalty"""
        if self.node.fromClause is None:
            return 0
        top_level = TopLevelAnalyzer(self.node)
        penalty = 0
        for outer_table in self.outer_tables:
            top_level.remove_table_from_join(outer_table)
        penalty += top_level.translate_join_on_dfs(self.node.fromClause[0], self.translate_map)
        return penalty
    
    def push_in_with_keys(self, keys: List[pglast.ast.Node]):
        """go into the inner scope with provided keys
           start links in translation_payload if it is None
        """
        root = deepcopy(self.node)
        # deduplicate 
        seen = set()
        new_links = {}
        for node in keys:
            translated = translate(node, self.translate_map)
            text_form = RawStream()(translated)
            if text_form not in seen:
                seen.add(text_form)
                new_links[RawStream()(node)] = translated
        if self.translation_payload.links is None:
            self.translation_payload.links = new_links
        root.groupClause = list(new_links.values())
        root.sortClause = None
        return root
        
        
             
    
if __name__ == "__main__":
    schema_file = "testschema.json"
    with open(schema_file) as file:
        schema = json.load(file)
    # sql = "SELECT 1 col FROM a INNER JOIN b ON a.id = b.id1 AND a.a1 = b.id2 INNER JOIN c ON a.id = c.id GROUP BY a.a1"
    # sql = "SELECT 1 col FROM a INNER JOIN b ON a.a1 = b.b1 WHERE a.id < b.id1 AND (CASE WHEN a.a1 < 3 THEN 1 ELSE 2 END) < 10 GROUP BY a.a1"
    # sql = "SELECT 1 col FROM a INNER JOIN b ON a.id = b.id1 AND b.id1 = b.id2 INNER JOIN c ON a.id = c.id GROUP BY a.id"
    sql = """SELECT a.id, a.a1 FROM a INNER JOIN b ON a.id = b.id1"""
    full_analyzer = FullAnalyzer(sql, schema)
    full_analyzer.find_hierarchy()
    full_analyzer.fill_columns_raw()
    # full_analyzer.unique_column_tuples["a"].append(["a1"])
    full_analyzer.fill_columns_dfs(TOP, [])
    table_ast_node = {table: node.ast_node for table, node in full_analyzer.table_node.items()}
    context = FullContext(
        table_ast_node, 
        full_analyzer.top_level_tables_inside, 
        full_analyzer.columns, 
        full_analyzer.unique_column_tuples, 
        full_analyzer.sublink_exterior_columns
    )
    node = context.table_node[TOP]
    phase2 = Phase2(node, context, ["b"])
    phase2.add_on_predicates_to_where(phase2.node)
    phase3 = Phase3(phase2.node, context, ["b"])
    phase3.construct_equality_graph(phase3.context.columns)
    if phase3.construct_translate_map():
        center_is_unique = phase3.check_center_is_unique()
        all_one_to_one = phase3.check_all_one_to_one()
        phase3.top_level.translate_targets(phase3.translate_map)
        print("where penalty =", phase3.top_level.translate_where_predicates(phase3.translate_map))
        print("from penalty =", phase3.remove_outer_table())
        print(RawStream()(phase3.node))
        if center_is_unique:
            root = phase3.push_in_with_keys(phase3.outer_columns_in_equalities())
            print("center is unique:", RawStream()(root))
        if all_one_to_one:
            root = phase3.push_in_with_keys(phase3.untranslated_inner_keys_from_center())
            print("all one to one:", RawStream()(root))
