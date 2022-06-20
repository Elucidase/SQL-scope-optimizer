from copy import deepcopy
from fnmatch import translate
import itertools
import json
import pglast
from pglast import parser, parse_sql
from pglast.visitors import Visitor
from phase2 import Phase2
from top_level_analyzer import TopLevelAnalyzer
from common import TOP, Column, ast_BoolExpr, deduplicate_column_by_stream, find_involved_columns, connected_component_dfs, find_involved_tables
from full_analyzer import FullAnalyzer, FullContext
from pglast.stream import RawStream
from typing import Dict, Set, List, Tuple
from pglast.enums.primnodes import BoolExprType
from pglast.enums.nodes import JoinType

class Phase3:
    def __init__(self, node: pglast.ast.Node, context: FullContext, outer_tables: List[str]):
        if not isinstance(node, pglast.ast.Node):
            raise Exception("ToplevelAnalyzer accepts ast.Node, not node.Node")
        self.node: pglast.ast.Node = node
        self.context: FullContext = context
        self.top_level: TopLevelAnalyzer = TopLevelAnalyzer(self.node)
        self.outer_tables: list[str] = outer_tables
        self.equalities = None
        self.equality_graph: Dict[Tuple[str, str], List[Tuple[str, str]]] = None
        self.equality_cluster_of: Dict[Tuple[str, str], Set[Tuple[str, str]]] = None
        self.translate_map: Dict[Tuple[str, str], Tuple[str, str]] = None
        # init
        self.top_level()

    def construct_equality_graph(self):
        """build a graph with (top_level_table, column) as vertices, equalities as edges
        """
        # initialize graph
        self.equality_graph = {}
        self.equality_cluster_of = {}
        for table in self.top_level.tables:
            for column in self.context.columns[table]:
                self.equality_graph[(table, column)] = []
        if self.node.whereClause is None:
            return
        self.equalities = Phase3.find_all_equalities_dfs(self.node.whereClause)
        for vertex1, vertex2 in self.equalities:
            self.equality_graph[vertex1].append(vertex2)
            self.equality_graph[vertex2].append(vertex1)
        # build cluster cache
        visited = set()
        for table in self.top_level.tables:
            for column in self.context.columns[table]:
                if (table, column) in visited:
                    continue
                component = []
                connected_component_dfs((table, column), self.equality_graph, visited, component)
                component_set = set(component)
                for vertex in component:
                    self.equality_cluster_of[vertex] = component_set
    
    @staticmethod
    def find_all_equalities_dfs(node: pglast.ast.Node):
        """get all equalities that are conjuncts of WHERE clause"""
        if not isinstance(node, pglast.ast.BoolExpr):
            equality = Phase3.extract_node_equality(node)
            return [equality] if equality is not None else []
        if node.boolop is not BoolExprType.AND_EXPR:
            return []
        return list(itertools.chain(*[Phase3.find_all_equalities_dfs(conjunct) for conjunct in node.args]))
    
    @staticmethod
    def extract_node_equality(node: pglast.ast.Node):
        """if the node is A_Expr of the form t1.c1 = t2.c2, returns [(t1, c1), (t2, c2)]; otherwise None"""
        if not isinstance(node, pglast.ast.A_Expr):
            return None
        if node.name[0].val != "=":
            return None
        if not isinstance(node.lexpr, pglast.ast.ColumnRef) or not isinstance(node.rexpr, pglast.ast.ColumnRef):
            return None
        assert(len(node.lexpr.fields) == 2)
        assert(len(node.rexpr.fields) == 2)
        left_column = (node.lexpr.fields[0].val, node.lexpr.fields[1].val)
        right_column = (node.rexpr.fields[0].val, node.rexpr.fields[1].val)
        return (left_column, right_column)
    
    def find_functionally_dependent_columns(self, columns: Set[Tuple[str, str]]):
        """find all (top_level_table, column) that are functionally dependent on columns, taken equalities into account
           assume equality_graph has been constructed
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
           assume equality_graph has been constructed
        """
        result = set()
        for vertex in columns:
            result |= self.equality_cluster_of[vertex]
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
    
    def construct_translate_map(self):
        """find all outer columns we must translate into inner scope and construct
           a mapping: outer_column -> inner_column
        """
        self.translate_map = {}
        obliged_columns = find_involved_columns(self.node.targetList[0], self.context.sublink_exterior_columns)
        for column in self.top_level.group_columns:
            obliged_columns |= find_involved_columns(column.val, self.context.sublink_exterior_columns)
        for table in self.outer_tables:
            for column in self.context.columns[table]:
                cluster = self.equality_cluster_of[(table, column)]
                try:
                    mapped_to = next((table, column) for table, column in cluster if table not in self.outer_tables)
                    self.translate_map[(table, column)] = mapped_to
                except StopIteration:
                    self.translate_map[(table, column)] = None
                    if (table, column) in obliged_columns:
                        raise Exception(f"Cannot translate column {table}.{column} which we must translate")
            
    def translate(self, node: pglast.ast.Node):
        """replace outer table column into inner column
           if we cannot translate, return None
        """
        class InterpretVisitor(Visitor):
            def __init__(self, translate_map):
                self.translate_map = translate_map

            def visit_ColumnRef(self, _, node):
                assert(len(node.fields) == 2)
                column = Column.columnRef_to_exact_inner(node)
                if column in self.translate_map:
                    if self.translate_map[column] == None:
                        # cannot translate
                        raise Exception(f"Cannot translate column {table}.{column}")
                    inner_table, inner_column_name = self.translate_map[column]
                    return Column.create(inner_table, inner_column_name).val
                return None
            def visit_SortBy(self, _, node):
                return pglast.visitors.Skip()
        # dummy node needed to be able to replace itself entirely
        dummy_node = pglast.ast.ResTarget(val=node)
        interpret_visitor = InterpretVisitor(self.translate_map)
        try:
            interpret_visitor(dummy_node)
        except:
            return None
        return dummy_node.val
    
    def check_center_is_unique(self):
        """check if the tuple of group-by columns is unique
           assume equality_graph has been constructed
        """
        # all group-by columns of the form top_level_table.column
        exact_center_columns = set()
        for column in self.top_level.group_columns:
            if isinstance(column.exact_inner, tuple):
                exact_center_columns.add(column.exact_inner)
        all_columns_count = sum(len(self.context.columns[table]) for table in self.top_level.tables)
        functionally_dependent_columns = self.find_functionally_dependent_columns(exact_center_columns)
        return len(functionally_dependent_columns) == all_columns_count
    
    def check_all_one_to_one(self):
        """check if all joins are one-to-one joins
           assume equalities, equality_graph has been constructed
        """
        equality_columns = set()
        for column1, column2 in self.equalities:
            equality_columns.add(column1)
            equality_columns.add(column2)
        all_columns_count = sum(len(self.context.columns[table]) for table in self.top_level.tables)
        functionally_dependent_columns = self.find_functionally_dependent_columns(equality_columns)
        return len(functionally_dependent_columns) == all_columns_count
    
    def outer_columns_in_equalities(self):
        """get all column ast_nodes in the outer table that participate in at least one equality
           assume equality_graph has been construcuted
        """
        inner_keys = []
        for table in self.outer_tables:
            for column in self.context.columns[table]:
                if len(self.equality_graph[(table, column)]) > 0:
                    inner_keys.append(Column.create(table, column).val)
        return inner_keys
    
    def untranslated_inner_keys_from_center(self):
        """get what will be the group-by column ast_nodes in the inner scope after they are translated, if
           we are to to move the group-clause inside
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
        if len(self.find_functionally_dependent_columns(exact_outer_center_columns)) == all_outer_columns_count:
            # group-by columns of the form outer_table.column is UCC for outer table
            inner_keys.extend(self.outer_columns_in_equalities())
        else:
            inner_keys.extend(Column.create(table, column).val for (table, column) in exact_outer_center_columns)
        return inner_keys
    
    def translate_target(self):
        """replace target column with the translated one"""
        target_column = self.node.targetList[0]
        translated = self.translate(target_column.val)
        self.node.targetList = [pglast.ast.ResTarget(name=target_column.name, val=translated)]
        
    def translate_predicates(self):
        """replace outer table columns in whereClause with inner table columns; remove predicates we can't translate
           returns penalty, i.e. number of predicates we removed because we can't translate
           assume translated_map is constructed
        """
        if self.node.whereClause is None:
            return 0
        translated, penalty = self.translate_predicates_dfs(self.node.whereClause)
        self.node.whereClause = translated
        return penalty
        
    def translate_predicates_dfs(self, node: pglast.ast.Node):
        """returns translated_node, penalty; if we cannot translate node, translated_node will be None"""
        if not isinstance(node, pglast.ast.BoolExpr):
            translated = self.translate(node)
            if translated is None:
                return None, 1
            # special case: if after translation it is t.c = t.c, then ignore
            equality = self.extract_node_equality(translated)
            if equality is not None and equality[0] == equality[1]:
                return None, 0
            return translated, 0
        # node is BoolExpr
        translated_args = []
        penalty = 0
        for arg in node.args:
            arg_translated, arg_penalty = self.translate_predicates_dfs(arg)
            if arg_translated is not None:
                translated_args.append(arg_translated)
            penalty += arg_penalty
        translated = ast_BoolExpr(node.boolop, translated_args)
        return translated, penalty
    
    def remove_outer_table(self):
        """remove outer table in FROM clause, return penalty"""
        top_level_analyzer = TopLevelAnalyzer(self.node)
        penalty = 0
        for outer_table in self.outer_tables:
            top_level_analyzer.remove_table_from_join(outer_table)
        for outer_table in self.outer_tables:
            penalty += self.translate_join_on_dfs(self.node.fromClause[0])
        return penalty
            
    def translate_join_on_dfs(self, join: pglast.ast.JoinExpr):
        """translate on conditions and return penalty of translation"""
        if not isinstance(join, pglast.ast.JoinExpr):
            return 0
        penalty = 0
        penalty += self.translate_join_on_dfs(join.larg)
        penalty += self.translate_join_on_dfs(join.rarg)
        involved_tables = find_involved_tables(join.quals, self.context.sublink_exterior_columns)
        if all(table not in self.outer_tables for table in involved_tables):
            return penalty
        translated, my_penalty = self.translate_predicates_dfs(join.quals)
        join.quals = translated
        penalty += my_penalty
        if translated is None:
            # cross join
            join.jointype = JoinType.JOIN_INNER
        return penalty
    
    def push_in_with_keys(self, keys: List[pglast.ast.Node]):
        root = deepcopy(self.node)
        group_column_nodes = [self.translate(node) for node in keys]
        root.groupClause = deduplicate_column_by_stream(group_column_nodes)
        root.sortClause = None
        return root
        
        
             
    
if __name__ == "__main__":
    schema_file = "testschema.json"
    with open(schema_file) as file:
        schema = json.load(file)
    # sql = "SELECT 1 col FROM a INNER JOIN b ON a.id = b.id1 AND a.a1 = b.id2 INNER JOIN c ON a.id = c.id GROUP BY a.a1"
    sql = "SELECT 1 col FROM a INNER JOIN b ON a.a1 = b.b1 WHERE a.id < b.id1 AND (CASE WHEN a.a1 < 3 THEN 1 ELSE 2 END) < 10 GROUP BY a.a1"
    # sql = "SELECT 1 col FROM a INNER JOIN b ON a.id = b.id1 AND b.id1 = b.id2 INNER JOIN c ON a.id = c.id GROUP BY a.id"
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
    phase2 = Phase2(node, context, ["a"])
    phase2.add_on_predicates_to_where(phase2.node)
    phase3 = Phase3(phase2.node, context, ["a"])
    phase3.construct_equality_graph()
    print(phase3.check_center_is_unique())
    print(phase3.check_all_one_to_one())
    print(phase3.outer_columns_in_equalities())
    print(phase3.untranslated_inner_keys_from_center())
    try:
        phase3.construct_translate_map()
    except Exception as err:
        print(err)
        return
    center_is_unique = phase3.check_center_is_unique()
    all_one_to_one = phase3.check_all_one_to_one()
    phase3.translate_target()
    print("where penalty =", phase3.translate_predicates())
    print("from penalty =", phase3.remove_outer_table())
    print(RawStream()(phase3.node))
    if center_is_unique:
        root = phase3.push_in_with_keys(phase3.outer_columns_in_equalities())
        print("center is unique:", RawStream()(root))
    if all_one_to_one:
        root = phase3.push_in_with_keys(phase3.untranslated_inner_keys_from_center())
        print("all one to one:", RawStream()(root))