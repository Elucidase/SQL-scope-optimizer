import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
from top_level_analyzer import Column, TopLevelAnalyzer, find_depending_columns, find_involved_tables
from full_analyzer import FullAnalyzer, FullContext, AGGREGATE_NAMES
import itertools
from typing import Dict, Set, Tuple
from pglast.stream import RawStream

class Phase1:
    def __init__(self, node: pglast.node.Node, context: FullContext):
        self.node = node
        self.center_columns = None
        self.side_tables = None
        self.clusters = None
        self.context = context
        self.analyzer = TopLevelAnalyzer(self.node)
        self.analyzer()
        self.analyzer.replace_column_alias_usage()
        
        
    def find_center_columns(self):
        """fill in center_columns"""
        if self.node.groupClause is Missing:
            candidates = FullAnalyzer.cartesian_of_child_unique_tuples(
                self.analyzer.tables,
                self.analyzer.target_columns,
                context.unique_column_tuples
            )
            self.center_columns = candidates[0] if len(candidates) > 0 else []
        else:
            self.center_columns = self.analyzer.center_exact_inner
            
    def find_clusters(self):
        """find clusters
           two side tables are in the same cluster iff there is a predicate that involve both
           assume center columns is filled
        """
        center_tables = set(table_column[0] for table_column in self.center_columns)
        side_tables = set(self.analyzer.tables) - center_tables
        edges = {side_table: [] for side_table in side_tables}
        predicates = self.analyzer.fetch_all_predicates()
        # construct edges
        for predicate in predicates:
            involved_tables = find_involved_tables(pglast.node.Node(predicate))
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
        """remove tables in irrelevant clusters from Join clause and all related predicates"""
        # only select one hole at a time
        assert(len(self.analyzer.target_columns) == 1)
        column = next(iter(self.analyzer.target_columns))
        column_content = self.analyzer.target_columns[column].val
        involved_tables = find_involved_tables(column_content)
        for cluster in self.clusters:
            if any(table in involved_tables for table in cluster):
                continue
            for table_name in cluster:
                self.remove_table_from_join(table_name)
                updated_where_clause = self.predicates_without_table_dfs(self.node.whereClause, table_name)
                self.node.ast_node.whereClause = updated_where_clause

    def remove_table_from_join(self, table_name: str):
        class RemoveTableVisitor(Visitor):
            def __init__(self, table_name):
                self.table_name = table_name
            def visit_JoinExpr(self, _, node):
                if isinstance(node.larg, pglast.ast.RangeVar):
                    rangeVar = node.larg
                    table_name = rangeVar.alias.aliasname if rangeVar.alias else rangeVar.relname
                    if table_name == self.table_name:
                        return node.rarg
                if isinstance(node.rarg, pglast.ast.RangeVar):
                    rangeVar = node.rarg
                    table_name = rangeVar.alias.aliasname if rangeVar.alias else rangeVar.relname
                    if table_name == self.table_name:
                        return node.larg
            def visit_RangeSubselect(self, _, node):
                return pglast.visitors.Skip()
            # do not consider sublink yet
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()
        remove_table_vistor = RemoveTableVisitor(table_name)
        remove_table_vistor(self.node.ast_node)
    
    def predicates_without_table_dfs(self, node: pglast.node.Node, table_name: str):
        if node is Missing:
            return None
        if isinstance(node, pglast.node.Scalar):
            return node.value
        if node.node_tag != "BoolExpr":
            involved_tables = find_involved_tables(node)
            return None if table_name in involved_tables else node.ast_node
        # node is BoolExpr
        args = [self.predicates_without_table_dfs(arg, table_name) for arg in node.args]
        args = [arg for arg in args if arg is not None]
        if len(args) == 0:
            return None
        elif len(args) == 1:
            NOT_EXPR = pglast.enums.primnodes.BoolExprType.NOT_EXPR
            if node.boolop.value == NOT_EXPR:
                return pglast.ast.BoolExpr(NOT_EXPR, args)
            else:
                return args[0]
        return pglast.ast.BoolExpr(node.boolop.value, args)
    
    def checkIdempotent(self):
        funcCall = self.node.targetList[0].val
        assert(funcCall.node_tag == "FuncCall")
        assert(funcCall.funcname[0].val.value in AGGREGATE_NAMES)
        if funcCall.agg_distinct:
            return True
        involved_tables = find_involved_tables(node)
        irrelevant_cluster = 0
        for cluster in self.clusters:
            if all(table not in involved_tables for table in cluster):
                irrelevant_cluster += 1
        return irrelevant_cluster == 0
        
        
        
def connected_component_dfs(vertex, edges: Dict[str, list], visited: Set, component: list):
    visited.add(vertex)
    component.append(vertex)
    for next in edges[vertex]:
        if next not in visited:
            connected_component_dfs(next, edges, visited, component)

if __name__ == "__main__":      
    schema_file = "phase1schema.json"
    # sql = """WITH cte AS (SELECT 1 as cst1, a.a1 as a1 FROM a) SELECT (SELECT 3 FROM d) k2, a2.a + 1 k2 FROM c c2 CROSS JOIN (SELECT * FROM a) as a2 WHERE EXISTS (SELECT 3 FROM d)"""
    sql = """SELECT
        COUNT(DISTINCT A.id, B.id) ab
    FROM I
        LEFT JOIN A
        ON I.x1 < A.a1
        INNER JOIN (
        B
        LEFT JOIN C
        ON I.x2 < C.c1
        CROSS JOIN E)
        ON B.b1 > A.a2
        LEFT JOIN D
        ON D.d1 = C.c2
        WHERE B.b1 >= A.a2 AND (A.a1 < A.a1 OR I.x2 < C.c1) OR NOT(D.d1 = C.c2 AND 1 AND B.id < 1 AND E.id = D.id)
    GROUP BY I.x"""

    root = pglast.node.Node(parse_sql(sql))
    node = root[0].stmt

    full_analyzer = FullAnalyzer(sql, schema_file)
    context = full_analyzer()

    phase1 = Phase1(node, context)
    phase1.find_center_columns()
    phase1.find_clusters()
    print(phase1.center_columns, phase1.clusters)
    print("before", RawStream()(phase1.node))
    phase1.remove_irrelevant_clusters()
    print("after", RawStream()(phase1.node))
    print(phase1.checkIdempotent())