import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
from top_level_analyzer import TopLevelAnalyzer
from common import find_involved_tables,connected_component_dfs, ast_BoolExpr
from full_analyzer import FullAnalyzer, FullContext, AGGREGATE_NAMES
from pglast.stream import RawStream

class Phase1:
    def __init__(self, node: pglast.ast.Node, context: FullContext):
        if not isinstance(node, pglast.ast.Node):
            raise Exception("ToplevelAnalyzer accepts ast.Node, not node.Node")
        self.node: pglast.ast.Node = node
        self.center_columns: list[tuple(str, str)] = None
        self.clusters: list[list[str]] = None
        self.context: FullContext = context
        self.top_level: TopLevelAnalyzer = TopLevelAnalyzer(self.node)
        # init
        self.top_level()
        self.top_level.replace_column_alias_usage()
        
        
    def find_center_columns(self):
        """fill in center_columns"""
        if self.node.groupClause is None:
            candidates = FullAnalyzer.cartesian_of_child_unique_tuples(
                self.top_level.tables,
                self.top_level.target_columns,
                context.unique_column_tuples
            )
            self.center_columns = candidates[0] if len(candidates) > 0 else []
        else:
            self.center_columns = [group_column.exact_inner for group_column in self.top_level.group_columns]
    
    def fetch_all_predicates(self):
        """fetch all predicates present in ON/WHERE clauses
        """
        class PredicateFetcher(Visitor):
            def __init__(self, predicates):
                self.predicates = predicates
            def visit_JoinExpr(self, _, node):
                if node.quals is not None and not isinstance(node.quals, pglast.ast.BoolExpr):
                    self.predicates.append(node.quals)
            def visit_BoolExpr(self, _, node):
                for arg in node.args:
                    if not isinstance(arg, pglast.ast.BoolExpr):
                        self.predicates.append(arg)
            def visit_RangeSubselect(self, _, node):
                return pglast.visitors.Skip()
            # do not consider sublink yet
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()
        predicates = []
        predicate_fetcher = PredicateFetcher(predicates)
        predicate_fetcher(self.node.fromClause[0])
        if self.node.whereClause is not None:
            if not isinstance(self.node.whereClause, pglast.ast.BoolExpr):
                predicates.append(self.node.whereClause)
            else:
                predicate_fetcher(self.node.whereClause)
        return predicates
            
    def find_clusters(self):
        """find clusters
           two side tables are in the same cluster iff there is a predicate that involve both
           assume center columns is filled
        """
        center_tables = set(table_column[0] for table_column in self.center_columns)
        side_tables = set(self.top_level.tables) - center_tables
        edges = {side_table: [] for side_table in side_tables}
        predicates = self.fetch_all_predicates()
        # construct edges
        for predicate in predicates:
            involved_tables = find_involved_tables(predicate)
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
        assert(len(self.top_level.target_columns) == 1)
        column = next(iter(self.top_level.target_columns))
        column_content = self.top_level.target_columns[column].val
        involved_tables = find_involved_tables(column_content)
        for cluster in self.clusters:
            if any(table in involved_tables for table in cluster):
                continue
            for table_name in cluster:
                self.remove_table_from_join(table_name)
                updated_where_clause = self.predicates_without_table_dfs(self.node.whereClause, table_name)
                self.node.whereClause = updated_where_clause

    def remove_table_from_join(self, table_name: str):
        """remove table table_name from JoinExpr in FROM clause"""
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
        remove_table_vistor(self.node)
    
    def predicates_without_table_dfs(self, node: pglast.ast.Node, table_name: str):
        """return a modified version of node that eliminates all predicates involving table_name"""
        node = pglast.node.Node(node)
        if node is Missing:
            return None
        if isinstance(node, pglast.node.Scalar):
            return node.value
        if node.node_tag != "BoolExpr":
            involved_tables = find_involved_tables(node.ast_node)
            return None if table_name in involved_tables else node.ast_node
        # node is BoolExpr
        args = [self.predicates_without_table_dfs(arg.ast_node, table_name) for arg in node.args]
        args = [arg for arg in args if arg is not None]
        return ast_BoolExpr(node.boolop.value, args)
    
    def check_idempotent(self):
        """check if the hole is idempotent, i.e. return same thing regardless of whether there is only one
           or more than one rows with same value in the fields it involves
        """
        funcCall = self.node.targetList[0].val
        assert(isinstance(funcCall, pglast.ast.FuncCall))
        assert(funcCall.funcname[0].val in AGGREGATE_NAMES)
        if funcCall.agg_distinct:
            return True
        involved_tables = find_involved_tables(node)
        irrelevant_cluster = 0
        for cluster in self.clusters:
            if all(table not in involved_tables for table in cluster):
                irrelevant_cluster += 1
        return irrelevant_cluster == 0
        

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

    phase1 = Phase1(node.ast_node, context)
    phase1.find_center_columns()
    phase1.find_clusters()
    print(phase1.center_columns, phase1.clusters)
    print("before", RawStream()(phase1.node))
    phase1.remove_irrelevant_clusters()
    print("after", RawStream()(phase1.node))
    print(phase1.check_idempotent())