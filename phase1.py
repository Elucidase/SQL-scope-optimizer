from copy import deepcopy
import json
import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
from top_level_analyzer import TopLevelAnalyzer
from common import Column, deduplicate_column_by_stream, find_involved_tables, connected_component_dfs, ast_BoolExpr, FullContext, AGGREGATE_NAMES, TOP
from full_analyzer import FullAnalyzer
from pglast.stream import RawStream
from typing import Dict
import itertools


class Phase1:
    def __init__(self, node: pglast.ast.Node, context: FullContext):
        if not isinstance(node, pglast.ast.Node):
            raise Exception("ToplevelAnalyzer accepts ast.Node, not node.Node")
        self.node: pglast.ast.Node = node
        self.context: FullContext = context
        self.top_level: TopLevelAnalyzer = TopLevelAnalyzer(self.node)
        self.center_tables: list[str] = None
        self.clusters: list[list[str]] = None
        self.relevant_clusters: list[list[str]] = None
        # init
        self.top_level()
        self.top_level.replace_column_alias_usage()

    def find_center_tables(self):
        """fill in center_tables"""
        if self.node.groupClause is None:
            self.center_tables = []
        else:
            center_tables = set()
            for group_column in self.top_level.group_columns:
                for table, column in group_column.dependsOn:
                    center_tables.add(table)
            self.center_tables = list(center_tables)

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
        center_tables = set(self.center_tables)
        side_tables = set(self.top_level.tables) - center_tables
        edges = {side_table: [] for side_table in side_tables}
        predicates = self.fetch_all_predicates()
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
        """
        # only select one hole at a time
        assert(len(self.top_level.target_columns) == 1)
        column = next(iter(self.top_level.target_columns))
        column_content = self.top_level.target_columns[column].val
        involved_tables = find_involved_tables(column_content, self.context.sublink_exterior_columns)
        self.relevant_clusters = []
        for cluster in self.clusters:
            if any(table in involved_tables for table in cluster):
                self.relevant_clusters.append(cluster)
                continue
            for table_name in cluster:
                self.top_level.remove_table_from_join(table_name)
                updated_where_clause = self.predicates_without_table_dfs(
                    pglast.node.Node(self.node).whereClause, table_name)
                self.node.whereClause = updated_where_clause

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

    def zoom_in_if_center_one_only(self):
        """if all side tables are irrelevant and have been removed and there is only one center table,
           then we zoom in to the center table
           returns true if this happens
           assume center_tables and relevant_clusters have been calculated
        """
        if len(self.center_tables) != 1 or len(self.relevant_clusters) > 0:
            return False
        center_table = self.center_tables[0]
        assert(len(self.top_level.target_columns) == 1)
        target_column = list(self.top_level.target_columns.values())[0]
        # replace each columnRef in the selected field with actual content in inner table
        # if the columnRef to be replaced is in agg function and the replacement contains another aggregate function, we can't proceed
        select_column_node = deepcopy(target_column.val)
        select_column_node, inner_has_aggregate, outer_has_aagregate = self.interpret_column_in_inner_scope(
            select_column_node, self.context.columns[center_table])
        if inner_has_aggregate and outer_has_aagregate:
            return False
        # construct new branch's select
        new_branch = deepcopy(self.context.table_node[center_table])
        if outer_has_aagregate and new_branch.distinctClause is not None:
            self.make_aggregate_distinct(select_column_node)
            new_branch.distinctClause = None
        new_branch.targetList = [pglast.ast.ResTarget(
            name=target_column.name, val=select_column_node)]
        # construct new branch's group by
        group_clause = []
        if new_branch.groupClause is not None:
            group_clause.extend(new_branch.groupClause)
        if len(self.top_level.group_columns) > 0:
            for column in self.top_level.group_columns:
                group_column_node, _, _ = self.interpret_column_in_inner_scope(
                    deepcopy(column.val), self.context.columns[center_table])
                group_clause.append(group_column_node)
        # deduplicate group by columns
        new_group_column_nodes = deduplicate_column_by_stream(group_clause)
        if len(new_group_column_nodes) > 0:
            new_branch.groupClause = new_group_column_nodes
        self.node = new_branch
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
        interpret_visitor = InterpretVisitor(columns)
        interpret_visitor(dummy_node)
        is_aggregate_visitor = IsAggregateVisitor()
        is_aggregate_visitor(dummy_node)
        return dummy_node.val, interpret_visitor.inner_has_aggregate, is_aggregate_visitor.is_aggregate

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
        remaining_tables = self.center_tables + relevant_side_tables
        edges = {table: [] for table in remaining_tables}
        predicates = self.fetch_all_predicates()
        # construct edges
        for predicate in predicates:
            involved_tables = find_involved_tables(predicate, self.context.sublink_exterior_columns)
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
            self.remove_table_from_join(table_name)
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
        funcCall = self.node.targetList[0].val
        assert(isinstance(funcCall, pglast.ast.FuncCall))
        assert(funcCall.funcname[0].val in AGGREGATE_NAMES)
        if funcCall.agg_distinct:
            return True
        involved_tables = find_involved_tables(node, self.context.sublink_exterior_columns)
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
    sql = """SELECT COUNT(a.id) c1 FROM a CROSS JOIN b CROSS JOIN c WHERE (SELECT id FROM c c2 WHERE c.id < c2.id) < 10"""
    with open(schema_file) as file:
        schema = json.load(file)

    full_analyzer = FullAnalyzer(sql, schema)
    context = full_analyzer()
    node = context.table_node[TOP]
    node.targetList = [node.targetList[0]]
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
