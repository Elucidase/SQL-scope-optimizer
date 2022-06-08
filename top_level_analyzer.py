import pglast
from pglast import parse_sql
from pglast.visitors import Visitor
from typing import Dict, Tuple
from pglast.enums.nodes import JoinType
from prometheus_client import Counter
from common import Column, check_null_sensitive_dfs, find_involved_tables, decompose_predicate, reversed_graph, AGGREGATE_NAMES, Counter


# Assumptions
# REMEDIABLE: Sublink yet to be supported
    
class TopLevelAnalyzer:
    def __init__(self, node: pglast.ast.Node):
        """
        Attributes:
        node (pglast.ast.Node): current node
        tables (list[str]): list of top-level table names
        target_columns: dict: column_name -> Column object for those declared in SELECT
        center_exact_inner (list): for each group-by column, if column is t.c for some inner table t, then (t, c);
            else if column is a column in SELECT, then alias name; else None
        """
        if not isinstance(node, pglast.ast.Node):
            raise Exception("ToplevelAnalyzer accepts ast.Node, not node.Node")
        self.node: pglast.ast.Node = node
        self.tables: list[str] = None
        self.target_columns: Dict[str, Column] = None
        self.group_columns: list[Column] = None
        
    def __call__(self):
        self.find_top_level_tables()
        self.find_target_columns()
        self.find_group_columns()
        
                
    def set_top_level_tables(self, top_level_tables):
        self.tables = top_level_tables
        
    def set_target_columns(self, target_columns):
        self.target_columns = target_columns
    
    def find_top_level_tables(self):
        """fill_in top_level_tables"""
        class TopLevelTableVisitor(Visitor):
            def __init__(self):
                self.top_level_tables = []
            def visit_RangeVar(self, _, node):
                name = node.alias.aliasname if node.alias else node.relname
                self.top_level_tables.append(name)
            def visit_RangeSubselect(self, _, node):
                self.top_level_tables.append(node.alias.aliasname)
                return pglast.visitors.Skip()
            # do not consider SubLink yet
            def visit_SubLink(self):
                return pglast.visitors.Skip()
        visitor = TopLevelTableVisitor()
        visitor(self.node)
        self.tables = visitor.top_level_tables
        return self.tables
    
    def find_target_columns(self):
        """fill in target_columns
           assume top_level_tables is filled 
        """
        result = {}
        # Assume after FullAnalyzer, there's no SELECT *
        for target in self.node.targetList:
            column_name = Column.name_from_resTarget(target)
            result[column_name] = Column.from_ast_node(target.val, column_name)
        self.target_columns = result
        return self.target_columns
    
    def find_group_columns(self):
        """fill in center_exact_inner, for select statement with group-by clause
           assume target_columns is filled 
        """
        self.group_columns = []
        if self.node.groupClause is None:
            return
        group_by_columns = self.node.groupClause
        # assume each group by column is either t.c or the name of a column in select clause
        for ast_node in group_by_columns:
            group_column = Column.from_ast_node(ast_node, "")
            # check content to see this group-by column is a select column
            if group_column.exact_inner is None:
                for target_name, target_column in self.target_columns.items():
                    if group_column.text_form == target_column.text_form:
                        group_column.exact_inner = target_name
                        break
            # if this group-by column is a select column, check if the select column has exact_inner
            if isinstance(group_column.exact_inner, str):
                if group_column.exact_inner not in self.target_columns:
                    raise Exception(f"Can't recognize column {group_column.exact_inner}")
                target_exact_inner = self.target_columns[group_column.exact_inner].exact_inner
                if target_exact_inner is not None:
                    group_column.exact_inner = target_exact_inner
            self.group_columns.append(group_column)
        return self.group_columns
    
    def replace_column_alias_usage(self):
        """replace each reference to a column alias (defined in SELECT clause) in an ON/WHERE clause with actual content
           assume target_columns is filled
        """
        class ReplaceVisitor(Visitor):
            def __init__(self, column_name: str, ast_expr: pglast.ast.A_Expr):
                self.column_name = column_name
                self.ast_expr = ast_expr
            def visit_ColumnRef(self, ancestor, node):
                if len(node.fields) == 1 and node.fields[0].val == self.column_name:
                    return self.ast_expr
                return None
            def visit_RangeSubselect(self, _, node):
                return pglast.visitors.Skip()
            # do not consider sublink yet
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip() 
        for column_name, column_obj in self.target_columns.items():
            replace_visitor = ReplaceVisitor(column_name, column_obj.val)
            replace_visitor(self.node.fromClause[0])
            if self.node.whereClause is not None:
                replace_visitor(self.node.whereClause)
    
    def find_null_graph_and_safety(self):
        """find null-graph
           Assume no raw table contains a record with NULL in all its fields,
           so if a record of an intermediate table has NULL in all fields of a relation, 
           it must be due to LEFT/RIGHT/OUTER Joins.
           Suppose we obtained an intermediate table by joining existing tables, which
           we call them its child tables. We say a child table "safe" if no record of the
           intermediate table can have NULL in all fields belonging to this child table.
           We say there is a "null-edge" from table a to table b iff, 
           all ta fields are null implies all tb fields are NULL.
           1. If there is a null-sensitive predicate in WHERE clause or ON clause of an
           INNER JOIN involving a child table, then this child table is safe. 
           2. If there is a null edge from child table ta to child table tb and tb is safe,
           then ta is also safe. Specifically, tables in a null-cluster are either all 
           safe or all unsafe. 
           3. If we view joins as a binary tree, then given a safe table (leaf), the join
           each of its ancestors (including itself) participates in can be transformed to an
           LEFT or INNER JOIN where the said ancestor acts as the left side of the join. 
        """
        edges = {table: [] for table in self.tables}
        safety = self.construct_null_edges_from_join_dfs(self.node.fromClause[0], edges)
        # construct edges from WHERE clause
        predicates = decompose_predicate(self.node.whereClause)
        for predicate in predicates:
            if not check_null_sensitive_dfs(pglast.node.Node(predicate)):
                continue
            involved_tables = find_involved_tables(predicate)
            # construct edges in both directions
            for table in involved_tables:
                safety[table] = True
                edges[table].extend(involved_tables - set([table]))
        TopLevelAnalyzer.populate_safety(edges, safety)
        return edges, safety
    
    @staticmethod
    def populate_safety(edges, safety):
        """infer more tables to be safe"""
        edges_reversed = reversed_graph(edges)
        visited = set()
        def populate_safety_dfs(vertex):
            visited.add(vertex)
            safety[vertex] = True
            for to_vertex in edges_reversed[vertex]:
                if to_vertex not in visited:
                    populate_safety_dfs(to_vertex)
        for table in edges_reversed:
            if safety[table] and table not in visited:
                populate_safety_dfs(table)

    @staticmethod
    def construct_null_edges_from_join_dfs(node: pglast.ast.Node, edges: Dict[str, list]):
        """add edges by examining ON predicates
           returns dict of table_name -> whether it is safe
        """
        if isinstance(node, pglast.ast.RangeVar):
            table_name = node.alias.aliasname if node.alias else node.relname
            return {table_name: True}
        elif isinstance(node, pglast.ast.RangeSubselect):
            table_name = node.alias.aliasname
            return {table_name: True}
        assert(isinstance(node, pglast.ast.JoinExpr))
        left_safety = TopLevelAnalyzer.construct_null_edges_from_join_dfs(node.larg, edges)
        right_safety = TopLevelAnalyzer.construct_null_edges_from_join_dfs(node.rarg, edges)
        safety = {**left_safety, **right_safety}
        # left/right/full join may cause tables to become unsafe
        if node.jointype in (JoinType.JOIN_LEFT, JoinType.JOIN_FULL):
            for table in right_safety:
                safety[table] = False
        if node.jointype in (JoinType.JOIN_RIGHT, JoinType.JOIN_FULL):
            for table in left_safety:
                safety[table] = False
        # null-sensitive predicate in ON can help with null-graph and safety
        if node.quals is None or not check_null_sensitive_dfs(pglast.node.Node(node.quals)):
            return safety
        involved_tables = find_involved_tables(node.quals)
        left_involved = [table for table in involved_tables if table in left_safety]
        right_involved = [table for table in involved_tables if table in right_safety]
        # ta -> tb means (all ta fields are null implies all tb fields are NULL)
        if node.jointype in (JoinType.JOIN_LEFT, JoinType.JOIN_INNER):
            for table in left_involved:
                edges[table].extend(right_safety)
        if node.jointype in (JoinType.JOIN_RIGHT, JoinType.JOIN_INNER):
            for table in right_involved:
                edges[table].extend(left_safety)
        if node.jointype is JoinType.JOIN_INNER:
            for table in involved_tables:
                safety[table] = True
        return safety
    
    def find_holes(self):
        """Find all holes"""
        # assume top-level select statement does not have set operation
        if self.node.op.value != pglast.enums.parsenodes.SetOperation.SETOP_NONE:
            raise Exception("Can only find holes for select statements without top-level set operation")
        class HoleVisitor(Visitor):
            def __init__(self):
                self.counter = Counter(-1)
                self.holes = []
            def visit_FuncCall(self, _, node):
                if node.funcname[0].val in AGGREGATE_NAMES:
                    self.holes.append(node)
                # record this is the nth hole
                node.location = self.counter.count()
            def visit_WithClause(self, _, node):
                return pglast.visitors.Skip()
            def visit_RangeSubselect(self, _, node):
                return pglast.visitors.Skip()
            # do not consider SubLink yet
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()    
        hole_visitor = HoleVisitor()
        hole_visitor(self.node)
        return hole_visitor.holes
        
    
if __name__ == "__main__":           
    schema_file = "phase1schema.json"
    # sql = """SELECT a.a1 a1, a.a1 + b.b1 AS sum FROM (a cross join b) left join (SELECT c.c1 FROM c WHERE c.c1 = sum) c0 on abs(sum + c0.c1) where sum < 10 AND (sum < 9 OR sum < 8) AND sum + c0.c1 = 1"""
    sql = """SELECT
        COUNT(DISTINCT A.id, B.id) ab,
        MAX(D.d1) cd
    FROM I
        LEFT JOIN A
        ON I.x1 < A.a1
        INNER JOIN (
        B
        LEFT JOIN C
        ON B.x2 < C.c1
        CROSS JOIN E)
        ON B.b1 > A.a2
        LEFT JOIN D
        ON D.d1 = C.c2

    GROUP BY I.x"""
    #         WHERE B.b1 >= A.a2 AND (A.a1 < A.a1 OR I.x2 < C.c1) OR NOT(D.d1 = C.c2 AND 1 AND B.id < 1 AND E.id = D.id)
    root = pglast.node.Node(parse_sql(sql))
    node = root[0].stmt
    analyzer = TopLevelAnalyzer(node.ast_node)
    analyzer()
    analyzer.replace_column_alias_usage()
    edges, safety = analyzer.find_null_graph_and_safety()
    holes = analyzer.find_holes()
    print(analyzer.node.targetList[1].val.location)

        