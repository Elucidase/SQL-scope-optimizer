import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
from typing import Dict, Tuple
from pglast.enums.nodes import JoinType
from common import Column, check_null_sensitive_dfs, find_involved_tables, decompose_predicate, strongly_connected_components


# Assumptions
# SAFE: A column, when used, is table-qualified (i.e t.c) unless referring to an alias of a column in the current scope
# SAFT: A column, when declared in SELECT clause, has an alias unless it is exactly of form t.c
# REMEDIABLE: A group by column is exactly of form t.c
# REMEDIABLE: Sublink yet to be supported
    
class TopLevelAnalyzer:
    def __init__(self, node: pglast.node.Node):
        """
        Attributes:
        node (pglast.node.Node): current node
        tables (list[str]): list of top-level table names
        target_columns: dict: column_name -> Column object for those declared in SELECT
        center_exact_inner (list): for each group-by column, if column is t.c for some inner table t, then (t, c);
            else if column is a column in SELECT, then alias name; else None
        """
        self.node: pglast.node.Node = node
        self.tables: list[str] = None
        self.target_columns: Dict[str, Column] = None
        self.center_exact_inner: list[Tuple] = None
        
    def __call__(self):
        self.find_top_level_tables()
        self.find_target_columns()
        self.find_center_exact_inner()
                
    def set_top_level_tables(self, top_level_tables):
        self.tables = top_level_tables
        
    def set_target_columns(self, target_columns):
        self.target_columns = target_columns
    
    def find_top_level_tables(self):
        # fill_in top_level_tables
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
        visitor(self.node.ast_node)
        self.tables = visitor.top_level_tables
        return self.tables
    
    def find_target_columns(self):
        """fill in target_columns
           assume top_level_tables is filled 
        """
        result = {}
        # Assume after FullAnalyzer, there's no SELECT *
        for target in self.node.targetList:
            column_name = Column.resTarget_columnRef_name(target)
            result[column_name] = Column.fromResTarget(target)
        self.target_columns = result
        return self.target_columns
    
    def find_center_exact_inner(self):
        """fill in center_exact_inner, for select statement with group-by clause
           assume target_columns is filled 
        """
        group_by_columns = self.node.groupClause
        exact_inners = []
        # assume each group by column is either t.c or the name of a column in select clause
        for columnRef in group_by_columns:
            if columnRef.node_tag != "ColumnRef":
                print(f"Warning: GROUP BY complex expression ({columnRef}) not yet supported")
                exact_inners.append(None)
                continue
            if len(columnRef.fields) == 1:
                column_name = columnRef.fields[0].val.value
                if column_name not in self.target_columns:
                    raise Exception(f"column {column_name} not recognized")
                exact_inner = self.target_columns[column_name].exact_inner
                exact_inners.append(exact_inner if exact_inner else column_name)
            else:
                exact_inners.append(Column.columnRef_to_exact_inner(columnRef))
        self.center_exact_inner = exact_inners
        return self.center_exact_inner
    
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
            replace_visitor = ReplaceVisitor(column_name, column_obj.val.ast_node)
            replace_visitor(self.node.fromClause[0].ast_node)
            if self.node.whereClause is not Missing:
                replace_visitor(self.node.whereClause.ast_node)
    
    def find_safe_child_tables(self):
        """find null-clusters
           Assume no raw table contains a record with NULL in all its fields,
           so if a record of an intermediate table has NULL in all fields of a relation, 
           it must be due to LEFT/RIGHT/OUTER Joins.
           Suppose we obtained an intermediate table by joining existing tables, which
           we call them its child tables. We say a child table "safe" if no record of the
           intermediate table can have NULL in all fields belonging to this child table.
           We say there is a "null-edge" from table a to table b iff, 
           all ta fields are null implies all tb fields are NULL.
           A "null-cluster" is a strongly connected component in the graph constructed.
           We have the following:
           1. If there is a null-sensitive predicate in WHERE clause involving a child
           table, then this child table is safe. 
           2. If a child table is safe, all other child tables in the same null-cluster
           are also safe.
        """
        edges = {table: [] for table in self.tables}
        safety = self.construct_null_edges_from_join_dfs(self.node.fromClause[0], edges)
        # construct edges from WHERE clause
        predicates = decompose_predicate(self.node.whereClause)
        for predicate in predicates:
            if not check_null_sensitive_dfs(pglast.node.Node(predicate)):
                continue
            involved_tables = find_involved_tables(pglast.node.Node(predicate))
            # construct edges in both directions
            for table in involved_tables:
                safety[table] = True
                edges[table].extend(involved_tables - set([table]))
        # construct null-clusters
        components = strongly_connected_components(edges)
        safe_child_tables = []
        for component in components:
            if any(safety[table] for table in component):
                safe_child_tables.extend(component)
        return safe_child_tables  

    @staticmethod
    def construct_null_edges_from_join_dfs(node: pglast.node.Node, edges: Dict[str, list]):
        """add edges by examining ON predicates
           returns dict of table_name -> whether it is safe
        """
        if node.node_tag == "RangeVar":
            table_name = node.alias.aliasname.value if node.alias else node.relname.value
            return {table_name: True}
        elif node.node_tag == "RangeSubselect":
            table_name = node.alias.aliasname.value
            return {table_name: True}
        assert(node.node_tag == "JoinExpr")
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
        if node.quals is Missing or not check_null_sensitive_dfs(node.quals):
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
            if all(safety[table] for table in left_involved):
                for table in right_involved:
                    safety[table] = True
            if all(safety[table] for table in right_involved):
                for table in left_involved:
                    safety[table] = True
        return safety
                    
    
if __name__ == "__main__":           
    schema_file = "phase1schema.json"
    # sql = """SELECT a.a1 a1, a.a1 + b.b1 AS sum FROM (a cross join b) left join (SELECT c.c1 FROM c WHERE c.c1 = sum) c0 on abs(sum + c0.c1) where sum < 10 AND (sum < 9 OR sum < 8) AND sum + c0.c1 = 1"""
    sql = """SELECT
        COUNT(DISTINCT A.id, B.id) ab
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
    analyzer = TopLevelAnalyzer(node)
    analyzer()
    analyzer.replace_column_alias_usage()
    safe_child_tables = analyzer.find_safe_child_tables()
    print(safe_child_tables)

        