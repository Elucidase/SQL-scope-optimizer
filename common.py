import pglast
from pglast.enums.primnodes import BoolExprType
from pglast.visitors import Visitor
from pglast import Missing
from typing import Dict, Set, List
from pglast.stream import RawStream

TOP = "%top%"
AGGREGATE_NAMES = ["count", "sum", "min", "max", "avg"]

class Column:
    """
    Attributes:
        name: column name
        val: pglast.ast.Node expression for the column
        exact_inner: (table, name) if the column is exactly table.name where table is in a smaller scope; otherwise None
        dependsOn: list of columns this column depends on
        text_form: plain text representation used to check if two columns are obviously equal
    """
    def __repr__(self):
        string = self.name
        if self.exact_inner is not None:
            string += f"({self.exact_inner[0]}.{self.exact_inner[1]})" 
        return string
    
    @classmethod
    def create(cls, table_name: str, column: str):
        """Create a Column from table.column"""
        self = cls()
        self.name = column
        self.val = pglast.ast.ColumnRef(
            [pglast.ast.String(table_name), pglast.ast.String(column)]
        )
        self.exact_inner = (table_name, column)
        self.dependsOn = [self.exact_inner]
        self.text_form = RawStream()(self.val)
        return self
    
    @classmethod
    def from_ast_node(cls, ast_node: pglast.ast.Node, name: str):
        """Takes in a ast node"""
        self = cls()
        self.name = name
        self.val = ast_node
        self.exact_inner = None
        if isinstance(ast_node, pglast.ast.ColumnRef):
            self.exact_inner = cls.columnRef_to_exact_inner(ast_node)
        # columns it depends on
        self.dependsOn = find_depending_columns(ast_node)
        self.text_form = RawStream()(self.val)
        return self
    
    @staticmethod
    def name_from_resTarget(target: pglast.ast.ResTarget):
        """Find name of column from ResTarget whose val is ColumnRef"""
        if target.name is None:
            if isinstance(target.val, pglast.ast.ColumnRef):
                return target.val.fields[-1].val
            else:
                raise Exception(f"Please add alias to column {target.val}")
        else:
            return target.name
        
    @staticmethod
    def name_to_resTarget(table_name: str, column_name: str):
        fields = (pglast.ast.String(value=table_name), pglast.ast.String(value=column_name))
        columnRef = pglast.ast.ColumnRef(fields=fields)
        return pglast.ast.ResTarget(val=columnRef, name=column_name)
         
    
    @staticmethod
    def columnRef_to_exact_inner(columnRef: pglast.ast.ColumnRef):
        """Convert ColumnRef to (table, column)"""
        fields = columnRef.fields
        if len(fields) == 1:
            return fields[0].val
        else:
            return (fields[0].val, fields[1].val)
        
        
    @staticmethod
    def merge(lhs, rhs):
        result = Column()
        result.name = lhs.name
        left_list = lhs.val if isinstance(lhs.val, list) else [lhs.val]
        right_list = rhs.val if isinstance(rhs.val, list) else [rhs.val]
        result.val = left_list + right_list
        result.exact_inner = lhs.exact_inner if lhs.exact_inner == rhs.exact_inner else None
        result.dependsOn = lhs.dependsOn + rhs.dependsOn
        return result
    
class FullContext:
    def __init__(self, table_node, top_level_tables_inside, columns, unique_column_tuples):
        self.table_node: Dict[str, pglast.ast.Node] = table_node
        self.top_level_tables_inside: Dict[str, list] = top_level_tables_inside
        self.columns: Dict[str, Dict[str, Column]] = columns
        self.unique_column_tuples: Dict[str, list] = unique_column_tuples
        
class Counter:
    def __init__(self, initial: int = 0):
        self.counter = initial

    def count(self):
        self.counter += 1
        return self.counter

def find_depending_columns(ast_node: pglast.ast.Node):
    """Find all (table, column) in a node, not considering sublink"""
    class FindColumnVisitor(Visitor):
        def __init__(self):
            self.dependsOn = []
        def visit_ColumnRef(self, _, node):
            self.dependsOn.append(Column.columnRef_to_exact_inner(node))
        def visit_SubLink(self, _, node):
            return pglast.visitors.Skip()
    find_column_visitor = FindColumnVisitor()
    find_column_visitor(ast_node)
    return find_column_visitor.dependsOn

def find_involved_tables(ast_node: pglast.ast.Node) -> set:
    depending_columns = find_depending_columns(ast_node)
    return set(table_column[0] for table_column in depending_columns)
    
        
def connected_component_dfs(vertex, edges: Dict[str, list], visited: Set, component: list):
    visited.add(vertex)
    component.append(vertex)
    for next in edges[vertex]:
        if next not in visited:
            connected_component_dfs(next, edges, visited, component)
            
def reversed_graph(edges):
    edges_rev = {vertex: [] for vertex in edges}
    for vertex, to_list in edges.items():
        for to_vertex in to_list:
            edges_rev[to_vertex].append(vertex)
    return edges_rev
    
def strongly_connected_components(edges):
    # find reverse graph
    edges_rev = reversed_graph(edges)
    visited = set()
    topo_sort_order = []
    components = []
    def reverse_topo_sort_dfs(vertex):
        visited.add(vertex)
        for to_vertex in edges[vertex]:
            if to_vertex not in visited:
                reverse_topo_sort_dfs(to_vertex)
        topo_sort_order.append(vertex)
    def collect_component_dfs(vertex, component: list):
        visited.add(vertex)
        component.append(vertex)
        for to_vertex in edges_rev[vertex]:
            if to_vertex not in visited:
                collect_component_dfs(to_vertex, component)
    for vertex in edges:
        if vertex not in visited:
            reverse_topo_sort_dfs(vertex)
    topo_sort_order = reversed(topo_sort_order)
    visited = set()
    for vertex in topo_sort_order:
        if vertex not in visited:
            component = []
            collect_component_dfs(vertex, component)
            components.append(component)
    return components

def add_ast_node_to_select(root: pglast.ast.SelectStmt, ast_node: pglast.ast.Node, name: str):
    resTarget = pglast.ast.ResTarget(name=name, val=ast_node)
    targetList = list(root.targetList)
    targetList.append(resTarget)
    root.targetList = targetList
    

def ast_BoolExpr(boolop: BoolExprType, predicates: List):
    if len(predicates) == 0:
        return None
    elif len(predicates) == 1 and boolop is not BoolExprType.NOT_EXPR:
        return predicates[0]
    else:
        return pglast.ast.BoolExpr(boolop, predicates)

def add_predicates_to_where(root: pglast.ast.SelectStmt, predicates: List[pglast.ast.Node]):
    predicates_node = ast_BoolExpr(BoolExprType.AND_EXPR, predicates)
    if predicates_node is None:
        return
    if root.whereClause is None:
        root.whereClause = predicates_node
    else:
        conjunction = pglast.ast.BoolExpr(BoolExprType.AND_EXPR, [root.whereClause, predicates_node])
        root.whereClause = conjunction
        
def check_null_sensitive_dfs(node: pglast.node.Base):
    """check if a predicate is null-sensitive
       A predicate is null-sensitive if it does not evaluate to TRUE when any of its argument is NULL
       We can't really check that, but we check a sufficient condition
    """
    if node is Missing:
        return True
    if isinstance(node, pglast.node.Scalar):
        return True
    if isinstance(node, pglast.node.List):
        return all(check_null_sensitive_dfs(child) for child in node)
    # pglast.node.Node
    if node.node_tag == "A_Const":
        return True
    if node.node_tag == "ColumnRef":
        return True
    if node.node_tag == "A_Expr":
        return check_null_sensitive_dfs(node.lexpr) and check_null_sensitive_dfs(node.rexpr)
    if node.node_tag == "BoolExpr":
        return all(check_null_sensitive_dfs(arg) for arg in node.args)
    # anything else is False to be safe
    return False
        
def decompose_predicate(node: pglast.ast.Node):
    """decompose a predicate into a list of predicates that do not contain AND/OR/NOT"""
    if node is None:
        return []
    if not isinstance(node, pglast.ast.BoolExpr):
        return [node]
    class DecomposeVisitor(Visitor):
        def __init__(self):
            self.predicates = []
        def visit_BoolExpr(self, _, node):
            for arg in node.args:
                if not isinstance(arg, pglast.ast.BoolExpr):
                    self.predicates.append(arg)
        # do not consider sublink yet
        def visit_SubLink(self, _, node):
            return pglast.visitors.Skip()
    decompose_visitor = DecomposeVisitor()
    decompose_visitor(node)
    return decompose_visitor.predicates