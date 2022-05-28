import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor


# Assumptions
# SAFE: A column, when used, is table-qualified (i.e t.c) unless referring to an alias of a column in the current scope
# SAFT: A column, when declared in SELECT clause, has an alias unless it is exactly of form t.c
# REMEDIABLE: A group by column is exactly of form t.c
# REMEDIABLE: Sublink yet to be supported


class Column:
    """
    Attributes:
        name: column name
        val: expression for the column
        exact_inner: (table, name) if the column is exactly table.name where table is in a smaller scope; otherwise None
        dependsOn: list of columns this column depends on
    """
    def __repr__(self):
        string = self.name
        if self.exact_inner is not None:
            string += f"({self.exact_inner[0]}.{self.exact_inner[1]})" 
        return string
    
    def find_depending_columns(self):
        """Find all ColumnRefs in the column expression
            Not considering SubLink
        """
        dependsOn = []
        for node in self.val.traverse():
            if isinstance(node, pglast.node.Node) and node.node_tag == "ColumnRef":
                dependsOn.append(Column.columnRef_to_exact_inner(node))
        return dependsOn
    
    @staticmethod
    def create(table_name: str, column: str):
        """Create a Column from table.column"""
        self = Column()
        self.name = column
        self.val = pglast.ast.ColumnRef(
            [pglast.ast.String(table_name), pglast.ast.String(column)]
        )
        self.exact_inner = (table_name, column)
        self.dependsOn = [self.exact_inner]
        return self
    
    @staticmethod
    def fromResTarget(node: pglast.node.Node):
        """Takes in a ResTarget"""
        self = Column()
        self.name = Column.resTarget_columnRef_name(node)
        self.val = node.val
        self.exact_inner = None
        if node.val.node_tag == "ColumnRef":
            self.exact_inner = Column.columnRef_to_exact_inner(node.val)
        # columns it depends on
        self.dependsOn = self.find_depending_columns()
        return self
    
    @staticmethod
    def resTarget_columnRef_name(target: pglast.node.Node):
        """Find name of column from ResTarget whose val is ColumnRef"""
        if target.name is Missing:
            if target.val.node_tag == "ColumnRef":
                return target.val.fields[-1].val.value
            else:
                raise Exception(f"Please add alias to column {target.val.ast_node}")
        else:
            return target.name.value
        
    @staticmethod
    def name_to_resTarget(table_name: str, column_name: str):
        fields = (pglast.ast.String(value=table_name), pglast.ast.String(value=column_name))
        columnRef = pglast.ast.ColumnRef(fields=fields)
        return pglast.ast.ResTarget(val=columnRef, name=column_name)
         
    
    @staticmethod
    def columnRef_to_exact_inner(node: pglast.node.Node):
        """Convert ColumnRef to (table, column)"""
        fields = node.fields
        if len(fields) < 2:
            raise Exception(f"column {fields[-1].val.value} need to be qualified with its table name")
        else:
            return (fields[0].val.value, fields[1].val.value)
        
        
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
        self.node = node
        self.tables = None
        self.target_columns = None
        self.center_exact_inner = None
        
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
        """fill in center_exact_inner
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
                    raise Exception(f"column {column_name} needs to be qualified with table name")
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
                
    def fetchAllPredicates(self):
        """fetch all predicates present in ON/WHERE clauses"""
        class PredicateVisitor(Visitor):
            def __init__(self):
                self.prediates = []
            def visit_JoinExpr(self):
                pass
        
            
    
    
if __name__ == "__main__":           
    schema_file = "testschema.json"
    # sql = """WITH cte AS (SELECT 1 as cst1, a.a1 as a1 FROM a) SELECT (SELECT 3 FROM d) k2, a2.a + 1 k2 FROM c c2 CROSS JOIN (SELECT * FROM a) as a2 WHERE EXISTS (SELECT 3 FROM d)"""
    sql = """SELECT a.a1 a1, a.a1 + b.b1 AS sum FROM (a cross join b) left join (SELECT c.c1 FROM c WHERE c.c1 = sum) c0 on sum = c0.c1 where sum < 10"""
    root = pglast.node.Node(parse_sql(sql))
    node = root[0].stmt
    analyzer = TopLevelAnalyzer(node)
    analyzer.find_target_columns()
    analyzer.replace_column_alias_usage()
    from pglast.stream import RawStream
    print(RawStream()(node))

        