import itertools
from typing import Dict, Tuple
import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
import json

TOP = "%top%"
AGGREGATE_NAMES = ["count", "sum", "min", "max", "avg"]
    
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
        self.val = pglast.ast.ColumnRef([table_name, column])
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
        
    
class BasicAnalyzer:
    """
    Attributes:
        table_node (Dict[str, pglast.node.Node]): table name -> node of subquery/cte
        top_level_tables_inside (Dict[str, list]): table name -> list of top-level tables directly inside
        columns (Dict[str, Dict[str, Column]]): table name -> dict from column name to Column object
        unique_column_tuples (Dict[str, list]): table name -> list of column names or combination of column names that are unique
        root (pglast.node.Node): root node
        schema (dict): parsed from json
        center_columns (list[list[Tuple[str, str]]]): possibilities for each center column
        holes (list[pglast.node.Node]): hole id -> function_call
    """
    def __init__(self, sql, schema_file):
        self.table_node: Dict[str, pglast.node.Node] = {}
        self.top_level_tables_inside: Dict[str, list] = {}
        self.columns: Dict[str, Dict[str, Column]] = {}
        self.unique_column_tuples: Dict[str, list] = {}
        self.root = pglast.Node(parse_sql(sql))
        with open(schema_file) as file:
            self.schema = json.load(file)
        self.center_columns = []
            
    def __call__(self):
        self.find_hierarchy()
        self.fill_columns_raw()
        self.fill_columns_dfs(TOP)
        self.find_center_columns()
        self.find_holes()

    def find_hierarchy(self):
        """fill in top_level_tables_inside and table_node"""
        self.find_hierarchy_dfs(self.root)
        self.fix_alias_hierarchy_dfs(TOP)
        

    def find_hierarchy_dfs(self, node: pglast.node.Base, stack: list = []):
        """fill in top_level_tables_inside and table_node for subqueries/CTE"""
        if isinstance(node, pglast.node.Scalar):
            return
        scope_name = ""
        # do not consider sublink yet
        sublink = False
        if isinstance(node, pglast.node.Node):
            if node.node_tag == "RangeVar":
                scope_name = node.alias.aliasname.value if node.alias else node.relname.value
                self.table_node[scope_name] = node
            elif node.node_tag == "RangeSubselect":
                scope_name = node.alias.aliasname.value
                self.table_node[scope_name] = node.subquery
            elif node.node_tag == "CommonTableExpr":
                scope_name = node.ctename.value
                self.table_node[scope_name] = node.ctequery
            elif node.node_tag == "RawStmt":
                scope_name = TOP
                self.table_node[scope_name] = node.stmt
            elif node.node_tag == "WithClause":
                # not in the main statement anymore
                stack = []
            elif node.node_tag == "SubLink":
                sublink = True
        if scope_name != "":
            self.top_level_tables_inside.setdefault(scope_name, [])
            if len(stack) > 0:
                self.top_level_tables_inside[stack[-1]].append(scope_name)
            stack.append(scope_name)
        for child in node:
            if not sublink:
                self.find_hierarchy_dfs(child, stack)
        if scope_name != "":
            del stack[-1]
    
    def fix_alias_hierarchy_dfs(self, table_name):
        """Assign hierachy to tables that are aliases"""
        node = self.table_node[table_name]
        if node.node_tag == "RangeVar":
            # table_name is alias for relname
            relname = node.relname.value
            if table_name == relname or relname not in self.table_node:
                # relname is a raw table
                self.top_level_tables_inside[table_name] = []
            else:
                self.fix_alias_hierarchy_dfs(relname)
                self.top_level_tables_inside[table_name] = self.top_level_tables_inside[relname]
        else:
            # node.node_tag == "SelectStmt"
            for table in self.top_level_tables_inside[table_name]:
                self.fix_alias_hierarchy_dfs(table)
            
    def fill_columns_raw(self):
        """fill columns and unique_column_tuples of raw tables"""
        for table in self.schema['Tables']:
            table_name = table['TableName']
            self.columns[table_name] = {}
            self.unique_column_tuples[table_name] = []
            for pkey in table['PKeys']:
                self.columns[table_name][pkey['Name']] = Column.create(table_name, pkey['Name'])
            self.unique_column_tuples[table_name].append(list(self.columns[table_name]))
            for fkey in table['FKeys']:
                if fkey['FName'] not in self.columns[table_name]:
                    self.columns[table_name][fkey['FName']] = Column.create(table_name, fkey['FName'])
            for other in table['Others']:
                self.columns[table_name][other['Name']] = Column.create(table_name, other['Name'])  
    
    def fill_columns_dfs(self, table_name):
        """fill columns and unique_column_tuples of intermediate tables"""
        node = self.table_node[table_name]
        # Case 1: RangeVar
        if node.node_tag == "RangeVar":
            # table_name is alias for relname
            relname = node.relname.value
            if table_name == relname:
                raise Exception(f"Raw table '{table_name}' not in spec!")
            if relname not in self.columns:
                self.fill_columns_dfs(relname)
            self.columns[table_name] = self.columns[relname]
            self.unique_column_tuples[table_name] = self.unique_column_tuples[relname]
            return
        # Case 2: SelectStmt
        top_level_tables = self.top_level_tables_inside[table_name]
        for top_level_table in top_level_tables:
            if top_level_table not in self.columns:
                self.fill_columns_dfs(top_level_table)
        
        self.fill_columns(table_name)
        self.fill_unique_column_tuples(table_name)
        if len(self.unique_column_tuples[table_name]) == 0:
            print("Warning: table", table_name, "has no primary key")

    def fill_columns(self, table_name):
        """helper function of fill_columns_dfs, fill columns for this table"""
        node = self.table_node[table_name]
        top_level_tables = self.top_level_tables_inside[table_name]
        # fill in columns
        # in case of set operations, i.e. UNION/INTERCECT/EXCEPT, analyze each
        # and combine the results
        self.columns[table_name] = self.fill_columns_combine_sets_dfs(node, top_level_tables)
        
        
    def fill_columns_combine_sets_dfs(self, node: pglast.node.Node, top_level_tables: list):
        """helper function of fill_column, combining results of single sets"""
        if node.op.value == pglast.enums.parsenodes.SetOperation.SETOP_NONE:
            return self.fill_columns_single_set(node, top_level_tables)
        left = self.fill_columns_combine_sets_dfs(node.larg, top_level_tables)
        right = self.fill_columns_combine_sets_dfs(node.rarg, top_level_tables)
        # column list should be same length
        assert(len(left) == len(right))
        # rely on the fact that dict type maintains insertion order by default
        result = {}
        left_names = list(left)
        right_names = list(right)
        for i, left_name in enumerate(left_names):
            right_name = right_names[i]
            result[left_name] = Column.merge(left[left_name], right[right_name])
        return result
        
    
    def fill_columns_single_set(self, node: pglast.node.Node, top_level_tables: list):
        """helper function of fill_column, handle the case of no set operation"""
        result = {}
        firstVal = node.targetList[0].val
        if firstVal.node_tag == "ColumnRef" and isinstance(firstVal.fields[0].ast_node, pglast.ast.A_Star):
            # SELECT *, all columns from all tables
            for top_level_table in top_level_tables:
                for column in self.columns[top_level_table]:
                    result[column] = Column.create(top_level_table, column)
        else:
            for target in node.targetList:
                column_name = Column.resTarget_columnRef_name(target)
                result[column_name] = Column.fromResTarget(target)
        return result

    def fill_unique_column_tuples(self, table_name):
        """helper function of fill_columns_dfs, fill unique_column_tuples for this table"""
        node = self.table_node[table_name]
        top_level_tables = self.top_level_tables_inside[table_name]
        self.unique_column_tuples[table_name] = []
        # find all columns that are directly from a children table
        inner_columns = {}
        for column_name, column_obj in self.columns[table_name].items():
            if column_obj.exact_inner:
                inner_columns[column_obj.exact_inner] = column_name
        # fill in unique_column_tuples
        if node.distinctClause is not Missing:
            self.unique_column_tuples[table_name] = [list(self.columns[table_name])]
        elif node.op.value == pglast.enums.parsenodes.SetOperation.SETOP_UNION:
            # union removes duplicates
            self.unique_column_tuples[table_name] = [list(self.columns[table_name])]
        elif node.groupClause is not Missing:
            group_by_columns = node.groupClause
            tabled_group_by_columns = []
            result_tuple = []
            # assume each gruop by column is either t.c or the name of a column in select clause
            for columnRef in group_by_columns:
                if len(columnRef.fields) == 1:
                    column_name = columnRef.fields[0].val.value
                    exact_inner = self.column_object(table_name, column_name).exact_inner
                    if exact_inner is None:
                        # columns that are not a column of an inner table
                        result_tuple.append(column_name)
                    else:
                        tabled_group_by_columns.append(exact_inner)
                else:
                    tabled_group_by_columns.append(Column.columnRef_to_exact_inner(columnRef))
            # for columns belonging to the same child table, try to eliminate unnecessary columns with unique info
            tabled_group_by_columns.sort(key = lambda table_column: table_column[0])
            by_table = itertools.groupby(tabled_group_by_columns, lambda table_column: table_column[0])
            by_table = {table: [table_column[1] for table_column in table_columns] for table, table_columns in by_table}
            for table in by_table:
                for unique_tuple in self.unique_column_tuples[table]:
                    if all(column_name in by_table[table] for column_name in unique_tuple):
                        by_table[table] = unique_tuple
                        break
                # convert it back to columns present in select clause and add to result
                for column_name in by_table[table]:
                    column = (table, column_name)
                    if column not in inner_columns:
                        print("Warning: table", table_name, "group-by column", column_name, "not selected")
                        return
                    else:
                        result_tuple.append(inner_columns[column])
            self.unique_column_tuples[table_name] = [result_tuple]
        else: 
            # nothing to guarentee uniqueness, so we use the cartesian product of child unique tuples
            uniques_of_children = []
            for table in top_level_tables:
                tabled_unique_tuples = []
                for unique_column_tuple in self.unique_column_tuples[table]:
                    tabled_unique_tuples.append([(table, column) for column in unique_column_tuple])
                uniques_of_children.append(tabled_unique_tuples)
            # a column tuple that contains a unique column (tuple) for each child table is unique
            # so we take Cartesian product of the unique column (tuple) of children tables
            product = itertools.product(*uniques_of_children)
            candidate_tuples = [list(itertools.chain.from_iterable(cols)) for cols in product]
            for candidate_tuple in candidate_tuples:
                if all(column in inner_columns for column in candidate_tuple):
                    candidate_tuple = [inner_columns[column] for column in candidate_tuple]
                    self.unique_column_tuples[table_name].append(candidate_tuple)
                    
    def column_object(self, table_name: str, column_name: str):
        """return Column object for table_name.column_name"""
        if column_name not in self.columns[table_name]:
            raise Exception(f"column {column_name} needs to be qualified with table name")
        return self.columns[table_name][column_name]
    
    def find_center_columns(self):
        """find center_columns"""
        self.center_columns = []
        top = self.table_node[TOP]
        if top.groupClause is Missing:
            unique_tuples = self.unique_column_tuples[TOP]
            self.center_columns = unique_tuples[0] if len(unique_tuples) > 0 else []
            return
        group_by_columns = top.groupClause
        # assume each gruop by column is either t.c or the name of a column in select clause
        for columnRef in group_by_columns:
            if len(columnRef.fields) == 1:
                column_name = columnRef.fields[-1].val.value
                exact_inner = self.column_object(TOP, column_name).exact_inner
            else:
                exact_inner = Column.columnRef_to_exact_inner(columnRef)
            sources = self.trace_column_to_raw_dfs(exact_inner)
            self.center_columns.append(sorted(set(sources)))
            
                
    def trace_column_to_raw_dfs(self, exact_inner: Tuple[str, str]):
        """helper function of find_center_columns"""
        scope, name = exact_inner
        column = self.column_object(*exact_inner)
        columns_to_explore = []
        if column.exact_inner is not None:
            if len(self.top_level_tables_inside[scope]) == 0:
                # reached raw table
                return [column.exact_inner]
            columns_to_explore = [column.exact_inner]
        else: 
            print(f"Warning: Column {name} is not exactly a column from an inner table")
            columns_to_explore = column.dependsOn
        result = []
        for inner_column in columns_to_explore:
            result.extend(self.trace_column_to_raw_dfs(inner_column))
        return result
        
    def find_holes(self):
        """Find all holes"""
        top = self.table_node[TOP]
        self.holes = []
        # assume top-level select statement does not have set operation
        if top.op.value != pglast.enums.parsenodes.SetOperation.SETOP_NONE:
            raise Exception("Run this algorithm on each top-level set (e.g. component of UNION)!")
        class HoleVisitor(Visitor):
            def __init__(self, holes):
                self.holes = holes
            def visit_FuncCall(self, _, node):
                if node.funcname[0].val in AGGREGATE_NAMES:
                    self.holes.append(node)
            def visit_FromClause(self):
                return pglast.visitors.Skip()   
            def visit_WithClause(self):
                return pglast.visitors.Skip()  
            # do not consider SubLink yet
            def visit_SubLink(self):
                return pglast.visitors.Skip()    
        visitor = HoleVisitor(self.holes)
        visitor(top.ast_node)
            
    
    
if __name__ == "__main__":           
    schema_file = "1212schema.json"
    # sql = """WITH cte AS (SELECT 1 as cst1, a.a1 as a1 FROM a) SELECT (SELECT 3 FROM d) k2, a2.a + 1 k2 FROM c c2 CROSS JOIN (SELECT * FROM a) as a2 WHERE EXISTS (SELECT 3 FROM d)"""
    sql = """SELECT  t.team_id
       ,t.team_name
       ,(SUM(CASE WHEN ((t.team_id = m.host_team) AND (m.host_goals > m.guest_goals)) OR ((t.team_id = m.guest_team) AND (m.host_goals < m.guest_goals)) THEN 3 ELSE 0 END)) + (SUM(CASE WHEN ((t.team_id = m.host_team) AND (m.host_goals = m.guest_goals)) OR ((t.team_id = m.guest_team) AND (m.host_goals = m.guest_goals)) THEN 1 ELSE 0 END)) AS num_points
FROM Teams AS t
CROSS JOIN Matches AS m
GROUP BY  t.team_id
         ,t.team_name
ORDER BY num_points DESC
         ,t.team_id ASC"""
    analyzer = BasicAnalyzer(sql, schema_file)
    analyzer()
    print(analyzer.center_columns)
    for hole in analyzer.holes:
        print(hole, "\n")
