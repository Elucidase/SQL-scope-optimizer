import itertools
import copy
from typing import Dict, Tuple
import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
import json
from top_level_analyzer import Column, TopLevelAnalyzer

TOP = "%top%"
AGGREGATE_NAMES = ["count", "sum", "min", "max", "avg"]

# Assumptions
# REMEDIABLE: A group by column is exactly of form t.c
# REMEDIABLE: Sublink yet to be supported

class FullContext:
    def __init__(self, top_level_tables_inside, columns, unique_column_tuples):
        self.top_level_tables_inside: Dict[str, list] = top_level_tables_inside
        self.columns: Dict[str, Dict[str, Column]] = columns
        self.unique_column_tuples: Dict[str, list] = unique_column_tuples

class FullAnalyzer:
    """
    Attributes:
        table_node (Dict[str, pglast.node.Node]): table name -> node of subquery/cte
        top_level_tables_inside (Dict[str, list]): table name -> list of top-level tables directly inside
        columns (Dict[str, Dict[str, Column]]): table name -> dict from column name to Column object
        unique_column_tuples (Dict[str, list]): table name -> list of column names or combination of column names that are unique
        root (pglast.node.Node): root node
        schema (str): json file name
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
        return FullContext(self.top_level_tables_inside, self.columns, self.unique_column_tuples)

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
        """fill columns and unique_column_tuples of intermediate tables
           SIDE EFFECTS:
           replace SELECT * with actual columns
           qualify columns with the inner tables they come from 
        """
        if table_name not in self.table_node:
            raise Exception(f"Table {table_name} can't be resolved. Check schema.")
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
        """fill in target_columns for the current scope
           replace SELECT * with actual columns
           qualify columns with the inner tables they come from
        """
        firstVal = node.targetList[0].val
        # if SELECT *, then SELECT all columns from all inner tables
        if firstVal.node_tag == "ColumnRef" and isinstance(firstVal.fields[0].ast_node, pglast.ast.A_Star):
            new_target_list = []
            for top_level_table in top_level_tables:
                for column in self.columns[top_level_table]:
                    new_target_list.append(Column.name_to_resTarget(top_level_table, column))
            node.ast_node.targetList = new_target_list
        self.qualify_columns_from_inner_table(node, top_level_tables)
        result = {}
        for target in node.targetList:
            column_name = Column.resTarget_columnRef_name(target)
            result[column_name] = Column.fromResTarget(target)
        return result
    
    def qualify_columns_from_inner_table(self, node: pglast.node.Node, top_level_tables: list):
        """qualify columns with the inner tables they come from, i.e. c -> t.c"""
        # column name from inner table -> ColumnRef with fields (inner table, column)
        qualified_columnRef = {}
        for top_level_table in top_level_tables:
            for column in self.columns[top_level_table]:
                qualified_columnRef[column] = Column.create(top_level_table, column).val
                
        class QualifyVisitor(Visitor):
            def __init__(self, qualified_columnRef):
                self.qualified_columnRef = qualified_columnRef
            def visit_ColumnRef(self, ancestor, node):
                if len(node.fields) == 1 and node.fields[0].val in self.qualified_columnRef:
                    column = node.fields[0].val
                    return self.qualified_columnRef[column]
                return None
            def visit_RangeSubselect(self, _, node):
                return pglast.visitors.Skip()
            # do not consider sublink yet
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip() 
        qualify_visitor = QualifyVisitor(qualified_columnRef)
        qualify_visitor(node.ast_node)
        

    def fill_unique_column_tuples(self, table_name):
        """helper function of fill_columns_dfs, fill unique_column_tuples for this table"""
        node = self.table_node[table_name]
        self.unique_column_tuples[table_name] = []
                    # find all columns that are directly from a children table
        inner_columns = {}
        for column_name, column_obj in self.columns[table_name].items():
            if column_obj.exact_inner:
                inner_columns[column_obj.exact_inner] = column_name
        # fill in unique_column_tuples
        if node.groupClause is not Missing:
            cartesian_components = []
            # t.c if a group-by column is column c of an inner table t, None otherwise 
            top_level_analyzer = TopLevelAnalyzer(node)
            top_level_analyzer.set_target_columns(self.columns[table_name])
            exact_inners = top_level_analyzer.find_center_exact_inner()
            for exact_inner in exact_inners:
                if isinstance(exact_inner, str):
                    # not an inner column, but is a select column
                    cartesian_components.append([exact_inner])
                elif exact_inner is None:
                    # some bad expression
                    cartesian_components.append([])
            # for exact group-by columns belonging to the same child table, try to eliminate some with unique info
            # i.e. find all child unique tuples for each child table that is a subset of the group-by columns
            exact_inners = [exact_inner for exact_inner in exact_inners if isinstance(exact_inner, Tuple)]
            exact_inners.sort(key = lambda table_column: table_column[0])
            by_table = itertools.groupby(exact_inners, lambda table_column: table_column[0])
            by_table = {table: [table_column[1] for table_column in table_columns] for table, table_columns in by_table}
            for table in by_table:
                cartesian_component = []
                group_columns = by_table[table]
                for unique_tuple in self.unique_column_tuples[table]:
                    if all(column in group_columns for column in unique_tuple) and \
                        all((table, column) in inner_columns for column in unique_tuple):
                        # convert it back to columns present in select clause and add to result
                        cartesian_component.append([inner_columns[(table, column)] for column in unique_tuple])
                # can't simplify, try default
                if len(cartesian_component) == 0:
                    if all((table, column) in inner_columns for column in group_columns):
                        cartesian_component.append([inner_columns[(table, column)] for column in group_columns])
                cartesian_components.append(cartesian_component)
            product = itertools.product(*cartesian_components)
            self.unique_column_tuples[table_name] = [list(itertools.chain.from_iterable(cols)) for cols in product]
        elif node.distinctClause is not Missing:
            self.unique_column_tuples[table_name] = [list(self.columns[table_name])]
        elif node.op.value == pglast.enums.parsenodes.SetOperation.SETOP_UNION:
            # union removes duplicates
            self.unique_column_tuples[table_name] = [list(self.columns[table_name])]
        else: 
            # nothing to guarentee uniqueness, so we use the cartesian product of child unique tuples
            candidate_tuples = self.cartesian_of_child_unique_tuples(
                self.top_level_tables_inside[table_name],
                self.columns[table_name],
                self.unique_column_tuples
            )
            # if a candidate tuple is a subset of what we select, accept it
            for candidate_tuple in candidate_tuples:
                if all(column in inner_columns for column in candidate_tuple):
                    candidate_tuple = [inner_columns[column] for column in candidate_tuple]
                    self.unique_column_tuples[table_name].append(candidate_tuple)
    
    @staticmethod                
    def cartesian_of_child_unique_tuples(top_level_tables: list, columns: Dict[str, Column], unique_column_tuples: Dict[str, list]):
        # find all columns we select that are exactly from an inner table
        inner_columns = {}
        for column_name, column_obj in columns.items():
            if column_obj.exact_inner:
                inner_columns[column_obj.exact_inner] = column_name
        cartesian_components = []
        for table in top_level_tables:
            tabled_unique_tuples = []
            for unique_column_tuple in unique_column_tuples[table]:
                tabled_unique_tuples.append([(table, column) for column in unique_column_tuple])
            cartesian_components.append(tabled_unique_tuples)
        # a column tuple that contains a unique column (tuple) for each child table is unique
        # so we take Cartesian product of the unique column (tuple) of children tables
        product = itertools.product(*cartesian_components)
        return [list(itertools.chain.from_iterable(cols)) for cols in product]
        

        return result_unique_column_tuples
                    
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
        top_level_analyzer = TopLevelAnalyzer(top)
        top_level_analyzer.set_target_columns(self.columns[TOP])
        exact_inners = top_level_analyzer.find_center_exact_inner()
        for exact_inner in exact_inners:
            if isinstance(exact_inner, Tuple):
                sources = self.trace_column_to_raw_dfs(exact_inner)
                self.center_columns.append(sorted(set(sources)))
            else:
                self.center_columns.append([])
            
                
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
        # assume top-level select statement does not have set operation
        if top.op.value != pglast.enums.parsenodes.SetOperation.SETOP_NONE:
            raise Exception("Run this algorithm on each top-level set (e.g. component of UNION)!")
        class HoleVisitor(Visitor):
            def __init__(self):
                self.holes = []
            def visit_FuncCall(self, _, node):
                if node.funcname[0].val in AGGREGATE_NAMES:
                    self.holes.append(node)
            def visit_WithClause(self, _, node):
                return pglast.visitors.Skip()
            def visit_SelectStmt(self, _, node):
                return pglast.visitors.Skip()
            # do not consider SubLink yet
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()    
        visitor = HoleVisitor()
        visitor(top.ast_node)
        self.holes = visitor.holes
            

if __name__ == "__main__":           
    schema_file = "testschema.json"
    sql = """WITH cte AS (SELECT 1 as cst1, a.a1 as a1 FROM a) SELECT (SELECT 3 FROM d) k2, a2.a + 1 k2 FROM c c2 CROSS JOIN (SELECT * FROM a) as a2 WHERE EXISTS (SELECT 3 FROM d)"""
    analyzer = FullAnalyzer(sql, schema_file)
    analyzer()
    from pglast.stream import RawStream
    # print(RawStream()(analyzer.table_node[TOP]))
    print(analyzer.columns)
    print(analyzer.unique_column_tuples)
