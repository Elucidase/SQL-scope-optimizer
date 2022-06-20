from copy import deepcopy
import itertools
from typing import Dict, List, Tuple
from numpy import isin
import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
import json
from common import Column, Counter, FullContext, TOP, SUBLINK, AGGREGATE_NAMES, add_ast_node_to_select, sublink_name
from top_level_analyzer import TopLevelAnalyzer


# Assumptions
# REMEDIABLE: Sublink yet to be supported

class FullAnalyzer:
    """
    Attributes:
        table_node (Dict[str, pglast.node.Node]): table name -> node of subquery/cte
        top_level_tables_inside (Dict[str, list]): table name -> list of top-level tables directly inside
        sublinks_inside (Dict[str, list]): table name -> list of sublinks_inside directly inside
        columns (Dict[str, Dict[str, Column]]): table name -> dict from column name to Column object
        unique_column_tuples (Dict[str, list]): table name -> list of column names or combination of column names that are unique
        sublink_context_columns (Dict[str, Dict[str, Column]]): same format as columns, only those tables 
        in the same scope as the sublink
        self.sublink_exterior_columns (Dict[str, set[Tuple[str, str]]]): list of exterior columns used in the sublink
        root (pglast.node.Node): root node
        schema: parsed from json
        center_columns (list[list[Tuple[str, str]]]): possibilities for each center column
        sublink_counter (Counter): counter for naming sublinks
    """
    def __init__(self, sql: str, schema):
        self.table_node: Dict[str, pglast.node.Node] = {}
        self.top_level_tables_inside: Dict[str, list] = {}
        self.sublinks_inside: Dict[str, list] = {}
        self.columns: Dict[str, Dict[str, Column]] = {}
        self.unique_column_tuples: Dict[str, list] = {}
        self.sublink_context_columns: Dict[str, Dict[str, Column]] = {}
        self.sublink_exterior_columns: Dict[str, set[Tuple[str, str]]] = {}
        self.root = pglast.node.Node(parse_sql(sql))
        self.schema = schema
        self.center_columns = []
        self.sublink_counter = Counter()
            
    def __call__(self):
        self.find_hierarchy()
        self.fill_columns_raw()
        self.fill_columns_dfs(TOP, [])
        self.find_center_columns()
        table_ast_node = {table: node.ast_node for table, node in self.table_node.items()}
        return FullContext(
            table_ast_node, 
            self.top_level_tables_inside, 
            self.columns, 
            self.unique_column_tuples, 
            self.sublink_exterior_columns
        )

    def find_hierarchy(self):
        """fill in top_level_tables_inside and table_node"""
        self.find_hierarchy_dfs(self.root)
        self.fix_alias_hierarchy_dfs(TOP)

    def find_hierarchy_dfs(self, node: pglast.node.Base, stack: list = []):
        """fill in top_level_tables_inside and table_node for subqueries/CTE"""
        if isinstance(node, pglast.node.Scalar):
            return
        scope_name = ""
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
                sublink_id = self.sublink_counter.count()
                scope_name = sublink_name(sublink_id)
                node.ast_node.location = sublink_id
                self.table_node[scope_name] = node.subselect
                self.sublink_exterior_columns.setdefault(scope_name, set())
                sublink = True
        if scope_name != "":
            self.top_level_tables_inside.setdefault(scope_name, [])
            self.sublinks_inside.setdefault(scope_name, [])
            if len(stack) > 0:
                children_list = self.top_level_tables_inside if not sublink else self.sublinks_inside
                children_list[stack[-1]].append(scope_name)
            stack.append(scope_name)
        for child in node:
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
            for table in self.sublinks_inside[table_name]:
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
    
    def fill_columns_dfs(self, table_name, inside_sublinks: List[str]):
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
        sublink_context_columns = {}
        for top_level_table in self.top_level_tables_inside[table_name]:
            if top_level_table not in self.columns:
                self.fill_columns_dfs(top_level_table, inside_sublinks)
            sublink_context_columns[top_level_table] = self.columns[top_level_table]
        for sublink in self.sublinks_inside[table_name]:
            self.sublink_context_columns[sublink] = sublink_context_columns
            self.fill_columns_dfs(sublink, inside_sublinks + [sublink])
        
        self.fill_columns(table_name, inside_sublinks)
        self.fill_unique_column_tuples(table_name)
        if len(self.unique_column_tuples[table_name]) == 0:
            print("Warning: table", table_name, "has no primary key")

    def fill_columns(self, table_name, inside_sublinks: List[str]):
        """helper function of fill_columns_dfs, fill columns for this table"""
        node = self.table_node[table_name]
        top_level_tables = self.top_level_tables_inside[table_name]
        # fill in columns
        # in case of set operations, i.e. UNION/INTERCECT/EXCEPT, analyze each
        # and combine the results
        self.columns[table_name] = self.fill_columns_combine_sets_dfs(node, top_level_tables, inside_sublinks)
        
        
    def fill_columns_combine_sets_dfs(self, node: pglast.node.Node, top_level_tables: list, inside_sublinks: List[str]):
        """helper function of fill_column, combining results of single sets"""
        if node.op.value == pglast.enums.parsenodes.SetOperation.SETOP_NONE:
            return self.fill_columns_single_set(node, top_level_tables, inside_sublinks)
        left = self.fill_columns_combine_sets_dfs(node.larg, top_level_tables, inside_sublinks)
        right = self.fill_columns_combine_sets_dfs(node.rarg, top_level_tables, inside_sublinks)
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
    
    def fill_columns_single_set(self, node: pglast.node.Node, top_level_tables: list, inside_sublinks: List[str]):
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
        self.qualify_columns_from_inner_table(node, top_level_tables, inside_sublinks)
        result = {}
        for target in node.targetList:
            column_name = Column.name_from_resTarget(target.ast_node)
            result[column_name] = Column.from_ast_node(target.val.ast_node, column_name)
        return result
    
    def qualify_columns_from_inner_table(self, node: pglast.node.Node, top_level_tables: list, inside_sublinks: List[str]):
        """qualify columns with the inner tables they come from, i.e. c -> t.c"""
        # find all column names we recognize
        # column name from inner table -> ColumnRef with fields (inner table, column)
        qualified_columnRef = {}
        repeated_names = set()
        for top_level_table in top_level_tables:
            for column in self.columns[top_level_table]:
                if column in qualified_columnRef:
                    repeated_names.add(column)
                # ColumnRef ast node
                qualified_columnRef[column] = Column.create(top_level_table, column).val
        # used when parsing sublinks
        qualified_exterior_columnRef = {}
        repeated_exterior_names = set()
        table_due_to_sublink = {}
        for sublink in inside_sublinks:
            sublink_context_columns = self.sublink_context_columns[sublink]
            for exterior_table in sublink_context_columns:
                table_due_to_sublink[exterior_table] = sublink
                for column in sublink_context_columns[exterior_table]:
                    if column in qualified_exterior_columnRef:
                        repeated_exterior_names.add(column)
                    qualified_exterior_columnRef[column] = Column.create(top_level_table, column).val
        
        class QualifyVisitor(Visitor):
            def __init__(self, sublink_exterior_columns):
                self.sublink_exterior_columns = sublink_exterior_columns
            def visit_ColumnRef(self, ancestor, node):
                new_node = deepcopy(node)
                if len(node.fields) == 1:
                   # need to qualify with table name
                    column = node.fields[0].val
                    # first try to resolve without using exterior context
                    if column in qualified_columnRef:
                        if column in repeated_names:
                            raise Exception(f"Column reference {column} is ambiguous without specifying table")
                        new_node = qualified_columnRef[column]
                    elif column in qualified_exterior_columnRef:
                        if column in repeated_exterior_names:
                            raise Exception(f"Column reference {column} is ambiguous without specifying table")
                        new_node = qualified_exterior_columnRef[column]
                    else:
                        raise Exception(f"Column reference {column} cannot be resolved")
                assert(len(new_node.fields) == 2)
                table, column = new_node.fields[0].val, new_node.fields[1].val
                if table in table_due_to_sublink:
                    # the outermost sublink that will consider this column exterior
                    due_to_sublink = table_due_to_sublink[table]
                    index = inside_sublinks.index(due_to_sublink)
                    for sublink in inside_sublinks[index:]:
                        self.sublink_exterior_columns[sublink].add((table, column))
                return new_node
            def visit_SortBy(self, _, node):
                return pglast.visitors.Skip()
            def visit_RangeSubselect(self, _, node):
                return pglast.visitors.Skip()
            # do not consider sublink yet
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip() 
        qualify_visitor = QualifyVisitor(self.sublink_exterior_columns)
        qualify_visitor(node.ast_node)

    def fill_unique_column_tuples(self, table_name):
        """helper function of fill_columns_dfs, fill unique_column_tuples for this table
           add columns to select if this is necessary for creating unique keys
        """
        node = self.table_node[table_name]
        self.unique_column_tuples[table_name] = []
        # find all columns that are directly from a children table
        inner_columns = {}
        for column_name, column_obj in self.columns[table_name].items():
            if column_obj.exact_inner:
                inner_columns[column_obj.exact_inner] = column_name
        # fill in unique_column_tuples
        if node.groupClause is not Missing:
            self.unique_column_tuples[table_name] = self.find_group_by_unique_tuples(table_name, inner_columns)
        elif node.distinctClause is not Missing:
            self.unique_column_tuples[table_name] = [list(self.columns[table_name])]
        elif node.op.value == pglast.enums.parsenodes.SetOperation.SETOP_UNION:
            # union removes duplicates
            self.unique_column_tuples[table_name] = [list(self.columns[table_name])]
        else: 
            # nothing to guarentee uniqueness, so we use the cartesian product of child unique tuples
            candidate_tuples = self.cartesian_of_child_unique_tuples(
                self.top_level_tables_inside[table_name],
                self.unique_column_tuples
            )
            # if a candidate tuple is a subset of what we select, accept it
            for candidate_tuple in candidate_tuples:
                if all(column in inner_columns for column in candidate_tuple):
                    candidate_tuple = [inner_columns[column] for column in candidate_tuple]
                    self.unique_column_tuples[table_name].append(candidate_tuple)
    
    def find_group_by_unique_tuples(self, table_name: str, inner_columns: Dict[Tuple[str, str], str]):
        """helper function to fill_unique_column_tuples"""
        node = self.table_node[table_name]
        cartesian_components = []
        top_level_analyzer = TopLevelAnalyzer(node.ast_node)
        top_level_analyzer.find_target_columns()
        group_columns = top_level_analyzer.find_group_columns()
        tuple_exact_inners = []
        counter = Counter()
        for group_column in group_columns:
            # an inner column
            if isinstance(group_column.exact_inner, Tuple):
                tuple_exact_inners.append(group_column.exact_inner)
            # not an inner column, but is a select column
            if isinstance(group_column.exact_inner, str):
                cartesian_components.append([[group_column.exact_inner]])
            # neither an inner column nor a select column, then make it a select column
            elif group_column.exact_inner is None:
                column_name = "groupby_column_" + str(counter.count())
                add_ast_node_to_select(node.ast_node, group_column.val, column_name)
                self.columns[table_name][column_name] = Column.from_ast_node(group_column.val, column_name)
                cartesian_components.append([[column_name]])
        # for exact group-by columns belonging to the same child table, try to eliminate some with unique info
        # i.e. find all child unique tuples for each child table that is a subset of the group-by columns
        tuple_exact_inners.sort(key = lambda table_column: table_column[0])
        by_table = itertools.groupby(tuple_exact_inners, lambda table_column: table_column[0])
        by_table = {table: [column for _, column in table_columns] for table, table_columns in by_table}
        for table in by_table:
            cartesian_component = []
            group_columns_about_this_child = by_table[table]
            subsets = [group_columns_about_this_child]
            for unique_tuple in self.unique_column_tuples[table]:
                if all(column in group_columns_about_this_child for column in unique_tuple):
                    subsets.append(unique_tuple)
            # has proper subset, don't need the full one
            if len(subsets) > 1:
                subsets.pop(0)
            for subset in subsets:
                if all((table, column) in inner_columns for column in subset):
                    cartesian_component.append([inner_columns[(table, column)] for column in subset])
            # no viable subsets, choose the first one and add necessary columns to select
            if len(cartesian_component) == 0:
                subset = subsets[0]
                outer_column_names = []
                for column in subset:
                    if (table, column) in inner_columns:
                        outer_column_names.append(inner_columns[(table, column)])
                    else:
                        column_name = "groupby_column_" + str(counter.count())
                        add_ast_node_to_select(node.ast_node, Column.create(table, column).val, column_name)
                        self.columns[table_name][column_name] = Column.create(table, column)
                        outer_column_names.append(column_name)
                cartesian_component.append(outer_column_names)
            cartesian_components.append(cartesian_component)
        product = itertools.product(*cartesian_components)
        return [list(itertools.chain.from_iterable(cols)) for cols in product]
    
    
    @staticmethod                
    def cartesian_of_child_unique_tuples(top_level_tables: list, unique_column_tuples: Dict[str, list]):
        # find all columns we select that are exactly from an inner table
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
        top_level_analyzer = TopLevelAnalyzer(top.ast_node)
        top_level_analyzer.set_target_columns(self.columns[TOP])
        exact_inners = [group_column.exact_inner for group_column in top_level_analyzer.find_group_columns()]
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
        columns_to_explore = set()
        if column.exact_inner is not None:
            if len(self.top_level_tables_inside[scope]) == 0:
                # reached raw table
                return [column.exact_inner]
            columns_to_explore.add(column.exact_inner)
        else: 
            print(f"Warning: Column {name} is not exactly a column from an inner table")
            columns_to_explore = column.dependsOn
        result = []
        for inner_column in columns_to_explore:
            result.extend(self.trace_column_to_raw_dfs(inner_column))
        return result
            

if __name__ == "__main__":           
    schema_file = "testschema.json"
    # sql = """WITH cte AS (SELECT 1 as cst1, a.a1 as a1 FROM a) SELECT (SELECT 3 FROM d) k2, a2.a + 1 k2 FROM c c2 CROSS JOIN (SELECT * FROM a) as a2 WHERE EXISTS (SELECT 3 FROM d)"""
    sql = "SELECT (SELECT 1 n1 FROM c WHERE a.a1 > 1) bruh FROM a WHERE (SELECT 2 n2 FROM b WHERE (SELECT 3 n3 FROM c WHERE b.b1 < c.c1 AND a.a1 < 1)) = 1"
    with open(schema_file) as file:
        schema = json.load(file)
    analyzer = FullAnalyzer(sql, schema)
    analyzer()
    from pglast.stream import RawStream
    print(analyzer.columns)
    print(analyzer.unique_column_tuples)
    print(analyzer.sublink_exterior_columns)
    print(RawStream()(analyzer.table_node[TOP]))
