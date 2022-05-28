from enum import unique
import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
from full_analyzer import BasicAnalyzer, Column


schema_file = "testschema.json"
# sql = """WITH cte AS (SELECT 1 as cst1, a.a1 as a1 FROM a) SELECT (SELECT 3 FROM d) k2, a2.a + 1 k2 FROM c c2 CROSS JOIN (SELECT * FROM a) as a2 WHERE EXISTS (SELECT 3 FROM d)"""
sql = """SELECT a.a1, c.c1 FROM a CROSS JOIN c c0 LEFT JOIN (SELECT 1 zc FROM b) d ON c0.c1 = d.zc"""
root = pglast.node.Node(parse_sql(sql))
node = root[0].stmt

analyzer = BasicAnalyzer(sql, schema_file)
analyzer()


def find_top_level_tables(node: pglast.node.Node):
    # return center table(s), side table(s)
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
    visitor(node.ast_node)
    return visitor.top_level_tables

def find_center_columns(node: pglast.node.Node):
    if node.groupClause is Missing:
        top_level_tables = find_top_level_tables(node)
        unique_top_level = [analyzer.unique_column_tuples[table] for table in top_level_tables]
        print(unique_top_level)
    

find_center_columns(node)