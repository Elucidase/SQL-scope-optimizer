import copy
import pglast
from pglast import parser, parse_sql, Node
from pglast.visitors import Visitor
from pglast.stream import RawStream

# sql = 'SELECT 2 c1, a.a1 c2, a.a1 + 1 c3, (SELECT 1 FROM b) c4, (CASE WHEN a.a1 < a.a2 THEN 1 ELSE 2 END) c5  FROM a a2'
sql = """SELECT a.a1 FROM a WHERE cd"""
sql_json = parser.parse_sql_json(sql)
# print(sql_json)
root = Node(parse_sql(sql))
stmt = root[0].stmt
aexpr = stmt.targetList[0].val.fields[-1].ast_node



print(aexpr)

class Vis(Visitor):
    def visit_ColumnRef(self, ancestor, node):
        print(ancestor, node, node.fields[-1])
vis = Vis()
vis(stmt.ast_node)
print(pglast.ast.ColumnRef([pglast.ast.String("a"), pglast.ast.String("b")]))
# print(RawStream()(stmt.whereClause.ast_node))