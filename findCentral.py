import copy
import pglast
from pglast import parser, parse_sql, Node
from pglast.visitors import Visitor
from pglast.stream import RawStream

# sql = 'SELECT 2 c1, a.a1 c2, a.a1 + 1 c3, (SELECT 1 FROM b) c4, (CASE WHEN a.a1 < a.a2 THEN 1 ELSE 2 END) c5  FROM a a2'
sql = """SELECT COUNT(DISTINCT a.a1) z1, COUNT(DISTINCT a.a1) OVER() z2 FROM a WHERE a.a1 < 1 AND a.a1 < 2 AND a.a1 < 3"""
sql_json = parser.parse_sql_json(sql)
# print(sql_json)
root = Node(parse_sql(sql))
stmt = root[0].stmt
args = []

# boolExpr.args = args
print(stmt.targetList[0].ast_node)
print(stmt.targetList[1].ast_node)
# stmt.whereClause.args = stmt.whereClause.args[1:3]
# print(stmt.whereClause.ast_node)

# print(pglast.ast.ColumnRef([pglast.ast.String("a"), pglast.ast.String("b")]))
# print(RawStream()(stmt.whereClause.ast_node))