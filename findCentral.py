import pglast
from pglast import parser, parse_sql, Node
from pglast.visitors import Visitor

# sql = 'SELECT 2 c1, a.a1 c2, a.a1 + 1 c3, (SELECT 1 FROM b) c4, (CASE WHEN a.a1 < a.a2 THEN 1 ELSE 2 END) c5  FROM a a2'
sql = """SELECT UPPER("string") aa, SUM(1) OVER(PARTITION BY a.a2) boo from a"""
sql_json = parser.parse_sql_json(sql)
# print(sql_json)
root = Node(parse_sql(sql))
node = root[0].stmt
print(node.targetList[0].val.funcname)
# print(node.ast_node)
# print(root[0].stmt.groupClause is pglast.Missing)