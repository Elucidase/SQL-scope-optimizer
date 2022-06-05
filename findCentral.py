import pglast
from pglast import parser, parse_sql
from pglast.visitors import Visitor
from pglast.enums.primnodes import BoolExprType
from pglast.stream import RawStream
from z3 import *
from typing import Dict, List
from pglast_z3 import Variable, construct_ast_node_from_formula_dfs, construct_formula_from_ast_node
from copy import deepcopy

# sql = """SELECT 1 FROM a CROSS JOIN b WHERE (a.a1 < 1 OR a.a1 <= 2) AND NOT(a.a1 = 3) AND a.a1 BETWEEN 1 AND a.a2 AND abs(a.a1)"""
# sql = """SELECT (CASE WHEN a.a2 < -1 THEN (CASE WHEN 1 THEN 1 ELSE -1 END) ELSE 0 END) col FROM a WHERE (CASE WHEN a.a1 < 1 THEN 1 WHEN a.a1 > 2 THEN 2 ELSE 0 END)"""
sql = "SELECT a.a1, CASE WHEN sum(a.a2) > 0 THEN 1 ELSE 2 END op from a CROSS JOIN b HAVING op > 1"
sql_json = parser.parse_sql_json(sql)
# print(sql_json)
root = pglast.node.Node(parse_sql(sql))
stmt = root[0].stmt
print(pglast.node.Node(None))
# args = []
# a = Int('a')
# b = Int('b')
# c = Bool('c')
# formula = And(c, True).children()[1]
# print(formula.decl().kind() == z3.Z3_OP_TRUE)

# def convert_formula_to_cnf(formula: z3.BoolRef):
#     cnf_tactic = z3.Then(z3.Tactic('tseitin-cnf'), z3.Tactic('ctx-solver-simplify'))
#     goal = z3.Goal()
#     goal.add(formula)
#     return cnf_tactic(goal).as_expr()

# formula, vars = construct_formula_from_ast_node(stmt.ast_node.whereClause)
# formula = convert_formula_to_cnf(formula)
# ast_node = construct_ast_node_from_formula_dfs(formula, vars)
# stmt.ast_node.whereClause = ast_node
# print(RawStream()(stmt))


# branches = expand_crossing_case_when(stmt)
# for branch in branches:
#     copy_stmt = deepcopy(branch[0])
#     branch_condition = pglast.ast.BoolExpr(BoolExprType.AND_EXPR, branch[1])
#     add_predicate_to_where(copy_stmt, branch_condition)
#     print(RawStream()(copy_stmt))