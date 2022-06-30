import itertools
import json
import pglast
from pglast import parser, parse_sql
from pglast.visitors import Visitor
from pglast.enums.primnodes import BoolExprType
from pglast.stream import RawStream
from z3 import *
from typing import Dict, List
from common import FALSE_NODE, SELECT_EMPTY, SELECT_SUM_ZERO, find_involved_tables, Counter, TOP
from full_analyzer import FullAnalyzer
from pglast_z3 import Variable, construct_ast_node_from_formula_dfs, construct_formula_from_ast_node
from copy import deepcopy
from pglast.enums.nodes import JoinType
from pglast.enums.parsenodes import SetOperation


schema_file="testschema.json"
with open(schema_file) as file:
    schema = json.load(file)
# sql = """SELECT 1 FROM a CROSS JOIN b WHERE (a.a1 < 1 OR a.a1 <= 2) AND NOT(a.a1 = 3) AND a.a1 BETWEEN 1 AND a.a2 AND abs(a.a1)"""
# sql = """SELECT (CASE WHEN a.a2 < -1 THEN (CASE WHEN 1 THEN 1 ELSE -1 END) ELSE 0 END) col FROM a WHERE (CASE WHEN a.a1 < 1 THEN 1 WHEN a.a1 > 2 THEN 2 ELSE 0 END)"""
sql = "SELECT 1"
proot = pglast.parse_sql(sql)[0].stmt
print(proot)
# full_analyzer=FullAnalyzer(sql, schema)
# context=full_analyzer()
# root = context.table_node[TOP]
# root.whereClause = pglast.ast.A_Const(val=pglast.ast.Integer(1))
cool = "SELECT a.a1 + 1"
# print(pglast.parse_sql(cool)[0].stmt.targetList[0].val)

# print(proot.fromClause[0])

# sql1 = "SELECT a2.col FROM a a1 CROSS JOIN a2 WHERE 1 AND 2"
# sql2 = "SELECT 1 FROM a a1 CROSS JOIN (SELECT col FROM a2) a2 WHERE 1 AND 2"

# z3.Tactic('tseitin-cnf').help()
# # z3.Tactic('ctx-solver-simplify').help()
# With(z3.Tactic('ctx-solver-simplify'), **{"arith.int_eq_branch": True})

# args = []
# a = Int('a')
# b = Int('b')
# c1 = Bool('c1')
# c2 = Bool('c2')
# formula = And(a == c1, b == c2, b == c1, b > a)

# ctx_solver_simplify = z3.With(
#         z3.Tactic('ctx-solver-simplify'),
#         **{"core.extend_patterns": True, "induction": True},
#         **{"arith.int_eq_branch": True, "theory_case_split": True, "theory_aware_branching": True, "pull_nested_quantifiers": True, "core.minimize": True}
# )

# simplify_tactic = z3.Then(
#     ctx_solver_simplify,
#     z3.Tactic("propagate-values"),
#     z3.Tactic("propagate-ineqs"),
#     ctx_solver_simplify,
#     z3.Tactic("propagate-values"),
#     z3.Tactic("propagate-ineqs")
# )

# goal = z3.Goal()
# goal.add(formula)
# result =  ctx_solver_simplify(goal).as_expr()
# # print(result)