import pglast
import z3
from pglast.enums.primnodes import BoolExprType
from pglast.enums.parsenodes import A_Expr_Kind
from typing import Dict, List
from pglast.stream import RawStream
from common import Counter


class Variable:
    def __init__(self, ast_node: pglast.ast.Node, type: type):
        self.ast_node = ast_node
        self.type = "Int" if type is int else "Bool"

    def __repr__(self):
        return f'{self.ast_node}: {self.type}'


def construct_formula_from_ast_node(expr: pglast.ast.Node):
    """return formula for the given ast node"""
    vars = {}
    # TRUE/FALSE literal
    type_name = typeName=pglast.ast.TypeName(
        names=(pglast.ast.String('pg_catalog'), pglast.ast.String('bool')), setof=False, pct_type=False, typemod=-1)
    vars['true'] = Variable(pglast.ast.TypeCast(arg=pglast.ast.A_Const(val=pglast.ast.String('t')), typeName=type_name), bool)
    vars['false'] = Variable(pglast.ast.TypeCast(arg=pglast.ast.A_Const(val=pglast.ast.String('f')), typeName=type_name), bool)
    var_strings = {}
    counter = Counter()
    formula_string, _ = construct_formula_dfs(
        expr, bool, vars, var_strings, counter)
    context = generate_formula_context(vars)
    return eval(formula_string, context), vars


def register_new_var(expr: pglast.ast.Node, type: type, vars: Dict[str, Variable], var_strings: Dict[str, str], counter: Counter):
    """Register a new (int) variable if it hasn't been created
    Deduplicate by comparing their RawStream string representation
    """
    var_string = RawStream()(expr)
    if var_string in var_strings:
        return var_strings[var_string]
    var_name = pglast.node.Node(expr).node_tag + str(counter.count())
    vars[var_name] = Variable(expr, type)
    var_strings[var_string] = var_name
    return var_name


def construct_formula_dfs(expr: pglast.ast.Node, expected_type: type, vars: Dict[str, Variable], var_strings: Dict[str, str], counter: Counter):
    """return formula string for the given ast node
    vars collects all variable defintions
    var_strings is for deduplication purpose to possibly reduce number of variables declared
    bool expressions will be Bool in Z3, and every other type will be Int
    """
    if isinstance(expr, pglast.ast.A_Const):
        if isinstance(expr.val, pglast.ast.Integer):
            result_str = str(expr.val.val)
        else:
            result_str = register_new_var(
                expr, int, vars, var_strings, counter)
        return result_str, int
    elif isinstance(expr, pglast.ast.ColumnRef):
        return register_new_var(expr, int, vars, var_strings, counter), int
    elif isinstance(expr, pglast.ast.A_Expr):
        if expr.kind == A_Expr_Kind.AEXPR_OP:
            op = expr.name[0].val
            if op == "=":
                op = "=="
            elif op == "<>":
                op = "!="
            # find argument strings
            if expr.lexpr:
                left_str, left_type = construct_formula_dfs(
                    expr.lexpr, int, vars, var_strings, counter)
            else:
                left_str, left_type = "", int
            right_str, right_type = construct_formula_dfs(
                expr.rexpr, int, vars, var_strings, counter)
            result_str = f"({left_str} {op} {right_str})"
            if left_type is not int or right_type is not int:
                raise Exception(f"argument of {result_str} is bogus")
            if op in ("=", "!=", "<", ">", "<=", ">="):
                return result_str, bool
            elif op in ("+", "-", "*", "/"):
                return result_str, int
    elif isinstance(expr, pglast.ast.NullTest):
        return register_new_var(expr, bool, vars, var_strings, counter), bool
    elif isinstance(expr, pglast.ast.BoolExpr):
        strs = []
        for arg in expr.args:
            arg_str, arg_type = construct_formula_dfs(
                arg, bool, vars, var_strings, counter)
            if arg_type is not bool:
                # coerce into a bool variable
                arg_str = register_new_var(
                    arg, bool, vars, var_strings, counter)
            strs.append(arg_str)
        BoolExprType = pglast.enums.primnodes.BoolExprType
        if expr.boolop is BoolExprType.AND_EXPR:
            boolop = "And"
        elif expr.boolop is BoolExprType.OR_EXPR:
            boolop = "Or"
        else:
            boolop = "Not"
        arg_str = ",".join(strs)
        return f"{boolop}({arg_str})", bool
    # default case: Z3 won't understand the expression, so we create a variable for it
    return register_new_var(expr, expected_type, vars, var_strings, counter), expected_type


def generate_formula_context(vars: Dict[str, Variable]):
    context = {"And": z3.And, "Or": z3.Or,
               "Not": z3.Not, "Int": z3.Int, "Bool": z3.Bool}
    for var, var_object in vars.items():
        if var_object.type == "Int":
            context[var] = z3.Int(var)
        else:
            context[var] = z3.Bool(var)
    return context


def construct_ast_node_from_formula_dfs(formula: z3.BoolRef, vars: Dict[str, Variable]):
    name = formula.decl().name()
    children = formula.children()
    if len(children) == 0:
        if isinstance(formula, z3.IntNumRef):
            return pglast.ast.A_Const(pglast.ast.Integer(formula.as_long()))
        else:
            # a variable
            return vars[name].ast_node
    child_nodes = []
    for child in children:
        child_nodes.append(construct_ast_node_from_formula_dfs(child, vars))
    if name in ("and", "or", "not"):
        if name == "and":
            boolop = BoolExprType.AND_EXPR
        elif name == "or":
            boolop = BoolExprType.OR_EXPR
        else:
            boolop = BoolExprType.NOT_EXPR
        return pglast.ast.BoolExpr(boolop, child_nodes)
    else:
        # op is one of the comparison or mathematical operators
        assert(len(child_nodes) in (1, 2))
        ast_node = pglast.ast.A_Expr(
            kind=A_Expr_Kind.AEXPR_OP,
            name=(pglast.ast.String(name),),
            rexpr=child_nodes[-1]
        )
        if len(child_nodes) == 2:
            ast_node.lexpr = child_nodes[0]
        return ast_node


def convert_formula_to_cnf(formula: z3.BoolRef):
    cnf_tactic = z3.Then(z3.Tactic('tseitin-cnf'),
                         z3.Tactic('ctx-solver-simplify'))
    goal = z3.Goal()
    goal.add(formula)
    return cnf_tactic(goal).as_expr()


def simplify_formula(formula: z3.BoolRef):
    simplify_tactic = z3.Repeat(
        z3.OrElse(
            z3.Then(z3.Tactic('split-clause'),
                    z3.Tactic('ctx-solver-simplify')),
            z3.Tactic('skip')
        )
    )
    goal = z3.Goal()
    goal.add(formula)
    return simplify_tactic(goal).as_expr()
