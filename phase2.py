import json
import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
from pglast.enums.primnodes import BoolExprType
from pglast.enums.parsenodes import A_Expr_Kind
from top_level_analyzer import TopLevelAnalyzer
from full_analyzer import FullAnalyzer, FullContext
from typing import Dict, Set, Tuple, List
from pglast.stream import RawStream
from copy import deepcopy
from common import TOP, find_involved_tables, add_predicates_to_where, ast_BoolExpr
from pglast_z3 import construct_formula_from_ast_node, construct_ast_node_from_formula_dfs, convert_formula_to_cnf, simplify_formula
import z3


class Phase2:
    def __init__(self, node: pglast.ast.Node, context: FullContext, center_tables: list):
        if not isinstance(node, pglast.ast.Node):
            raise Exception("ToplevelAnalyzer accepts ast.Node, not node.Node")
        self.node: pglast.ast.Node = node
        self.context: FullContext = context
        self.top_level: TopLevelAnalyzer = TopLevelAnalyzer(node)
        self.center_tables: list[str] = center_tables
        self.outer_tables: list[str] = None
        # init
        self.top_level()
        
    def find_outer_table(self):
        """find outer tables, which will be used to determine whether a predicate "crosses"
        """
        if len(self.center_tables) == 0 or len(self.center_tables) == len(self.top_level.tables):
            # no center table or everything is center table
            tables_in_hole = find_involved_tables(self.node.targetList[0], self.context.sublink_exterior_columns)
            tables_not_in_hole = set(self.top_level.tables) - set(tables_in_hole)
            if len(tables_not_in_hole) == 0:
                # hole involves every table , so skip Phase 2
                self.outer_tables = []
                return
            # randomly choose one table involved in hole to be outer table
            self.outer_tables = next(iter(tables_not_in_hole))
        else:
            self.outer_tables = self.center_tables
    
    def check_crosses(self, tables: List[str]):
        """check whether a list of tables contain both an outer table and an inner table
           assume outer_tables has been computed
        """
        contains_outer = any(table in self.outer_tables for table in tables)
        contains_inner = any(table not in self.outer_tables for table in tables)
        return contains_outer and contains_inner

    def replace_between_and(self):
        """replace expr BETWEEN lower AND higher to expr >= lower AND expr <= higher"""
        class BetweenAndVisitor(Visitor):
            def visit_A_Expr(self, _, node):
                if node.kind is not A_Expr_Kind.AEXPR_BETWEEN and \
                    node.kind is not A_Expr_Kind.AEXPR_NOT_BETWEEN:
                    return None
                geq_node = pglast.ast.A_Expr(
                    kind = A_Expr_Kind.AEXPR_OP,
                    name = (pglast.ast.String(">="),),
                    lexpr = node.lexpr,
                    rexpr = node.rexpr[0]
                )
                leq_node  = pglast.ast.A_Expr(
                    kind = A_Expr_Kind.AEXPR_OP,
                    name = (pglast.ast.String("<="),),
                    lexpr = node.lexpr,
                    rexpr = node.rexpr[1]
                )
                new_ast_node = pglast.ast.BoolExpr(BoolExprType.AND_EXPR, [geq_node, leq_node])
                if node.kind is A_Expr_Kind.AEXPR_NOT_BETWEEN:
                    new_ast_node = pglast.ast.BoolExpr(BoolExprType.NOT_EXPR, [new_ast_node])
                return new_ast_node
                    
            def visit_RangeSubSelectStmt(self, _, node):
                return pglast.visitors.Skip()
            # do not consider SubLink yet
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()    
        between_and_visitor = BetweenAndVisitor()
        between_and_visitor(self.node)
    
    def expand_crossing_case_when(self):
        """For each CASE WHEN, if it crosses, i.e. involves both outer table(s) and inner table(s),
           then we split into branches corresponding to branches in case when
           assume no nested case expressions
           assume outer_tables has been computed
           return a list of nodes
        """
        class ExpandCaseWhenVisitor(Visitor):
            def __init__(self, root: pglast.ast.Node, check_crosses, sublink_exterior_columns):
                self.branches = [(root, [])]
                self.check_crosses = check_crosses
                self.sublink_exterior_columns = sublink_exterior_columns
            def visit_CaseExpr(self, ancestors, node):
                involved_tables = find_involved_tables(node, self.sublink_exterior_columns)
                if not self.check_crosses(involved_tables):
                    return None
                # this case expression "crosses"
                cases = [(case.result, case.expr) for case in node.args]
                else_expr = pglast.ast.BoolExpr(
                    BoolExprType.NOT_EXPR, 
                    [ast_BoolExpr(BoolExprType.OR_EXPR, [case[1] for case in cases])]
                )
                cases.append((node.defresult, else_expr))
                # construct new branches
                next_branches = []
                for branch in self.branches:
                    root, conditions = branch
                    for value, condition in cases:
                        new_root = deepcopy(root)
                        self.set_this_node(new_root, ancestors, value)
                        next_branches.append((new_root, conditions + [condition]))
                self.branches = next_branches
                    
            @staticmethod
            def set_this_node(root, ancestors, replacement):
                """replace the node identified by its ancestors with replacement"""
                steps = list(ancestors)
                assert(len(steps) >= 2)
                node = root
                for next_step in steps[:-2]:
                    if isinstance(next_step, str):
                        node = getattr(node, next_step)
                    elif isinstance(next_step, int):
                        node = node[next_step]
                second_last_step = steps[-2]
                last_step = steps[-1]
                if isinstance(last_step, str):
                    if second_last_step is not None:
                        node = getattr(node, second_last_step)
                    setattr(node, last_step, replacement)
                elif isinstance(last_step, int):
                    # last step is indexing a list
                    updated_list = [*getattr(node, second_last_step)]
                    updated_list[last_step] = replacement
                    setattr(node, second_last_step, updated_list)
            
        visitor = ExpandCaseWhenVisitor(self.node, self.check_crosses, self.context.sublink_exterior_columns)
        visitor(self.node)
        branches = []
        for root, branch_conditions in visitor.branches:
            copied_root = deepcopy(root)
            add_predicates_to_where(copied_root, branch_conditions)
            branches.append(copied_root)
        return branches
    
    def expand_crossing_conjuncts(self, root: pglast.ast.SelectStmt):
        """Given a select statement ast_node, expand its crossing disjunctions into different branches
           for example, if o is an outer table and a is an inner table, WHERE a.a1 = o.o1 OR a.a1 < 1
           will be expanded into two branches, one with WHERE a.a1 = o.o1, another with WHERE a.a1 < 1
           assume outer_tables has been computed
        """
        penalty = self.add_on_predicates_to_where(root)
        # convert WHERE clause to CNF form
        if not isinstance(root.whereClause, pglast.ast.BoolExpr):
            return [root], penalty
        formula, vars = construct_formula_from_ast_node(root.whereClause)
        formula = simplify_formula(formula)
        formula = convert_formula_to_cnf(formula)
        cnf_where_node = construct_ast_node_from_formula_dfs(formula, vars)
        if not isinstance(cnf_where_node, pglast.ast.BoolExpr):
            root.whereClause = cnf_where_node
            return [root], penalty
        # split crossing conjuncts
        where_branches = [cnf_where_node]
        for index, conjunct in enumerate(cnf_where_node.args):
            if not isinstance(conjunct, pglast.ast.BoolExpr):
                continue
            if conjunct.boolop is BoolExprType.NOT_EXPR:
                continue
            assert(conjunct.boolop is BoolExprType.OR_EXPR)
            replacement_predicates = []
            non_crossing_predicates = []
            for predicate in conjunct.args:
                involved_tables = find_involved_tables(predicate, self.context.sublink_exterior_columns)
                if self.check_crosses(involved_tables):
                    replacement_predicates.append(predicate)
                else:
                    non_crossing_predicates.append(predicate)
            replacement_predicates.append(ast_BoolExpr(BoolExprType.OR_EXPR, non_crossing_predicates))
            # construct new branches
            next_where_branches = []
            for where_branch in where_branches:
                for replacement_predicate in replacement_predicates:
                    args = [*where_branch.args]
                    args[index] = replacement_predicate
                    new_where_branch = ast_BoolExpr(BoolExprType.AND_EXPR, args)
                    next_where_branches.append(new_where_branch)
            where_branches = next_where_branches
        # simplify where branches and incorporate them into select statements
        branches = []
        for where_branch in where_branches:
            new_root = deepcopy(root)
            formula, vars = construct_formula_from_ast_node(where_branch)
            formula = simplify_formula(formula)
            if formula.decl().kind() == z3.Z3_OP_FALSE:
                # condition evaluates to false
                continue
            # formula = convert_formula_to_cnf(formula)
            where_branch = construct_ast_node_from_formula_dfs(formula, vars)
            new_root.whereClause = where_branch
            branches.append(new_root)
        return branches, penalty
    
    def add_on_predicates_to_where(self, root: pglast.ast.SelectStmt):
        """Add all predicates appearing in ON clause to WHERE clause
           Incur penalty when doing so is not safe
        """
        top_level = TopLevelAnalyzer(root)
        top_level()
        top_level.replace_column_alias_usage()
        _, safety = top_level.find_null_graph_and_safety(self.context.sublink_exterior_columns)
        # fetch all predicates in "ON" clause
        class OnPredicateFetcher(Visitor):
            def __init__(self):
                self.predicates = []
            def visit_JoinExpr(self, _, node):
                if node.quals is not None:
                    self.predicates.append(deepcopy(node.quals))
            def visit_RangeSubselect(self, _, node):
                return pglast.visitors.Skip()
            # do not consider sublink yet
            def visit_SubLink(self, _, node):
                return pglast.visitors.Skip()
        on_predicate_fetcher = OnPredicateFetcher()
        on_predicate_fetcher(root.fromClause[0])
        on_predicates = on_predicate_fetcher.predicates
        # we try to add all on-predicates to WHERE clause
        # if not all tables involved in an on-predicate are safe, impose penalty
        penalty = 0
        for predicate in on_predicates:
            involved_tables = set(find_involved_tables(predicate, self.context.sublink_exterior_columns))
            if any(safety[table] == False for table in involved_tables):
                penalty += 1
        add_predicates_to_where(root, on_predicates)
        return penalty

            

if __name__ == "__main__":
    schema_file = "1212schema.json"
    with open(schema_file) as file:
        schema = json.load(file)
    # sql1 = """SELECT sum(a.a2 + b.b1) col FROM a LEFT JOIN b ON (a.a1 < 1 AND a.a1 <= b.b1) INNER JOIN c ON a.a1 = c.c1  WHERE (a.a1 <= a.a2) GROUP BY a.a1"""
    sql2 = """
    SELECT  t.team_id
       ,t.team_name
       ,(SUM(CASE WHEN ((t.team_id = m.host_team) AND (m.host_goals > m.guest_goals)) OR ((t.team_id = m.guest_team) AND (m.host_goals < m.guest_goals)) THEN 3 ELSE 0 END)) AS num_points
FROM Teams AS t
CROSS JOIN Matches AS m
GROUP BY  t.team_id
         ,t.team_name
ORDER BY num_points DESC
         ,t.team_id ASC"""
    full_analyzer = FullAnalyzer(sql2, schema)
    context = full_analyzer()
    node = context.table_node[TOP]
    phase2 = Phase2(node, context, ['t'])
    phase2.find_outer_table()
    case_branches = phase2.expand_crossing_case_when()
    print("Case branches")
    for index, case_branch in enumerate(case_branches):
        print(index, RawStream()(case_branch),"\n")
        conj_branches, penalty = phase2.expand_crossing_conjuncts(case_branch)
        for conj_branch in conj_branches:
            # print(conj_branch)
            print(RawStream()(conj_branch),"\n")
    
            
    