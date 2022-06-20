import pglast
from pglast.enums.parsenodes import SetOperation
from pglast.stream import RawStream
from copy import deepcopy
from enum import Enum
from typing import Dict, Set, Tuple, List

from sqlalchemy import false
from common import Counter, FullContext
from full_analyzer import FullAnalyzer
from phase1 import Phase1
from phase2 import Phase2
from top_level_analyzer import TopLevelAnalyzer


class Penalty(Enum):
    NotIdempotent = 2


class Branch:
    counter: Counter = Counter()

    def __init__(
        self,
        root: pglast.ast.Node,
        join_level: int,
        parent: int,
        penalty: list = [],
        eq_pool: List[pglast.ast.Node] = [],
        obl_list: list = [],
        ) -> int:
        assert(isinstance(root, pglast.ast.Node))
        assert(len(root.targetList) == 1)
        self.ast_node: pglast.ast.Node = root
        self.join_level: int = join_level
        self.parent: int = parent
        self.penalty: list = penalty
        self.eq_pool: list[pglast.ast.Node] = eq_pool
        self.obl_list: list = obl_list
        self.children: Dict[int, List[int]] = []
        # SetOperation:
        # None means no children
        # SETOP_UNION, SETOP_INTERSECT, SETOP_EXCEPT have literal meaning
        # SETOP_NONE means combining through holes
        self.children_type: SetOperation = None
        # starts with 1
        self.id = self.counter.count()


class BranchBuilder:
    def __init__(self, initial_root: pglast.ast.SelectStmt, context: FullContext):
        self.id_to_branch: Dict[int, List[Branch]] = {}
        initial_branch = Branch(initial_root, 1, 0)
        self.id_to_branch[initial_branch.id] = [initial_branch]
        self.new_branches = [initial_branch.id]

    def build(self):
        while len(self.new_branches) > 0:
            self.next_branches = []
            for branch in self.new_branches:
                self.execute_one_round(branch)

    def execute_one_round(self, branch: Branch):
        # Phase 0
        # split branch if there's top level set operation
        if self.split_set_operation(branch):
            return
        # Phase 1
        phase1 = Phase1(deepcopy(branch.ast_node), self.context)
        phase1.find_center_columns()
        phase1.find_clusters()
        phase1.remove_irrelevant_clusters()
        if phase1.zoom_in_if_center_one_only():
            branch.children_type = SetOperation.SETOP_UNION
            self.fork_branch_and_add_to_next(branch, phase1.node, True)
            return
        if phase1.check_free_from_center():
            branch.children_type = SetOperation.SETOP_UNION
            self.free_branch_and_add_to_next(branch, phase1.node)
            return
        idempotent_penalty = phase1.check_idempotent()
        # Phase 2
        phase2 = Phase2(phase1.node, self.context, phase1.center_tables)
        phase2.find_outer_table()
        phase2.replace_between_and()
        case_branches = phase2.expand_crossing_case_when()
        print("Case branches")
        subbranches = []
        for index, case_branch in enumerate(case_branches):
            print(index, RawStream()(case_branch),"\n")
            conjunct_branches, penalty = phase2.expand_crossing_conjuncts(case_branch)
            for conjunct_branch in conjunct_branches:
                print(RawStream()(conjunct_branch),"\n")
                subbranches.append(conjunct_branch)
        # Phase 3

    def split_set_operation(self, branch: Branch):
        """if there is set operations like UNION/INTERSECTION/EXCEPT in top level,
           split them into different branches
        """
        root = branch.ast_node
        child_roots = []
        if branch.ast_node.op.value != SetOperation.SETOP_NONE:
            # check union/intersection/except
            branch.children_type = branch.ast_node.op.value
            child_roots.extend([root.larg, root.rarg])
        else:
            top_level_analyzer = TopLevelAnalyzer(root)
            holes = top_level_analyzer.find_holes()
            # split only if we have at least 2 holes
            if len(holes) > 1:
                # means children_type is "holes"
                branch.children_type = SetOperation.SETOP_NONE
            for hole in holes:
                child_root = deepcopy(root)
                child_root.targetList = [pglast.ast.ResTarget(name="agg", val=hole)]
                child_roots.append(child_root)
        if branch.children_type is None:
            return False
        for child_root in child_roots:
            self.fork_branch_and_add_to_next(branch, child_root, False)  
        return True
            
    def fork_branch_and_add_to_next(self, parent: Branch, child_root: pglast.ast.SelectStmt, increment_join_level: bool):
        child = Branch(
            child_root, 
            parent.join_level + (1 if increment_join_level else 0),
            parent.id, 
            parent.penalty, 
            parent.eq_pool,
            parent.obl_list,
        )
        self.id_to_branch[child.id] = [child]
        parent.children[parent.id].append(child.id)
        self.next_branches.append(child) 

    def free_branch_and_add_to_next(self, parent: Branch, child_root: pglast.ast.SelectStmt):
        child = Branch(
            child_root, 
            0,
            parent.id, 
            parent.penalty
        )
        self.id_to_branch[child.id] = [child]
        parent.children[parent.id].append(child.id)
        self.next_branches.append(child) 





schema_file="1212schema.json"

sql="""
    SELECT  t.team_id
       ,t.team_name
       ,(SUM(CASE WHEN ((t.team_id = m.host_team) AND (m.host_goals > m.guest_goals)) OR ((t.team_id = m.guest_team) AND (m.host_goals < m.guest_goals)) THEN 3 ELSE 0 END)) AS num_points
FROM Teams AS t
CROSS JOIN Matches AS m
GROUP BY  t.team_id
         ,t.team_name
ORDER BY num_points DESC
         ,t.team_id ASC"""

def main(sql, schema_file):
    # analyze incoming sql
    full_analyzer=FullAnalyzer(sql, schema_file)
    context=full_analyzer()
    for index, hole in enumerate(full_analyzer.holes):
        root=deepcopy(full_analyzer.root.ast_node)
        hole_name=f"HOLE_{index}"
        root.targetList=[pglast.ast.ResTarget(name = hole_name, val = hole)]
        hole_builder=BranchBuilder(root, context)
        hole_builder.build()
