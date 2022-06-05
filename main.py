import pglast
from pglast.enums.parsenodes import SetOperation
from copy import deepcopy
from enum import Enum
from typing import Dict, Set, Tuple, List
from common import Counter, FullContext
from full_analyzer import FullAnalyzer
from phase1 import Phase1
from phase2 import Phase2


class Penalty(Enum):
    NotIdempotent = 2


class Branch:
    counter: Counter = Counter()

    def __init__(
        self,
        root: pglast.ast.Node,
        depth: int,
        parent: int,
        penalty: list = [],
        eqPool: List[pglast.ast.Node] = [],
        oblList: list = [],
        agg: str = None,
        key: list = None,
        ) -> int:
        """return id"""
        assert(isinstance(root, pglast.ast.Node))
        assert(len(root.targetList) == 1)
        self.ast_node: pglast.ast.Node = root
        self.depth: int = depth
        self.parent: int = parent
        self.penalty: list = penalty
        self.eqPool: list[pglast.ast.Node] = eqPool
        self.oblList: list = oblList
        self.agg: str = agg
        self.key: list = key
        self.children: Dict[int, List[int]] = []
        # Set operation type
        self.children_type: Dict[int, SetOperation] = {}
        self.leaf = False
        self.free = False
        # starts with 1
        self.id = self.counter.count()


class HoleBuilder:
    def __init__(self, initial_root: pglast.ast.SelectStmt, context: FullContext):
        self.id_to_branch: Dict[int, List[Branch]] = {}
        initial_branch = Branch(initial_root, 1, 0)
        self.new_branches = [initial_branch.id]
        self.next_branches = []

    def build(self):
        while len(self.new_branches) > 0:
            self.next_branches = []
            for branch in self.new_branches:
                self.execute_one_round(branch)

    def execute_one_round(self, branch: Branch):
        # split branch if there's top level set operation
        if self.split_set_operation(branch):
            return
        # Phase 1
        phase1 = Phase1(deepcopy(branch.ast_node), self.context)
        phase1.find_center_columns()
        phase1.find_clusters()
        phase1.remove_irrelevant_clusters()
        idempotentphase1.check_idempotent())

    def split_set_operation(self, branch: Branch):
        """if there is set operations like UNION/INTERSECTION/EXCEPT in top level,
           split them into different branches
        """
        root=branch.ast_node
        if branch.ast_node.op.value == SetOperation.SETOP_NONE:
            return False
        # create children and add to next_branches
        for ast_node in (root.larg, root.rarg):
            child=Branch(ast_node, branch.depth + 1, branch.id)
            child.penalty=branch.penalty
            child.eqPool=branch.eqPool
            child.oblList=branch.oblList
            child.agg=branch.agg
            child.key=branch.key
            self.id_to_branch[child.id]=[child]
            branch.children[branch.id].append(child.id)
            self.next_branches.append(child)
        branch.children_type=branch.ast_node.op.value
        return True






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
        hole_builder=HoleBuilder(root, context)
        hole_builder.build()
