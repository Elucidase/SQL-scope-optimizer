import pglast
from typing import Dict, Set, Tuple, List
from common import Counter
from full_analyzer import FullAnalyzer
from phase1 import Phase1
from phase2 import Phase2


class Branch:
    counter: Counter = Counter()
    def __init__(self, root: pglast.ast.Node, depth: int, parent: int) -> int :
        """return id"""
        assert(isinstance(root, pglast.ast.Node))
        assert(len(root.targetList) == 1)
        self.ast_node: pglast.ast.Node = root
        self.penalty:int = 0, 
        self.eqPool: list[pglast.ast.Node] = []
        self.oblList: list = []
        self.agg: str = None
        self.key: list = None
        self.depth: int = depth
        self.parent: int = parent
        self.children = []
        self.leaf = False
        self.free = False
        self.id = self.counter.count()
        return self.id

schema_file = "1212schema.json"

sql = """
    SELECT  t.team_id
       ,t.team_name
       ,(SUM(CASE WHEN ((t.team_id = m.host_team) AND (m.host_goals > m.guest_goals)) OR ((t.team_id = m.guest_team) AND (m.host_goals < m.guest_goals)) THEN 3 ELSE 0 END)) AS num_points
FROM Teams AS t
CROSS JOIN Matches AS m
GROUP BY  t.team_id
         ,t.team_name
ORDER BY num_points DESC
         ,t.team_id ASC"""

full_analyzer = FullAnalyzer(sql, schema_file)
context = full_analyzer()


phase1 = Phase1(node, context)
phase1.find_center_columns()
phase1.find_clusters()
print(phase1.center_columns, phase1.clusters)
print("before", RawStream()(phase1.node))
phase1.remove_irrelevant_clusters()
print("after", RawStream()(phase1.node))
print(phase1.check_idempotent())