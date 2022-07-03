from __future__ import annotations
import pglast
from pglast.enums.parsenodes import SetOperation
from pglast.stream import RawStream
from copy import deepcopy
from typing import Dict, List, Optional

from common import HOLE_AGG_NAME, SELECT_EMPTY, Counter, FullContext, TranslationPayload
from full_analyzer import FullAnalyzer
from phase1 import Phase1
from phase2 import Phase2
from phase3 import Phase3
from top_level_analyzer import TopLevelAnalyzer
from penalty import Penalty, NotIdempotentPenalty, UnsafeOnPredicatePenalty, RemovePredicatePenalty, CenterNotUniquePenalty
    

class Branch:
    id_counter: Counter = Counter()

    def __init__(
        self,
        root: pglast.ast.Node,
        join_level: int,
        parent: int,
        penalty: list = [],
        translation_payload = TranslationPayload(),
        zoom_in_payload = None,
        ) -> int:
        assert(isinstance(root, pglast.ast.Node))
        self.root: pglast.ast.Node = root
        self.join_level: int = join_level
        self.parent: int = parent
        self.penalty: list = penalty
        # used when instantiating queries
        self.translation_payload: TranslationPayload = translation_payload
        # whether this branch is self-contained
        self.free: bool = False
        # children ids
        self.children: list[int] = []
        # SetOperation:
        # None means no children
        # SETOP_UNION, SETOP_INTERSECT, SETOP_EXCEPT have literal meaning
        # SETOP_NONE means combining through holes
        self.children_type: Optional[SetOperation] = None
        # information needed when we propagate aggregation function into a root with set operations, e.g. UNION
        self.zoom_in_payload: Phase1 = zoom_in_payload
        # starts with 1
        self.id = self.id_counter.count()



class BranchBuilder:
    # counter for the keys of translation_payload.links
    DUMMY_ORIGIN: str = "%dummy_origin%"
    dummy_origin_counter: Counter = Counter()
    
    @staticmethod
    def check_dummy_origin_str(origin_str: str):
        """check if an origin_str is dummy"""
        return origin_str.startswith(BranchBuilder.DUMMY_ORIGIN)
    
    def __init__(self, initial_root: pglast.ast.SelectStmt, context: FullContext):
        self.context = context
        self.id_to_branch: Dict[int, List[Branch]] = {}
        initial_branch = Branch(initial_root, 1, 0)
        self.id_to_branch[initial_branch.id] = [initial_branch]
        self.new_branches = [initial_branch]
        self.next_branches = []
    
    def add_branch_of_id(self, id: int, branch: Branch):
        """add branch to id_to_branch while checking for duplication"""
        # text_form = RawStream()(branch.root)
        # for existing in self.id_to_branch[id]:
        #     if RawStream()(existing.root) == text_form:
        #         return False
        self.id_to_branch[id].append(branch)
        return True

    def build(self):
        while len(self.new_branches) > 0:
            self.next_branches = []
            for branch in self.new_branches:
                self.execute_one_round(branch)
            self.new_branches = self.next_branches
        return self.id_to_branch

    def execute_one_round(self, branch: Branch):
        print("execute id", branch.id, RawStream()(branch.root))
        # Phase 0
        assert(branch.children_type is None)
        # resolve any translation payload inherited from parent
        self.resolve_zoom_in_payload(branch)
        self.create_translation_payload_dummy_links(branch)
        # split branch if there's top level set operation
        if self.split_set_operation(branch):
            return
        # Phase 1
        phase1 = Phase1(deepcopy(branch.root), self.context, branch.translation_payload)
        round_terminated = self.execute_phase1(phase1, branch)
        if round_terminated:
            return
        # Phase 2
        phase2 = Phase2(deepcopy(branch.root), self.context)
        subbranches = self.execute_phase2(phase2)
        if len(subbranches) == 0:
            subbranches = [SELECT_EMPTY]
        # Phase 3
        # if only one subbranch, add new possibilities to the same id
        use_new_id = len(subbranches) > 1
        if use_new_id:
            branch.children_type = SetOperation.SETOP_UNION
        for subbranch, on_predicate_penalty in subbranches:
            # each subbranch has a distinguished branch id
            prototype = Branch(
                pglast.ast.SelectStmt(), 
                branch.join_level,
                branch.id, 
                branch.penalty, 
                TranslationPayload()
            )
            prototype.free = branch.free
            if not use_new_id:
                prototype.id = branch.id
            if on_predicate_penalty:
                branch.penalty.append(UnsafeOnPredicatePenalty(""))
            phase3 = Phase3(subbranch, self.context, phase2.outer_tables, deepcopy(branch.translation_payload))
            push_in_results = self.execute_phase3(phase3)
            self.new_subbranch_end_of_round(branch, prototype, push_in_results, use_new_id)
    
    def resolve_zoom_in_payload(self, branch: Branch):
        """if branch has inherited zoom_in_payload from parent and the current root does not
           have set operation, then we apply the zoom_in_payload
        """
        # execute any zoom in postponed
        if branch.zoom_in_payload is None:
            return
        # can't resolve because we still have set operation
        if branch.root.op is not SetOperation.SETOP_NONE:
            return
        top_level = TopLevelAnalyzer(branch.root)
        top_level()
        zoom_in_successful = Phase1.apply_zoom_in(branch.zoom_in_payload, branch.translation_payload, top_level)
        if not zoom_in_successful:
            subselect_alias = "inner" + str(branch.id)
            Phase1.enforce_zoom_in(branch.zoom_in_payload, top_level, subselect_alias)
        branch.root = top_level.node
        branch.zoom_in_payload = None
        
    def create_translation_payload_dummy_links(self, branch: Branch):
        """when root has no set operation and has group-by clause
           then set dummy links so that the branch is not "keyless"
        """
        root = branch.root
        if branch.translation_payload.links is not None:
            return branch
        if root.op is not SetOperation.SETOP_NONE:
            return branch
        if root.groupClause is None:
            return branch
        branch.translation_payload.links = {}
        minimal_sets = FullAnalyzer.minimal_equidependent_subset(root, root.groupClause, self.context.unique_column_tuples)
        assert(len(minimal_sets) > 0)
        for node in minimal_sets[0]:
            dummy_origin_str = BranchBuilder.DUMMY_ORIGIN + str(BranchBuilder.dummy_origin_counter.count())
            branch.translation_payload.links[dummy_origin_str] = node
        return branch
    
    def split_set_operation(self, branch: Branch):
        """if there is set operations like UNION/INTERSECTION/EXCEPT in top level,
           split them into different branches
        """
        root = branch.root
        child_roots = []
        if root.op is not SetOperation.SETOP_NONE:
            # check union/intersection/except
            branch.children_type = root.op
            child_roots.extend([root.larg, root.rarg])
        else:
            top_level_analyzer = TopLevelAnalyzer(root)
            top_level_analyzer()
            holes = top_level_analyzer.find_holes()
            # split only if we have at least 2 holes
            if (len(top_level_analyzer.target_columns) > 1 and len(holes) > 0) or len(holes) > 1:
                # means children_type is "holes"
                branch.children_type = SetOperation.SETOP_NONE
            for hole in holes:
                child_root = deepcopy(root)
                child_root.targetList = [pglast.ast.ResTarget(name=HOLE_AGG_NAME, val=deepcopy(hole))]
                child_roots.append(child_root)
        if branch.children_type is None:
            return False
        translation_payload = branch.translation_payload
        # if children_type is "holes", reset translation_payload.links so that child don't need to have same keys as parent
        if branch.children_type is SetOperation.SETOP_NONE:
            translation_payload = TranslationPayload()
        for child_root in child_roots:
            new_branch = Branch(
                child_root,
                branch.join_level,
                branch.id,
                branch.penalty,
                deepcopy(translation_payload),
                branch.zoom_in_payload
            )
            branch.children.append(new_branch.id)
            self.id_to_branch[new_branch.id] = [new_branch]
            self.next_branches.append(new_branch)
        return True
                
    def execute_phase1(self, phase1: Phase1, branch: Branch):
        """execute phase 1 logic, returns whether the current round terminates"""
        phase1.find_center_tables()
        phase1.find_clusters()
        modified = phase1.remove_irrelevant_clusters()
        idempotent_penalty = not phase1.check_idempotent() if modified else False
        resolved = False
        phase1.top_level()
        zoom_in_finished, zoom_in_successful = phase1.try_zoom_in()
        if zoom_in_finished:
            if zoom_in_successful:
                self.fork_branch_end_of_phase1(branch, phase1.node, True, idempotent_penalty, phase1.translation_payload, None)
                resolved = True
        else:
            # need to postpone zoom in because center table has set operation
            inner_root = phase1.set_op_inner_root_with_where()
            # for simplicity, for now do not support value_map zoom in
            translation_payload = deepcopy(branch.translation_payload)
            translation_payload.value_map = {}
            self.fork_branch_end_of_phase1(branch, inner_root, True, idempotent_penalty, translation_payload, phase1)
            resolved = True
        # zoom in finished in failure
        if phase1.check_free_from_center():
            self.free_branch_end_of_phase1(branch, phase1.node, idempotent_penalty)
            resolved = True
        if modified and not resolved:
            self.fork_branch_end_of_phase1(branch, phase1.node, False, idempotent_penalty, phase1.translation_payload, None)
        return not modified and resolved
    
    def fork_branch_end_of_phase1(
        self, 
        origin: Branch, 
        root: pglast.ast.SelectStmt,
        increment_join_level: bool, 
        idempotent_penalty: bool,
        translation_payload: TranslationPayload,
        zoom_in_payload: Phase1
        ):
        """create a modified copy of origin that has same id as origin, and push it to next_branches"""
        forked = deepcopy(origin)
        forked.root = root
        if increment_join_level:
            forked.join_level += 1
        if idempotent_penalty:
            forked.penalty.append(NotIdempotentPenalty(""))
        forked.children = []
        forked.children_type = None
        forked.translation_payload = translation_payload
        forked.zoom_in_payload = zoom_in_payload
        if self.add_branch_of_id(origin.id, forked):
            self.next_branches.append(forked)

    def free_branch_end_of_phase1(self, origin: Branch, root: pglast.ast.SelectStmt, idempotent_penalty: bool):
        """create a free branch of given root, , and push it to next_branches"""
        forked = deepcopy(origin)
        forked.root = root
        forked.join_level = 0
        if idempotent_penalty:
            forked.penalty.append(NotIdempotentPenalty(""))
        forked.children = []
        forked.children_type = None
        forked.translation_payload.links = None
        forked.free = True
        self.id_to_branch[origin.id].append(forked)
        if self.add_branch_of_id(origin.id, forked):
            self.next_branches.append(forked)
    
    def execute_phase2(self, phase2: Phase2):
        """execute phase 2 logic, returns a list of (subbranch, penalty) where the union of subbranches will be the parent branch"""
        phase2.find_outer_tables()
        phase2.replace_between_and()
        case_branches = phase2.expand_crossing_case_when()
        subbranches = []
        for index, case_branch in enumerate(case_branches):
            conjunct_branches, on_predicate_penalty = phase2.expand_crossing_conjuncts(case_branch)
            for conjunct_branch in conjunct_branches:
                subbranches.append((conjunct_branch, on_predicate_penalty))
        return subbranches
    
    def execute_phase3(self, phase3: Phase3):
        """execute phase 3 logic, returns a list of (result ast.SelectStmt, keys, pushed_in, translate_penalty, center_unique_penalty) of this round"""
        # first node is default node: don't push in
        results = [(deepcopy(phase3.node), deepcopy(phase3.translation_payload), False, 0, False)]
        if len(phase3.outer_tables) == 0:
            # nothing to push in
            return results
        # if translation_payload.links is dummy, reset it to None so that it can be reinitialized
        if phase3.translation_payload.links is not None and \
            any(BranchBuilder.check_dummy_origin_str(origin_str) for origin_str in phase3.translation_payload.links):
            phase3.translation_payload.links = None
        phase3.construct_equality_graph()
        keys_outer = None
        all_one_to_one_success, center_is_unique_success = False, False
        center_is_unique = phase3.check_center_is_unique()
        if phase3.check_all_one_to_one():
            # try to push in with all-one-to-one rule
            keys_outer = phase3.untranslated_inner_keys_from_center()
            all_one_to_one_success = phase3.construct_translate_map(keys_outer)
        if not all_one_to_one_success:
            # if all-one-to-one rule doesn't work, use center-is-unique rule
            keys_outer = phase3.outer_columns_in_equalities()
            center_is_unique_success = phase3.construct_translate_map(keys_outer)
        if not all_one_to_one_success and not center_is_unique_success:
            # can't push in
            return results

        phase3.update_translation_payload()
        translate_penalty = phase3.prepare_for_push_in()
        # actually push in
        center_unique_penalty = False if all_one_to_one_success else not center_is_unique
        root_pushed_in = phase3.push_in_with_keys(keys_outer)
        results.append((root_pushed_in, phase3.translation_payload, True, translate_penalty, center_unique_penalty))
        return results
    
    def new_subbranch_end_of_round(self, parent: Branch, prototype: Branch, push_in_results, use_new_id: bool):
        """create new branches out of a subbranch of origin branch"""
        if use_new_id:
            id = prototype.id
            self.id_to_branch[id] = []
            parent.children.append(id)
        else:
            id = parent.id
        for index, push_in_result in enumerate(push_in_results):
            new_branch = deepcopy(prototype)
            BranchBuilder.process_branch_end_of_round(new_branch, *push_in_result)
            # do not explore the default node if single subbranch; see execute_phase3
            if self.add_branch_of_id(id, new_branch) and (use_new_id or index > 0):
                self.next_branches.append(new_branch) 
            
    @staticmethod
    def process_branch_end_of_round(
        branch: Branch, 
        root: pglast.ast.SelectStmt, 
        translation_payload: TranslationPayload, 
        pushed_in: bool,
        translate_penalty: int, 
        center_unique_penalty: bool
        ):
        """update branch to reflect push in results """
        branch.root = root
        branch.translation_payload = translation_payload
        if root.fromClause is None:
            branch.free = True
            branch.translation_payload.links = None
        if pushed_in:
            branch.join_level += 1
        for _ in range(translate_penalty):
            branch.penalty.append(RemovePredicatePenalty(""))
        if center_unique_penalty:
            branch.penalty.append(CenterNotUniquePenalty(""))