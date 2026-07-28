#!/usr/bin/env python3
"""Frozen B/F ablation for proof-carrying forward demodulation.

This is diagnostic-only.  It loads the frozen embedded Stair-climber
paramodulator, leaves the production solver untouched, and represents every
demodulation as an ordinary recorded paramodulation step so the existing
translator and an independently authored MathGraph plan replayer can check it.
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
import importlib.util
import json
import platform
import re
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
SOLVER = ROOT / "submissions/mathgraph/solver.py"
sys.path.insert(0, str(ROOT))
EXPECTED_SOLVER_SHA256 = (
    "fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1"
)
DEFAULT_INPUT = Path("/tmp/mathgraph-six-residuals.json")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_solver():
    if sha256(SOLVER) != EXPECTED_SOLVER_SHA256:
        raise RuntimeError("production solver is not the frozen 794/800 build")
    spec = importlib.util.spec_from_file_location("mathgraph_demod_frozen", SOLVER)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def load_independent_replayer():
    path = ROOT / "experiments/mathgraph/audit_stair_climber_components.py"
    spec = importlib.util.spec_from_file_location("mathgraph_plan_replayer", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def judge(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    started = time.monotonic()
    result = verify_answer(
        _to_judge_problem(problem),
        json.dumps({"verdict": "true", "code": code}),
    )
    return result, time.monotonic() - started


def prepare_engine(module):
    engine, external_replay = module._load_stair_specialist()
    aliases = {
        "Clause": "pm_Clause",
        "all_paths": "pm_all_paths",
        "alpha_key": "pm_alpha_key",
        "can_close": "pm_can_close",
        "clause_weight": "pm_clause_weight",
        "formula": "pm_formula",
        "infer_paramod": "pm_infer_paramod",
        "instantiate_goal": "pm_instantiate_goal",
        "parse_equation": "pm_parse_equation",
        "prove": "pm_prove",
        "quantified_line": "pm_quantified_line",
        "rewrite_sides": "pm_rewrite_sides",
        "term_identical": "pm_term_identical",
        "term_size": "pm_term_size",
        "term_str": "pm_p9p_term_str",
        "translate_proof": "pm_p9t_translate_proof",
        "vars_in_equation": "pm_vars_in_equation",
    }
    for name, source in aliases.items():
        engine[name] = engine[source]
    return engine, external_replay


class ForwardDemodulationRun:
    """A minimal configurable fork of the frozen given-clause loop."""

    def __init__(
        self,
        engine,
        problem,
        args,
        *,
        forward_demodulation=True,
        scheduler=False,
        local_demodulation=False,
        dual_retention=False,
        per_given_budget=None,
        global_budget=None,
        quotient_mode=False,
        expose_all_representatives=False,
        merge_passive_classes=False,
        operation_relative_representatives=False,
        lazy_representative_materialization=False,
        continuation_novelty=False,
        corridor_lookahead=False,
        trace_events=False,
        blocked_demodulation_signatures=(),
    ):
        self.e = engine
        self.problem = problem
        self.args = args
        self.forward_demodulation = forward_demodulation
        self.scheduler = scheduler
        self.local_demodulation = local_demodulation
        self.dual_retention = dual_retention
        self.per_given_budget = per_given_budget
        self.global_budget = global_budget
        self.quotient_mode = quotient_mode
        self.expose_all_representatives = expose_all_representatives
        self.merge_passive_classes = merge_passive_classes
        self.operation_relative_representatives = (
            operation_relative_representatives
        )
        self.lazy_representative_materialization = (
            lazy_representative_materialization
        )
        self.continuation_novelty = continuation_novelty
        self.corridor_lookahead = corridor_lookahead
        self.trace_events = trace_events
        self.blocked_demodulation_signatures = frozenset(
            blocked_demodulation_signatures
        )
        self.metrics = {
            "demodulation_queries": 0,
            "demodulation_attempts": 0,
            "forward_demodulations": 0,
            "clauses_reduced": 0,
            "trivial_after_demodulation": 0,
            "demodulation_weight_reduction": 0,
            "demodulation_proof_nodes": 0,
            "duplicate_deleted": 0,
            "subsumed_deleted": 0,
            "tautology_deleted": 0,
            "peak_passive": 0,
            "peak_active": 0,
            "superposition_candidates": 0,
            "selected_by_age": 0,
            "selected_by_weight": 0,
            "selected_by_goal": 0,
            "goal_relevant_selected": 0,
            "raw_children_retained": 0,
            "simplified_siblings_retained": 0,
            "demodulation_budget_exhaustions": 0,
            "clause_classes_created": 0,
            "representative_updates": 0,
            "maximum_representatives_per_class": 0,
            "quotient_merge_opportunities": 0,
            "passive_classes_merged": 0,
            "continuation_signatures_computed": 0,
            "continuation_operations_checked": 0,
            "candidate_contractions_checked": 0,
            "contractions_without_operational_novelty": 0,
            "operationally_novel_materializations": 0,
            "novel_continuations_created": 0,
            "novel_frontier_partners_created": 0,
            "novel_inferences_attempted": 0,
            "novel_inferences_retained": 0,
            "corridor_candidates_checked": 0,
            "corridor_materializations": 0,
        }
        self.parent_ids = {}
        self.demodulation_ids = set()
        self.superposition_ids = set()
        self.selection_events = []
        self.demodulation_events = {}
        self.raw_child_events = []
        self.continuation_materializations = {}

    def term_key(self, term):
        return self.e["term_size"](term), self.e["term_str"](term)

    def clause_key(self, clause):
        return (
            self.e["clause_weight"](clause),
            self.e["term_str"](clause.lhs),
            self.e["term_str"](clause.rhs),
            clause.polarity,
        )

    def clause_snapshot(self, clause):
        return {
            "polarity": clause.polarity,
            "lhs": self.e["term_str"](clause.lhs),
            "rhs": self.e["term_str"](clause.rhs),
            "weight": self.e["clause_weight"](clause),
            "depth": clause.depth,
            "alpha_key": repr(
                self.e["alpha_key"](clause.lhs, clause.rhs, clause.polarity)
            ),
        }

    def demodulation_signature(
        self,
        demodulator,
        current,
        from_side,
        into_side,
        path,
        candidate,
    ):
        record = {
            "demodulator": self.clause_snapshot(demodulator),
            "before": self.clause_snapshot(current),
            "from_side": from_side,
            "into_side": into_side,
            "path": list(path),
            "after": self.clause_snapshot(candidate),
        }
        encoded = json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(encoded).hexdigest(), record

    def term_at_path(self, term, path):
        current = term
        for direction in path:
            current = current[1] if direction in (1, "L") else current[2]
        return current

    def strict_demodulator_sides(self, clause):
        output = []
        for side in self.e["rewrite_sides"](clause, False):
            lhs, rhs = (
                (clause.lhs, clause.rhs)
                if side == 1
                else (clause.rhs, clause.lhs)
            )
            if lhs[0] != "var" and self.term_key(lhs) > self.term_key(rhs):
                output.append(side)
        return tuple(output)

    def solve(self):
        e = self.e
        args = self.args
        eq1_lhs, eq1_rhs = e["parse_equation"](self.problem["equation1"])
        eq2_lhs, eq2_rhs = e["parse_equation"](self.problem["equation2"])
        goal_vars = e["vars_in_equation"](eq2_lhs, eq2_rhs)
        skolem_map = {variable: f"c{index + 1}" for index, variable in enumerate(goal_vars)}
        rigid = set(skolem_map.values())
        Clause = e["Clause"]
        clauses = {
            "1": Clause("1", "pos", eq1_lhs, eq1_rhs, "assumption", 0),
            "2": Clause("2", "pos", eq2_lhs, eq2_rhs, "goal", 0),
            "3": Clause("3", "pos", eq1_lhs, eq1_rhs, "clausify(1)", 0),
            "4": Clause(
                "4",
                "neg",
                e["instantiate_goal"](eq2_lhs, skolem_map),
                e["instantiate_goal"](eq2_rhs, skolem_map),
                "deny(2)",
                0,
            ),
        }
        seen = {
            e["alpha_key"](clauses["3"].lhs, clauses["3"].rhs, "pos"),
            e["alpha_key"](clauses["4"].lhs, clauses["4"].rhs, "neg"),
        }
        queue = []
        age_queue = []
        goal_queue = []
        sequence = 0
        positives = [] if self.quotient_mode else ["3"]
        inference_ids = ["3", "4"]
        searchable_ids = [] if self.quotient_mode else inference_ids
        active = []
        demodulators = []
        generated = 0
        retained = 2
        processed = set()
        next_id = 5
        closed_id = None
        started = time.monotonic()
        global_demodulations = 0
        remaining_given_demodulations = 0
        current_given_goal_score = 0
        class_of = {}
        classes = {}
        retired_classes = set()
        key_clause = {
            e["alpha_key"](clauses["3"].lhs, clauses["3"].rhs, "pos"): "3",
            e["alpha_key"](clauses["4"].lhs, clauses["4"].rhs, "neg"): "4",
        }
        next_class = 1
        denied_subterms = {
            e["term_str"](subterm)
            for term in (clauses["4"].lhs, clauses["4"].rhs)
            for path in e["all_paths"](term)
            for subterm in [self.term_at_path(term, path)]
        }

        def goal_score(clause):
            overlap = 0
            for term in (clause.lhs, clause.rhs):
                for path in e["all_paths"](term):
                    if e["term_str"](self.term_at_path(term, path)) in denied_subterms:
                        overlap += 1
            return overlap + (8 if clause.polarity == "neg" else 0)

        def goal_descended(clause_id):
            pending = [clause_id]
            visited = set()
            while pending:
                current = pending.pop()
                if current == "4":
                    return True
                if current in visited:
                    continue
                visited.add(current)
                pending.extend(self.parent_ids.get(current, ()))
            return False

        def continuation_signature(representative_id, frontier_ids):
            """Exact legal inferences currently exposed by one representation."""
            self.metrics["continuation_signatures_computed"] += 1
            representative = clauses[representative_id]
            frontier_version = len(processed)
            records = {}
            checks = 0

            def retain(
                role,
                partner_id,
                from_side,
                into_side,
                path,
                candidate,
            ):
                nonlocal checks
                checks += 1
                self.metrics["continuation_operations_checked"] += 1
                if candidate is None:
                    return
                result_key = repr(
                    e["alpha_key"](
                        candidate.lhs,
                        candidate.rhs,
                        candidate.polarity,
                    )
                )
                partner = clauses[partner_id]
                key = (
                    role,
                    repr(
                        e["alpha_key"](
                            partner.lhs, partner.rhs, partner.polarity
                        )
                    ),
                    from_side,
                    into_side,
                    tuple(path),
                    result_key,
                )
                records.setdefault(
                    key,
                    {
                        "frontier_version": frontier_version,
                        "role": role,
                        "partner_id": partner_id,
                        "partner_alpha_key": key[1],
                        "representation_id": representative_id,
                        "representation_alpha_key": repr(
                            e["alpha_key"](
                                representative.lhs,
                                representative.rhs,
                                representative.polarity,
                            )
                        ),
                        "literal_side": into_side,
                        "term_path": list(path),
                        "orientation": from_side,
                        "result_alpha_key": result_key,
                        "goal_descended_partner": goal_descended(partner_id),
                        "would_close": (
                            candidate.polarity == "neg"
                            and e["can_close"](candidate, rigid)
                        ),
                        "result_goal_score": goal_score(candidate),
                    },
                )

            if representative.polarity == "neg" and e["can_close"](
                representative, rigid
            ):
                records[("denied_goal_closure",)] = {
                    "frontier_version": frontier_version,
                    "role": "denied-goal-closure",
                    "partner_id": "4",
                    "partner_alpha_key": repr(
                        e["alpha_key"](
                            clauses["4"].lhs,
                            clauses["4"].rhs,
                            clauses["4"].polarity,
                        )
                    ),
                    "representation_id": representative_id,
                    "representation_alpha_key": repr(
                        e["alpha_key"](
                            representative.lhs,
                            representative.rhs,
                            representative.polarity,
                        )
                    ),
                    "literal_side": None,
                    "term_path": [],
                    "orientation": None,
                    "result_alpha_key": "$F",
                    "goal_descended_partner": True,
                    "would_close": True,
                    "result_goal_score": goal_score(representative),
                }
            if representative.polarity == "pos":
                for partner_id in frontier_ids:
                    partner = clauses[partner_id]
                    for from_side in e["rewrite_sides"](
                        representative, args.unordered
                    ):
                        for into_side in (1, 2):
                            term = (
                                partner.lhs
                                if into_side == 1
                                else partner.rhs
                            )
                            for path in sorted(
                                e["all_paths"](term),
                                key=lambda item: (len(item), item),
                            ):
                                if checks >= 512:
                                    return records
                                retain(
                                    "superposition-source",
                                    partner_id,
                                    from_side,
                                    into_side,
                                    path,
                                    e["infer_paramod"](
                                        representative,
                                        partner,
                                        from_side,
                                        into_side,
                                        path,
                                        generated + next_id + checks,
                                        rigid,
                                    ),
                                )
            for partner_id in frontier_ids:
                partner = clauses[partner_id]
                if partner.polarity != "pos":
                    continue
                for from_side in e["rewrite_sides"](
                    partner, args.unordered
                ):
                    for into_side in (1, 2):
                        term = (
                            representative.lhs
                            if into_side == 1
                            else representative.rhs
                        )
                        for path in sorted(
                            e["all_paths"](term),
                            key=lambda item: (len(item), item),
                        ):
                            if checks >= 512:
                                return records
                            retain(
                                "superposition-target",
                                partner_id,
                                from_side,
                                into_side,
                                path,
                                e["infer_paramod"](
                                    partner,
                                    representative,
                                    from_side,
                                    into_side,
                                    path,
                                    generated + next_id + checks,
                                    rigid,
                                ),
                            )
            return records

        def enqueue(clause_id):
            nonlocal sequence, next_class
            clause = clauses[clause_id]
            queue_id = clause_id
            if self.quotient_mode:
                class_id = class_of.get(clause_id)
                if class_id is None:
                    class_id = f"q{next_class}"
                    next_class += 1
                    class_of[clause_id] = class_id
                    classes[class_id] = {
                        "raw": clause_id,
                        "cheapest": clause_id,
                        "goal": clause_id,
                        "age": sequence,
                    }
                    self.metrics["clause_classes_created"] += 1
                else:
                    record = classes[class_id]
                    if self.clause_key(clause) < self.clause_key(
                        clauses[record["cheapest"]]
                    ):
                        record["cheapest"] = clause_id
                    if (
                        goal_score(clause),
                        tuple(-value if isinstance(value, int) else value for value in self.clause_key(clause)[:1]),
                    ) > (
                        goal_score(clauses[record["goal"]]),
                        tuple(-value if isinstance(value, int) else value for value in self.clause_key(clauses[record["goal"]])[:1]),
                    ):
                        record["goal"] = clause_id
                    self.metrics["representative_updates"] += 1
                    count = len(
                        {
                            record["raw"],
                            record["cheapest"],
                            record["goal"],
                        }
                    )
                    self.metrics["maximum_representatives_per_class"] = max(
                        self.metrics["maximum_representatives_per_class"], count
                    )
                    return
                queue_id = class_id
            priority = (
                (args.neg_bias if clause.polarity == "neg" else 0)
                + e["clause_weight"](clause)
                + clause.depth
            )
            heapq.heappush(queue, (priority, sequence, queue_id))
            if self.scheduler:
                heapq.heappush(age_queue, (sequence, queue_id))
                score = goal_score(clause)
                heapq.heappush(goal_queue, (-score, priority, sequence, queue_id))
            sequence += 1

        enqueue("3")
        enqueue("4")

        def allocate(clause, retain, kind):
            nonlocal next_id, generated, retained
            clause.id = str(next_id)
            next_id += 1
            clauses[clause.id] = clause
            inference_ids.append(clause.id)
            generated += 1
            if retain:
                retained += 1
            match = re.search(
                r"para\((\d+)\([^)]*\),(\d+)\(",
                clause.justification,
            )
            self.parent_ids[clause.id] = (
                (match.group(1), match.group(2)) if match else ()
            )
            if (
                self.quotient_mode
                and kind == "demodulation"
                and self.parent_ids[clause.id]
            ):
                target_parent = self.parent_ids[clause.id][1]
                if target_parent in class_of:
                    class_of[clause.id] = class_of[target_parent]
            if kind == "demodulation":
                self.demodulation_ids.add(clause.id)
            elif kind == "superposition":
                self.superposition_ids.add(clause.id)
            return clause.id

        def materialize_with_demodulation(raw):
            """Store a proof-only raw node and retain only its normal form."""
            nonlocal closed_id, retained
            nonlocal global_demodulations, remaining_given_demodulations
            if (
                generated >= args.max_clauses
                or e["clause_weight"](raw) > args.max_weight
                or e["term_size"](raw.lhs) > args.max_term_size
                or e["term_size"](raw.rhs) > args.max_term_size
            ):
                return None
            if self.dual_retention:
                raw_key = e["alpha_key"](raw.lhs, raw.rhs, raw.polarity)
                if raw_key in seen:
                    self.metrics["duplicate_deleted"] += 1
                    return None
                raw_id = allocate(raw, True, "superposition")
                seen.add(raw_key)
                key_clause[raw_key] = raw_id
                enqueue(raw_id)
                self.metrics["raw_children_retained"] += 1
                if raw.polarity == "pos":
                    positives.append(raw_id)
                if raw.polarity == "neg" and e["can_close"](raw, rigid):
                    closed_id = raw_id
                    return raw_id
                eligible = (
                    self.forward_demodulation
                    and not self.lazy_representative_materialization
                    and not self.continuation_novelty
                    and remaining_given_demodulations > 0
                    and (
                        self.global_budget is None
                        or global_demodulations < self.global_budget
                    )
                    and (
                        raw.polarity == "neg"
                        or goal_score(raw) >= current_given_goal_score
                    )
                )
                if not eligible:
                    return raw_id
                current_id = raw_id
                previous_weight = e["clause_weight"](raw)
                simplified = False
                for _ in range(remaining_given_demodulations):
                    if (
                        self.global_budget is not None
                        and global_demodulations >= self.global_budget
                    ):
                        self.metrics["demodulation_budget_exhaustions"] += 1
                        break
                    selected = None
                    for demod_id, from_side in demodulators[-8:]:
                        demodulator = clauses[demod_id]
                        current = clauses[current_id]
                        for into_side in (1, 2):
                            side_term = current.lhs if into_side == 1 else current.rhs
                            for path in sorted(
                                e["all_paths"](side_term),
                                key=lambda item: (len(item), item),
                            ):
                                self.metrics["demodulation_attempts"] += 1
                                candidate = e["infer_paramod"](
                                    demodulator,
                                    current,
                                    from_side,
                                    into_side,
                                    path,
                                    generated + next_id,
                                    rigid,
                                )
                                if (
                                    candidate is None
                                    or self.clause_key(candidate)
                                    >= self.clause_key(current)
                                    or goal_score(candidate) < goal_score(current)
                                ):
                                    continue
                                signature, event = self.demodulation_signature(
                                    demodulator,
                                    current,
                                    from_side,
                                    into_side,
                                    path,
                                    candidate,
                                )
                                if signature in self.blocked_demodulation_signatures:
                                    continue
                                selected = (
                                    candidate,
                                    signature,
                                    event,
                                    demod_id,
                                )
                                break
                            if selected is not None:
                                break
                        if selected is not None:
                            break
                    self.metrics["demodulation_queries"] += 1
                    if selected is None:
                        break
                    selected_clause, signature, event, demod_id = selected
                    parent_id = current_id
                    current_id = allocate(
                        selected_clause, False, "demodulation"
                    )
                    self.demodulation_events[current_id] = {
                        "signature": signature,
                        "proof_node": current_id,
                        "demodulator_id": demod_id,
                        "target_parent_id": parent_id,
                        **event,
                    }
                    remaining_given_demodulations -= 1
                    global_demodulations += 1
                    simplified = True
                    self.metrics["forward_demodulations"] += 1
                    self.metrics["demodulation_proof_nodes"] += 1
                    if remaining_given_demodulations <= 0:
                        break
                if not simplified:
                    return raw_id
                final = clauses[current_id]
                final_key = e["alpha_key"](
                    final.lhs, final.rhs, final.polarity
                )
                if (
                    final_key in seen
                    or (
                        final.polarity == "pos"
                        and e["term_identical"](final.lhs, final.rhs)
                    )
                ):
                    if final_key in seen and self.quotient_mode:
                        self.metrics["quotient_merge_opportunities"] += 1
                        if self.merge_passive_classes:
                            existing_id = key_clause.get(final_key)
                            current_class = class_of.get(raw_id)
                            existing_class = class_of.get(existing_id)
                            if (
                                current_class
                                and existing_class
                                and current_class != existing_class
                                and current_class not in processed
                                and existing_class not in processed
                            ):
                                target = classes[existing_class]
                                source = classes[current_class]
                                candidates = {
                                    source["raw"],
                                    source["cheapest"],
                                    source["goal"],
                                    target["raw"],
                                    target["cheapest"],
                                    target["goal"],
                                }
                                target["cheapest"] = min(
                                    candidates,
                                    key=lambda item: self.clause_key(
                                        clauses[item]
                                    ),
                                )
                                target["goal"] = min(
                                    candidates,
                                    key=lambda item: (
                                        -goal_score(clauses[item]),
                                        self.clause_key(clauses[item]),
                                    ),
                                )
                                for representative in candidates:
                                    class_of[representative] = existing_class
                                retired_classes.add(current_class)
                                self.metrics["passive_classes_merged"] += 1
                    return raw_id
                seen.add(final_key)
                key_clause[final_key] = current_id
                retained += 1
                enqueue(current_id)
                self.metrics["simplified_siblings_retained"] += 1
                self.metrics["clauses_reduced"] += 1
                self.metrics["demodulation_weight_reduction"] += (
                    previous_weight - e["clause_weight"](final)
                )
                if final.polarity == "pos":
                    positives.append(current_id)
                if final.polarity == "neg" and e["can_close"](final, rigid):
                    closed_id = current_id
                return current_id
            current = raw
            plan = []
            demodulation_limit = 4 if self.local_demodulation else 64
            eligible_demodulators = (
                demodulators[-8:] if self.local_demodulation else demodulators
            )
            initial_goal_score = goal_score(raw)
            for _ in range(demodulation_limit):
                selected = None
                if not self.forward_demodulation:
                    break
                for demod_id, from_side in eligible_demodulators:
                    demodulator = clauses[demod_id]
                    for into_side in (1, 2):
                        side_term = current.lhs if into_side == 1 else current.rhs
                        for path in sorted(e["all_paths"](side_term), key=lambda item: (len(item), item)):
                            self.metrics["demodulation_attempts"] += 1
                            candidate = e["infer_paramod"](
                                demodulator,
                                current,
                                from_side,
                                into_side,
                                path,
                                generated + len(plan) + next_id,
                                rigid,
                            )
                            if candidate is None or self.clause_key(candidate) >= self.clause_key(current):
                                continue
                            if (
                                self.local_demodulation
                                and goal_score(candidate) < initial_goal_score
                            ):
                                continue
                            signature, event = self.demodulation_signature(
                                demodulator,
                                current,
                                from_side,
                                into_side,
                                path,
                                candidate,
                            )
                            if signature in self.blocked_demodulation_signatures:
                                continue
                            selected = (
                                demod_id,
                                from_side,
                                into_side,
                                path,
                                candidate,
                                signature,
                                event,
                            )
                            break
                        if selected is not None:
                            break
                    if selected is not None:
                        break
                self.metrics["demodulation_queries"] += 1
                if selected is None:
                    break
                plan.append(
                    (
                        *selected[:4],
                        selected[5],
                        selected[6],
                    )
                )
                current = selected[4]
            key = e["alpha_key"](current.lhs, current.rhs, current.polarity)
            if key in seen:
                self.metrics["duplicate_deleted"] += 1
                return None
            raw_id = allocate(raw, False, "superposition")
            current_id = raw_id
            previous_weight = e["clause_weight"](raw)
            for demod_id, from_side, into_side, path, signature, event in plan:
                parent_id = current_id
                step = e["infer_paramod"](
                    clauses[demod_id],
                    clauses[current_id],
                    from_side,
                    into_side,
                    path,
                    generated + next_id,
                    rigid,
                )
                if step is None:
                    raise RuntimeError("demodulation materialization diverged")
                current_id = allocate(step, False, "demodulation")
                self.demodulation_events[current_id] = {
                    "signature": signature,
                    "proof_node": current_id,
                    "demodulator_id": demod_id,
                    "target_parent_id": parent_id,
                    **event,
                }
                self.metrics["forward_demodulations"] += 1
                self.metrics["demodulation_proof_nodes"] += 1
            final = clauses[current_id]
            if plan:
                self.metrics["clauses_reduced"] += 1
                self.metrics["demodulation_weight_reduction"] += (
                    previous_weight - e["clause_weight"](final)
                )
            if final.polarity == "pos" and e["term_identical"](final.lhs, final.rhs):
                self.metrics["trivial_after_demodulation"] += 1
                return None
            seen.add(key)
            retained += 1
            enqueue(current_id)
            if final.polarity == "pos":
                positives.append(current_id)
            if final.polarity == "neg" and e["can_close"](final, rigid):
                closed_id = current_id
            return current_id

        while (
            queue
            and generated < args.max_clauses
            and len(processed) < args.max_processed
            and time.monotonic() - started < args.timeout
        ):
            self.metrics["peak_passive"] = max(self.metrics["peak_passive"], len(queue))
            if self.scheduler:
                selection_number = len(processed)
                use_goal = selection_number % 4 == 3
                use_age = selection_number % 5 == 0
                selected_from = "weight"
                selected_heap = queue
                if use_goal:
                    selected_from = "goal"
                    selected_heap = goal_queue
                elif use_age:
                    selected_from = "age"
                    selected_heap = age_queue
                queue_id = None
                while selected_heap:
                    item = heapq.heappop(selected_heap)
                    candidate_id = item[-1]
                    if candidate_id not in processed:
                        queue_id = candidate_id
                        break
                if queue_id is None:
                    continue
                self.metrics[f"selected_by_{selected_from}"] += 1
            else:
                _priority, _sequence, queue_id = heapq.heappop(queue)
            if queue_id in processed:
                continue
            if self.quotient_mode and queue_id in retired_classes:
                continue
            processed.add(queue_id)
            if self.quotient_mode:
                record = classes[queue_id]
                if self.continuation_novelty:
                    retained_before = {
                        record["raw"],
                        record["cheapest"],
                        record["goal"],
                    }
                    baseline_signature = {}
                    for representative in retained_before:
                        baseline_signature.update(
                            continuation_signature(
                                representative, list(searchable_ids)
                            )
                        )
                    contraction_candidates = []
                    eligible_contractions_checked = 0
                    raw_id = record["raw"]
                    raw_clause = clauses[raw_id]
                    for demod_id, from_side in demodulators[-8:]:
                        demodulator = clauses[demod_id]
                        for into_side in (1, 2):
                            side_term = (
                                raw_clause.lhs
                                if into_side == 1
                                else raw_clause.rhs
                            )
                            for path in sorted(
                                e["all_paths"](side_term),
                                key=lambda item: (len(item), item),
                            ):
                                candidate = e["infer_paramod"](
                                    demodulator,
                                    raw_clause,
                                    from_side,
                                    into_side,
                                    path,
                                    generated + next_id,
                                    rigid,
                                )
                                if (
                                    candidate is None
                                    or self.clause_key(candidate)
                                    >= self.clause_key(raw_clause)
                                ):
                                    continue
                                eligible_contractions_checked += 1
                                self.metrics[
                                    "candidate_contractions_checked"
                                ] += 1
                                temporary_id = (
                                    f"continuation_probe_{queue_id}_"
                                    f"{len(contraction_candidates)}"
                                )
                                candidate.id = temporary_id
                                clauses[temporary_id] = candidate
                                candidate_signature = continuation_signature(
                                    temporary_id, list(searchable_ids)
                                )
                                all_novel = {
                                    key: value
                                    for key, value in candidate_signature.items()
                                    if key not in baseline_signature
                                }
                                novel = {
                                    key: value
                                    for key, value in all_novel.items()
                                    if (
                                        value["would_close"]
                                        or value["goal_descended_partner"]
                                        or value["result_goal_score"] > 0
                                    )
                                }
                                corridor = None
                                if (
                                    not novel
                                    and self.corridor_lookahead
                                    and all_novel
                                ):
                                    self.metrics[
                                        "corridor_candidates_checked"
                                    ] += 1
                                    first_key, first_continuation = min(
                                        all_novel.items(),
                                        key=lambda item: (
                                            not item[1][
                                                "goal_descended_partner"
                                            ],
                                            item[1]["role"],
                                            item[1][
                                                "partner_alpha_key"
                                            ],
                                            item[1]["literal_side"] or 0,
                                            tuple(item[1]["term_path"]),
                                            item[1]["orientation"] or 0,
                                            item[1][
                                                "result_alpha_key"
                                            ],
                                        ),
                                    )
                                    partner_id = first_continuation[
                                        "partner_id"
                                    ]
                                    partner = clauses[partner_id]
                                    if (
                                        first_continuation["role"]
                                        == "superposition-source"
                                    ):
                                        child = e["infer_paramod"](
                                            candidate,
                                            partner,
                                            first_continuation[
                                                "orientation"
                                            ],
                                            first_continuation[
                                                "literal_side"
                                            ],
                                            tuple(
                                                first_continuation[
                                                    "term_path"
                                                ]
                                            ),
                                            generated + next_id + 1,
                                            rigid,
                                        )
                                    else:
                                        child = e["infer_paramod"](
                                            partner,
                                            candidate,
                                            first_continuation[
                                                "orientation"
                                            ],
                                            first_continuation[
                                                "literal_side"
                                            ],
                                            tuple(
                                                first_continuation[
                                                    "term_path"
                                                ]
                                            ),
                                            generated + next_id + 1,
                                            rigid,
                                        )
                                    if child is not None:
                                        child_id = (
                                            f"{temporary_id}_corridor_child"
                                        )
                                        child.id = child_id
                                        clauses[child_id] = child
                                        child_signature = (
                                            continuation_signature(
                                                child_id,
                                                list(searchable_ids),
                                            )
                                        )
                                        del clauses[child_id]
                                        child_novel = {
                                            key: value
                                            for key, value in (
                                                child_signature.items()
                                            )
                                            if (
                                                value["would_close"]
                                                or value[
                                                    "goal_descended_partner"
                                                ]
                                                or value[
                                                    "result_goal_score"
                                                ]
                                                > 0
                                            )
                                        }
                                        if child_novel:
                                            novel = {
                                                first_key:
                                                first_continuation
                                            }
                                            corridor = {
                                                "first_continuation":
                                                first_continuation,
                                                "child_alpha_key": repr(
                                                    e["alpha_key"](
                                                        child.lhs,
                                                        child.rhs,
                                                        child.polarity,
                                                    )
                                                ),
                                                "child_novel_count": len(
                                                    child_novel
                                                ),
                                            }
                                del clauses[temporary_id]
                                if not novel:
                                    self.metrics[
                                        "contractions_without_operational_novelty"
                                    ] += 1
                                    continue
                                partners = {
                                    value["partner_alpha_key"]
                                    for value in novel.values()
                                }
                                closes = any(
                                    value["would_close"]
                                    for value in novel.values()
                                )
                                goal_partners = sum(
                                    bool(value["goal_descended_partner"])
                                    for value in novel.values()
                                )
                                candidate_demodulation_signature, _ = (
                                    self.demodulation_signature(
                                        demodulator,
                                        raw_clause,
                                        from_side,
                                        into_side,
                                        path,
                                        candidate,
                                    )
                                )
                                if (
                                    candidate_demodulation_signature
                                    in self.blocked_demodulation_signatures
                                ):
                                    continue
                                contraction_candidates.append(
                                    {
                                        "candidate": candidate,
                                        "demodulator_id": demod_id,
                                        "from_side": from_side,
                                        "into_side": into_side,
                                        "path": path,
                                        "novel": novel,
                                        "corridor": corridor,
                                        "signature":
                                        candidate_demodulation_signature,
                                        "rank": (
                                            int(closes),
                                            goal_partners,
                                            len(partners),
                                            len(novel),
                                            -candidate.depth,
                                            -e["term_size"](candidate.lhs)
                                            - e["term_size"](candidate.rhs),
                                            e["term_str"](candidate.lhs),
                                            e["term_str"](candidate.rhs),
                                        ),
                                    }
                                )
                                candidate_limit = (
                                    1 if self.corridor_lookahead else 16
                                )
                                if (
                                    len(contraction_candidates)
                                    >= candidate_limit
                                    or (
                                        self.corridor_lookahead
                                        and eligible_contractions_checked >= 1
                                    )
                                ):
                                    break
                            if (
                                len(contraction_candidates)
                                >= (
                                    1
                                    if self.corridor_lookahead
                                    else 16
                                )
                                or (
                                    self.corridor_lookahead
                                    and eligible_contractions_checked >= 1
                                )
                            ):
                                break
                        if (
                            len(contraction_candidates)
                            >= (
                                1 if self.corridor_lookahead else 16
                            )
                            or (
                                self.corridor_lookahead
                                and eligible_contractions_checked >= 1
                            )
                        ):
                            break
                    if contraction_candidates and (
                        self.global_budget is None
                        or global_demodulations < self.global_budget
                    ):
                        selected_contraction = max(
                            contraction_candidates,
                            key=lambda item: item["rank"],
                        )
                        candidate = selected_contraction["candidate"]
                        demod_id = selected_contraction["demodulator_id"]
                        from_side = selected_contraction["from_side"]
                        into_side = selected_contraction["into_side"]
                        path = selected_contraction["path"]
                        signature, event = self.demodulation_signature(
                            clauses[demod_id],
                            raw_clause,
                            from_side,
                            into_side,
                            path,
                            candidate,
                        )
                        if signature != selected_contraction["signature"]:
                            raise RuntimeError(
                                "continuation contraction signature diverged"
                            )
                        candidate.id = str(next_id)
                        contracted_id = allocate(
                            candidate, False, "demodulation"
                        )
                        class_of[contracted_id] = queue_id
                        self.demodulation_events[contracted_id] = {
                            "signature": signature,
                            "proof_node": contracted_id,
                            "demodulator_id": demod_id,
                            "target_parent_id": raw_id,
                            **event,
                        }
                        novel_records = list(
                            selected_contraction["novel"].values()
                        )
                        for value in novel_records:
                            value["representation_id"] = contracted_id
                        self.continuation_materializations[contracted_id] = {
                            "frontier_version": len(processed),
                            "class_id": queue_id,
                            "raw_id": raw_id,
                            "contracted_id": contracted_id,
                            "novel_continuations": novel_records,
                            "attempted_novel_keys": [],
                            "retained_novel_keys": [],
                            "corridor_preview": selected_contraction[
                                "corridor"
                            ],
                        }
                        record["cheapest"] = contracted_id
                        if goal_score(clauses[contracted_id]) >= goal_score(
                            clauses[record["goal"]]
                        ):
                            record["goal"] = contracted_id
                        global_demodulations += 1
                        self.metrics["forward_demodulations"] += 1
                        self.metrics["demodulation_proof_nodes"] += 1
                        self.metrics[
                            "operationally_novel_materializations"
                        ] += 1
                        if selected_contraction["corridor"] is not None:
                            self.metrics["corridor_materializations"] += 1
                        self.metrics["novel_continuations_created"] += len(
                            novel_records
                        )
                        self.metrics[
                            "novel_frontier_partners_created"
                        ] += len(
                            {
                                value["partner_alpha_key"]
                                for value in novel_records
                            }
                        )
                elif self.lazy_representative_materialization:
                    current_id = record["raw"]
                    for _ in range(self.per_given_budget or 0):
                        if (
                            self.global_budget is not None
                            and global_demodulations >= self.global_budget
                        ):
                            self.metrics[
                                "demodulation_budget_exhaustions"
                            ] += 1
                            break
                        selected = None
                        for demod_id, from_side in demodulators[-8:]:
                            demodulator = clauses[demod_id]
                            current = clauses[current_id]
                            for into_side in (1, 2):
                                side_term = (
                                    current.lhs
                                    if into_side == 1
                                    else current.rhs
                                )
                                for path in sorted(
                                    e["all_paths"](side_term),
                                    key=lambda item: (len(item), item),
                                ):
                                    self.metrics[
                                        "demodulation_attempts"
                                    ] += 1
                                    candidate = e["infer_paramod"](
                                        demodulator,
                                        current,
                                        from_side,
                                        into_side,
                                        path,
                                        generated + next_id,
                                        rigid,
                                    )
                                    if (
                                        candidate is None
                                        or self.clause_key(candidate)
                                        >= self.clause_key(current)
                                    ):
                                        continue
                                    selected = (
                                        candidate,
                                        demod_id,
                                        from_side,
                                        into_side,
                                        path,
                                    )
                                    break
                                if selected is not None:
                                    break
                            if selected is not None:
                                break
                        self.metrics["demodulation_queries"] += 1
                        if selected is None:
                            break
                        candidate, demod_id, from_side, into_side, path = selected
                        signature, event = self.demodulation_signature(
                            clauses[demod_id],
                            clauses[current_id],
                            from_side,
                            into_side,
                            path,
                            candidate,
                        )
                        parent_id = current_id
                        current_id = allocate(
                            candidate, False, "demodulation"
                        )
                        class_of[current_id] = queue_id
                        self.demodulation_events[current_id] = {
                            "signature": signature,
                            "proof_node": current_id,
                            "demodulator_id": demod_id,
                            "target_parent_id": parent_id,
                            **event,
                        }
                        global_demodulations += 1
                        self.metrics["forward_demodulations"] += 1
                        self.metrics["demodulation_proof_nodes"] += 1
                    if current_id != record["raw"]:
                        if self.clause_key(
                            clauses[current_id]
                        ) < self.clause_key(clauses[record["cheapest"]]):
                            record["cheapest"] = current_id
                        if goal_score(clauses[current_id]) >= goal_score(
                            clauses[record["goal"]]
                        ):
                            record["goal"] = current_id
                        self.metrics["representative_updates"] += 1
                candidates = {
                    record["raw"],
                    record["cheapest"],
                    record["goal"],
                }
                cid = min(
                    candidates,
                    key=lambda representative: (
                        -goal_score(clauses[representative]),
                        self.clause_key(clauses[representative]),
                    ),
                )
                given_ids = (
                    sorted(candidates, key=lambda item: int(item))
                    if self.expose_all_representatives
                    else [cid]
                )
                if self.operation_relative_representatives:
                    def source_site_score(representative):
                        clause = clauses[representative]
                        if clause.polarity != "pos":
                            return -1
                        eligible_sides = len(
                            e["rewrite_sides"](clause, args.unordered)
                        )
                        positions = sum(
                            1
                            for term in (clause.lhs, clause.rhs)
                            for _path in e["all_paths"](term)
                        )
                        return eligible_sides * 1000 + positions

                    source_representative = max(
                        candidates,
                        key=lambda item: (
                            source_site_score(item),
                            item == record["raw"],
                            -self.clause_key(clauses[item])[0],
                        ),
                    )
                    target_representative = max(
                        candidates,
                        key=lambda item: (
                            goal_score(clauses[item]),
                            sum(
                                1
                                for term in (
                                    clauses[item].lhs,
                                    clauses[item].rhs,
                                )
                                for _path in e["all_paths"](term)
                            ),
                            item == record["raw"],
                        ),
                    )
                    given_ids = sorted(
                        {source_representative, target_representative},
                        key=lambda item: int(item),
                    )
                    if self.continuation_novelty:
                        given_ids = sorted(
                            {
                                record["raw"],
                                *self.continuation_materializations.keys(),
                            }
                            & candidates,
                            key=lambda item: int(item),
                        )
                for representative in given_ids:
                    if representative not in searchable_ids:
                        searchable_ids.append(representative)
                    if (
                        clauses[representative].polarity == "pos"
                        and representative not in positives
                    ):
                        positives.append(representative)
            else:
                cid = queue_id
                given_ids = [cid]
            active.append(cid)
            self.metrics["peak_active"] = max(self.metrics["peak_active"], len(active))
            given = clauses[cid]
            current_given_goal_score = goal_score(given)
            if self.trace_events:
                self.selection_events.append(
                    {
                        "selection_index": len(self.selection_events),
                        "queue_token": queue_id,
                        "representative_ids": list(given_ids),
                        "chosen_id": cid,
                        "chosen": self.clause_snapshot(given),
                        "goal_score": current_given_goal_score,
                        "active_size": len(active),
                        "passive_size": len(queue),
                        "selected_from": (
                            selected_from if self.scheduler else "weight"
                        ),
                    }
                )
            remaining_given_demodulations = (
                self.per_given_budget
                if self.per_given_budget is not None
                else 0
            )
            if goal_score(given) > 0:
                self.metrics["goal_relevant_selected"] += 1
            if self.forward_demodulation:
                for representative in given_ids:
                    representative_clause = clauses[representative]
                    if representative_clause.polarity != "pos":
                        continue
                    for side in self.strict_demodulator_sides(
                        representative_clause
                    ):
                        demodulators.append((representative, side))
            pair_budget = args.pair_budget

            def run_pairs(from_ids, into_ids):
                nonlocal pair_budget
                for from_id in from_ids:
                    source = clauses[from_id]
                    if source.polarity != "pos":
                        continue
                    for into_id in into_ids:
                        target = clauses[into_id]
                        for from_side in e["rewrite_sides"](source, args.unordered):
                            for into_side in (1, 2):
                                term = target.lhs if into_side == 1 else target.rhs
                                for path in sorted(e["all_paths"](term), key=lambda item: (len(item), item)):
                                    if pair_budget <= 0 or generated >= args.max_clauses:
                                        return False
                                    pair_budget -= 1
                                    candidate = e["infer_paramod"](
                                        source,
                                        target,
                                        from_side,
                                        into_side,
                                        path,
                                        generated + pair_budget + next_id,
                                        rigid,
                                    )
                                    if candidate is None:
                                        continue
                                    self.metrics["superposition_candidates"] += 1
                                    novel_hits = []
                                    result_alpha = repr(
                                        e["alpha_key"](
                                            candidate.lhs,
                                            candidate.rhs,
                                            candidate.polarity,
                                        )
                                    )
                                    for representation_id, materialization in (
                                        self.continuation_materializations.items()
                                    ):
                                        role = None
                                        partner_id = None
                                        if from_id == representation_id:
                                            role = "superposition-source"
                                            partner_id = into_id
                                        elif into_id == representation_id:
                                            role = "superposition-target"
                                            partner_id = from_id
                                        if role is None:
                                            continue
                                        for index, novelty in enumerate(
                                            materialization[
                                                "novel_continuations"
                                            ]
                                        ):
                                            if (
                                                novelty["role"] == role
                                                and novelty[
                                                    "partner_alpha_key"
                                                ]
                                                == repr(
                                                    e["alpha_key"](
                                                        clauses[
                                                            partner_id
                                                        ].lhs,
                                                        clauses[
                                                            partner_id
                                                        ].rhs,
                                                        clauses[
                                                            partner_id
                                                        ].polarity,
                                                    )
                                                )
                                                and novelty["literal_side"]
                                                == into_side
                                                and novelty["term_path"]
                                                == list(path)
                                                and novelty["orientation"]
                                                == from_side
                                            ):
                                                key = (
                                                    f"{representation_id}:"
                                                    f"{index}"
                                                )
                                                novel_hits.append(
                                                    (
                                                        materialization,
                                                        key,
                                                    )
                                                )
                                                if key not in materialization[
                                                    "attempted_novel_keys"
                                                ]:
                                                    materialization[
                                                        "attempted_novel_keys"
                                                    ].append(key)
                                                    self.metrics[
                                                        "novel_inferences_attempted"
                                                    ] += 1
                                    materialized_id = materialize_with_demodulation(
                                        candidate
                                    )
                                    if materialized_id is not None:
                                        for materialization, key in novel_hits:
                                            if key not in materialization[
                                                "retained_novel_keys"
                                            ]:
                                                materialization[
                                                    "retained_novel_keys"
                                                ].append(key)
                                                self.metrics[
                                                    "novel_inferences_retained"
                                                ] += 1
                                    if self.trace_events:
                                        self.raw_child_events.append(
                                            {
                                                "source_id": from_id,
                                                "target_id": into_id,
                                                "from_side": from_side,
                                                "into_side": into_side,
                                                "path": list(path),
                                                "raw": self.clause_snapshot(candidate),
                                                "materialized_id": materialized_id,
                                                "retained": materialized_id is not None,
                                            }
                                        )
                                    if closed_id is not None:
                                        return True
                return False

            closed = False
            for representative in given_ids:
                representative_clause = clauses[representative]
                if representative_clause.polarity == "pos":
                    closed = (
                        run_pairs([representative], list(searchable_ids))
                        or run_pairs(list(positives), [representative])
                    )
                else:
                    closed = run_pairs(
                        list(positives), [representative]
                    )
                if closed or pair_budget <= 0:
                    break
            if closed:
                break

        result = {
            "status": "proved" if closed_id is not None else "unproved",
            "generated": generated,
            "retained": retained,
            "processed": len(processed),
            "seen": len(seen),
            "active": len(active),
            "passive": len(queue),
            "elapsed_s": round(time.monotonic() - started, 6),
            "exit": (
                "proof"
                if closed_id is not None
                else "maximum_clauses"
                if generated >= args.max_clauses
                else "maximum_processed"
                if len(processed) >= args.max_processed
                else "timeout"
                if time.monotonic() - started >= args.timeout
                else "exhausted"
            ),
            **self.metrics,
        }
        if self.trace_events:
            result["selection_events"] = self.selection_events
            result["demodulation_events"] = list(
                self.demodulation_events.values()
            )
            result["raw_child_events"] = self.raw_child_events
        if self.continuation_novelty:
            result["continuation_materializations"] = list(
                self.continuation_materializations.values()
            )
        if closed_id is not None:
            ancestry = set()
            stack = [closed_id]
            while stack:
                current = stack.pop()
                if current in ancestry:
                    continue
                ancestry.add(current)
                stack.extend(self.parent_ids.get(current, ()))
            result["proof_ancestry_nodes"] = len(ancestry)
            result["proof_ancestry_demodulations"] = len(
                ancestry & self.demodulation_ids
            )
            result["proof_ancestry_superpositions"] = len(
                ancestry & self.superposition_ids
            )
            result["proof_ancestry_ids"] = sorted(
                ancestry, key=lambda value: int(value)
            )
            result["proof_ancestry_demodulation_events"] = [
                self.demodulation_events[node_id]
                for node_id in sorted(
                    ancestry & self.demodulation_ids,
                    key=lambda value: int(value),
                )
                if node_id in self.demodulation_events
            ]
        if closed_id is None:
            return result
        close_num = str(next_id)
        proof_lines = [
            f"1 {e['quantified_line'](self.problem['equation1'], 'assumption')}.  [assumption].",
            f"2 {e['quantified_line'](self.problem['equation2'], 'goal')}.  [goal].",
            f"3 {e['formula'](clauses['3'])}.  [clausify(1)].",
            f"4 {e['formula'](clauses['4'])}.  [deny(2)].",
        ]
        for number in range(5, next_id):
            clause = clauses.get(str(number))
            if clause is not None:
                proof_lines.append(
                    f"{clause.id} {e['formula'](clause)}.  [{clause.justification}]."
                )
        proof_lines.append(f"{close_num} $F.  [copy({closed_id}),xx(a)].")
        proof_text = "\n".join(proof_lines)
        result["closed_id"] = closed_id
        result["proof_text"] = proof_text
        spec = e["translate_proof"](
            self.problem["equation1"], self.problem["equation2"], proof_text
        )
        plan_ok, feedback = e["ckl"].verify_plan(spec)
        result["plan_ok"] = plan_ok
        if not plan_ok:
            result["plan_feedback"] = feedback
            return result
        result["spec"] = spec
        result["code"] = e["ckl"].make_submission(spec)
        result["n_lemmas"] = len(spec.get("lemmas", []))
        result["total_steps"] = len(spec.get("goal_steps", [])) + sum(
            len(lemma.get("steps", [])) for lemma in spec.get("lemmas", [])
        )
        return result


def run(args):
    module = load_solver()
    independent = load_independent_replayer()
    engine, external_replay = prepare_engine(module)
    payload = json.loads(args.input.read_text())
    rows = payload.get("rows", payload) if isinstance(payload, dict) else payload
    conditions = {}
    requested = tuple(part.strip() for part in args.conditions.split(",") if part.strip())
    budgeted = {
        "K1": (1, 256),
        "K2": (2, 256),
        "K4": (4, 256),
        "K2G64": (2, 64),
        "K2G128": (2, 128),
        "K4G128": (4, 128),
        "K4G256": (4, 256),
        "Q": (4, 256),
        "QA": (4, 256),
        "QM": (4, 256),
        "QR": (4, 256),
        "QL": (4, 256),
        "CN1": (1, 256),
        "CN2": (1, 256),
    }
    permitted = {"B", "F", "S", "FS", *budgeted}
    if not requested or any(condition not in permitted for condition in requested):
        raise ValueError(f"conditions must be a comma-separated subset of {sorted(permitted)}")
    for condition in requested:
        condition_rows = []
        for row in rows:
            settings = engine["argparse"].Namespace(
                max_clauses=args.max_clauses,
                max_weight=args.max_weight,
                max_term_size=args.max_term_size,
                max_processed=args.max_processed,
                pair_budget=args.pair_budget,
                timeout=args.timeout,
                translate=True,
                unordered=False,
                neg_bias=0,
                old_rules_first=False,
                tautology_prune=False,
                forward_subsumption=False,
            )
            started = time.monotonic()
            if condition == "B":
                result = engine["prove"](row, settings)
                result.setdefault("retained", result.get("seen"))
                result.setdefault("exit", "proof" if result.get("status") == "proved" else (
                    "maximum_clauses"
                    if result.get("generated", 0) >= args.max_clauses
                    else "timeout"
                ))
            else:
                per_given, global_budget = budgeted.get(
                    condition, (None, None)
                )
                result = ForwardDemodulationRun(
                    engine,
                    row,
                    settings,
                    forward_demodulation=condition in {"F", "FS"} or condition in budgeted,
                    scheduler=condition in {"S", "FS"} or condition in budgeted,
                    local_demodulation=condition == "FS",
                    dual_retention=condition in budgeted,
                    per_given_budget=per_given,
                    global_budget=global_budget,
                    quotient_mode=condition in {
                        "Q", "QA", "QM", "QR", "QL", "CN1", "CN2"
                    },
                    expose_all_representatives=condition == "QA",
                    merge_passive_classes=condition == "QM",
                    operation_relative_representatives=condition in {
                        "QR", "QL", "CN1", "CN2"
                    },
                    lazy_representative_materialization=condition == "QL",
                    continuation_novelty=condition in {"CN1", "CN2"},
                    corridor_lookahead=condition == "CN2",
                ).solve()
            record = {
                key: value
                for key, value in result.items()
                if key not in (
                    "proof_text",
                    "spec",
                    "code",
                    "continuation_materializations",
                )
            }
            record["id"] = row["id"]
            record["condition"] = condition
            record["wall_seconds"] = round(time.monotonic() - started, 6)
            record["independent_replay"] = False
            record["external_plan_replay"] = False
            record["lean_status"] = None
            record["judge_seconds"] = None
            if result.get("status") == "proved" and result.get("plan_ok"):
                record["independent_replay"] = bool(
                    independent.replay_plan(result["spec"])
                )
                record["external_plan_replay"] = bool(
                    external_replay["replay_plan"](result["spec"])
                )
                if record["independent_replay"] and record["external_plan_replay"]:
                    judged, judge_seconds = judge(row, result["code"])
                    record["lean_status"] = judged.get("status")
                    record["judge_seconds"] = round(judge_seconds, 6)
                    record["certificate_bytes"] = len(result["code"].encode())
            condition_rows.append(record)
            print(json.dumps({
                "condition": condition,
                "id": row["id"],
                "status": record["status"],
                "generated": record.get("generated"),
                "processed": record.get("processed"),
                "demod": record.get("forward_demodulations", 0),
                "lean": record["lean_status"],
            }), flush=True)
        conditions[condition] = condition_rows
    payload = {
        "schema": "mathgraph.forward-demodulation-ablation.v1",
        "diagnostic_only": True,
        "production_changed": False,
        "solver_sha256": sha256(SOLVER),
        "environment": {
            "python": sys.version,
            "platform": platform.platform(),
        },
        "frozen_limits": {
            "max_clauses": args.max_clauses,
            "max_processed": args.max_processed,
            "max_weight": args.max_weight,
            "max_term_size": args.max_term_size,
            "pair_budget": args.pair_budget,
            "timeout_seconds": args.timeout,
            "demodulation_steps_per_clause": {
                "F": 64,
                "FS": 4,
            },
            "local_demodulator_window": 8,
            "scheduler": {
                "age_to_weight": "1:4",
                "goal_quota": "1 selection opportunity in 4",
            },
            "budgeted_dual_retention": {
                "K1": {"per_given": 1, "global": 256},
                "K2": {"per_given": 2, "global": 256},
                "K4": {"per_given": 4, "global": 256},
                "K2G64": {"per_given": 2, "global": 64},
                "K2G128": {"per_given": 2, "global": 128},
                "K4G128": {"per_given": 4, "global": 128},
                "K4G256": {"per_given": 4, "global": 256}
            },
        },
        "conditions": conditions,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    return payload


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "experiments/mathgraph/paramodulator_control/"
        "six_residual_forward_demodulation_results.json",
    )
    parser.add_argument("--max-clauses", type=int, default=8000)
    parser.add_argument("--max-processed", type=int, default=8000)
    parser.add_argument("--max-weight", type=int, default=36)
    parser.add_argument("--max-term-size", type=int, default=30)
    parser.add_argument("--pair-budget", type=int, default=300)
    parser.add_argument("--timeout", type=float, default=2.0)
    parser.add_argument("--conditions", default="B,F")
    args = parser.parse_args()
    run(args)


if __name__ == "__main__":
    main()
