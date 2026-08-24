#!/usr/bin/env python3
"""Trace one independently causal 0036 source instance through cleanroom search."""

import argparse
import ast
import hashlib
import importlib.util
import json
import sys
import time
import types
from pathlib import Path


sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
PROTO = Path(__file__).with_name(
    "0036_causal_contractor_attribution_preregistration.json"
)
DEFAULT_SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
DEFAULT_INPUT = Path(__file__).with_name("released_residuals_unlabelled.json")
DEFAULT_OUTPUT = Path(__file__).with_name(
    "0036_causal_contractor_attribution_results.json"
)


def load_solver(path):
    spec = importlib.util.spec_from_file_location(
        "mathgraph_0036_attribution_solver", path
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def alpha_pair(module, left, right):
    names = {}
    return (
        module.alpha_canonical_term(left, names),
        module.alpha_canonical_term(right, names),
    )


def simultaneous_match(module, pattern, concrete):
    mapping = {}
    if not module.match_term(pattern[0], concrete[0], mapping):
        return None
    if not module.match_term(pattern[1], concrete[1], mapping):
        return None
    variables = module.term_variables(pattern[0]) | module.term_variables(
        pattern[1]
    )
    if not variables <= set(mapping):
        return None
    return mapping


class AttributionTracker:
    def __init__(self, solver, engine, contractor):
        self.solver = solver
        self.engine = engine
        self.module = engine.search.m
        self.contractor = (
            engine.encode_rigid(contractor[0]),
            engine.encode_rigid(contractor[1]),
        )
        self.events = {}
        self.descendant_events = {}
        self.selected = []

    def pair(self, recipe):
        return recipe.lhs, recipe.rhs

    def public_pair(self, recipe):
        return {
            "lhs": self.solver.render_term(self.engine.inline(recipe.lhs)),
            "rhs": self.solver.render_term(self.engine.inline(recipe.rhs)),
            "kind": recipe.kind,
            "cost": recipe.cost,
        }

    def match_modes(self, recipe):
        pair = self.pair(recipe)
        reverse = (pair[1], pair[0])
        modes = []
        if pair == self.contractor:
            modes.append("exact")
        if reverse == self.contractor:
            modes.append("symmetric_exact")
        target_alpha = alpha_pair(
            self.module, self.contractor[0], self.contractor[1]
        )
        if alpha_pair(self.module, pair[0], pair[1]) == target_alpha:
            modes.append("shared_alpha")
        if alpha_pair(self.module, pair[1], pair[0]) == target_alpha:
            modes.append("symmetric_shared_alpha")
        if (
            simultaneous_match(self.module, pair, self.contractor) is not None
            or simultaneous_match(self.module, reverse, self.contractor)
            is not None
        ):
            modes.append("simultaneous_specialization_coverage")
        return tuple(dict.fromkeys(modes))

    def observe(self, stage, recipe):
        modes = self.match_modes(recipe)
        if not modes:
            return
        record = self.events.setdefault(stage, {
            "count": 0,
            "exact_count": 0,
            "modes": set(),
            "first": None,
        })
        record["count"] += 1
        if any(mode != "simultaneous_specialization_coverage" for mode in modes):
            record["exact_count"] += 1
        record["modes"].update(modes)
        if record["first"] is None:
            record["first"] = self.public_pair(recipe)

    def is_exact(self, recipe):
        return any(
            mode != "simultaneous_specialization_coverage"
            for mode in self.match_modes(recipe)
        )

    def has_exact_ancestor(self, recipe):
        stack = list(recipe.parents)
        seen = set()
        while stack:
            current = stack.pop()
            if id(current) in seen:
                continue
            seen.add(id(current))
            if self.is_exact(current):
                return True
            stack.extend(current.parents)
        return False

    def observe_descendant(self, stage, recipe):
        if not self.has_exact_ancestor(recipe):
            return
        record = self.descendant_events.setdefault(stage, {
            "count": 0,
            "first": None,
        })
        record["count"] += 1
        if record["first"] is None:
            record["first"] = self.public_pair(recipe)

    def observe_selected(self, recipe):
        self.observe("selected_given_clause", recipe)
        if len(self.selected) < 64:
            self.selected.append(self.public_pair(recipe))

    def observe_ancestry(self, recipe):
        if recipe is None:
            return
        stack = [recipe]
        seen = set()
        while stack:
            current = stack.pop()
            if id(current) in seen:
                continue
            seen.add(id(current))
            self.observe("used_in_returned_proof_ancestry", current)
            stack.extend(current.parents)

    def has_exact(self, *stages):
        return any(self.events.get(stage, {}).get("exact_count", 0) for stage in stages)

    def public(self):
        output = {}
        for stage, record in sorted(self.events.items()):
            output[stage] = {
                **record,
                "modes": sorted(record["modes"]),
            }
        for stage, record in sorted(self.descendant_events.items()):
            output[stage] = record
        return output


def install_observation_hooks(search, tracker):
    original_instantiate = search.instantiate
    original_critical_pair = search.critical_pair
    original_add_clause = search.add_clause

    def instantiate(_self, recipe, mapping):
        result = original_instantiate(recipe, mapping)
        tracker.observe("constructed_by_instantiation", result)
        return result

    def critical_pair(_self, outer, inner, outer_index, inner_index, path):
        result = original_critical_pair(
            outer, inner, outer_index, inner_index, path
        )
        if result is not None:
            tracker.observe("constructed_by_critical_pair", result)
        return result

    def add_clause(_self, recipe):
        before = len(search.clauses)
        result = original_add_clause(recipe)
        for clause in search.clauses[before:]:
            tracker.observe("admitted_clause", clause)
            tracker.observe_descendant(
                "contractor_descendant_admitted", clause
            )
        return result

    search.instantiate = types.MethodType(instantiate, search)
    search.critical_pair = types.MethodType(critical_pair, search)
    search.add_clause = types.MethodType(add_clause, search)


def instrumented_given_clause(
    search, tracker, maximum_given, focus_per_age,
    force_contractor_once=False,
):
    """The frozen solver loop with observation-only stage hooks."""
    passive = list(search.clauses)
    active = []
    age = {id(clause): index for index, clause in enumerate(passive)}
    next_age = len(passive)
    selected_count = 0
    for clause in passive:
        tracker.observe("initial_schematic_coverage", clause)
        tracker.observe("retained_passive", clause)

    def active_rules():
        output = []
        for clause in active:
            oriented = search.orient(clause)
            if oriented is not None:
                output.append(oriented)
        output.sort(key=search.target_score)
        return output[:search.limits["maximum_rules"]]

    while (
        passive
        and selected_count < maximum_given
        and len(search.clauses) < search.limits["maximum_clauses"]
        and not search.expired()
    ):
        rules = active_rules()
        goal = search.target_proof(rules)
        if goal is not None:
            tracker.observe_ancestry(goal)
            return goal, active, passive, active_rules()
        if force_contractor_once and selected_count == 0:
            forced = [
                item for item, clause in enumerate(passive)
                if tracker.is_exact(clause)
            ]
            if not forced:
                raise RuntimeError("forced contractor is absent from passive")
            index = forced[0]
            tracker.observe("forced_selected_counterfactual", passive[index])
        elif selected_count % (focus_per_age + 1) == focus_per_age:
            index = min(
                range(len(passive)),
                key=lambda item: age.get(id(passive[item]), 10 ** 18),
            )
        else:
            index = min(
                range(len(passive)),
                key=lambda item: (
                    search.target_score(passive[item]),
                    age.get(id(passive[item]), 10 ** 18),
                ),
            )
        selected = passive.pop(index)
        tracker.observe_selected(selected)
        selected = search.interreduce(selected, rules)
        tracker.observe("selected_given_clause", selected)
        active.append(selected)
        tracker.observe("active_clause", selected)
        selected_count += 1
        search.rounds = selected_count

        rules = active_rules()
        goal = search.target_proof(rules)
        if goal is not None:
            tracker.observe_ancestry(goal)
            return goal, active, passive, active_rules()

        proposals = []
        for other_index, other in enumerate(active):
            pairs = (
                (selected, other, selected_count, other_index),
                (other, selected, other_index, selected_count),
            )
            for outer, inner, outer_index, inner_index in pairs:
                for path in search.m.nonvariable_positions(
                    outer.lhs,
                    maximum_depth=search.limits["maximum_depth"],
                    include_root=True,
                ):
                    if search.expired():
                        break
                    proposal = search.critical_pair(
                        outer, inner, outer_index, inner_index, path
                    )
                    if proposal is None:
                        continue
                    proposal = search.interreduce(proposal, rules)
                    proposals.append((search.target_score(proposal), proposal))
        proposals.sort(key=lambda item: item[0])
        for _, proposal in proposals[
            :search.limits["new_clauses_per_round"]
        ]:
            before = len(search.clauses)
            if search.add_clause(proposal):
                search.superpositions += 1
                retained = (
                    search.clauses[-1]
                    if len(search.clauses) > before
                    else proposal
                )
                passive.append(retained)
                tracker.observe("retained_passive", retained)
                age[id(retained)] = next_age
                next_age += 1

        reduced_passive = []
        seen = set()
        for clause in passive:
            if search.expired():
                break
            clause = search.interreduce(clause, rules)
            forward = search.alpha_signature(clause.lhs, clause.rhs)
            reverse = search.alpha_signature(clause.rhs, clause.lhs)
            signature = min(forward, reverse)
            if signature in seen:
                continue
            seen.add(signature)
            reduced_passive.append(clause)
            tracker.observe("retained_passive", clause)
        passive = reduced_passive

    goal = search.target_proof(active_rules())
    tracker.observe_ancestry(goal)
    return goal, active, passive, active_rules()


def contractor_recipe(solver, engine):
    stack = list(engine.search.clauses)
    seen = set()
    source_clause = None
    while stack:
        clause = stack.pop()
        if id(clause) in seen:
            continue
        seen.add(id(clause))
        if clause.kind == "source":
            source_clause = clause
            break
        stack.extend(clause.parents)
    if source_clause is None:
        raise RuntimeError("frozen source recipe not found")
    rigid_x = engine.encode_rigid(("var", "x"))
    rigid_z = engine.encode_rigid(("var", "z"))
    mapping = {
        "x": rigid_x,
        "y": ("op", rigid_x, rigid_z),
        "z": rigid_x,
    }
    return engine.search.instantiate(source_clause, mapping)


def verify_contractor(solver, engine, recipe, contractor, limits):
    inlined = engine.inline_recipe(recipe)
    compiler = solver.CompactSuperposition(
        solver, engine.source, engine.target, time.monotonic() + 5, limits
    )
    nodes, root = compiler.compile(inlined)
    pair = (nodes[root].lhs, nodes[root].rhs)
    expected = contractor[:2]
    root_matches = pair == expected or pair == (expected[1], expected[0])
    replayed = solver.replay_dag(
        engine.source,
        nodes,
        root,
        maximum_term_size=limits["maximum_replay_term_size"],
        maximum_nodes=limits["maximum_proof_nodes"],
    )
    return {
        "root_matches": root_matches,
        "replayed": replayed,
        "proof_nodes": len(nodes),
        "lhs": solver.render_term(pair[0]),
        "rhs": solver.render_term(pair[1]),
    }


def officially_verify(problem, code):
    from judge.verify import verify_answer

    proxy_tree = ast.parse(
        (ROOT / "pipeline/proxy.py").read_text(encoding="utf-8")
    )
    policy = None
    for node in proxy_tree.body:
        if (
            isinstance(node, ast.Assign)
            and any(
                isinstance(target, ast.Name)
                and target.id == "DEFAULT_PROOF_POLICY"
                for target in node.targets
            )
        ):
            policy = ast.literal_eval(node.value)
            break
    if policy is None:
        raise RuntimeError("DEFAULT_PROOF_POLICY not found")
    answer = json.dumps({"verdict": "true", "code": code})
    return verify_answer({**problem, "proof_policy": policy}, answer).get(
        "status", "unparsed"
    )


def target_state(solver, engine, rules):
    left, _ = engine.search.normalize(engine.search.target[0], rules)
    right, _ = engine.search.normalize(engine.search.target[1], rules)
    left = engine.inline(left)
    right = engine.inline(right)
    return {
        "left": solver.render_term(left),
        "right": solver.render_term(right),
        "structural_distance": solver.structural_distance(left, right),
        "equal": left == right,
    }


def run_arm(
    solver, source, target, contractor, limits, seconds, maximum_given,
    focus_per_age, install_contractor, force_contractor_once, official,
    problem,
):
    started = time.monotonic()
    engine = solver.TargetGroundedRefutation(
        source, target, started + seconds, dict(limits)
    )
    tracker = AttributionTracker(solver, engine, contractor)
    injected_validity = None
    if install_contractor:
        injected = contractor_recipe(solver, engine)
        injected_validity = verify_contractor(
            solver, engine, injected, contractor, limits
        )
        tracker.observe("installed_counterfactual", injected)
        before = len(engine.search.clauses)
        admitted = engine.search.add_clause(injected)
        for clause in engine.search.clauses[before:]:
            tracker.observe("admitted_clause", clause)
        injected_validity["admitted"] = admitted

    install_observation_hooks(engine.search, tracker)
    recipe, active, passive, rules = instrumented_given_clause(
        engine.search, tracker, maximum_given, focus_per_age,
        force_contractor_once=force_contractor_once,
    )
    compiled = engine.compile_recipe(recipe)
    internal = {
        "found_recipe": recipe is not None,
        "compiled": compiled is not None,
        "root_matches": False,
        "replayed": False,
        "certificate_bytes": 0,
        "proof_nodes": 0,
        "judge_status": None,
    }
    if compiled is not None:
        nodes, root = compiled
        internal["root_matches"] = (
            nodes[root].lhs, nodes[root].rhs
        ) == target[:2]
        internal["replayed"] = solver.replay_dag(
            source,
            nodes,
            root,
            maximum_term_size=limits["maximum_replay_term_size"],
            maximum_nodes=limits["maximum_proof_nodes"],
        )
        code, proof_nodes = solver.make_dag_certificate(
            target, nodes, root
        )
        internal["proof_nodes"] = proof_nodes
        internal["certificate_bytes"] = len(code.encode("utf-8"))
        if official and internal["root_matches"] and internal["replayed"]:
            internal["judge_status"] = officially_verify(problem, code)

    state = target_state(solver, engine, rules)
    return {
        "installed_contractor": install_contractor,
        "forced_contractor_once": force_contractor_once,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "clauses": len(engine.search.clauses),
        "rounds": engine.search.rounds,
        "superpositions": engine.search.superpositions,
        "reductions": engine.search.reductions,
        "active_count": len(active),
        "passive_count": len(passive),
        "expired": engine.search.expired(),
        "contractor_validity": injected_validity,
        "attribution": tracker.public(),
        "selected_prefix": tracker.selected,
        "target_state": state,
        "proof": internal,
    }


def equivalence_probe(solver, source, target, contractor, limits):
    probe_given = 8
    native = solver.TargetGroundedRefutation(
        source, target, time.monotonic() + 20, dict(limits)
    )
    native_found = native.solve_given_clause(
        maximum_given=probe_given, focus_per_age=4
    )
    observed = solver.TargetGroundedRefutation(
        source, target, time.monotonic() + 20, dict(limits)
    )
    tracker = AttributionTracker(solver, observed, contractor)
    install_observation_hooks(observed.search, tracker)
    recipe, _, _, _ = instrumented_given_clause(
        observed.search, tracker, probe_given, 4
    )
    observed_found = observed.compile_recipe(recipe)
    native_signatures = sorted(
        repr(native.search.alpha_signature(c.lhs, c.rhs))
        for c in native.search.clauses
    )
    observed_signatures = sorted(
        repr(observed.search.alpha_signature(c.lhs, c.rhs))
        for c in observed.search.clauses
    )
    checks = {
        "found_equal": (native_found is None) == (observed_found is None),
        "clauses_equal": len(native.search.clauses) == len(
            observed.search.clauses
        ),
        "rounds_equal": native.search.rounds == observed.search.rounds,
        "superpositions_equal": native.search.superpositions
        == observed.search.superpositions,
        "signatures_equal": native_signatures == observed_signatures,
    }
    return {
        "maximum_given": probe_given,
        "checks": checks,
        "passed": all(checks.values()),
    }


def decide(arm_a, arm_b, arm_c, measurement_ok, smoke):
    if smoke:
        return "SMOKE_ONLY"
    if not measurement_ok:
        return "MEASUREMENT_FAILURE"
    proof_a = arm_a["proof"]
    proof_b = arm_b["proof"]
    proof_c = arm_c["proof"]
    b_closes = (
        proof_b["root_matches"]
        and proof_b["replayed"]
        and proof_b["judge_status"] == "accepted"
    )
    a_closes = (
        proof_a["root_matches"]
        and proof_a["replayed"]
        and proof_a["judge_status"] == "accepted"
    )
    if b_closes and not a_closes:
        return "KNOWN_CONTRACTOR_CLOSES"
    c_closes = (
        proof_c["root_matches"]
        and proof_c["replayed"]
        and proof_c["judge_status"] == "accepted"
    )
    if c_closes and not a_closes and not b_closes:
        return "CONTRACTOR_SELECTION_CAUSAL"

    events_a = arm_a["attribution"]
    events_b = arm_b["attribution"]
    constructed = any(
        events_a.get(stage, {}).get("exact_count", 0)
        for stage in (
            "constructed_by_instantiation",
            "constructed_by_critical_pair",
            "admitted_clause",
        )
    )
    retained = events_a.get("retained_passive", {}).get("exact_count", 0) > 0
    selected = events_a.get("selected_given_clause", {}).get(
        "exact_count", 0
    ) > 0
    b_active = events_b.get("active_clause", {}).get("exact_count", 0) > 0
    events_c = arm_c["attribution"]
    c_active = events_c.get("active_clause", {}).get("exact_count", 0) > 0
    c_improved = arm_c["target_state"]["structural_distance"] < min(
        arm_a["target_state"]["structural_distance"],
        arm_b["target_state"]["structural_distance"],
    )
    c_descendants = events_c.get(
        "contractor_descendant_admitted", {}
    ).get("count", 0)
    if c_active and c_improved:
        return "CONTRACTOR_SELECTION_CAUSAL"
    if constructed and retained and not selected:
        return "EXISTING_CLOSURE_UNSELECTED"
    if constructed and not retained:
        return "RETENTION_FAILURE"
    if not constructed and b_active:
        return "CONSTRUCTOR_ABSENT"
    if c_active and c_descendants:
        return "POST_CONTRACTOR_COMPOSITION_FAILURE"
    return "CONTRACTOR_REPRESENTATION_DISPLACED"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=DEFAULT_SOLVER)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--official", action="store_true")
    parser.add_argument("--smoke", action="store_true")
    args = parser.parse_args()

    protocol = json.loads(PROTO.read_text(encoding="utf-8"))
    expected_hash = protocol["constraints"]["solver_sha256"]
    actual_hash = hashlib.sha256(args.solver.read_bytes()).hexdigest()
    rows = json.loads(args.input.read_text(encoding="utf-8"))
    expected_headers = {
        "id", "index", "difficulty", "eq1_id", "eq2_id",
        "equation1", "equation2",
    }
    header_ok = bool(rows) and all(set(row) == expected_headers for row in rows)
    row = next(row for row in rows if row["id"] == "evaluation_normal_0036")
    body_ok = (
        row["equation1"] == protocol["target"]["source"]
        and row["equation2"] == protocol["target"]["goal"]
        and "answer" not in row
    )
    solver = load_solver(args.solver)
    source = solver.parse_equation(row["equation1"])
    target = solver.parse_equation(row["equation2"])
    contractor = solver.parse_equation(protocol["target"]["contractor"])

    constraints = protocol["constraints"]
    limits = {
        key: constraints[key]
        for key in (
            "maximum_term_size", "maximum_replay_term_size",
            "maximum_depth", "maximum_rules", "maximum_rounds",
            "new_clauses_per_round", "maximum_clauses",
            "normalization_steps", "maximum_proof_nodes",
        )
    }
    limits["seconds"] = constraints["seconds_per_arm"]
    seconds = 0.5 if args.smoke else constraints["seconds_per_arm"]
    maximum_given = 8 if args.smoke else constraints["maximum_given"]

    equivalence = equivalence_probe(
        solver, source, target, contractor, limits
    )
    problem = {
        "id": "evaluation_normal_0036_attribution",
        "eq1_id": row["eq1_id"],
        "eq2_id": row["eq2_id"],
        "equation1": row["equation1"],
        "equation2": row["equation2"],
    }
    arm_a = run_arm(
        solver, source, target, contractor, limits, seconds,
        maximum_given, constraints["focus_per_age"], False, False,
        args.official and not args.smoke, problem,
    )
    arm_b = run_arm(
        solver, source, target, contractor, limits, seconds,
        maximum_given, constraints["focus_per_age"], True, False,
        args.official and not args.smoke, problem,
    )
    arm_c = run_arm(
        solver, source, target, contractor, limits, seconds,
        maximum_given, constraints["focus_per_age"], True, True,
        args.official and not args.smoke, problem,
    )
    validity = arm_b["contractor_validity"] or {}
    measurement_ok = (
        actual_hash == expected_hash
        and header_ok
        and body_ok
        and equivalence["passed"]
        and validity.get("root_matches") is True
        and validity.get("replayed") is True
        and validity.get("admitted") is True
        and (arm_c["contractor_validity"] or {}).get("root_matches") is True
        and (arm_c["contractor_validity"] or {}).get("replayed") is True
        and (arm_c["contractor_validity"] or {}).get("admitted") is True
        and arm_c["attribution"].get(
            "forced_selected_counterfactual", {}
        ).get("exact_count", 0) > 0
    )
    decision = decide(arm_a, arm_b, arm_c, measurement_ok, args.smoke)
    output = {
        "schema": "mathgraph.0036-causal-contractor-attribution-results.v2",
        "decision": decision,
        "measurement_ok": measurement_ok,
        "smoke_only": args.smoke,
        "official_enabled": args.official and not args.smoke,
        "solver_sha256": actual_hash,
        "input_headers": sorted(expected_headers),
        "input_headers_ok": header_ok,
        "equation_bodies_ok": body_ok,
        "label_fields_available_to_runner": [],
        "observational_equivalence_probe": equivalence,
        "arm_A_frozen_baseline": arm_a,
        "arm_B_known_contractor_installed": arm_b,
        "arm_C_known_contractor_forced_once": arm_c,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "decision": decision,
        "measurement_ok": measurement_ok,
        "arm_A_rounds": arm_a["rounds"],
        "arm_B_rounds": arm_b["rounds"],
        "arm_C_rounds": arm_c["rounds"],
        "arm_A_found": arm_a["proof"]["compiled"],
        "arm_B_found": arm_b["proof"]["compiled"],
        "arm_C_found": arm_c["proof"]["compiled"],
        "contractor_validity": validity,
    }, sort_keys=True), flush=True)
    if not measurement_ok:
        raise SystemExit("measurement failure")


if __name__ == "__main__":
    main()
