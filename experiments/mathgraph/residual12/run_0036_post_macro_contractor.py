#!/usr/bin/env python3
"""Attribute residual 0036 after the frozen target bridge macro."""

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from pathlib import Path


sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PROTO = HERE / "0036_post_macro_contractor_preregistration.json"
ATTRIBUTION_RUNNER = HERE / "run_0036_causal_contractor_attribution.py"
INTERFACE_RUNNER = HERE / "run_0036_boundary_interface_reachability.py"
MACRO_RUNNER = HERE / "run_0036_target_bridge_macro.py"
DEFAULT_SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
DEFAULT_INPUT = HERE / "released_residuals_unlabelled.json"
DEFAULT_OUTPUT = HERE / "0036_post_macro_contractor_results.json"


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_rhs(solver, equation):
    return solver.parse_equation(equation)[1]


def reconstruct_macro(
    solver, attribution, interface, macro, source, original_target,
    contractor, limits, constraints
):
    seconds = constraints["seconds_for_macro_reconstruction"]
    started = time.monotonic()
    engine = solver.TargetGroundedRefutation(
        source, original_target, started + seconds, dict(limits)
    )
    tracker = attribution.AttributionTracker(solver, engine, contractor)
    injected = attribution.contractor_recipe(solver, engine)
    validity = attribution.verify_contractor(
        solver, engine, injected, contractor, limits
    )
    tracker.observe("installed_counterfactual", injected)
    before = len(engine.search.clauses)
    validity["admitted"] = engine.search.add_clause(injected)
    for clause in engine.search.clauses[before:]:
        tracker.observe("admitted_clause", clause)
    attribution.install_observation_hooks(engine.search, tracker)
    recipe, active, passive, active_rules = (
        attribution.instrumented_given_clause(
            engine.search,
            tracker,
            constraints["maximum_given"],
            constraints["focus_per_age"],
            force_contractor_once=True,
        )
    )
    clauses = list(engine.search.clauses)
    graph = interface.census_graph(
        solver,
        engine,
        tracker,
        clauses,
        "expanded_equational",
        limits,
        constraints,
    )
    bridge_data = macro.enumerate_and_select_bridge(
        solver,
        interface,
        engine,
        tracker,
        clauses,
        limits,
        constraints,
    )
    selected = bridge_data["selected"]
    selected_public = macro.selected_bridge_public(
        solver, engine, selected
    )
    macro_public = (
        None if selected is None else engine.inline_recipe(selected["macro"])
    )
    _, macro_verification = (
        (None, {
            "compiled": False,
            "root_matches": False,
            "replayed": False,
            "proof_nodes": 0,
        })
        if macro_public is None
        else macro.verify_recipe(
            solver, source, original_target, macro_public, limits
        )
    )
    expected_transformed = parse_rhs(
        solver,
        constraints["macro_transformed_goal"],
    )
    macro_verification["boundary_root_matches"] = (
        macro_public is not None
        and macro_public.lhs == original_target[1]
        and macro_public.rhs == expected_transformed
    )
    target_state = attribution.target_state(
        solver, engine, active_rules
    )
    checks = {
        "contractor_root_matches": validity.get("root_matches") is True,
        "contractor_replayed": validity.get("replayed") is True,
        "contractor_admitted": validity.get("admitted") is True,
        "forced_selected": tracker.events.get(
            "forced_selected_counterfactual", {}
        ).get("exact_count", 0) > 0,
        "no_original_target_proof": recipe is None,
        "target_distance_10": target_state["structural_distance"] == 10,
        "graph_complete": not graph["truncated"],
        "pair_count_7": graph["pair_bridge_count"] == 7,
        "selection_complete": not bridge_data["truncated"],
        "selected_pair_count_7": bridge_data["pair_count"] == 7,
        "selected_score": selected_public is not None
        and selected_public["score"][:3] == [15, 15, 349],
        "selected_target": selected_public is not None
        and selected_public["second_after"].replace("◇", "*")
        == solver.render_term(expected_transformed).replace("◇", "*"),
        "macro_compiled": macro_verification["compiled"],
        "macro_root_matches": macro_verification["root_matches"],
        "macro_replayed": macro_verification["replayed"],
        "macro_boundary_root_matches": macro_verification[
            "boundary_root_matches"
        ],
    }
    return {
        "engine": engine,
        "tracker": tracker,
        "clauses": clauses,
        "selected": selected,
        "macro_public": macro_public,
        "public": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "clauses": len(clauses),
            "rounds": engine.search.rounds,
            "superpositions": engine.search.superpositions,
            "active_count": len(active),
            "passive_count": len(passive),
            "contractor_validity": validity,
            "target_state": target_state,
            "graph": {
                "rule_count": graph["rule_count"],
                "unique_first_step_states": graph[
                    "unique_first_step_states"
                ],
                "direct_bridge_count": graph["direct_bridge_count"],
                "pair_bridge_count": graph["pair_bridge_count"],
                "truncated": graph["truncated"],
            },
            "selected_bridge": selected_public,
            "macro_verification": macro_verification,
            "checks": checks,
        },
    }


def run_arm(
    solver, attribution, macro, source, original_target, transformed_target,
    contractor, boundary_macro, limits, seconds, maximum_given,
    focus_per_age, problem, official, certificate_limit,
    install_contractor, force_contractor
):
    started = time.monotonic()
    engine = solver.TargetGroundedRefutation(
        source, transformed_target, started + seconds, dict(limits)
    )
    tracker = attribution.AttributionTracker(solver, engine, contractor)
    validity = None
    if install_contractor:
        injected = attribution.contractor_recipe(solver, engine)
        validity = attribution.verify_contractor(
            solver, engine, injected, contractor, limits
        )
        tracker.observe("installed_counterfactual", injected)
        before = len(engine.search.clauses)
        validity["admitted"] = engine.search.add_clause(injected)
        for clause in engine.search.clauses[before:]:
            tracker.observe("admitted_clause", clause)
    attribution.install_observation_hooks(engine.search, tracker)
    recipe, active, passive, active_rules = (
        attribution.instrumented_given_clause(
            engine.search,
            tracker,
            maximum_given,
            focus_per_age,
            force_contractor_once=force_contractor,
        )
    )
    verification = macro.reconstruct_original(
        solver,
        source,
        original_target,
        engine,
        recipe,
        boundary_macro,
        limits,
        problem,
        official,
        certificate_limit,
    )
    state = attribution.target_state(solver, engine, active_rules)
    public = {
        "installed_contractor": install_contractor,
        "forced_contractor_once": force_contractor,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "clauses": len(engine.search.clauses),
        "rounds": engine.search.rounds,
        "superpositions": engine.search.superpositions,
        "reductions": engine.search.reductions,
        "active_count": len(active),
        "passive_count": len(passive),
        "expired": engine.search.expired(),
        "contractor_validity": validity,
        "attribution": tracker.public(),
        "selected_prefix": tracker.selected,
        "target_state": state,
        "verification": verification,
    }
    return public, {
        "engine": engine,
        "tracker": tracker,
        "clauses": list(engine.search.clauses),
    }


def shared_context_census(
    solver, interface, engine, tracker, clauses, contractor_boundary,
    transformed_boundary, limits, constraints
):
    entries = interface.make_rule_entries(
        solver, engine, clauses, tracker, "expanded_equational"
    )
    seed = engine.encode_rigid(contractor_boundary)
    target = engine.encode_rigid(transformed_boundary)
    transition_limit = constraints["maximum_transitions_per_graph"]
    state_limit = constraints[
        "maximum_unique_first_step_states_per_graph"
    ]
    seen = set()
    states = {}
    direct_count = 0
    pair_count = 0
    witness = None
    truncated = False

    for entry in entries:
        for path, after, proof in interface.apply_entry(
            solver, engine, seed, entry, require_decrease=False
        ):
            key = interface.transition_key(
                engine.search.m, 0, seed, after, entry, path
            )
            if key in seen:
                continue
            seen.add(key)
            if len(seen) > transition_limit:
                truncated = True
                break
            state_key = interface.state_signature(engine.search.m, after)
            states.setdefault(state_key, {
                "term": after,
                "proof": proof,
            })
            if after == target:
                direct_count += 1
                witness = witness or proof
            if len(states) > state_limit:
                truncated = True
                break
        if truncated:
            break

    first_transition_count = len(seen)
    if not truncated:
        for state_key in sorted(states):
            state = states[state_key]
            for entry in entries:
                for path, after, second_proof in interface.apply_entry(
                    solver,
                    engine,
                    state["term"],
                    entry,
                    require_decrease=False,
                ):
                    key = interface.transition_key(
                        engine.search.m,
                        0,
                        state["term"],
                        after,
                        entry,
                        path,
                    )
                    if key in seen:
                        continue
                    seen.add(key)
                    if len(seen) > transition_limit:
                        truncated = True
                        break
                    if after == target:
                        pair_count += 1
                        if witness is None:
                            witness = solver.Recipe(
                                state["proof"].lhs,
                                second_proof.rhs,
                                "transitivity",
                                (state["proof"], second_proof),
                            )
                if truncated:
                    break
            if truncated:
                break

    witness_verification = interface.verify_witness(
        solver, engine, witness, limits
    )
    return {
        "seed": solver.render_term(contractor_boundary),
        "target": solver.render_term(transformed_boundary),
        "rule_count": len(entries),
        "first_step_transitions": first_transition_count,
        "unique_first_step_states": len(states),
        "direct_bridge_count": direct_count,
        "pair_bridge_count": pair_count,
        "total_transitions_examined": len(seen),
        "truncated": truncated,
        "first_bridge_witness": witness_verification,
    }


def arm_success(arm, official):
    proof = arm["verification"]
    internal = (
        proof["reconstruction_root_matches"]
        and proof["reconstruction_replayed"]
        and proof["certificate_within_limit"]
    )
    return internal and (
        not official or proof["judge_status"] == "accepted"
    )


def decide(arms, census, measurement_ok, smoke, official):
    if smoke:
        return "SMOKE_ONLY"
    if not measurement_ok:
        return "MEASUREMENT_FAILURE"
    if arm_success(arms["A_transformed_baseline"], official):
        return "TRANSFORMED_BASELINE_CLOSES"
    if arm_success(arms["B_contractor_installed"], official):
        return "CONTRACTOR_INSTALLATION_CAUSAL_AFTER_MACRO"
    if arm_success(arms["C_contractor_forced_once"], official):
        return "CONTRACTOR_SELECTION_CAUSAL_AFTER_MACRO"
    distances = {
        name: arm["target_state"]["structural_distance"]
        for name, arm in arms.items()
    }
    if distances["C_contractor_forced_once"] < min(
        distances["A_transformed_baseline"],
        distances["B_contractor_installed"],
    ):
        return "CONTRACTOR_SELECTION_PARTIAL_AFTER_MACRO"
    if census["direct_bridge_count"] or census["pair_bridge_count"]:
        return "SHARED_CONTEXT_BRIDGE_PRESENT"
    attribution = arms["C_contractor_forced_once"]["attribution"]
    active = attribution.get("active_clause", {}).get("exact_count", 0)
    descendants = attribution.get(
        "contractor_descendant_admitted", {}
    ).get("count", 0)
    if active and descendants:
        return "SIBLING_ATTACHMENT_OBSTRUCTION"
    return "CONTRACTOR_DISPLACED_AFTER_MACRO"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=DEFAULT_SOLVER)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--official", action="store_true")
    parser.add_argument("--smoke", action="store_true")
    args = parser.parse_args()

    protocol = json.loads(PROTO.read_text(encoding="utf-8"))
    constraints = dict(protocol["constraints"])
    constraints["macro_transformed_goal"] = protocol["target"][
        "macro_transformed_goal"
    ]
    actual_solver_hash = sha256(args.solver)

    rows = json.loads(args.input.read_text(encoding="utf-8"))
    expected_headers = {
        "id", "index", "difficulty", "eq1_id", "eq2_id",
        "equation1", "equation2",
    }
    header_ok = bool(rows) and all(set(row) == expected_headers for row in rows)
    row = next(row for row in rows if row["id"] == protocol["target"]["id"])
    body_ok = (
        row["equation1"] == protocol["target"]["source"]
        and row["equation2"] == protocol["target"]["original_goal"]
        and "answer" not in row
    )

    attribution = load_module(
        ATTRIBUTION_RUNNER, "mathgraph_0036_post_macro_attribution"
    )
    interface = load_module(
        INTERFACE_RUNNER, "mathgraph_0036_post_macro_interface"
    )
    macro = load_module(
        MACRO_RUNNER, "mathgraph_0036_post_macro_dependency"
    )
    solver = attribution.load_solver(args.solver)
    source = solver.parse_equation(row["equation1"])
    original_target = solver.parse_equation(row["equation2"])
    transformed_target = solver.parse_equation(
        protocol["target"]["macro_transformed_goal"]
    )
    contractor = solver.parse_equation(
        protocol["target"]["known_contractor"]
    )
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

    equivalence = attribution.equivalence_probe(
        solver, source, transformed_target, contractor, limits
    )
    macro_data = reconstruct_macro(
        solver,
        attribution,
        interface,
        macro,
        source,
        original_target,
        contractor,
        limits,
        constraints,
    )
    boundary_macro = macro_data["macro_public"]
    seconds = 0.5 if args.smoke else constraints["seconds_per_arm"]
    maximum_given = 8 if args.smoke else constraints["maximum_given"]
    official = args.official and not args.smoke
    problem = {
        "id": "evaluation_normal_0036_post_macro_contractor",
        "eq1_id": row["eq1_id"],
        "eq2_id": row["eq2_id"],
        "equation1": row["equation1"],
        "equation2": row["equation2"],
    }
    arm_specs = {
        "A_transformed_baseline": (False, False),
        "B_contractor_installed": (True, False),
        "C_contractor_forced_once": (True, True),
    }
    arms = {}
    private = {}
    for name, (install, force) in arm_specs.items():
        arms[name], private[name] = run_arm(
            solver,
            attribution,
            macro,
            source,
            original_target,
            transformed_target,
            contractor,
            boundary_macro,
            limits,
            seconds,
            maximum_given,
            constraints["focus_per_age"],
            problem,
            official,
            constraints["certificate_limit_bytes"],
            install,
            force,
        )

    forced = private["C_contractor_forced_once"]
    context_census = shared_context_census(
        solver,
        interface,
        forced["engine"],
        forced["tracker"],
        forced["clauses"],
        contractor[1],
        transformed_target[1],
        limits,
        constraints,
    )
    common_core = contractor[1][1]
    factorization_checks = {
        "both_compound": contractor[1][0] == transformed_target[1][0] == "op",
        "shared_left_exact": common_core == transformed_target[1][1],
        "shared_left_size_9": solver.term_size(common_core) == 9,
        "contractor_sibling_size_3": solver.term_size(contractor[1][2]) == 3,
        "target_sibling_size_5": solver.term_size(transformed_target[1][2]) == 5,
        "sibling_distance_5": solver.structural_distance(
            contractor[1][2], transformed_target[1][2]
        ) == 5,
        "whole_distance_5": solver.structural_distance(
            contractor[1], transformed_target[1]
        ) == 5,
    }

    contractor_checks = {}
    for name in ("B_contractor_installed", "C_contractor_forced_once"):
        validity = arms[name]["contractor_validity"] or {}
        contractor_checks[name] = {
            "root_matches": validity.get("root_matches") is True,
            "replayed": validity.get("replayed") is True,
            "admitted": validity.get("admitted") is True,
        }
    forced_attribution = arms["C_contractor_forced_once"]["attribution"]
    forced_checks = {
        "forced_selected": forced_attribution.get(
            "forced_selected_counterfactual", {}
        ).get("exact_count", 0) > 0,
        "active": forced_attribution.get(
            "active_clause", {}
        ).get("exact_count", 0) > 0,
    }
    witness = context_census["first_bridge_witness"]
    census_integrity = (
        not context_census["truncated"]
        and (
            witness is None
            or (
                witness["compiled"]
                and witness["root_matches"]
                and witness["replayed"]
            )
        )
    )
    reconstruction_integrity = all(
        not arm["verification"]["target_recipe_found"]
        or (
            arm["verification"]["target_compiled"]
            and arm["verification"]["target_root_matches"]
            and arm["verification"]["target_replayed"]
            and arm["verification"]["reconstruction_compiled"]
            and arm["verification"]["reconstruction_root_matches"]
            and arm["verification"]["reconstruction_replayed"]
            and arm["verification"]["certificate_within_limit"]
        )
        for arm in arms.values()
    )
    official_integrity = (
        not official
        or all(
            not arm["verification"]["target_recipe_found"]
            or arm["verification"]["judge_status"] == "accepted"
            for arm in arms.values()
        )
    )
    measurement_ok = (
        protocol["schema"]
        == "mathgraph.0036-post-macro-contractor-preregistration.v2"
        and protocol["status"]
        == "AMENDED_BEFORE_EXECUTABLE_AFTER_STATIC_DECISION_COVERAGE_REVIEW"
        and actual_solver_hash == constraints["solver_sha256"]
        and header_ok
        and body_ok
        and equivalence["passed"]
        and all(macro_data["public"]["checks"].values())
        and all(factorization_checks.values())
        and all(
            all(checks.values()) for checks in contractor_checks.values()
        )
        and all(forced_checks.values())
        and census_integrity
        and reconstruction_integrity
        and official_integrity
    )
    decision = decide(
        arms, context_census, measurement_ok, args.smoke, official
    )
    output = {
        "schema": "mathgraph.0036-post-macro-contractor-results.v1",
        "decision": decision,
        "measurement_ok": measurement_ok,
        "smoke_only": args.smoke,
        "official_enabled": official,
        "solver_sha256": actual_solver_hash,
        "input_headers": sorted(expected_headers),
        "input_headers_ok": header_ok,
        "equation_bodies_ok": body_ok,
        "label_fields_available_to_runner": [],
        "pending_public_parent": protocol["pending_public_parent"],
        "observational_equivalence_probe": equivalence,
        "macro_reconstruction": macro_data["public"],
        "factorization": {
            "shared_left": solver.render_term(common_core),
            "contractor_sibling": solver.render_term(contractor[1][2]),
            "target_sibling": solver.render_term(transformed_target[1][2]),
            "checks": factorization_checks,
        },
        "contractor_checks": contractor_checks,
        "forced_checks": forced_checks,
        "arms": arms,
        "shared_context_census": context_census,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "decision": decision,
        "measurement_ok": measurement_ok,
        "smoke_only": args.smoke,
        "macro_pairs": macro_data["public"]["graph"][
            "pair_bridge_count"
        ],
        "shared_context": {
            "direct": context_census["direct_bridge_count"],
            "pairs": context_census["pair_bridge_count"],
            "states": context_census["unique_first_step_states"],
            "truncated": context_census["truncated"],
        },
        "arms": {
            name: {
                "found": arm["verification"]["target_recipe_found"],
                "distance": arm["target_state"]["structural_distance"],
                "rounds": arm["rounds"],
                "judge": arm["verification"]["judge_status"],
            }
            for name, arm in arms.items()
        },
    }, sort_keys=True), flush=True)
    if not measurement_ok:
        raise SystemExit("measurement failure")


if __name__ == "__main__":
    main()
