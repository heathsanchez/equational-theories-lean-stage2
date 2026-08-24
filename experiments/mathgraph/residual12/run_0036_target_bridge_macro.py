#!/usr/bin/env python3
"""Causally test one frozen target-side bridge macro for residual 0036."""

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
PROTO = HERE / "0036_target_bridge_macro_preregistration.json"
INTERFACE_RUNNER = HERE / "run_0036_boundary_interface_reachability.py"
ATTRIBUTION_RUNNER = HERE / "run_0036_causal_contractor_attribution.py"
DEFAULT_SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
DEFAULT_INPUT = HERE / "released_residuals_unlabelled.json"
DEFAULT_PARENT = (
    HERE / "evidence" /
    "0036_boundary_interface_reachability_run_32683209277.json"
)
DEFAULT_OUTPUT = HERE / "0036_target_bridge_macro_results.json"


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_parent(path, protocol):
    expected = protocol["immediate_parent"]
    data = json.loads(path.read_text(encoding="utf-8"))
    expected_headers = {
        "schema", "recorded_date", "repository", "workflow",
        "workflow_run", "job", "head_branch", "head_sha", "conclusion",
        "artifact", "result_summary", "selected_bridge", "claim_boundary",
    }
    headers_ok = set(data) == expected_headers
    artifact = data.get("artifact", {})
    result = data.get("result_summary", {})
    graphs = result.get("graphs", {})
    directed = graphs.get("expanded_directed", {})
    equational = graphs.get("expanded_equational", {})
    checks = {
        "headers": headers_ok,
        "sha256": sha256(path) == expected["evidence_sha256"],
        "workflow_run": data.get("workflow_run")
        == expected["workflow_run"],
        "head_sha": data.get("head_sha") == expected["head_sha"],
        "conclusion": data.get("conclusion") == "success",
        "artifact_id": artifact.get("id") == expected["artifact_id"],
        "artifact_zip_sha256": artifact.get("zip_sha256")
        == expected["artifact_zip_sha256"],
        "decision": result.get("decision")
        == expected["required_decision"],
        "measurement_ok": result.get("measurement_ok")
        is expected["required_measurement_ok"],
        "equational_pair_bridges": equational.get("pair_bridges")
        == expected["required_equational_pair_bridges"],
        "directed_pair_bridges": directed.get("pair_bridges")
        == expected["required_directed_pair_bridges"],
        "no_truncation": all(
            graph.get("truncated") is False for graph in graphs.values()
        ),
    }
    return {
        "path": str(path.relative_to(ROOT)),
        "sha256": sha256(path),
        "headers": sorted(expected_headers),
        "checks": checks,
        "passed": all(checks.values()),
    }


def parse_rhs(solver, text):
    return solver.parse_equation("x = " + text)[1]


def public_term(solver, engine, term):
    return solver.render_term(engine.inline(term))


def public_recipe(solver, engine, recipe):
    inlined = engine.inline_recipe(recipe)
    return {
        "lhs": solver.render_term(inlined.lhs),
        "rhs": solver.render_term(inlined.rhs),
        "kind": recipe.kind,
        "cost": recipe.cost,
    }


def bridge_score(solver, engine, seed, first_after, second_after,
                 first_entry, second_entry):
    expanded_seed = engine.inline(seed)
    expanded_first = engine.inline(first_after)
    expanded_second = engine.inline(second_after)
    return (
        max(
            solver.term_size(expanded_seed),
            solver.term_size(expanded_first),
            solver.term_size(expanded_second),
        ),
        solver.term_size(expanded_second),
        first_entry["recipe"].cost + second_entry["recipe"].cost,
        solver.render_term(expanded_second),
    )


def enumerate_and_select_bridge(
    solver, interface, engine, tracker, clauses, limits, constraints
):
    search = engine.search
    seeds = [
        engine.encode_rigid(engine.target[0]),
        engine.encode_rigid(engine.target[1]),
    ]
    entries = interface.make_rule_entries(
        solver, engine, clauses, tracker, "expanded_equational"
    )
    lineage_entries = [entry for entry in entries if entry["lineage"]]
    transition_limit = constraints["maximum_transitions_per_graph"]
    state_limit = constraints[
        "maximum_unique_first_step_states_per_graph"
    ]
    transition_seen = set()
    first_states = {}
    truncated = False

    for seed_index, seed in enumerate(seeds):
        for entry in entries:
            for path, after, proof in interface.apply_entry(
                solver, engine, seed, entry, require_decrease=False
            ):
                key = interface.transition_key(
                    search.m, seed_index, seed, after, entry, path
                )
                if key in transition_seen:
                    continue
                transition_seen.add(key)
                if len(transition_seen) > transition_limit:
                    truncated = True
                    break
                state_key = (
                    seed_index,
                    interface.state_signature(search.m, after),
                )
                state = first_states.setdefault(state_key, {
                    "term": after,
                    "proof": None,
                    "entry": None,
                    "path": None,
                })
                if not entry["lineage"] and state["proof"] is None:
                    state["proof"] = proof
                    state["entry"] = entry
                    state["path"] = path
                if len(first_states) > state_limit:
                    truncated = True
                    break
            if truncated:
                break
        if truncated:
            break

    candidates = []
    if not truncated:
        for (seed_index, _), state in sorted(
            first_states.items(), key=lambda item: repr(item[0])
        ):
            if state["proof"] is None:
                continue
            for entry in lineage_entries:
                for path, after, second_proof in interface.apply_entry(
                    solver,
                    engine,
                    state["term"],
                    entry,
                    require_decrease=False,
                ):
                    key = interface.transition_key(
                        search.m,
                        seed_index,
                        state["term"],
                        after,
                        entry,
                        path,
                    )
                    if key in transition_seen:
                        continue
                    transition_seen.add(key)
                    if len(transition_seen) > transition_limit:
                        truncated = True
                        break
                    score = bridge_score(
                        solver,
                        engine,
                        seeds[seed_index],
                        state["term"],
                        after,
                        state["entry"],
                        entry,
                    )
                    candidates.append({
                        "score": score,
                        "seed_index": seed_index,
                        "seed": seeds[seed_index],
                        "first_after": state["term"],
                        "second_after": after,
                        "first_entry": state["entry"],
                        "second_entry": entry,
                        "first_path": state["path"],
                        "second_path": path,
                        "first_proof": state["proof"],
                        "second_proof": second_proof,
                    })
                if truncated:
                    break
            if truncated:
                break

    candidates.sort(key=lambda candidate: candidate["score"])
    selected = candidates[0] if candidates else None
    if selected is not None:
        selected["macro"] = solver.Recipe(
            selected["first_proof"].lhs,
            selected["second_proof"].rhs,
            "transitivity",
            (selected["first_proof"], selected["second_proof"]),
        )
    return {
        "entries": entries,
        "lineage_entries": lineage_entries,
        "first_states": first_states,
        "first_transition_count": sum(
            1 for key in transition_seen if key is not None
        ) - len(candidates),
        "pair_count": len(candidates),
        "total_transition_count": len(transition_seen),
        "truncated": truncated,
        "selected": selected,
    }


def selected_bridge_public(solver, engine, selected):
    if selected is None:
        return None
    return {
        "score": list(selected["score"]),
        "seed_index": selected["seed_index"],
        "seed": public_term(solver, engine, selected["seed"]),
        "first_path": list(selected["first_path"]),
        "first_after": public_term(
            solver, engine, selected["first_after"]
        ),
        "first_rule": interface_rule_public(
            solver, engine, selected["first_entry"]
        ),
        "second_path": list(selected["second_path"]),
        "second_after": public_term(
            solver, engine, selected["second_after"]
        ),
        "second_rule": interface_rule_public(
            solver, engine, selected["second_entry"]
        ),
        "macro": public_recipe(solver, engine, selected["macro"]),
    }


def interface_rule_public(solver, engine, entry):
    recipe = entry["recipe"]
    return {
        "lhs": public_term(solver, engine, recipe.lhs),
        "rhs": public_term(solver, engine, recipe.rhs),
        "kind": recipe.kind,
        "cost": recipe.cost,
        "contractor_lineage": entry["lineage"],
    }


def selected_bridge_checks(
    solver, engine, selected, public, protocol, pair_count, truncated
):
    expected = protocol["selected_macro"]
    expected_score = list(expected["selection_score"])
    return {
        "not_truncated": not truncated,
        "pair_count": pair_count
        == protocol["immediate_parent"]["required_equational_pair_bridges"],
        "selected": selected is not None,
        "seed_side": selected is not None and selected["seed_index"] == 1,
        "score": public is not None and public["score"] == expected_score,
        "seed": public is not None
        and public["seed"].replace("◇", "*")
        == solver.render_term(parse_rhs(solver, expected["seed"])).replace(
            "◇", "*"
        ),
        "first_after": public is not None
        and engine.inline(selected["first_after"])
        == parse_rhs(solver, expected["first_after"]),
        "second_after": public is not None
        and engine.inline(selected["second_after"])
        == parse_rhs(solver, expected["second_after"]),
        "first_kind": public is not None
        and public["first_rule"]["kind"] == expected["first_rule_kind"],
        "first_cost": public is not None
        and public["first_rule"]["cost"] == expected["first_rule_cost"],
        "first_path": public is not None
        and public["first_path"] == expected["first_path"],
        "second_kind": public is not None
        and public["second_rule"]["kind"] == expected["second_rule_kind"],
        "second_cost": public is not None
        and public["second_rule"]["cost"] == expected["second_rule_cost"],
        "second_path": public is not None
        and public["second_path"] == expected["second_path"],
    }


def verify_recipe(solver, source, target, recipe, limits):
    compiler = solver.CompactSuperposition(
        solver, source, target, time.monotonic() + 10, limits
    )
    compiled = compiler.compile(recipe)
    if compiled is None:
        return None, {
            "compiled": False,
            "root_matches": False,
            "replayed": False,
            "proof_nodes": 0,
        }
    nodes, root = compiled
    root_pair = (nodes[root].lhs, nodes[root].rhs)
    root_matches = root_pair == recipe_pair(recipe)
    replayed = solver.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=limits["maximum_replay_term_size"],
        maximum_nodes=limits["maximum_proof_nodes"],
    )
    return compiled, {
        "compiled": True,
        "root_matches": root_matches,
        "replayed": replayed,
        "proof_nodes": len(nodes),
        "lhs": solver.render_term(root_pair[0]),
        "rhs": solver.render_term(root_pair[1]),
    }


def recipe_pair(recipe):
    return recipe.lhs, recipe.rhs


def direct_second_matches(
    solver, interface, engine, selected, original_boundary
):
    matches = list(interface.apply_entry(
        solver,
        engine,
        original_boundary,
        selected["second_entry"],
        require_decrease=False,
    ))
    return {
        "count": len(matches),
        "after": [
            public_term(solver, engine, item[1]) for item in matches
        ],
    }


def reconstruct_original(
    solver, source, original_target, engine, raw_recipe, boundary_macro,
    limits, problem, official, certificate_limit
):
    output = {
        "target_recipe_found": raw_recipe is not None,
        "target_compiled": False,
        "target_root_matches": False,
        "target_replayed": False,
        "reconstruction_compiled": False,
        "reconstruction_root_matches": False,
        "reconstruction_replayed": False,
        "proof_nodes": 0,
        "certificate_bytes": 0,
        "certificate_within_limit": False,
        "judge_status": None,
    }
    if raw_recipe is None:
        return output

    target_compiled = engine.compile_recipe(raw_recipe)
    if target_compiled is None:
        return output
    target_nodes, target_root = target_compiled
    output["target_compiled"] = True
    output["target_root_matches"] = (
        target_nodes[target_root].lhs,
        target_nodes[target_root].rhs,
    ) == engine.target[:2]
    output["target_replayed"] = solver.replay_dag(
        source,
        target_nodes,
        target_root,
        maximum_term_size=limits["maximum_replay_term_size"],
        maximum_nodes=limits["maximum_proof_nodes"],
    )

    target_recipe = engine.inline_recipe(raw_recipe)
    reconstructed = target_recipe
    if boundary_macro is not None:
        if target_recipe.rhs != boundary_macro.rhs:
            output["reconstruction_mismatch"] = {
                "target_rhs": solver.render_term(target_recipe.rhs),
                "macro_rhs": solver.render_term(boundary_macro.rhs),
            }
            return output
        reverse_macro = solver.Recipe(
            boundary_macro.rhs,
            boundary_macro.lhs,
            "symmetry",
            (boundary_macro,),
        )
        reconstructed = solver.Recipe(
            target_recipe.lhs,
            reverse_macro.rhs,
            "transitivity",
            (target_recipe, reverse_macro),
        )

    compiler = solver.CompactSuperposition(
        solver, source, original_target, time.monotonic() + 10, limits
    )
    compiled = compiler.compile(reconstructed)
    if compiled is None:
        return output
    nodes, root = compiled
    output["reconstruction_compiled"] = True
    output["reconstruction_root_matches"] = (
        nodes[root].lhs, nodes[root].rhs
    ) == original_target[:2]
    output["reconstruction_replayed"] = solver.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=limits["maximum_replay_term_size"],
        maximum_nodes=limits["maximum_proof_nodes"],
    )
    code, proof_nodes = solver.make_dag_certificate(
        original_target, nodes, root
    )
    output["proof_nodes"] = proof_nodes
    output["certificate_bytes"] = len(code.encode("utf-8"))
    output["certificate_within_limit"] = (
        output["certificate_bytes"] <= certificate_limit
    )
    if (
        official
        and output["reconstruction_root_matches"]
        and output["reconstruction_replayed"]
        and output["certificate_within_limit"]
    ):
        attribution = sys.modules["mathgraph_0036_macro_attribution"]
        output["judge_status"] = attribution.officially_verify(problem, code)
    return output


def run_arm(
    solver, source, original_target, target, boundary_macro, limits,
    seconds, maximum_given, focus_per_age, problem, official,
    certificate_limit, installed_recipes=()
):
    started = time.monotonic()
    engine = solver.TargetGroundedRefutation(
        source, target, started + seconds, dict(limits)
    )
    installation = []
    for recipe in installed_recipes:
        before = len(engine.search.clauses)
        admitted = engine.search.add_clause(recipe)
        installation.append({
            "recipe": public_recipe(solver, engine, recipe),
            "admitted": admitted,
            "new_clauses": len(engine.search.clauses) - before,
        })
    raw_recipe = engine.search.solve_given_clause(
        maximum_given=maximum_given,
        focus_per_age=focus_per_age,
    )
    verification = reconstruct_original(
        solver,
        source,
        original_target,
        engine,
        raw_recipe,
        boundary_macro,
        limits,
        problem,
        official,
        certificate_limit,
    )
    return {
        "target": {
            "lhs": solver.render_term(target[0]),
            "rhs": solver.render_term(target[1]),
        },
        "boundary_macro": (
            None if boundary_macro is None else {
                "lhs": solver.render_term(boundary_macro.lhs),
                "rhs": solver.render_term(boundary_macro.rhs),
                "cost": boundary_macro.cost,
            }
        ),
        "installation": installation,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "clauses": len(engine.search.clauses),
        "rounds": engine.search.rounds,
        "superpositions": engine.search.superpositions,
        "reductions": engine.search.reductions,
        "expired": engine.search.expired(),
        "verification": verification,
    }


def arm_succeeds(arm):
    proof = arm["verification"]
    return (
        proof["reconstruction_root_matches"]
        and proof["reconstruction_replayed"]
        and proof["certificate_within_limit"]
        and proof["judge_status"] == "accepted"
    )


def decide(arms, direct_second, measurement_ok, smoke):
    if smoke:
        return "SMOKE_ONLY"
    if not measurement_ok:
        return "MEASUREMENT_FAILURE"
    if arm_succeeds(arms["A_frozen_original"]) or arm_succeeds(
        arms["B_pair_installed_directed"]
    ):
        return "BASELINE_OR_INSTALLED_PAIR_CLOSES"
    if arm_succeeds(arms["C_first_step_only"]):
        return "SINGLE_STEP_SUFFICIENT"
    if (
        arm_succeeds(arms["E_full_two_step_macro"])
        and not arm_succeeds(arms["D_second_step_only"])
        and direct_second["count"] == 0
    ):
        return "TARGET_BRIDGE_MACRO_CAUSAL"
    return "POST_MACRO_SEARCH_FAILURE"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=DEFAULT_SOLVER)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--parent", type=Path, default=DEFAULT_PARENT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--official", action="store_true")
    parser.add_argument("--smoke", action="store_true")
    args = parser.parse_args()

    protocol = json.loads(PROTO.read_text(encoding="utf-8"))
    parent = validate_parent(args.parent, protocol)
    constraints = protocol["constraints"]
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
        ATTRIBUTION_RUNNER, "mathgraph_0036_macro_attribution"
    )
    interface = load_module(
        INTERFACE_RUNNER, "mathgraph_0036_macro_interface"
    )
    solver = attribution.load_solver(args.solver)
    source = solver.parse_equation(row["equation1"])
    original_target = solver.parse_equation(row["equation2"])
    contractor = solver.parse_equation(
        "x = (((x * (x * z)) * (x * x)) * (x * z))"
    )
    first_target = (
        original_target[0],
        parse_rhs(solver, protocol["selected_macro"]["first_after"]),
        original_target[2],
    )
    second_target = (
        original_target[0],
        parse_rhs(solver, protocol["selected_macro"]["second_after"]),
        original_target[2],
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
        solver, source, original_target, contractor, limits
    )
    reconstruction_seconds = constraints[
        "seconds_for_bridge_reconstruction"
    ]
    started = time.monotonic()
    parent_engine = solver.TargetGroundedRefutation(
        source,
        original_target,
        started + reconstruction_seconds,
        dict(limits),
    )
    tracker = attribution.AttributionTracker(
        solver, parent_engine, contractor
    )
    injected = attribution.contractor_recipe(solver, parent_engine)
    contractor_validity = attribution.verify_contractor(
        solver, parent_engine, injected, contractor, limits
    )
    tracker.observe("installed_counterfactual", injected)
    before = len(parent_engine.search.clauses)
    contractor_validity["admitted"] = parent_engine.search.add_clause(injected)
    for clause in parent_engine.search.clauses[before:]:
        tracker.observe("admitted_clause", clause)
    attribution.install_observation_hooks(parent_engine.search, tracker)
    closure_recipe, active, passive, active_rules = (
        attribution.instrumented_given_clause(
            parent_engine.search,
            tracker,
            constraints["maximum_given"],
            constraints["focus_per_age"],
            force_contractor_once=True,
        )
    )
    closure_elapsed = time.monotonic() - started
    clauses = list(parent_engine.search.clauses)
    closure_state = attribution.target_state(
        solver, parent_engine, active_rules
    )
    closure_checks = {
        "contractor_root_matches": contractor_validity.get(
            "root_matches"
        ) is True,
        "contractor_replayed": contractor_validity.get("replayed") is True,
        "contractor_admitted": contractor_validity.get("admitted") is True,
        "forced_selected": tracker.events.get(
            "forced_selected_counterfactual", {}
        ).get("exact_count", 0) > 0,
        "contractor_descendants": tracker.descendant_events.get(
            "contractor_descendant_admitted", {}
        ).get("count", 0) > 0,
        "target_distance_10": closure_state["structural_distance"] == 10,
        "no_target_proof": closure_recipe is None,
    }

    graph_constraints = dict(constraints)
    graphs = {
        graph: interface.census_graph(
            solver,
            parent_engine,
            tracker,
            clauses,
            graph,
            limits,
            graph_constraints,
        )
        for graph in (
            "internal_operational",
            "expanded_directed",
            "expanded_equational",
        )
    }
    bridge_data = enumerate_and_select_bridge(
        solver,
        interface,
        parent_engine,
        tracker,
        clauses,
        limits,
        graph_constraints,
    )
    selected = bridge_data["selected"]
    selected_public = selected_bridge_public(
        solver, parent_engine, selected
    )
    selected_checks = selected_bridge_checks(
        solver,
        parent_engine,
        selected,
        selected_public,
        protocol,
        bridge_data["pair_count"],
        bridge_data["truncated"],
    )
    macro_public = (
        None if selected is None else parent_engine.inline_recipe(
            selected["macro"]
        )
    )
    first_public = (
        None if selected is None else parent_engine.inline_recipe(
            selected["first_proof"]
        )
    )
    second_public = (
        None if selected is None else parent_engine.inline_recipe(
            selected["second_proof"]
        )
    )
    macro_compiled, macro_verification = (
        (None, {
            "compiled": False,
            "root_matches": False,
            "replayed": False,
            "proof_nodes": 0,
        })
        if macro_public is None
        else verify_recipe(
            solver,
            source,
            original_target,
            macro_public,
            limits,
        )
    )
    if macro_compiled is not None:
        macro_verification["boundary_root_matches"] = (
            macro_public.lhs == original_target[1]
            and macro_public.rhs == second_target[1]
        )
    else:
        macro_verification["boundary_root_matches"] = False

    direct_second = (
        {"count": -1, "after": []}
        if selected is None
        else direct_second_matches(
            solver,
            interface,
            parent_engine,
            selected,
            parent_engine.encode_rigid(original_target[1]),
        )
    )

    seconds = 0.5 if args.smoke else constraints["seconds_per_arm"]
    maximum_given = 8 if args.smoke else constraints["maximum_given"]
    official = args.official and not args.smoke
    problem = {
        "id": "evaluation_normal_0036_target_bridge_macro",
        "eq1_id": row["eq1_id"],
        "eq2_id": row["eq2_id"],
        "equation1": row["equation1"],
        "equation2": row["equation2"],
    }
    installed = () if selected is None else (
        selected["first_proof"], selected["second_proof"]
    )
    arms = {
        "A_frozen_original": run_arm(
            solver, source, original_target, original_target, None,
            limits, seconds, maximum_given, constraints["focus_per_age"],
            problem, official, constraints["certificate_limit_bytes"],
        ),
        "B_pair_installed_directed": run_arm(
            solver, source, original_target, original_target, None,
            limits, seconds, maximum_given, constraints["focus_per_age"],
            problem, official, constraints["certificate_limit_bytes"],
            installed_recipes=installed,
        ),
        "C_first_step_only": run_arm(
            solver, source, original_target, first_target, first_public,
            limits, seconds, maximum_given, constraints["focus_per_age"],
            problem, official, constraints["certificate_limit_bytes"],
        ),
        "D_second_step_only": run_arm(
            solver, source, original_target, original_target, None,
            limits, seconds, maximum_given, constraints["focus_per_age"],
            problem, official, constraints["certificate_limit_bytes"],
        ),
        "E_full_two_step_macro": run_arm(
            solver, source, original_target, second_target, macro_public,
            limits, seconds, maximum_given, constraints["focus_per_age"],
            problem, official, constraints["certificate_limit_bytes"],
        ),
    }

    graph_integrity = all(
        not graph["truncated"]
        and (
            graph["first_bridge_witness"] is None
            or (
                graph["first_bridge_witness"]["compiled"]
                and graph["first_bridge_witness"]["root_matches"]
                and graph["first_bridge_witness"]["replayed"]
            )
        )
        for graph in graphs.values()
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
        == "mathgraph.0036-target-bridge-macro-preregistration.v1"
        and protocol["status"] == "FROZEN_BEFORE_EXECUTABLE"
        and parent["passed"]
        and actual_solver_hash == constraints["solver_sha256"]
        and header_ok
        and body_ok
        and equivalence["passed"]
        and all(closure_checks.values())
        and graph_integrity
        and graphs["internal_operational"]["pair_bridge_count"] == 0
        and graphs["expanded_directed"]["pair_bridge_count"] == 0
        and graphs["expanded_equational"]["pair_bridge_count"]
        == protocol["immediate_parent"][
            "required_equational_pair_bridges"
        ]
        and all(selected_checks.values())
        and macro_verification["compiled"]
        and macro_verification["root_matches"]
        and macro_verification["replayed"]
        and macro_verification["boundary_root_matches"]
        and direct_second["count"] == 0
        and reconstruction_integrity
        and official_integrity
    )
    decision = decide(
        arms, direct_second, measurement_ok, args.smoke
    )
    output = {
        "schema": "mathgraph.0036-target-bridge-macro-results.v1",
        "decision": decision,
        "measurement_ok": measurement_ok,
        "smoke_only": args.smoke,
        "official_enabled": official,
        "solver_sha256": actual_solver_hash,
        "input_headers": sorted(expected_headers),
        "input_headers_ok": header_ok,
        "equation_bodies_ok": body_ok,
        "label_fields_available_to_runner": [],
        "parent_evidence": parent,
        "observational_equivalence_probe": equivalence,
        "closure_reproduction": {
            "elapsed_seconds": round(closure_elapsed, 6),
            "clauses": len(clauses),
            "rounds": parent_engine.search.rounds,
            "superpositions": parent_engine.search.superpositions,
            "active_count": len(active),
            "passive_count": len(passive),
            "target_state": closure_state,
            "contractor_validity": contractor_validity,
            "checks": closure_checks,
        },
        "graphs": {
            name: {
                "rule_count": graph["rule_count"],
                "contractor_lineage_rule_count": graph[
                    "contractor_lineage_rule_count"
                ],
                "unique_first_step_states": graph[
                    "unique_first_step_states"
                ],
                "direct_bridge_count": graph["direct_bridge_count"],
                "pair_bridge_count": graph["pair_bridge_count"],
                "total_transitions_examined": graph[
                    "total_transitions_examined"
                ],
                "truncated": graph["truncated"],
                "first_bridge_witness": graph[
                    "first_bridge_witness"
                ],
            }
            for name, graph in graphs.items()
        },
        "selected_bridge": selected_public,
        "selected_bridge_checks": selected_checks,
        "macro_verification": macro_verification,
        "direct_second_step_at_original_boundary": direct_second,
        "arms": arms,
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
        "closure_clauses": len(clauses),
        "equational_pair_bridges": graphs[
            "expanded_equational"
        ]["pair_bridge_count"],
        "selected_score": (
            None if selected_public is None else selected_public["score"]
        ),
        "direct_second_matches": direct_second["count"],
        "arms": {
            name: {
                "found": arm["verification"]["target_recipe_found"],
                "reconstructed": arm["verification"][
                    "reconstruction_replayed"
                ],
                "judge": arm["verification"]["judge_status"],
                "rounds": arm["rounds"],
            }
            for name, arm in arms.items()
        },
    }, sort_keys=True), flush=True)
    if not measurement_ok:
        raise SystemExit("measurement failure")


if __name__ == "__main__":
    main()
