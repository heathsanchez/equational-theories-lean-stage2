#!/usr/bin/env python3
"""Census the boundary-to-contractor interface in the frozen 0036 closure."""

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
PROTO = HERE / "0036_boundary_interface_reachability_preregistration.json"
ATTRIBUTION_RUNNER = HERE / "run_0036_causal_contractor_attribution.py"
DEFAULT_SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
DEFAULT_INPUT = HERE / "released_residuals_unlabelled.json"
DEFAULT_PARENT = (
    HERE / "evidence" /
    "0036_causal_contractor_attribution_results_run_32677423657.json"
)
DEFAULT_OUTPUT = HERE / "0036_boundary_interface_reachability_results.json"


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
    digest = sha256(path)
    data = json.loads(path.read_text(encoding="utf-8"))
    arm_c = data.get("arm_C_known_contractor_forced_once", {})
    attribution = arm_c.get("attribution", {})
    forced = attribution.get("forced_selected_counterfactual", {})
    descendants = attribution.get("contractor_descendant_admitted", {})
    checks = {
        "sha256": digest == expected["result_json_sha256"],
        "schema": data.get("schema") == expected["required_schema"],
        "decision": data.get("decision") == expected["required_decision"],
        "measurement_ok": data.get("measurement_ok")
        is expected["required_measurement_ok"],
        "forced_exact": forced.get("exact_count", 0)
        >= expected["required_forced_exact_minimum"],
        "contractor_descendants": descendants.get("count", 0)
        >= expected["required_contractor_descendants_minimum"],
    }
    return {
        "sha256": digest,
        "checks": checks,
        "passed": all(checks.values()),
        "decision": data.get("decision"),
        "forced_exact": forced.get("exact_count", 0),
        "contractor_descendants": descendants.get("count", 0),
    }


def directional_signature(module, recipe):
    names = {}
    return repr((
        module.alpha_canonical_term(recipe.lhs, names),
        module.alpha_canonical_term(recipe.rhs, names),
    ))


def state_signature(module, term):
    return repr(module.alpha_canonical_term(term, {}))


def public_term(solver, engine, term):
    return solver.render_term(engine.inline(term))


def public_rule(solver, engine, entry):
    recipe = entry["recipe"]
    return {
        "lhs": public_term(solver, engine, recipe.lhs),
        "rhs": public_term(solver, engine, recipe.rhs),
        "kind": recipe.kind,
        "cost": recipe.cost,
        "contractor_lineage": entry["lineage"],
    }


def lineage_clause(tracker, recipe):
    return tracker.is_exact(recipe) or tracker.has_exact_ancestor(recipe)


def make_rule_entries(solver, engine, clauses, tracker, graph):
    search = engine.search
    entries = {}
    for clause in clauses:
        lineage = lineage_clause(tracker, clause)
        working = (
            engine.inline_recipe(clause)
            if graph != "internal_operational"
            else clause
        )
        candidates = []
        if graph in {"internal_operational", "expanded_directed"}:
            oriented = search.orient(working)
            if oriented is not None:
                candidates.append(oriented)
        else:
            if working.lhs[0] != "var":
                candidates.append(working)
            if working.rhs[0] != "var":
                candidates.append(solver.Recipe(
                    working.rhs,
                    working.lhs,
                    "symmetry",
                    (working,),
                ))
        for candidate in candidates:
            all_variables = (
                search.m.term_variables(candidate.lhs)
                | search.m.term_variables(candidate.rhs)
            )
            key = directional_signature(search.m, candidate)
            existing = entries.get(key)
            record = {
                "recipe": candidate,
                "lineage": lineage,
                "all_variables": all_variables,
                "signature": key,
            }
            if existing is None or (lineage and not existing["lineage"]):
                entries[key] = record
    return [entries[key] for key in sorted(entries)]


def transition_key(module, seed_index, before, after, entry, path):
    return repr((
        seed_index,
        module.alpha_canonical_term(before, {}),
        module.alpha_canonical_term(after, {}),
        entry["signature"],
        tuple(path),
    ))


def apply_entry(solver, engine, term, entry, require_decrease):
    search = engine.search
    recipe = entry["recipe"]
    for path in search.m.nonvariable_positions(
        term,
        maximum_depth=search.limits["maximum_depth"],
        include_root=True,
    ):
        selected = search.m.get_subterm(term, path)
        mapping = {}
        if not search.m.match_term(recipe.lhs, selected, mapping):
            continue
        if not entry["all_variables"] <= set(mapping):
            continue
        replacement = search.m.substitute_partial(recipe.rhs, mapping)
        after = search.m.replace_subterm(term, path, replacement)
        if after == term:
            continue
        if search.m.term_size(after) > search.limits["maximum_term_size"]:
            continue
        if require_decrease and search.key(after) >= search.key(term):
            continue
        proof = search.instantiate(recipe, mapping)
        proof = search.lift(proof, term, path)
        yield path, after, proof


def verify_witness(solver, engine, recipe, limits):
    if recipe is None:
        return None
    inlined = engine.inline_recipe(recipe)
    compiler = solver.CompactSuperposition(
        solver,
        engine.source,
        engine.target,
        time.monotonic() + 10,
        limits,
    )
    compiled = compiler.compile(inlined)
    if compiled is None:
        return {
            "compiled": False,
            "root_matches": False,
            "replayed": False,
            "proof_nodes": 0,
        }
    nodes, root = compiled
    pair = (nodes[root].lhs, nodes[root].rhs)
    expected = (inlined.lhs, inlined.rhs)
    root_matches = pair == expected
    replayed = solver.replay_dag(
        engine.source,
        nodes,
        root,
        maximum_term_size=limits["maximum_replay_term_size"],
        maximum_nodes=limits["maximum_proof_nodes"],
    )
    return {
        "compiled": True,
        "root_matches": root_matches,
        "replayed": replayed,
        "proof_nodes": len(nodes),
        "lhs": solver.render_term(pair[0]),
        "rhs": solver.render_term(pair[1]),
    }


def census_graph(solver, engine, tracker, clauses, graph, limits, constraints):
    search = engine.search
    expanded = graph != "internal_operational"
    require_decrease = graph != "expanded_equational"
    seeds = (
        [search.target[0], search.target[1]]
        if not expanded
        else [
            engine.encode_rigid(engine.target[0]),
            engine.encode_rigid(engine.target[1]),
        ]
    )
    entries = make_rule_entries(
        solver, engine, clauses, tracker, graph
    )
    lineage_entries = [entry for entry in entries if entry["lineage"]]
    transition_limit = constraints["maximum_transitions_per_graph"]
    state_limit = constraints["maximum_unique_first_step_states_per_graph"]
    example_limit = constraints["report_examples"]
    transition_seen = set()
    first_states = {}
    direct_count = 0
    direct_witness = None
    examples = []
    truncated = False

    for seed_index, seed in enumerate(seeds):
        for entry in entries:
            for path, after, proof in apply_entry(
                solver, engine, seed, entry, require_decrease
            ):
                key = transition_key(
                    search.m, seed_index, seed, after, entry, path
                )
                if key in transition_seen:
                    continue
                transition_seen.add(key)
                if len(transition_seen) > transition_limit:
                    truncated = True
                    break
                state_key = (seed_index, state_signature(search.m, after))
                state_record = first_states.setdefault(state_key, {
                    "term": after,
                    "nonlineage_proof": None,
                    "nonlineage_entry": None,
                    "nonlineage_path": None,
                })
                if not entry["lineage"] and state_record["nonlineage_proof"] is None:
                    state_record["nonlineage_proof"] = proof
                    state_record["nonlineage_entry"] = entry
                    state_record["nonlineage_path"] = path
                if entry["lineage"]:
                    direct_count += 1
                    if direct_witness is None:
                        direct_witness = proof
                if len(examples) < example_limit:
                    examples.append({
                        "seed": seed_index,
                        "path": list(path),
                        "after": public_term(solver, engine, after),
                        "rule": public_rule(solver, engine, entry),
                    })
                if len(first_states) > state_limit:
                    truncated = True
                    break
            if truncated:
                break
        if truncated:
            break

    first_transition_count = len(transition_seen)
    pair_count = 0
    pair_witness = None
    pair_examples = []
    if not truncated:
        for (seed_index, _), state in sorted(
            first_states.items(), key=lambda item: repr(item[0])
        ):
            if state["nonlineage_proof"] is None:
                continue
            for entry in lineage_entries:
                for path, after, second_proof in apply_entry(
                    solver,
                    engine,
                    state["term"],
                    entry,
                    require_decrease,
                ):
                    key = transition_key(
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
                    pair_count += 1
                    if pair_witness is None:
                        pair_witness = solver.Recipe(
                            state["nonlineage_proof"].lhs,
                            second_proof.rhs,
                            "transitivity",
                            (state["nonlineage_proof"], second_proof),
                        )
                    if len(pair_examples) < example_limit:
                        pair_examples.append({
                            "seed": seed_index,
                            "first_rule": public_rule(
                                solver, engine, state["nonlineage_entry"]
                            ),
                            "first_after": public_term(
                                solver, engine, state["term"]
                            ),
                            "second_path": list(path),
                            "second_rule": public_rule(
                                solver, engine, entry
                            ),
                            "second_after": public_term(
                                solver, engine, after
                            ),
                        })
                if truncated:
                    break
            if truncated:
                break

    witness_recipe = direct_witness or pair_witness
    witness = verify_witness(solver, engine, witness_recipe, limits)
    return {
        "graph": graph,
        "expanded": expanded,
        "require_decrease": require_decrease,
        "seed_terms": [public_term(solver, engine, seed) for seed in seeds],
        "rule_count": len(entries),
        "contractor_lineage_rule_count": len(lineage_entries),
        "first_step_transitions": first_transition_count,
        "unique_first_step_states": len(first_states),
        "direct_bridge_count": direct_count,
        "pair_bridge_count": pair_count,
        "minimum_bridge_depth": (
            1 if direct_count else (2 if pair_count else None)
        ),
        "total_transitions_examined": len(transition_seen),
        "truncated": truncated,
        "examples": examples,
        "pair_examples": pair_examples,
        "first_bridge_witness": witness,
    }


def decide(graphs, measurement_ok):
    if not measurement_ok:
        return "MEASUREMENT_FAILURE"
    internal = graphs["internal_operational"]
    directed = graphs["expanded_directed"]
    equational = graphs["expanded_equational"]

    def bridge(graph):
        return graph["direct_bridge_count"] + graph["pair_bridge_count"] > 0

    if bridge(internal):
        return "INTERNAL_OPERATIONAL_BRIDGE_PRESENT"
    if bridge(directed):
        return "ALIAS_INTERFACE_OBSTRUCTION"
    if bridge(equational):
        return "ORIENTATION_ORDER_OBSTRUCTION"
    return "BOUNDARY_INTERFACE_DISCONNECTED"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=DEFAULT_SOLVER)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--parent", type=Path, default=DEFAULT_PARENT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--smoke", action="store_true")
    args = parser.parse_args()

    protocol = json.loads(PROTO.read_text(encoding="utf-8"))
    parent = validate_parent(args.parent, protocol)
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
        and row["equation2"] == protocol["target"]["goal"]
        and "answer" not in row
    )

    attribution = load_module(
        ATTRIBUTION_RUNNER, "mathgraph_0036_attribution_dependency"
    )
    solver = attribution.load_solver(args.solver)
    source = solver.parse_equation(row["equation1"])
    target = solver.parse_equation(row["equation2"])
    contractor = solver.parse_equation(protocol["target"]["known_contractor"])
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
    limits["seconds"] = constraints["seconds_for_closure"]

    equivalence = attribution.equivalence_probe(
        solver, source, target, contractor, limits
    )
    seconds = 0.5 if args.smoke else constraints["seconds_for_closure"]
    maximum_given = 8 if args.smoke else constraints["maximum_given"]
    started = time.monotonic()
    engine = solver.TargetGroundedRefutation(
        source, target, started + seconds, dict(limits)
    )
    tracker = attribution.AttributionTracker(solver, engine, contractor)
    injected = attribution.contractor_recipe(solver, engine)
    validity = attribution.verify_contractor(
        solver, engine, injected, contractor, limits
    )
    tracker.observe("installed_counterfactual", injected)
    before = len(engine.search.clauses)
    admitted = engine.search.add_clause(injected)
    for clause in engine.search.clauses[before:]:
        tracker.observe("admitted_clause", clause)
    validity["admitted"] = admitted
    attribution.install_observation_hooks(engine.search, tracker)
    recipe, active, passive, active_rules = attribution.instrumented_given_clause(
        engine.search,
        tracker,
        maximum_given,
        constraints["focus_per_age"],
        force_contractor_once=True,
    )
    closure_elapsed = time.monotonic() - started
    clauses = list(engine.search.clauses)
    lineage_count = sum(lineage_clause(tracker, clause) for clause in clauses)
    state = attribution.target_state(solver, engine, active_rules)
    reproduction_checks = {
        "contractor_root_matches": validity.get("root_matches") is True,
        "contractor_replayed": validity.get("replayed") is True,
        "contractor_admitted": validity.get("admitted") is True,
        "forced_selected": tracker.events.get(
            "forced_selected_counterfactual", {}
        ).get("exact_count", 0) > 0,
        "contractor_active": tracker.events.get(
            "active_clause", {}
        ).get("exact_count", 0) > 0,
        "descendants_admitted": tracker.descendant_events.get(
            "contractor_descendant_admitted", {}
        ).get("count", 0) > 0,
        "target_distance_10": state["structural_distance"] == 10,
        "no_target_proof": recipe is None,
    }

    graphs = {}
    for graph in (
        "internal_operational",
        "expanded_directed",
        "expanded_equational",
    ):
        graphs[graph] = census_graph(
            solver,
            engine,
            tracker,
            clauses,
            graph,
            limits,
            constraints,
        )

    graph_integrity = all(
        not result["truncated"]
        and (
            result["first_bridge_witness"] is None
            or (
                result["first_bridge_witness"]["compiled"]
                and result["first_bridge_witness"]["root_matches"]
                and result["first_bridge_witness"]["replayed"]
            )
        )
        for result in graphs.values()
    )
    measurement_ok = (
        protocol["schema"]
        == "mathgraph.0036-boundary-interface-reachability-preregistration.v2"
        and parent["passed"]
        and actual_solver_hash == constraints["solver_sha256"]
        and header_ok
        and body_ok
        and equivalence["passed"]
        and all(reproduction_checks.values())
        and lineage_count > 0
        and graph_integrity
    )
    decision = "SMOKE_ONLY" if args.smoke else decide(graphs, measurement_ok)
    output = {
        "schema": "mathgraph.0036-boundary-interface-reachability-results.v2",
        "decision": decision,
        "measurement_ok": measurement_ok,
        "smoke_only": args.smoke,
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
            "rounds": engine.search.rounds,
            "superpositions": engine.search.superpositions,
            "active_count": len(active),
            "passive_count": len(passive),
            "contractor_lineage_clauses": lineage_count,
            "contractor_validity": validity,
            "attribution": tracker.public(),
            "target_state": state,
            "checks": reproduction_checks,
        },
        "graphs": graphs,
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
        "lineage_clauses": lineage_count,
        "graphs": {
            name: {
                "rules": result["rule_count"],
                "states": result["unique_first_step_states"],
                "direct": result["direct_bridge_count"],
                "pairs": result["pair_bridge_count"],
                "truncated": result["truncated"],
            }
            for name, result in graphs.items()
        },
    }, sort_keys=True))


if __name__ == "__main__":
    main()
