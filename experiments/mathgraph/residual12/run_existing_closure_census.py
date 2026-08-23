#!/usr/bin/env python3
"""Run one frozen strongest configuration from each existing TRUE constructor."""

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from pathlib import Path


sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
DEFAULT_SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
DEFAULT_INPUT = Path(__file__).with_name("released_residuals_unlabelled.json")
EXPECTED_COLUMNS = {
    "id", "index", "difficulty", "eq1_id", "eq2_id",
    "equation1", "equation2",
}


def load_solver(path):
    spec = importlib.util.spec_from_file_location(
        "mathgraph_residual12_closure_solver", path
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def finish(solver, source, target, found, maximum_term_size, maximum_nodes):
    result = {
        "found": found is not None,
        "root_matches": False,
        "replayed": False,
        "proof_nodes": 0,
        "certificate_bytes": 0,
        "certificate_sha256": None,
    }
    if found is None:
        return result
    nodes, root = found
    result["root_matches"] = (nodes[root].lhs, nodes[root].rhs) == target[:2]
    result["replayed"] = solver.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=maximum_term_size,
        maximum_nodes=maximum_nodes,
    )
    code, proof_nodes = solver.make_dag_certificate(target, nodes, root)
    encoded = code.encode("utf-8")
    result.update({
        "proof_nodes": proof_nodes,
        "certificate_bytes": len(encoded),
        "certificate_sha256": hashlib.sha256(encoded).hexdigest(),
    })
    return result


def safe_run(name, budget, operation):
    started = time.monotonic()
    error = None
    try:
        result, metrics = operation(started + budget)
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError, ValueError
    ) as exc:
        result, metrics = None, {}
        error = type(exc).__name__
    return {
        "route": name,
        "budget_seconds": budget,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "error": error,
        "result": result,
        "metrics": metrics,
    }


def compact_route(solver, source, target):
    configuration = dict(solver.COMPACT_SUPERPOSITION_FAST)

    def run(deadline):
        search = solver.CompactSuperposition(
            solver, source, target, deadline, configuration
        )
        recipe = search.solve()
        found = None if recipe is None else search.compile(recipe)
        result = finish(
            solver, source, target, found,
            configuration["maximum_replay_term_size"],
            configuration["maximum_proof_nodes"],
        )
        metrics = {
            "clauses": len(search.clauses),
            "rounds": search.rounds,
            "superpositions": search.superpositions,
            "reductions": search.reductions,
        }
        return result, metrics

    return safe_run(configuration["name"] if "name" in configuration else
                    "compact-fast", configuration["seconds"], run)


def normalization_route(solver, source, target):
    configuration = dict(solver.NORMALIZATION_PORTFOLIO[3])

    def run(deadline):
        search = solver.EquationalNormalizer(
            source, target, deadline, configuration
        )
        found = search.solve()
        result = finish(
            solver, source, target, found,
            configuration["maximum_term_size"],
            configuration["maximum_proof_nodes"],
        )
        fields = (
            "source_instances_generated", "composed_consequences",
            "replayed_candidates", "replay_failures", "decreasing_rules",
            "nonorientable_equalities", "local_critical_pairs",
            "joined_critical_pairs", "unresolved_critical_pairs",
            "distinct_normal_forms", "exhaustion",
        )
        return result, {field: getattr(search, field) for field in fields}

    return safe_run(configuration["name"], configuration["seconds"], run)


def bridge_route(solver, source, target):
    configuration = dict(solver.BRIDGE_IR_PORTFOLIO[3])

    def run(deadline):
        search = solver.BridgeIR(source, target, deadline, configuration)
        found = search.solve()
        result = finish(
            solver, source, target, found,
            configuration["normalizer"]["maximum_term_size"],
            configuration["maximum_proof_nodes"],
        )
        fields = (
            "bridge_equality_candidates", "replayed_bridge_equalities",
            "bridge_replay_failures", "bridge_matches_attempted",
            "bridge_states_created", "bridge_states_deduplicated",
            "anti_unification_proposals", "anti_unification_replayed",
            "maximum_bridge_depth", "initial_normalizer_matches",
            "post_bridge_normalizer_matches", "shared_normal_form_hits",
            "deadline_exits", "state_budget_exits", "exhaustion",
        )
        return result, {field: getattr(search, field) for field in fields}

    return safe_run(configuration["name"], configuration["seconds"], run)


def reentry_route(solver, source, target):
    configuration = solver.REENTRY_PORTFOLIO[2]

    def run(deadline):
        search = solver.EqualitySearch(
            source, target, deadline, configuration["limits"]
        )
        found = search.solve()
        generation_zero = found is not None
        if found is None:
            search.max_term_size = configuration["reentry_term_size"]
            search.max_derivation_nodes = configuration["reentry_nodes"]
            search.max_graph_edges = configuration["reentry_edges"]
            search.exhaustion = None
            found = search.solve_reentry(
                configuration["generations"],
                configuration["new_terms"],
                configuration["instances"],
                targeted=configuration["targeted"],
            )
        result = finish(
            solver, source, target, found,
            configuration["reentry_term_size"],
            configuration["reentry_nodes"],
        )
        metrics = {
            "generation_zero_found": generation_zero,
            "nodes": len(search.nodes),
            "edges": search.graph_edges,
            "generations_completed": search.generations_completed,
            "source_instances_by_generation":
                search.source_instances_by_generation,
            "reentry_terms_used": len(search.reentry_terms_used),
            "exhaustion": search.exhaustion,
        }
        return result, metrics

    return safe_run(configuration["name"], configuration["seconds"], run)


def contextual_route(solver, source, target):
    configuration = solver.CONTEXTUAL_PORTFOLIO[0]

    def run(deadline):
        search = solver.ContextualSearch(
            source, target, deadline, configuration["limits"]
        )
        found = search.solve_target_narrowing(
            configuration["maximum_depth"],
            configuration["branching"],
            configuration["maximum_terms"],
            configuration["maximum_context_depth"],
        )
        result = finish(
            solver, source, target, found,
            configuration["limits"]["max_term_size"],
            configuration["limits"]["max_derivation_nodes"],
        )
        fields = (
            "narrowing_successors", "missing_target_introduced",
            "components_joined", "term_size_rejections", "exhaustion",
        )
        metrics = {
            field: getattr(search, field, None) for field in fields
        }
        return result, metrics

    return safe_run(configuration["name"], configuration["seconds"], run)


ROUTES = (
    compact_route,
    normalization_route,
    bridge_route,
    reentry_route,
    contextual_route,
)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=DEFAULT_SOLVER)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rows = json.loads(args.input.read_text(encoding="utf-8"))
    if (
        not isinstance(rows, list)
        or len(rows) != 12
        or any(set(row) != EXPECTED_COLUMNS for row in rows)
    ):
        raise SystemExit("unexpected unlabelled residual schema")
    solver_bytes = args.solver.read_bytes()
    if hashlib.sha256(solver_bytes).hexdigest() != (
        "a92eae8cce4fdf7c787c3218fa4f7eb1158c92a6b57f2920199ddbe6e7726a08"
    ):
        raise SystemExit("solver hash differs from frozen preregistration")
    solver = load_solver(args.solver)
    output_rows = []
    started = time.monotonic()
    for index, row in enumerate(rows, 1):
        source = solver.parse_equation(row["equation1"])
        target = solver.parse_equation(row["equation2"])
        attempts = []
        for route in ROUTES:
            attempt = route(solver, source, target)
            attempts.append(attempt)
            print(json.dumps({"id": row["id"], **attempt}), flush=True)
        output_rows.append({
            "id": row["id"],
            "difficulty": row["difficulty"],
            "ordinal": index,
            "attempts": attempts,
        })
    output = {
        "schema": "mathgraph.verified-residual-12-closure-census.v1",
        "solver_sha256": hashlib.sha256(solver_bytes).hexdigest(),
        "input_sha256": hashlib.sha256(args.input.read_bytes()).hexdigest(),
        "label_fields_available_to_runner": [],
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "rows": output_rows,
    }
    args.output.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    successes = sum(
        attempt["result"] is not None
        and attempt["result"]["found"]
        and attempt["result"]["root_matches"]
        and attempt["result"]["replayed"]
        and attempt["result"]["certificate_bytes"] <= 100000
        for row in output_rows for attempt in row["attempts"]
    )
    print(json.dumps({
        "rows": len(output_rows),
        "route_attempts": len(output_rows) * len(ROUTES),
        "internal_successes": successes,
        "elapsed_seconds": output["elapsed_seconds"],
    }), flush=True)


if __name__ == "__main__":
    main()
