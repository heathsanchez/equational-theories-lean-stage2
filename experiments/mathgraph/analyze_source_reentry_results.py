#!/usr/bin/env python3
"""Structural post-freeze audit for unresolved TRUE sample_200 rows."""

import argparse
import importlib.util
import json
import statistics
import sys
import time
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOLVER_FILE = ROOT / "submissions" / "mathgraph" / "solver.py"
BASELINE_SOLVER = (
    ROOT / "experiments" / "mathgraph" / "regressions" / "solver_896e063.py"
)
BASELINE_RESULTS = (
    ROOT / "experiments" / "mathgraph" / "results"
    / "sample_200_equality_chain.json"
)
PROBLEMS = ROOT / "examples" / "problems" / "sample_200.json"


def load_solver(path=SOLVER_FILE, name="mathgraph_solver"):
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def constructor(row):
    code = row.get("code") or ""
    marker = "-- mathgraph constructor: "
    if marker in code:
        return code.split(marker, 1)[1].splitlines()[0]
    if row.get("verdict") == "true":
        return "direct source instance"
    if row.get("verdict") == "false":
        return "Fin 2 countermodel"
    return "unresolved"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    solver = load_solver()
    problems = json.loads(PROBLEMS.read_text(encoding="utf-8"))
    results = {
        row["id"]: row
        for row in json.loads(args.results.read_text(encoding="utf-8"))
    }
    unresolved_true = [
        problem
        for problem in problems
        if problem.get("answer") is True and not results[problem["id"]].get("solved")
    ]
    phenotypes = Counter()
    resources = Counter()
    graph_sizes = []
    largest_nodes = 0
    largest_edges = 0

    configuration = solver.PROMOTED_REENTRY_PORTFOLIO[0]
    for problem in unresolved_true:
        source = solver.parse_equation(problem["equation1"])
        target = solver.parse_equation(problem["equation2"])
        search = solver.EqualitySearch(
            source,
            target,
            time.monotonic() + configuration["seconds"],
            configuration["limits"],
        )
        found = search.solve()
        if found is None:
            search.max_term_size = configuration["reentry_term_size"]
            search.max_derivation_nodes = configuration["reentry_nodes"]
            search.max_graph_edges = configuration["reentry_edges"]
            search.exhaustion = None
            found = search.solve_reentry(
                configuration["generations"],
                configuration["new_terms"],
                configuration["instances"],
                configuration["targeted"],
            )
        left, right = target[:2]
        components = search.components()
        left_in = left in search.adjacency
        right_in = right in search.adjacency
        if not left_in and not right_in:
            phenotype = "neither target side enters graph"
        elif left_in and not right_in:
            phenotype = "only left target side enters graph"
        elif right_in and not left_in:
            phenotype = "only right target side enters graph"
        elif components.get(left) != components.get(right):
            phenotype = "both enter graph but remain disconnected"
        elif found is None:
            phenotype = "graph connects mathematically but proof extraction fails"
        else:
            phenotype = "unexpected solved prefix"
        phenotypes[phenotype] += 1
        if search.exhaustion:
            resources[search.exhaustion] += 1
        graph_sizes.append(search.graph_edges)
        largest_nodes = max(largest_nodes, len(search.nodes))
        largest_edges = max(largest_edges, search.graph_edges)

    rows = list(results.values())
    baseline_results = {
        row["id"]: row
        for row in json.loads(BASELINE_RESULTS.read_text(encoding="utf-8"))
    }
    baseline_solver = load_solver(BASELINE_SOLVER, "mathgraph_baseline_solver")
    solved_former_one_side = 0
    for problem in problems:
        if not (
            problem.get("answer") is True
            and results[problem["id"]].get("solved")
            and not baseline_results[problem["id"]].get("solved")
        ):
            continue
        source = baseline_solver.parse_equation(problem["equation1"])
        target = baseline_solver.parse_equation(problem["equation2"])
        search = baseline_solver.EqualitySearch(
            source, target, time.monotonic() + 2.0
        )
        search.solve()
        left, right = target[:2]
        if (left in search.adjacency) != (right in search.adjacency):
            solved_former_one_side += 1
    rejected = Counter(
        event.get("response", {}).get("status", "unparsed")
        for row in rows
        for event in row.get("log", [])
        if event.get("type") == "judge"
        and event.get("response", {}).get("status") != "accepted"
    )
    certificates = [
        len(row["code"].encode("utf-8"))
        for row in rows
        if row.get("code")
    ]
    report = {
        "unresolved_true": len(unresolved_true),
        "phenotypes": dict(sorted(phenotypes.items())),
        "only_one_target_side": (
            phenotypes["only left target side enters graph"]
            + phenotypes["only right target side enters graph"]
        ),
        "primary_causal_metric": {
            "recorded_baseline_only_one": 21,
            "solved_former_one_side": solved_former_one_side,
            "recorded_bucket_after_solved_cases": 21 - solved_former_one_side,
            "strict_exact_side_baseline": 28,
            "strict_exact_side_after": (
                phenotypes["only left target side enters graph"]
                + phenotypes["only right target side enters graph"]
            ),
        },
        "resource_exhaustion": dict(sorted(resources.items())),
        "constructor_hits": dict(
            sorted(Counter(constructor(row) for row in rows).items())
        ),
        "rejected_judge_attempts": dict(sorted(rejected.items())),
        "llm_calls": sum(row.get("llm_calls", 0) for row in rows),
        "runtime_seconds": {
            "total": round(sum(row["elapsed_seconds"] for row in rows), 2),
            "median": statistics.median(row["elapsed_seconds"] for row in rows),
            "maximum": max(row["elapsed_seconds"] for row in rows),
        },
        "largest_search": {
            "nodes": largest_nodes,
            "edges": largest_edges,
            "median_edges_unresolved_true": statistics.median(graph_sizes),
        },
        "largest_certificate_bytes": max(certificates),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
