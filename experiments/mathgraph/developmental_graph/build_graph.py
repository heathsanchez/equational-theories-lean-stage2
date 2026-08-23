#!/usr/bin/env python3
"""Build a typed developmental experiment graph from repo-local verified results.

This is deliberately not a solver and not an autonomous hypothesis generator.
It externalizes the evidence state that future controllers/agents may query.
Raw result JSON remains authoritative; curated scientific relations live only in
lineage-v1.json.
"""
from __future__ import annotations

import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PROTO = HERE / "protocol-v1.json"
LINEAGE = HERE / "lineage-v1.json"
RESULTS = ROOT / "experiments" / "mathgraph" / "results"
OUT = HERE / "developmental-graph-v1.json"
SUMMARY = HERE / "developmental-graph-summary-v1.json"


def canonical_sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def first(obj, *keys):
    for k in keys:
        if isinstance(obj, dict) and k in obj:
            return obj[k]
    return None


def result_node(path: Path, data: dict) -> dict:
    protocol = data.get("protocol") if isinstance(data.get("protocol"), dict) else None
    bounds = None
    if protocol:
        bounds = protocol.get("bounds")
    if bounds is None:
        bounds = data.get("bounds")
    evidence = {}
    for key in (
        "counts",
        "stage_counts",
        "cells_reaching",
        "frozen",
        "baseline",
        "admitted",
        "ablation",
        "decision_table",
    ):
        if key in data:
            evidence[key] = data[key]
    raw = path.read_bytes()
    return {
        "node_id": path.name,
        "node_type": "EXPERIMENT_RESULT",
        "problem_id": data.get("id"),
        "source_path": str(path.relative_to(ROOT)),
        "source_sha256": canonical_sha256(raw),
        "schema": data.get("schema"),
        "decision": data.get("decision"),
        "protocol": protocol,
        "bounds": bounds,
        "diagnosis": data.get("diagnosis"),
        "residual": data.get("residual"),
        "evidence": evidence or None,
    }


def main() -> None:
    protocol = json.loads(PROTO.read_text())
    lineage = json.loads(LINEAGE.read_text())
    scope = set(protocol["scope"])

    problem_nodes = [
        {
            "node_id": problem_id,
            "node_type": "PROBLEM",
            "problem_id": problem_id,
        }
        for problem_id in sorted(scope)
    ]

    result_nodes = []
    parse_failures = []
    for path in sorted(RESULTS.glob("*.json")):
        try:
            data = json.loads(path.read_text())
        except Exception as exc:
            parse_failures.append({"path": str(path.relative_to(ROOT)), "error": type(exc).__name__})
            continue
        if not isinstance(data, dict) or data.get("id") not in scope:
            continue
        result_nodes.append(result_node(path, data))

    result_by_name = {n["node_id"]: n for n in result_nodes}
    edges = []
    unresolved_curated_edges = []
    allowed_edges = set(protocol["edge_types"])
    for idx, edge in enumerate(lineage.get("edges", [])):
        if edge.get("type") not in allowed_edges:
            raise AssertionError(f"unapproved edge type: {edge.get('type')}")
        row = dict(edge)
        row["edge_id"] = f"curated:{idx:04d}"
        row["provenance"] = "experiments/mathgraph/developmental_graph/lineage-v1.json"
        if row.get("from") in result_by_name and row.get("to") in result_by_name:
            edges.append(row)
        else:
            unresolved_curated_edges.append(row)

    # Explicit containment edges are intentionally not invented. Problem membership is
    # represented directly by node.problem_id so graph consumers can query it without
    # introducing an un-frozen edge vocabulary.
    by_problem = Counter(n["problem_id"] for n in result_nodes)
    by_decision = Counter(n["decision"] or "<NONE>" for n in result_nodes)
    schemas = Counter(n["schema"] or "<NONE>" for n in result_nodes)

    graph = {
        "schema": "mathgraph.developmental-experiment-graph.v1",
        "protocol": protocol,
        "nodes": problem_nodes + result_nodes,
        "edges": edges,
        "unresolved_curated_edges": unresolved_curated_edges,
        "parse_failures": parse_failures,
    }
    summary = {
        "schema": "mathgraph.developmental-experiment-graph.summary.v1",
        "scope": sorted(scope),
        "problem_count": len(problem_nodes),
        "result_node_count": len(result_nodes),
        "curated_edge_count": len(edges),
        "unresolved_curated_edge_count": len(unresolved_curated_edges),
        "parse_failure_count": len(parse_failures),
        "results_by_problem": dict(sorted(by_problem.items())),
        "decisions": dict(by_decision.most_common()),
        "schemas": dict(schemas.most_common()),
        "coverage": {
            problem_id: by_problem.get(problem_id, 0) > 0 for problem_id in sorted(scope)
        },
    }

    # Determinism/admission checks.
    assert len({n["node_id"] for n in result_nodes}) == len(result_nodes)
    assert all(n["source_sha256"] for n in result_nodes)
    assert all(e["type"] in allowed_edges for e in edges)
    assert not parse_failures, parse_failures

    OUT.write_text(json.dumps(graph, indent=2, sort_keys=True) + "\n")
    SUMMARY.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
