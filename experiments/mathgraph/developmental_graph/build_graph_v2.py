#!/usr/bin/env python3
"""Build the typed developmental experiment graph v2.

V2 preserves the failed v1 lesson: repo-local result JSONs are not the only
research evidence substrate.  It distinguishes raw committed results from
explicit CI-run references, repo experiment references, and scope-only nodes.
No scientific result is inferred from filenames or experiment definitions.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PROTO = HERE / "protocol-v2.json"
REGISTRY = HERE / "evidence-registry-v2.json"
LINEAGE = HERE / "lineage-v1.json"
DEFAULT_OUT = HERE / "graph-v2.json"


def stable_hash(obj):
    payload = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    return hashlib.sha256(payload).hexdigest()


def load_json(path):
    return json.loads(path.read_text())


def raw_node(path, data):
    protocol = data.get("protocol") if isinstance(data.get("protocol"), dict) else None
    evidence = {}
    for key in ("stage_counts", "counts", "frozen", "summary", "evidence"):
        if key in data:
            evidence[key] = data[key]
    return {
        "node_id": path.name,
        "problem_id": data.get("id"),
        "evidence_class": "RAW_RESULT_JSON",
        "decision": data.get("decision"),
        "schema": data.get("schema"),
        "source_path": str(path.relative_to(ROOT)),
        "run_id": None,
        "protocol": protocol,
        "bounds": protocol.get("bounds") if protocol else None,
        "evidence": evidence or None,
        "provenance": "committed repo-local result JSON",
        "content_sha256": stable_hash(data),
    }


def registry_node(entry):
    out = {
        "node_id": entry["node_id"],
        "problem_id": entry["problem_id"],
        "evidence_class": entry["evidence_class"],
        "decision": entry.get("decision"),
        "schema": entry.get("schema"),
        "source_path": entry.get("source_path"),
        "run_id": entry.get("run_id"),
        "protocol": None,
        "bounds": None,
        "evidence": entry.get("evidence"),
        "provenance": entry["provenance"],
        "content_sha256": stable_hash(entry),
    }
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()

    proto = load_json(PROTO)
    registry = load_json(REGISTRY)
    lineage = load_json(LINEAGE)
    scope = list(proto["scope"])
    scope_set = set(scope)
    allowed_classes = set(proto["evidence_classes"])

    nodes = {}
    parse_failures = []
    source_path_failures = []

    # Explicit registry first; raw committed results overwrite it by rule.
    for entry in registry.get("entries", []):
        try:
            if entry["problem_id"] not in scope_set:
                continue
            if entry["evidence_class"] not in allowed_classes:
                raise ValueError(f"unknown evidence class {entry['evidence_class']}")
            if not entry.get("provenance"):
                raise ValueError("missing provenance")
            if entry["evidence_class"] == "SCOPE_ONLY" and entry.get("decision") is not None:
                raise ValueError("scope-only entry may not assert a decision")
            src = entry.get("source_path")
            if src and not (ROOT / src).exists():
                source_path_failures.append({"node_id": entry["node_id"], "source_path": src})
            nodes[entry["node_id"]] = registry_node(entry)
        except Exception as exc:
            parse_failures.append({"source": "registry", "node_id": entry.get("node_id"), "error": repr(exc)})

    result_dir = ROOT / "experiments/mathgraph/results"
    if result_dir.exists():
        for path in sorted(result_dir.glob("*.json")):
            try:
                data = load_json(path)
                if not isinstance(data, dict) or data.get("id") not in scope_set:
                    continue
                node = raw_node(path, data)
                nodes[node["node_id"]] = node
            except Exception as exc:
                parse_failures.append({"source": str(path.relative_to(ROOT)), "error": repr(exc)})

    # Ensure every problem is explicitly represented in the graph without
    # fabricating a scientific result.  Registry normally provides these.
    represented = {n["problem_id"] for n in nodes.values()}
    for problem_id in scope:
        if problem_id not in represented:
            node_id = f"scope-auto-{problem_id}"
            nodes[node_id] = {
                "node_id": node_id,
                "problem_id": problem_id,
                "evidence_class": "SCOPE_ONLY",
                "decision": None,
                "schema": None,
                "source_path": None,
                "run_id": None,
                "protocol": None,
                "bounds": None,
                "evidence": None,
                "provenance": "automatic scope node; no scientific result asserted",
                "content_sha256": stable_hash({"problem_id": problem_id, "class": "SCOPE_ONLY"}),
            }

    # Curated scientific relations remain manifest-only.
    edges = []
    unresolved = []
    edge_types = set(proto["edge_types"])
    for edge in lineage.get("edges", []):
        if edge.get("type") not in edge_types:
            unresolved.append({"edge": edge, "reason": "unknown edge type"})
            continue
        src, dst = edge.get("from"), edge.get("to")
        if src not in nodes or dst not in nodes:
            unresolved.append({"edge": edge, "reason": "node missing"})
            continue
        edges.append(edge)

    node_list = sorted(nodes.values(), key=lambda n: (n["problem_id"], n["node_id"]))
    edges = sorted(edges, key=lambda e: (e["from"], e["to"], e["type"]))
    class_counts = Counter(n["evidence_class"] for n in node_list)

    scope_coverage = {pid: any(n["problem_id"] == pid for n in node_list) for pid in scope}
    scientific_result_coverage = {
        pid: any(
            n["problem_id"] == pid
            and n["evidence_class"] in {"RAW_RESULT_JSON", "CI_RUN_REFERENCE"}
            and n.get("decision") is not None
            for n in node_list
        )
        for pid in scope
    }

    graph = {
        "schema": "mathgraph.developmental-experiment-graph.v2",
        "protocol_schema": proto["schema"],
        "scope": scope,
        "nodes": node_list,
        "edges": edges,
        "gaps": {
            "unresolved_curated_edges": unresolved,
            "parse_failures": parse_failures,
            "source_path_failures": source_path_failures,
            "problems_without_scientific_result_evidence": [pid for pid, ok in scientific_result_coverage.items() if not ok],
        },
        "summary": {
            "problem_count": len(scope),
            "node_count": len(node_list),
            "raw_result_node_count": class_counts.get("RAW_RESULT_JSON", 0),
            "registry_node_count": sum(v for k, v in class_counts.items() if k != "RAW_RESULT_JSON"),
            "evidence_class_counts": dict(sorted(class_counts.items())),
            "curated_edge_count": len(edges),
            "unresolved_curated_edge_count": len(unresolved),
            "parse_failure_count": len(parse_failures),
            "source_path_failure_count": len(source_path_failures),
            "scope_coverage": scope_coverage,
            "scientific_result_coverage": scientific_result_coverage,
            "scientific_result_problem_count": sum(scientific_result_coverage.values()),
        },
    }
    graph["graph_sha256"] = stable_hash({k: v for k, v in graph.items() if k != "graph_sha256"})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(graph, indent=2, sort_keys=True) + "\n")
    print(json.dumps(graph["summary"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
