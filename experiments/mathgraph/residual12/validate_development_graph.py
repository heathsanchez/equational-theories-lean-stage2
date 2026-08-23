#!/usr/bin/env python3
"""Validate the minimal typed developmental graph and print live frontiers."""

import json
from pathlib import Path


GRAPH = Path(__file__).with_name("development_graph.json")
REQUIRED_SCIENTIFIC_FIELDS = {"rho", "D", "H", "K", "Delta", "V", "B", "E"}


def main():
    graph = json.loads(GRAPH.read_text(encoding="utf-8"))
    nodes = graph["nodes"]
    node_ids = [node["id"] for node in nodes]
    assert len(node_ids) == len(set(node_ids)), "duplicate node id"
    allowed = set(graph["allowed_edge_types"])
    known = set(node_ids)
    for edge in graph["edges"]:
        assert edge["type"] in allowed, edge
        assert edge["source"] in known, edge
        assert edge["target"] in known, edge
    for node in nodes:
        if node["kind"] == "experiment":
            missing = REQUIRED_SCIENTIFIC_FIELDS - set(node)
            assert not missing, (node["id"], sorted(missing))
    selected = {
        edge["target"]
        for edge in graph["edges"]
        if edge["type"] == "SELECTS_NEXT"
    }
    frontiers = [
        node["id"] for node in nodes
        if node.get("status") in {"frontier", "frozen"}
    ]
    assert selected <= set(frontiers), "SELECTS_NEXT target is not actionable"
    print(json.dumps({
        "schema": graph["schema"],
        "nodes": len(nodes),
        "edges": len(graph["edges"]),
        "frontiers": frontiers,
        "selected_next": sorted(selected),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
