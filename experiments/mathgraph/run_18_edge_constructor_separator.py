import importlib.util
import json
import re
import sys
import time
import urllib.request
from pathlib import Path

UPSTREAM_SHA = "e5a88a1479011ece4aad8e3c2e7e5c0ebc0a5b2a"
ROUTES = {
    "2666_to_2062": [2666, 2860, 2062],
    "3366_to_3390": [3366, 41, 3390],
    "1367_to_3599": [
        1367, 678, 1696, 979, 2945, 2938, 2922, 2920,
        1151, 689, 688, 2, 41, 3602, 3599,
    ],
}
EDGES = [
    (route_name, index, source, target)
    for route_name, route in ROUTES.items()
    for index, (source, target) in enumerate(zip(route, route[1:]), start=1)
]
assert len(EDGES) == 18


def load_equations():
    api = (
        "https://api.github.com/repos/teorth/equational_theories/contents/"
        "equational_theories/Equations?ref=" + UPSTREAM_SHA
    )
    request = urllib.request.Request(api, headers={"User-Agent": "mathgraph-separator"})
    with urllib.request.urlopen(request, timeout=30) as response:
        listing = json.load(response)
    files = [
        item for item in listing
        if item["name"].endswith(".lean") and item.get("download_url")
    ]
    needed = {number for _, _, source, target in EDGES for number in (source, target)}
    equations = {}
    declaration = re.compile(r"^equation\s+(\d+)\s*:=\s*(.+?)\s*$")
    for item in files:
        with urllib.request.urlopen(item["download_url"], timeout=30) as response:
            text = response.read().decode("utf-8")
        for line in text.splitlines():
            match = declaration.match(line)
            if not match:
                continue
            number = int(match.group(1))
            if number in needed:
                equations[number] = match.group(2)
        if needed <= equations.keys():
            break
    missing = sorted(needed - equations.keys())
    if missing:
        raise RuntimeError(f"missing equation declarations: {missing}")
    return equations


def load_solver():
    spec = importlib.util.spec_from_file_location(
        "mg_separator", "submissions/mathgraph/solver.py"
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def proof_ids(nodes, root):
    seen = set()
    stack = [root]
    while stack:
        node_id = stack.pop()
        if node_id in seen:
            continue
        seen.add(node_id)
        stack.extend(getattr(nodes[node_id], "parents", ()))
    return sorted(seen)


def proof_summary(nodes, root):
    ids = proof_ids(nodes, root)
    return {
        "proof_nodes": len(ids),
        "constructors": sorted(
            {str(getattr(nodes[node_id], "constructor", None)) for node_id in ids}
        ),
        "kinds": sorted({str(getattr(nodes[node_id], "kind", None)) for node_id in ids}),
    }


def run_equality_search(module, source, target):
    record = {}
    start = time.monotonic()
    try:
        search = module.EqualitySearch(source, target, time.monotonic() + 8.0)
        found = search.solve()
        record.update({
            "seconds": time.monotonic() - start,
            "exhaustion": getattr(search, "exhaustion", None),
            "graph_edges": getattr(search, "graph_edges", None),
            "nodes": len(getattr(search, "nodes", ())),
            "generations": getattr(search, "generations_completed", None),
        })
        if isinstance(found, tuple) and len(found) == 2:
            nodes, root = found
            record["found"] = True
            record["proof"] = proof_summary(nodes, root)
            try:
                replayed = module.replay_dag(source, nodes, root)
            except TypeError:
                replayed = module.replay_dag(
                    source,
                    nodes,
                    root,
                    maximum_term_size=getattr(search, "max_term_size", 256),
                    maximum_nodes=getattr(search, "max_derivation_nodes", 50000),
                )
            record["replayed"] = bool(replayed)
        else:
            record["found"] = bool(found)
            record["raw_result"] = repr(found)[:500]
    except Exception as error:
        record.update({
            "seconds": time.monotonic() - start,
            "found": False,
            "replayed": False,
            "error": type(error).__name__ + ": " + str(error),
        })
    return record


def run_target_grounded(module, source, target):
    record = {}
    start = time.monotonic()
    try:
        limits = dict(module.COMPACT_SUPERPOSITION_PROBE)
        engine = module.TargetGroundedRefutation(
            source, target, time.monotonic() + 8.0, limits
        )
        recipe = engine.solve()
        record.update({
            "seconds": time.monotonic() - start,
            "found": bool(recipe),
            "recipe_type": type(recipe).__name__ if recipe else None,
            "recipe": repr(recipe)[:1000] if recipe else None,
            "clauses": len(getattr(engine.search, "clauses", ())),
            "rounds": getattr(engine.search, "rounds", None),
            "superpositions": getattr(engine.search, "superpositions", None),
            "reductions": getattr(engine.search, "reductions", None),
        })
    except Exception as error:
        record.update({
            "seconds": time.monotonic() - start,
            "found": False,
            "error": type(error).__name__ + ": " + str(error),
        })
    return record


def main():
    equations = load_equations()
    module = load_solver()
    output = {
        "schema": "mathgraph.18-edge-constructor-separator.v2",
        "upstream_equations_commit": UPSTREAM_SHA,
        "solver_ref": "mathgraph/superposition-selector-tournament-20260820",
        "routes": ROUTES,
        "edges": [],
    }

    for route_name, route_index, source_id, target_id in EDGES:
        source_text = equations[source_id]
        target_text = equations[target_id]
        source = module.parse_equation(source_text)
        target = module.parse_equation(target_text)
        equality = run_equality_search(module, source, target)
        target_grounded = run_target_grounded(module, source, target)
        record = {
            "route": route_name,
            "route_edge_index": route_index,
            "source_id": source_id,
            "target_id": target_id,
            "source_equation": source_text,
            "target_equation": target_text,
            "equality_search": equality,
            "target_grounded": target_grounded,
        }
        output["edges"].append(record)
        print(json.dumps({
            "edge": f"{source_id}->{target_id}",
            "route": route_name,
            "equality_found": equality.get("found"),
            "equality_replayed": equality.get("replayed"),
            "equality_exhaustion": equality.get("exhaustion"),
            "target_grounded_found": target_grounded.get("found"),
            "equality_error": equality.get("error"),
            "target_error": target_grounded.get("error"),
        }, sort_keys=True), flush=True)

    output["equality_found_count"] = sum(
        bool(row["equality_search"].get("found")) for row in output["edges"]
    )
    output["equality_replayed_count"] = sum(
        bool(row["equality_search"].get("replayed")) for row in output["edges"]
    )
    output["target_grounded_count"] = sum(
        bool(row["target_grounded"].get("found")) for row in output["edges"]
    )
    output["equality_gaps"] = [
        [row["source_id"], row["target_id"]]
        for row in output["edges"] if not row["equality_search"].get("replayed")
    ]
    output["target_grounded_gaps"] = [
        [row["source_id"], row["target_id"]]
        for row in output["edges"] if not row["target_grounded"].get("found")
    ]

    path = Path("experiments/mathgraph/results/18-edge-constructor-separator.json")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("SUMMARY", json.dumps({
        "equality_found": output["equality_found_count"],
        "equality_replayed": output["equality_replayed_count"],
        "equality_gaps": output["equality_gaps"],
        "target_grounded": output["target_grounded_count"],
        "target_gaps": output["target_grounded_gaps"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
