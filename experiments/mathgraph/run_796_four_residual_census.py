#!/usr/bin/env python3
import argparse
import importlib.util
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER_PATH = ROOT / "submissions" / "mathgraph" / "solver.py"

CASES = (
    "evaluation_normal_0036",
    "evaluation_normal_0040",
    "evaluation_order5_0014",
    "evaluation_order5_0042",
)


def load_solver_module():
    spec = importlib.util.spec_from_file_location("mathgraph_796_census_solver", SOLVER_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_rows(paths):
    rows = {}
    for path in paths:
        for raw in Path(path).read_text().splitlines():
            if raw.strip():
                row = json.loads(raw)
                rows[row["id"]] = row
    return rows


def direct_matches(m, source, target):
    target_subterms = set(m.walk_subterms(target[0])) | set(m.walk_subterms(target[1]))
    hits = 0
    for side in source[:2]:
        for term in target_subterms:
            sub = {}
            if m.match_term(side, term, sub) and all(v in sub for v in source[2]):
                hits += 1
    return hits


def min_distance(m, terms, target_term):
    if not terms:
        return None
    return min(m.structural_distance(term, target_term) for term in terms)


def census_case(m, row, seconds):
    source = m.parse_equation(row["equation1"])
    target = m.parse_equation(row["equation2"])
    deadline = time.monotonic() + seconds
    search = m.EqualitySearch(source, target, deadline)
    pool = search.make_pool()
    search.initial_pool = tuple(pool)
    search.instantiate_sources(pool)

    after_sources_nodes = len(search.nodes)
    after_sources_edges = search.graph_edges
    source_instances = dict(search.source_instances_by_generation)
    source_root = search.shortest_path()

    siblings = pool[:10]
    first = 0
    congruence_rounds = []
    if source_root is None:
        for round_index in range(search.max_congruence_rounds):
            before_nodes = len(search.nodes)
            before_edges = search.graph_edges
            search.add_congruence_round(siblings, first)
            root = search.shortest_path()
            congruence_rounds.append({
                "round": round_index + 1,
                "nodes_added": len(search.nodes) - before_nodes,
                "edges_added": search.graph_edges - before_edges,
                "solved": root is not None,
            })
            first = before_nodes
            if root is not None or search.expired() or len(search.nodes) == before_nodes:
                break

    terms = set(search.adjacency)
    for neighbors in search.adjacency.values():
        terms.update(n for n, _, _ in neighbors)
    target_subterms = set(m.walk_subterms(target[0])) | set(m.walk_subterms(target[1]))
    missing_target_terms = sorted(
        (m.render_term(t) for t in target_subterms if t not in terms)
    )
    components = search.components()
    left_component = components.get(target[0])
    right_component = components.get(target[1])
    connected = (
        left_component is not None
        and right_component is not None
        and left_component == right_component
    )

    # Diagnostic-only: score the existing retained bank for reentry usefulness.
    # collect_reentry_terms does not add graph edges or proof nodes.
    reentry = search.collect_reentry_terms(1, 64, targeted=False)
    targeted_reentry_search = m.EqualitySearch(source, target, time.monotonic() + max(0.25, seconds / 4))
    targeted_pool = targeted_reentry_search.make_pool()
    targeted_reentry_search.initial_pool = tuple(targeted_pool)
    targeted_reentry_search.instantiate_sources(targeted_pool)
    targeted_reentry = targeted_reentry_search.collect_reentry_terms(1, 64, targeted=True)

    return {
        "id": row["id"],
        "source_variables": len(source[2]),
        "target_variables": len(target[2]),
        "source_term_sizes": [m.term_size(source[0]), m.term_size(source[1])],
        "target_term_sizes": [m.term_size(target[0]), m.term_size(target[1])],
        "pool_terms": len(pool),
        "direct_source_target_matches": direct_matches(m, source, target),
        "after_sources_nodes": after_sources_nodes,
        "after_sources_edges": after_sources_edges,
        "source_instances_by_generation": source_instances,
        "congruence_rounds": congruence_rounds,
        "final_nodes": len(search.nodes),
        "final_edges": search.graph_edges,
        "exhaustion": search.exhaustion,
        "target_terms_total": len(target_subterms),
        "missing_target_terms": missing_target_terms,
        "target_endpoints_present": [target[0] in terms, target[1] in terms],
        "target_endpoints_connected": connected,
        "best_distance_to_target_left": min_distance(m, terms, target[0]),
        "best_distance_to_target_right": min_distance(m, terms, target[1]),
        "components": len(set(components.values())),
        "reentry_candidates_64": len(reentry),
        "targeted_reentry_candidates_64": len(targeted_reentry),
        "sample_reentry": [m.render_term(term) for term, _ in reentry[:8]],
        "sample_targeted_reentry": [m.render_term(term) for term, _ in targeted_reentry[:8]],
    }


def phenotype(row):
    if row["missing_target_terms"]:
        return "REPRESENTATION_VISIBILITY_GAP"
    if not row["target_endpoints_connected"] and row["final_edges"] >= 0.9 * 4000:
        return "CLOSURE_OR_COMPOSITION_GAP"
    if not row["target_endpoints_connected"] and row["targeted_reentry_candidates_64"] > 0:
        return "CONTINUATION_OR_REENTRY_CANDIDATE"
    if not row["target_endpoints_connected"]:
        return "CONSTRUCTOR_GAP"
    return "CONNECTED_BUT_NO_CERTIFICATE"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--normal", required=True)
    ap.add_argument("--order5", required=True)
    ap.add_argument("--seconds", type=float, default=6.0)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()

    rows = load_rows((args.normal, args.order5))
    missing = [rid for rid in CASES if rid not in rows]
    if missing:
        raise SystemExit(f"missing rows: {missing}")

    m = load_solver_module()
    results = []
    for rid in CASES:
        row = census_case(m, rows[rid], args.seconds)
        row["phenotype"] = phenotype(row)
        results.append(row)
        print("FOUR_RESIDUAL_CENSUS", json.dumps(row, sort_keys=True), flush=True)

    out = {
        "schema": "mathgraph.796-four-residual-census.v1",
        "diagnostic_only": True,
        "solver_behavior_changed": False,
        "results": results,
    }
    path = Path(args.output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
