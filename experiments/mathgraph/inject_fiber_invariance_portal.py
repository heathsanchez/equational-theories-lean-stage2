#!/usr/bin/env python3
"""Inject a problem-blind source-fiber invariance portal.

If one side of the source law depends on fewer variables than the other, then
varying an extra variable on the richer side while holding the anchor side
fixed yields a new universal equality between two fibers.  The portal builds
that equality from two source instances, independently replays it, promotes it
as a new law, and restarts target-directed superposition.
"""

import argparse
from pathlib import Path

MARKER = "    try:\n        # World A: streaming frontier.\n"

PORTAL = r'''    # Source-fiber invariance: turn variables that disappear across the source
    # equality into explicit, replayable dependency-erasure laws.
    def build_fiber_laws(search):
        left_vars = term_variables(source[0])
        right_vars = term_variables(source[1])
        orientations = []
        if left_vars < right_vars:
            orientations.append((0, 1, left_vars, right_vars))
        if right_vars < left_vars:
            orientations.append((1, 0, right_vars, left_vars))
        target_vars = list(target[2])
        source_vars = list(source[2])
        laws = []
        diagnostics = []
        if not orientations or not target_vars:
            return laws, diagnostics

        # Preserve source variable names where the target binds them; otherwise
        # assign deterministic target variables.  We only form a fiber law if a
        # genuinely distinct in-scope variable is available for the variation.
        base_mapping = {}
        unused = [v for v in target_vars if v not in source_vars]
        fallback_index = 0
        for variable in source_vars:
            if variable in target_vars:
                base_mapping[variable] = ("var", variable)
            else:
                base_mapping[variable] = (
                    "var", target_vars[fallback_index % len(target_vars)]
                )
                fallback_index += 1

        def source_recipe(mapping):
            return Recipe(
                substitute(source[0], mapping),
                substitute(source[1], mapping),
                "source",
                data=(
                    tuple((v, mapping[v]) for v in source[2]),
                    False,
                ),
            )

        for anchor_index, rich_index, anchor_vars, rich_vars in orientations:
            for erased in sorted(rich_vars - anchor_vars):
                first = dict(base_mapping)
                used_names = {
                    term[1] for term in first.values() if term[0] == "var"
                }
                spare = next(
                    (v for v in target_vars if v not in used_names), None
                )
                if spare is None:
                    spare = next(
                        (v for v in target_vars if v != first[erased][1]),
                        None,
                    )
                if spare is None or spare == first[erased][1]:
                    continue
                second = dict(first)
                second[erased] = ("var", spare)
                a = source_recipe(first)
                b = source_recipe(second)
                if anchor_index == 0:
                    # anchor = rich₁ and anchor = rich₂  ==>  rich₁ = rich₂
                    a_rev = Recipe(a.rhs, a.lhs, "symmetry", (a,))
                    law = Recipe(
                        a_rev.lhs, b.rhs, "transitivity", (a_rev, b)
                    )
                else:
                    # rich₁ = anchor and rich₂ = anchor  ==>  rich₁ = rich₂
                    b_rev = Recipe(b.rhs, b.lhs, "symmetry", (b,))
                    law = Recipe(
                        a.lhs, b_rev.rhs, "transitivity", (a, b_rev)
                    )
                nodes, root = search.compile(law)
                replay_ok = replay_dag(
                    source, nodes, root,
                    maximum_term_size=300, maximum_nodes=60000,
                )
                diagnostics.append({
                    "erased": erased,
                    "anchor_side": "left" if anchor_index == 0 else "right",
                    "lhs": render_term(law.lhs),
                    "rhs": render_term(law.rhs),
                    "proof_nodes": len(nodes),
                    "replay": bool(replay_ok),
                })
                if replay_ok:
                    laws.append(law)
        return laws, diagnostics

    fiber_engine, fiber_search, _, _ = setup(90.0)
    fiber_laws, fiber_trace = build_fiber_laws(fiber_search)
    fiber_added = 0
    for law in fiber_laws:
        if fiber_search.add_clause(law):
            fiber_added += 1
    fiber_found = fiber_search.solve() if fiber_added else None
    fiber_info = {
        "derived": len(fiber_laws),
        "added": fiber_added,
        "laws": fiber_trace,
        "found": fiber_found is not None,
        "rounds": fiber_search.rounds,
        "superpositions": fiber_search.superpositions,
        "clauses": len(fiber_search.clauses),
        "replay_judge": False,
    }
    if fiber_found is not None:
        accepted = finish(fiber_engine, fiber_search, fiber_found)
        fiber_info["replay_judge"] = bool(accepted)
        open('/tmp/mathgraph_fiber_trace.json', 'w').write(
            json.dumps(fiber_info, sort_keys=True)
        )
        if accepted:
            return True
    open('/tmp/mathgraph_fiber_trace.json', 'w').write(
        json.dumps(fiber_info, sort_keys=True)
    )
    return False

'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("solver")
    args = parser.parse_args()
    path = Path(args.solver)
    source = path.read_text()
    if source.count(MARKER) != 1:
        raise SystemExit(f"expected one portal marker, found {source.count(MARKER)}")
    patched = source.replace(MARKER, PORTAL + MARKER, 1)
    compile(patched, str(path), "exec")
    path.write_text(patched)
    print(f"injected source-fiber invariance portal into {path}")


if __name__ == "__main__":
    main()
