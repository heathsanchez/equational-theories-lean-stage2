#!/usr/bin/env python3
"""Inject fiber-law genesis followed by target-grounded given-clause attachment.

The source-derived fiber laws are the same two-instance replayable theorems as
in the one-step fiber experiment.  The only change is attachment: certified
laws enter the target-grounded active/passive scheduler before target search.
"""

import argparse
from pathlib import Path

MARKER = "    try:\n        # World A: streaming frontier.\n"

PORTAL = r'''    # Build explicit dependency-erasure laws from two source instances, then
    # attach them through the target-grounded active/passive scheduler.
    def build_fiber_attachment_laws(search):
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

        base_mapping = {}
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

        for anchor_index, _, anchor_vars, rich_vars in orientations:
            for erased in sorted(rich_vars - anchor_vars):
                first = dict(base_mapping)
                used = {v[1] for v in first.values() if v[0] == "var"}
                spare = next((v for v in target_vars if v not in used), None)
                if spare is None:
                    spare = next(
                        (v for v in target_vars if v != first[erased][1]), None
                    )
                if spare is None or spare == first[erased][1]:
                    continue
                second = dict(first)
                second[erased] = ("var", spare)
                a = source_recipe(first)
                b = source_recipe(second)
                if anchor_index == 0:
                    a_rev = Recipe(a.rhs, a.lhs, "symmetry", (a,))
                    law = Recipe(a_rev.lhs, b.rhs, "transitivity", (a_rev, b))
                else:
                    b_rev = Recipe(b.rhs, b.lhs, "symmetry", (b,))
                    law = Recipe(a.lhs, b_rev.rhs, "transitivity", (a, b_rev))
                nodes, root = search.compile(law)
                replay_ok = replay_dag(
                    source, nodes, root,
                    maximum_term_size=300, maximum_nodes=60000,
                )
                diagnostics.append({
                    "erased": erased,
                    "lhs": render_term(law.lhs),
                    "rhs": render_term(law.rhs),
                    "proof_nodes": len(nodes),
                    "replay": bool(replay_ok),
                })
                if replay_ok:
                    laws.append(law)
        return laws, diagnostics

    attach_engine, attach_search, _, _ = setup(90.0)
    attach_laws, attach_trace = build_fiber_attachment_laws(attach_search)
    attach_added = 0
    for law in attach_laws:
        if attach_search.add_clause(law):
            attach_added += 1

    attach_recipe = None
    if attach_added and "_mg_given_clause_recipe" in globals():
        attach_recipe = _mg_given_clause_recipe(
            attach_search, maximum_given=320, focus_per_age=4
        )
    attach_info = {
        "derived": len(attach_laws),
        "added": attach_added,
        "laws": attach_trace,
        "found": attach_recipe is not None,
        "clauses": len(attach_search.clauses),
        "rounds": attach_search.rounds,
        "superpositions": attach_search.superpositions,
        "replay_judge": False,
    }
    if attach_recipe is not None:
        accepted = finish(attach_engine, attach_search, attach_recipe)
        attach_info["replay_judge"] = bool(accepted)
        open('/tmp/mathgraph_fiber_attach_trace.json', 'w').write(
            json.dumps(attach_info, sort_keys=True)
        )
        if accepted:
            return True
    open('/tmp/mathgraph_fiber_attach_trace.json', 'w').write(
        json.dumps(attach_info, sort_keys=True)
    )
    return False

'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("solver")
    args = ap.parse_args()
    p = Path(args.solver)
    s = p.read_text()
    if s.count(MARKER) != 1:
        raise SystemExit(f"expected one portal marker, found {s.count(MARKER)}")
    s = s.replace(MARKER, PORTAL + MARKER, 1)
    compile(s, str(p), "exec")
    p.write_text(s)
    print(f"injected fiber given-clause attachment portal into {p}")


if __name__ == "__main__":
    main()
