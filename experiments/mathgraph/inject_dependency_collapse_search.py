#!/usr/bin/env python3
"""Inject a problem-blind dependency-collapse discovery portal.

The portal runs a bounded source-only superposition phase whose selection
objective is not target proximity.  It rewards consequences that strictly
reduce variable dependence, especially universal bare-variable omission laws
v = T where v does not occur in T.  Only replayable source consequences are
promoted into a fresh target-directed proof world.
"""

import argparse
from pathlib import Path

MARKER = "    try:\n        # World A: streaming frontier.\n"

PORTAL = r'''    # Search for source consequences that compress variable dependence rather
    # than for clauses that merely resemble the current target.
    def dependency_score(recipe):
        left_vars = term_variables(recipe.lhs)
        right_vars = term_variables(recipe.rhs)
        bare_omit = (
            recipe.lhs[0] == "var" and recipe.lhs[1] not in right_vars
        ) or (
            recipe.rhs[0] == "var" and recipe.rhs[1] not in left_vars
        )
        strict_drop = left_vars < right_vars or right_vars < left_vars
        drop = abs(len(left_vars) - len(right_vars))
        return (
            0 if bare_omit else 1 if strict_drop else 2,
            -drop,
            min(len(left_vars), len(right_vars)),
            len(left_vars | right_vars),
            term_size(recipe.lhs) + term_size(recipe.rhs),
            recipe.cost,
            render_term(recipe.lhs),
            render_term(recipe.rhs),
        )

    def is_dependency_repair(recipe):
        left_vars = term_variables(recipe.lhs)
        right_vars = term_variables(recipe.rhs)
        bare_omit = (
            recipe.lhs[0] == "var" and recipe.lhs[1] not in right_vars
        ) or (
            recipe.rhs[0] == "var" and recipe.rhs[1] not in left_vars
        )
        strict_drop = left_vars < right_vars or right_vars < left_vars
        return bare_omit, strict_drop

    dep_engine, dep, _, _ = setup(90.0)
    initial_signatures = set(dep.signatures)
    dep_trace = []
    certified = []
    certified_keys = set()
    enumerated = 0
    for dep_round in range(5):
        rules = dep.rules()
        proposals = []
        for outer_index, outer in enumerate(rules):
            for inner_index, inner in enumerate(rules):
                for path in nonvariable_positions(
                    outer.lhs, maximum_depth=10, include_root=True
                ):
                    if dep.expired():
                        break
                    candidate = dep.critical_pair(
                        outer, inner, outer_index, inner_index, path
                    )
                    if candidate is None:
                        continue
                    candidate = dep.interreduce(candidate, rules)
                    enumerated += 1
                    proposals.append((dependency_score(candidate), candidate))
                if dep.expired():
                    break
            if dep.expired():
                break
        proposals.sort(key=lambda item: item[0])
        added = 0
        for score, candidate in proposals:
            signature = dep.alpha_signature(candidate.lhs, candidate.rhs)
            reverse = dep.alpha_signature(candidate.rhs, candidate.lhs)
            was_initial = signature in initial_signatures or reverse in initial_signatures
            if dep.add_clause(candidate):
                dep.superpositions += 1
                added += 1
                bare_omit, strict_drop = is_dependency_repair(candidate)
                if (bare_omit or strict_drop) and not was_initial:
                    nodes, root = dep.compile(candidate)
                    replay_ok = replay_dag(
                        source, nodes, root,
                        maximum_term_size=300, maximum_nodes=60000,
                    )
                    dep_trace.append({
                        "round": dep_round + 1,
                        "bare_omit": bare_omit,
                        "strict_drop": strict_drop,
                        "lhs": render_term(candidate.lhs),
                        "rhs": render_term(candidate.rhs),
                        "left_vars": sorted(term_variables(candidate.lhs)),
                        "right_vars": sorted(term_variables(candidate.rhs)),
                        "size": term_size(candidate.lhs) + term_size(candidate.rhs),
                        "cost": candidate.cost,
                        "replay": bool(replay_ok),
                    })
                    key = (signature, candidate.lhs, candidate.rhs)
                    if replay_ok and key not in certified_keys:
                        certified_keys.add(key)
                        certified.append(candidate)
                if added >= 64:
                    break
        if any(is_dependency_repair(q)[0] for q in certified):
            break
        if not added or dep.expired():
            break

    # Prefer the strongest information loss, then the shortest replayable law.
    certified.sort(key=dependency_score)
    selected = certified[:16]
    warm_engine, warm, _, _ = setup(90.0)
    warm_added = 0
    for law in selected:
        if warm.add_clause(law):
            warm_added += 1
    warm_found = warm.solve() if warm_added else None
    dep_info = {
        "enumerated": enumerated,
        "generated": len(dep.clauses),
        "candidates": dep_trace[:32],
        "certified": len(certified),
        "selected": len(selected),
        "warm_added": warm_added,
        "found": warm_found is not None,
        "rounds": warm.rounds,
        "superpositions": warm.superpositions,
        "clauses": len(warm.clauses),
        "replay_judge": False,
    }
    if warm_found is not None:
        accepted = finish(warm_engine, warm, warm_found)
        dep_info["replay_judge"] = bool(accepted)
        open('/tmp/mathgraph_dependency_trace.json', 'w').write(
            json.dumps(dep_info, sort_keys=True)
        )
        if accepted:
            return True
    open('/tmp/mathgraph_dependency_trace.json', 'w').write(
        json.dumps(dep_info, sort_keys=True)
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
    print(f"injected dependency-collapse search into {path}")


if __name__ == "__main__":
    main()
