#!/usr/bin/env python3
"""Inject a problem-blind two-focus fiber representation portal.

The current dependency ratchet can discover replay-certified laws of the form
x = F(x,y), but then plateaus because ordinary critical-pair search represents
one overlap at a time.  This portal changes the representation: it keeps two
independent instantiations of such a law related through their shared anchor,
and also relates distinct equally minimal reducers through that anchor.

Every generated fiber is an explicit Recipe built from replay-certified source
consequences, replayed again from the original source before promotion.  No
problem IDs, proof IDs, benchmark labels, or target-specific bridge equations
are stored in the mechanism.
"""

import argparse
from pathlib import Path

MARKER = "    try:\n        # World A: streaming frontier.\n"

PORTAL = r'''    # Two-focus fiber portal: represent the relation between two
    # independently varied surviving arguments rather than flattening either
    # focus into a single ordinary critical-pair state.
    def tf_profile(recipe):
        left_vars = term_variables(recipe.lhs)
        right_vars = term_variables(recipe.rhs)
        for variable_side, other_side in (
            (recipe.lhs, recipe.rhs), (recipe.rhs, recipe.lhs)
        ):
            if variable_side[0] == "var":
                distinguished = variable_side[1]
                other_vars = term_variables(other_side)
                if distinguished not in other_vars:
                    return (0, 0, len(other_vars))
                return (1, len(other_vars - {distinguished}), len(other_vars))
        if left_vars < right_vars:
            return (2, len(right_vars - left_vars), len(right_vars))
        if right_vars < left_vars:
            return (2, len(left_vars - right_vars), len(left_vars))
        return (3, len(left_vars | right_vars), len(left_vars | right_vars))

    def tf_informative(recipe):
        return (
            recipe.lhs != recipe.rhs
            and render_term(recipe.lhs) != render_term(recipe.rhs)
            and not any(
                name.startswith("@")
                for name in term_variables(recipe.lhs) | term_variables(recipe.rhs)
            )
        )

    def tf_rank(recipe):
        return tf_profile(recipe) + (
            term_size(recipe.lhs) + term_size(recipe.rhs),
            recipe.cost,
            render_term(recipe.lhs), render_term(recipe.rhs),
        )

    def tf_snapshot(recipe):
        return {
            "lhs": render_term(recipe.lhs),
            "rhs": render_term(recipe.rhs),
            "profile": list(tf_profile(recipe)),
            "support": sorted(term_variables(recipe.lhs) | term_variables(recipe.rhs)),
            "size": term_size(recipe.lhs) + term_size(recipe.rhs),
            "cost": recipe.cost,
        }

    def tf_replay(search, recipe):
        nodes, root = search.compile(recipe)
        return replay_dag(
            source, nodes, root,
            maximum_term_size=300, maximum_nodes=60000,
        ), len(nodes)

    def tf_discover_reducers(search, expand_recipe):
        source_profile = tf_profile(Recipe(source[0], source[1], "reflexivity"))
        proposals = []
        seen = set()
        enumerated = 0
        rejected = 0
        rules = search.rules()
        snapshot = list(rules)
        for outer_index, outer in enumerate(snapshot):
            for inner_index, inner in enumerate(snapshot):
                for path in nonvariable_positions(
                    outer.lhs, maximum_depth=12, include_root=True
                ):
                    if search.expired():
                        break
                    candidate = search.critical_pair(
                        outer, inner, outer_index, inner_index, path
                    )
                    if candidate is None:
                        continue
                    candidate = search.interreduce(candidate, rules)
                    candidate = expand_recipe(candidate)
                    enumerated += 1
                    if not tf_informative(candidate):
                        rejected += 1
                        continue
                    if not tf_profile(candidate) < source_profile:
                        continue
                    key = (
                        search.alpha_signature(candidate.lhs, candidate.rhs),
                        candidate.lhs, candidate.rhs,
                    )
                    if key in seen:
                        continue
                    seen.add(key)
                    proposals.append((tf_rank(candidate), candidate))
                if search.expired():
                    break
            if search.expired():
                break
        proposals.sort(key=lambda item: item[0])
        certified = []
        diagnostics = []
        for _, candidate in proposals[:96]:
            replay_ok, proof_nodes = tf_replay(search, candidate)
            diagnostics.append({
                **tf_snapshot(candidate),
                "replay": bool(replay_ok),
                "proof_nodes": proof_nodes,
            })
            if replay_ok:
                certified.append(candidate)
        if not certified:
            return [], diagnostics, enumerated, rejected
        best = tf_profile(certified[0])
        return [q for q in certified if tf_profile(q) == best][:8], diagnostics, enumerated, rejected

    def tf_variable_form(recipe):
        if recipe.lhs[0] == "var":
            anchor = recipe.lhs[1]
            body = recipe.rhs
            return "left", anchor, body
        if recipe.rhs[0] == "var":
            anchor = recipe.rhs[1]
            body = recipe.lhs
            return "right", anchor, body
        return None

    def tf_instantiate(recipe, mapping):
        data = tuple((name, mapping[name]) for name in sorted(mapping))
        return Recipe(
            substitute(recipe.lhs, mapping),
            substitute(recipe.rhs, mapping),
            "instantiate", (recipe,), data,
        )

    def tf_compose_shared_anchor(first, second):
        # Both instances are either anchor = body or body = anchor.  Compose
        # through the common anchor to retain the relation between both bodies.
        f = tf_variable_form(first)
        s = tf_variable_form(second)
        if f is None or s is None:
            return None
        if f[0] == "left" and s[0] == "left":
            rev = Recipe(first.rhs, first.lhs, "symmetry", (first,))
            return Recipe(rev.lhs, second.rhs, "transitivity", (rev, second))
        if f[0] == "right" and s[0] == "right":
            rev = Recipe(second.rhs, second.lhs, "symmetry", (second,))
            return Recipe(first.lhs, rev.rhs, "transitivity", (first, rev))
        return None

    def tf_instantiation_pair(recipe, parameter_a, parameter_b, anchor_name):
        form = tf_variable_form(recipe)
        if form is None:
            return None
        _, anchor, body = form
        parameters = sorted(term_variables(body) - {anchor})
        all_vars = sorted(term_variables(recipe.lhs) | term_variables(recipe.rhs))
        if len(parameters) != 1:
            return None
        parameter = parameters[0]
        base = {name: ("var", anchor_name) for name in all_vars}
        base[anchor] = ("var", anchor_name)
        first_map = dict(base); first_map[parameter] = ("var", parameter_a)
        second_map = dict(base); second_map[parameter] = ("var", parameter_b)
        return tf_instantiate(recipe, first_map), tf_instantiate(recipe, second_map)

    tf_engine, tf_search, _, tf_expand = setup(75.0)
    tf_reducers, tf_reducer_trace, tf_enumerated, tf_rejected = tf_discover_reducers(
        tf_search, tf_expand
    )
    tf_target_vars = list(target[2])
    tf_fibers = []
    tf_fiber_trace = []

    # Need three in-scope names: shared anchor plus two independently varied
    # focus variables.  This is a representation requirement, not a row test.
    if len(tf_target_vars) >= 3:
        anchor_name = tf_target_vars[0]
        parameter_a = tf_target_vars[1]
        parameter_b = tf_target_vars[2]

        # Self-fibers: F(x,a) = F(x,b) for each independently discovered law.
        instances = []
        for reducer_index, reducer in enumerate(tf_reducers):
            pair = tf_instantiation_pair(
                reducer, parameter_a, parameter_b, anchor_name
            )
            if pair is None:
                continue
            a, b = pair
            instances.append((reducer_index, a, b))
            fiber = tf_compose_shared_anchor(a, b)
            if fiber is None or not tf_informative(fiber):
                continue
            replay_ok, proof_nodes = tf_replay(tf_search, fiber)
            tf_fiber_trace.append({
                "kind": "self-fiber",
                "parents": [reducer_index, reducer_index],
                **tf_snapshot(fiber),
                "replay": bool(replay_ok),
                "proof_nodes": proof_nodes,
            })
            if replay_ok:
                tf_fibers.append(fiber)

        # Cross-fibers: preserve relations between distinct equally minimal
        # repairs instead of arbitrarily selecting one member of the version
        # space.  Test both parameter alignments.
        for i in range(len(instances)):
            for j in range(i + 1, len(instances)):
                ri, ia, ib = instances[i]
                rj, ja, jb = instances[j]
                for left, right, label in (
                    (ia, ja, "cross-same-a"),
                    (ib, jb, "cross-same-b"),
                    (ia, jb, "cross-two-focus"),
                    (ib, ja, "cross-two-focus-reverse"),
                ):
                    fiber = tf_compose_shared_anchor(left, right)
                    if fiber is None or not tf_informative(fiber):
                        continue
                    replay_ok, proof_nodes = tf_replay(tf_search, fiber)
                    tf_fiber_trace.append({
                        "kind": label,
                        "parents": [ri, rj],
                        **tf_snapshot(fiber),
                        "replay": bool(replay_ok),
                        "proof_nodes": proof_nodes,
                    })
                    if replay_ok:
                        tf_fibers.append(fiber)

    # Canonicalize before promotion; only replay-certified source consequences
    # enter the new representation.
    tf_unique = []
    tf_seen = set()
    for law in sorted(tf_fibers, key=tf_rank):
        key = (
            tf_search.alpha_signature(law.lhs, law.rhs),
            law.lhs, law.rhs,
        )
        if key in tf_seen:
            continue
        tf_seen.add(key)
        tf_unique.append(law)

    warm_engine, warm, _, _ = setup(120.0)
    reducer_added = 0
    fiber_added = 0
    for law in tf_reducers:
        if warm.add_clause(law):
            reducer_added += 1
    for law in tf_unique[:16]:
        if warm.add_clause(law):
            fiber_added += 1

    warm_found = None
    if reducer_added or fiber_added:
        collapse = warm.collapse_proof()
        warm_found = collapse if collapse is not None else warm.target_proof(warm.rules())
        if warm_found is None:
            warm_found = warm.solve()

    tf_info = {
        "reducers": len(tf_reducers),
        "reducer_enumerated": tf_enumerated,
        "reducer_rejected": tf_rejected,
        "reducer_trace": tf_reducer_trace[:16],
        "fibers_replayed": sum(1 for x in tf_fiber_trace if x["replay"]),
        "fibers_unique": len(tf_unique),
        "fiber_trace": tf_fiber_trace[:24],
        "reducer_added": reducer_added,
        "fiber_added": fiber_added,
        "clauses": len(warm.clauses),
        "rounds": warm.rounds,
        "superpositions": warm.superpositions,
        "found": warm_found is not None,
        "replay_judge": False,
    }
    if warm_found is not None:
        accepted = finish(warm_engine, warm, warm_found)
        tf_info["replay_judge"] = bool(accepted)
        open('/tmp/mathgraph_two_focus_trace.json', 'w').write(
            json.dumps(tf_info, sort_keys=True)
        )
        if accepted:
            return True
    open('/tmp/mathgraph_two_focus_trace.json', 'w').write(
        json.dumps(tf_info, sort_keys=True)
    )
    return False

'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("solver")
    args = parser.parse_args()
    path = Path(args.solver)
    text = path.read_text()
    if text.count(MARKER) != 1:
        raise SystemExit(f"expected one portal marker, found {text.count(MARKER)}")
    patched = text.replace(MARKER, PORTAL + MARKER, 1)
    compile(patched, str(path), "exec")
    path.write_text(patched)
    print(f"injected two-focus fiber portal into {path}")


if __name__ == "__main__":
    main()
