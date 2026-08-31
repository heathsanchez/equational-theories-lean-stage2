#!/usr/bin/env python3
"""Inject a problem-blind two-site target attachment portal.

A strict dependency reducer x = F(x,y) can be valid yet fail to help if search
requires every single attachment to improve immediately. This portal keeps a
pair of non-overlapping attachments as one state. It then asks a minimal causal
question: does the pair expose a direct, size-decreasing instance of the
original source law that neither attachment had to expose alone?

All reducers are discovered and replay-certified from the incoming source.
Every target-context attachment is represented by instantiate/congruence
Recipes, and every source activation is an explicit source Recipe. Any final
candidate is replayed by the existing kernel before judge access.
"""

import argparse
from pathlib import Path

MARKER = "    try:\n        # World A: streaming frontier.\n"

PORTAL = r'''    # Two-site attachment portal: the pair, not either intermediate
    # one-site state, is the unit judged for usefulness.
    def ta_profile(recipe):
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

    def ta_informative(recipe):
        return (
            recipe.lhs != recipe.rhs
            and render_term(recipe.lhs) != render_term(recipe.rhs)
            and not any(
                name.startswith("@")
                for name in term_variables(recipe.lhs) | term_variables(recipe.rhs)
            )
        )

    def ta_rank(recipe):
        return ta_profile(recipe) + (
            term_size(recipe.lhs) + term_size(recipe.rhs),
            recipe.cost, render_term(recipe.lhs), render_term(recipe.rhs),
        )

    def ta_replay(search, recipe):
        nodes, root = search.compile(recipe)
        return replay_dag(
            source, nodes, root,
            maximum_term_size=300, maximum_nodes=60000,
        )

    def ta_discover_reducers(search, expand_recipe):
        source_profile = ta_profile(Recipe(source[0], source[1], "reflexivity"))
        seen = set(); proposals = []
        rules = search.rules(); snapshot = list(rules)
        enumerated = 0; rejected = 0
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
                    candidate = expand_recipe(search.interreduce(candidate, rules))
                    enumerated += 1
                    if not ta_informative(candidate):
                        rejected += 1
                        continue
                    if not ta_profile(candidate) < source_profile:
                        continue
                    key = (
                        search.alpha_signature(candidate.lhs, candidate.rhs),
                        candidate.lhs, candidate.rhs,
                    )
                    if key in seen:
                        continue
                    seen.add(key); proposals.append((ta_rank(candidate), candidate))
                if search.expired():
                    break
            if search.expired():
                break
        proposals.sort(key=lambda item: item[0])
        certified = []
        for _, candidate in proposals[:96]:
            if ta_replay(search, candidate):
                certified.append(candidate)
        if not certified:
            return [], enumerated, rejected
        best = ta_profile(certified[0])
        return [q for q in certified if ta_profile(q) == best][:8], enumerated, rejected

    def ta_variable_form(recipe):
        if recipe.lhs[0] == "var":
            return recipe, recipe.lhs[1], recipe.rhs
        if recipe.rhs[0] == "var":
            oriented = Recipe(recipe.rhs, recipe.lhs, "symmetry", (recipe,))
            return oriented, recipe.rhs[1], recipe.lhs
        return None

    def ta_paths(term):
        out = []
        def visit(node, path):
            out.append(path)
            if node[0] == "op":
                visit(node[1], path + ("L",))
                visit(node[2], path + ("R",))
        visit(term, ())
        return out

    def ta_nonoverlap(first, second):
        if first == second:
            return False
        return not (
            first[:len(second)] == second
            or second[:len(first)] == first
        )

    def ta_vocab():
        values = []
        for variable in target[2]:
            term = ("var", variable)
            if term not in values:
                values.append(term)
        for side in target[:2]:
            for term in walk_subterms(side):
                if term_size(term) <= 5 and term not in values:
                    values.append(term)
        values.sort(key=lambda t: (term_size(t), render_term(t)))
        return values[:10]

    def ta_expand_at(search, reducer, root, path, parameter_value):
        form = ta_variable_form(reducer)
        if form is None:
            return None
        oriented, anchor, body = form
        parameters = sorted(term_variables(body) - {anchor})
        if len(parameters) != 1:
            return None
        selected = get_subterm(root, path)
        mapping = {anchor: selected, parameters[0]: parameter_value}
        proof = search.instantiate(oriented, mapping)
        if proof.lhs != selected or proof.rhs == selected:
            return None
        if term_size(proof.rhs) > 65:
            return None
        lifted = search.lift(proof, root, path)
        if term_size(lifted.rhs) > 65:
            return None
        return lifted.rhs, lifted

    def ta_source_reductions(search, term):
        matches = []
        for path in ta_paths(term):
            selected = get_subterm(term, path)
            # Only the non-variable side can be a genuine decreasing source
            # activation. The variable side matches everything and is not an
            # information-gaining attachment signal.
            for source_side in (0, 1):
                pattern = source[source_side]
                other = source[1 - source_side]
                if pattern[0] == "var" or term_size(other) >= term_size(pattern):
                    continue
                mapping = {}
                if not match_term(pattern, selected, mapping):
                    continue
                if not all(variable in mapping for variable in source[2]):
                    continue
                replacement = substitute(other, mapping)
                if term_size(replacement) >= term_size(selected):
                    continue
                matches.append((
                    -len(path), term_size(replacement), tuple(path),
                    source_side, tuple((v, mapping[v]) for v in source[2]),
                    replacement,
                ))
        matches.sort()
        return matches

    def ta_apply_source_reduction(search, root, match):
        _, _, path, source_side, mapping_data, replacement = match
        mapping = dict(mapping_data)
        base_recipe = Recipe(
            substitute(source[0], mapping),
            substitute(source[1], mapping),
            "source", data=(mapping_data, source_side == 1),
        )
        if source_side == 1:
            # The source Recipe's orientation flag already denotes the reversed
            # source instance, so make the visible endpoints agree with it.
            base_recipe = Recipe(
                substitute(source[1], mapping),
                substitute(source[0], mapping),
                "source", data=(mapping_data, True),
            )
        selected = get_subterm(root, path)
        if base_recipe.lhs != selected or base_recipe.rhs != replacement:
            return None
        lifted = search.lift(base_recipe, root, path)
        return lifted.rhs, lifted

    def ta_reduce_activated(search, term, proof):
        current = term
        current_proof = proof
        steps = 0
        peak_matches = len(ta_source_reductions(search, current))
        while steps < 6:
            matches = ta_source_reductions(search, current)
            if not matches:
                break
            applied = ta_apply_source_reduction(search, current, matches[0])
            if applied is None:
                break
            after, segment = applied
            current_proof = Recipe(
                current_proof.lhs, segment.rhs,
                "transitivity", (current_proof, segment),
            )
            current = after
            steps += 1
            peak_matches = max(peak_matches, len(ta_source_reductions(search, current)))
        return current, current_proof, steps, peak_matches

    ta_engine, ta_search, _, ta_expand = setup(75.0)
    ta_reducers, ta_enumerated, ta_rejected = ta_discover_reducers(
        ta_search, ta_expand
    )
    vocab = ta_vocab()

    def ta_side_states(side):
        base_proof = Recipe(side, side, "reflexivity")
        states = [(side, base_proof, 0, 0, "zero")]
        singles = []
        paths = ta_paths(side)
        for path in paths:
            for reducer in ta_reducers:
                for parameter in vocab:
                    applied = ta_expand_at(
                        ta_search, reducer, side, path, parameter
                    )
                    if applied is None:
                        continue
                    term1, proof1 = applied
                    reduced, full, steps, peak = ta_reduce_activated(
                        ta_search, term1, proof1
                    )
                    singles.append((reduced, full, steps, peak, "single"))
        states.extend(singles)

        pair_states = []
        generated = 0
        for first_index, first_path in enumerate(paths):
            for second_path in paths[first_index + 1:]:
                if not ta_nonoverlap(first_path, second_path):
                    continue
                for first_reducer in ta_reducers:
                    for second_reducer in ta_reducers:
                        for first_parameter in vocab:
                            first = ta_expand_at(
                                ta_search, first_reducer, side,
                                first_path, first_parameter,
                            )
                            if first is None:
                                continue
                            term1, proof1 = first
                            for second_parameter in vocab:
                                second = ta_expand_at(
                                    ta_search, second_reducer, term1,
                                    second_path, second_parameter,
                                )
                                if second is None:
                                    continue
                                term2, proof2 = second
                                pair_proof = Recipe(
                                    proof1.lhs, proof2.rhs,
                                    "transitivity", (proof1, proof2),
                                )
                                reduced, full, steps, peak = ta_reduce_activated(
                                    ta_search, term2, pair_proof
                                )
                                pair_states.append((
                                    reduced, full, steps, peak, "pair"
                                ))
                                generated += 1
                                if generated >= 4096:
                                    break
                            if generated >= 4096:
                                break
                        if generated >= 4096:
                            break
                    if generated >= 4096:
                        break
                if generated >= 4096:
                    break
            if generated >= 4096:
                break
        states.extend(pair_states)

        best = {}
        for state in states:
            term, proof, steps, peak, kind = state
            score = (
                term_size(term),
                proof.cost,
                0 if kind == "pair" else 1,
                render_term(term),
            )
            previous = best.get(term)
            if previous is None or score < previous[0]:
                best[term] = (score, state)
        ordered = [entry[1] for entry in sorted(best.values(), key=lambda x: x[0])]
        return ordered[:1024], len(singles), len(pair_states)

    left_states, left_singles, left_pairs = ta_side_states(target[0])
    right_states, right_singles, right_pairs = ta_side_states(target[1])
    left_by_term = {state[0]: state for state in left_states}
    right_by_term = {state[0]: state for state in right_states}
    shared = sorted(
        set(left_by_term) & set(right_by_term),
        key=lambda term: (
            term_size(term),
            left_by_term[term][1].cost + right_by_term[term][1].cost,
            render_term(term),
        ),
    )

    ta_result = None
    winning = None
    for common in shared[:32]:
        left_state = left_by_term[common]
        right_state = right_by_term[common]
        left_proof = left_state[1]
        right_proof = right_state[1]
        reverse_right = Recipe(
            right_proof.rhs, right_proof.lhs,
            "symmetry", (right_proof,),
        )
        candidate = Recipe(
            left_proof.lhs, reverse_right.rhs,
            "transitivity", (left_proof, reverse_right),
        )
        if candidate.lhs != target[0] or candidate.rhs != target[1]:
            continue
        if not ta_replay(ta_search, candidate):
            continue
        ta_result = candidate
        winning = {
            "common": render_term(common),
            "left_kind": left_state[4],
            "right_kind": right_state[4],
            "left_source_steps": left_state[2],
            "right_source_steps": right_state[2],
            "left_peak_activations": left_state[3],
            "right_peak_activations": right_state[3],
            "cost": candidate.cost,
        }
        break

    ta_info = {
        "reducers": len(ta_reducers),
        "reducer_enumerated": ta_enumerated,
        "reducer_rejected": ta_rejected,
        "vocabulary": [render_term(x) for x in vocab],
        "left_singles": left_singles,
        "left_pairs": left_pairs,
        "right_singles": right_singles,
        "right_pairs": right_pairs,
        "left_states": len(left_states),
        "right_states": len(right_states),
        "shared_states": len(shared),
        "single_activation_max": max(
            [s[3] for s in left_states + right_states if s[4] == "single"] or [0]
        ),
        "pair_activation_max": max(
            [s[3] for s in left_states + right_states if s[4] == "pair"] or [0]
        ),
        "winning": winning,
        "found": ta_result is not None,
        "replay_judge": False,
    }
    if ta_result is not None:
        accepted = finish(ta_engine, ta_search, ta_result)
        ta_info["replay_judge"] = bool(accepted)
        open('/tmp/mathgraph_two_site_trace.json','w').write(
            json.dumps(ta_info, sort_keys=True)
        )
        if accepted:
            return True
    open('/tmp/mathgraph_two_site_trace.json','w').write(
        json.dumps(ta_info, sort_keys=True)
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
    print(f"injected two-site attachment portal into {path}")


if __name__ == "__main__":
    main()
