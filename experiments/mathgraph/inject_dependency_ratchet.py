#!/usr/bin/env python3
"""Inject a monotone verifier-certified dependency-development ratchet.

The ratchet is problem-blind.  It repeatedly discovers replayable source
consequences that strictly reduce variable dependence, preserves the minimal
residual-relative version space of equally strong reductions, promotes that
small cohort into a fresh proof world, and searches again.  Every promoted law
remains a Recipe derived from the original source.  A universal bare-variable
omission is terminal: CompactSuperposition.collapse_proof constructs the
original target from it and the usual replay + Lean judge boundary applies.
"""

import argparse
from pathlib import Path

MARKER = "    try:\n        # World A: streaming frontier.\n"

PORTAL = r'''    # Monotone developmental ratchet: one verifier-certified permission to
    # forget at a time, preserving equally minimal repairs until attachment
    # decides between them.
    def dependence_profile(recipe):
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
                extras = len(other_vars - {distinguished})
                return (1, extras, len(other_vars))
        if left_vars < right_vars:
            return (2, len(right_vars - left_vars), len(right_vars))
        if right_vars < left_vars:
            return (2, len(left_vars - right_vars), len(left_vars))
        return (3, len(left_vars | right_vars), len(left_vars | right_vars))

    def terminal_omission(recipe):
        for variable_side, other_side in (
            (recipe.lhs, recipe.rhs), (recipe.rhs, recipe.lhs)
        ):
            if (
                variable_side[0] == "var"
                and variable_side[1] not in term_variables(other_side)
            ):
                return True
        return False

    def candidate_rank(recipe):
        return dependence_profile(recipe) + (
            term_size(recipe.lhs) + term_size(recipe.rhs),
            recipe.cost,
            render_term(recipe.lhs),
            render_term(recipe.rhs),
        )

    def ordinary_variables(recipe):
        endpoints = term_variables(recipe.lhs) | term_variables(recipe.rhs)
        return not any(name.startswith("@") for name in endpoints)

    def informative_dependency_law(recipe):
        # Interreduction may turn a nontrivial proof recipe into t = t. Such a
        # reflexive endpoint carries no new information and must never count as
        # a representation improvement merely because its support is tiny.
        return recipe.lhs != recipe.rhs

    def dependency_snapshot(recipe):
        return {
            "lhs": render_term(recipe.lhs),
            "rhs": render_term(recipe.rhs),
            "profile": list(dependence_profile(recipe)),
            "size": term_size(recipe.lhs) + term_size(recipe.rhs),
            "cost": recipe.cost,
            "terminal": terminal_omission(recipe),
        }

    def discover_improvement(search, expand_recipe, current_profile, generation):
        seen = set()
        replayed = []
        enumerated = 0
        rejected_reflexive = 0
        for local_round in range(3):
            rules = search.rules()
            snapshot = list(rules)
            proposals = []
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
                        if not informative_dependency_law(candidate):
                            rejected_reflexive += 1
                            continue
                        key = (
                            search.alpha_signature(candidate.lhs, candidate.rhs),
                            candidate.lhs, candidate.rhs,
                        )
                        if key in seen or not ordinary_variables(candidate):
                            continue
                        seen.add(key)
                        profile = dependence_profile(candidate)
                        if profile >= current_profile:
                            continue
                        proposals.append((candidate_rank(candidate), candidate))
                    if search.expired():
                        break
                if search.expired():
                    break
            proposals.sort(key=lambda item: item[0])
            added = 0
            for _, candidate in proposals[:96]:
                nodes, root = search.compile(candidate)
                replay_ok = replay_dag(
                    source, nodes, root,
                    maximum_term_size=300, maximum_nodes=60000,
                )
                if replay_ok:
                    replayed.append(candidate)
                    if search.add_clause(candidate):
                        search.superpositions += 1
                        added += 1
                    if terminal_omission(candidate):
                        replayed.sort(key=candidate_rank)
                        return candidate, replayed, enumerated, rejected_reflexive
                if added >= 32:
                    break
            if replayed or search.expired():
                break
        replayed.sort(key=candidate_rank)
        return (
            replayed[0] if replayed else None,
            replayed,
            enumerated,
            rejected_reflexive,
        )

    promoted = []
    current_profile = dependence_profile(Recipe(source[0], source[1], "reflexivity"))
    ratchet_trace = []
    final_engine = None
    final_search = None
    final_recipe = None

    for generation in range(3):
        engine, search, _, expand_recipe = setup(75.0)
        promoted_added = 0
        for law in promoted:
            if search.add_clause(law):
                promoted_added += 1

        collapse = search.collapse_proof()
        if collapse is not None:
            final_engine, final_search, final_recipe = engine, search, collapse
            ratchet_trace.append({
                "generation": generation,
                "event": "terminal-promoted-collapse",
                "profile": list(current_profile),
                "promoted_added": promoted_added,
            })
            break

        selected, replayed, enumerated, rejected_reflexive = discover_improvement(
            search, expand_recipe, current_profile, generation
        )
        record = {
            "generation": generation,
            "start_profile": list(current_profile),
            "promoted_in": len(promoted),
            "promoted_added": promoted_added,
            "enumerated": enumerated,
            "rejected_reflexive": rejected_reflexive,
            "replayable_improvements": len(replayed),
            "replayable_top": [dependency_snapshot(r) for r in replayed[:8]],
            "selected": None,
            "cohort": [],
        }
        if selected is None:
            record["event"] = "plateau"
            ratchet_trace.append(record)
            break

        selected_profile = dependence_profile(selected)
        # The residual does not justify choosing arbitrarily between distinct
        # equally minimal repairs. Preserve the small version space and let
        # attachment in the rebuilt proof world decide what composes.
        cohort = [
            r for r in replayed if dependence_profile(r) == selected_profile
        ][:8]
        record.update({
            "event": "promotion-cohort",
            "selected": dependency_snapshot(selected),
            "cohort": [dependency_snapshot(r) for r in cohort],
        })
        ratchet_trace.append(record)
        if not selected_profile < current_profile or not cohort:
            break

        known = {(r.lhs, r.rhs) for r in promoted}
        for law in cohort:
            if (law.lhs, law.rhs) not in known:
                promoted.append(law)
                known.add((law.lhs, law.rhs))
        current_profile = selected_profile

        # Test the reorganized representation immediately with the whole
        # equally minimal repair cohort attached.
        for law in cohort:
            if search.add_clause(law):
                search.superpositions += 1
        collapse = search.collapse_proof()
        if collapse is not None:
            final_engine, final_search, final_recipe = engine, search, collapse
            break
        target_recipe = search.target_proof(search.rules())
        if target_recipe is not None:
            final_engine, final_search, final_recipe = engine, search, target_recipe
            break

    ratchet_info = {
        "generations": ratchet_trace,
        "promoted": len(promoted),
        "final_profile": list(current_profile),
        "found": final_recipe is not None,
        "replay_judge": False,
    }
    if final_recipe is not None:
        accepted = finish(final_engine, final_search, final_recipe)
        ratchet_info["replay_judge"] = bool(accepted)
        open('/tmp/mathgraph_ratchet_trace.json', 'w').write(
            json.dumps(ratchet_info, sort_keys=True)
        )
        if accepted:
            return True
    open('/tmp/mathgraph_ratchet_trace.json', 'w').write(
        json.dumps(ratchet_info, sort_keys=True)
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
    print(f"injected dependency ratchet into {path}")


if __name__ == "__main__":
    main()
