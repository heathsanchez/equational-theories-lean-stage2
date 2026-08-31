#!/usr/bin/env python3
"""Inject a verifier-certified dependency-development ratchet.

The ratchet is problem-blind. It discovers replayable source consequences that
strictly reduce variable dependence, preserves equally minimal repairs, and
promotes that residual-relative version space into a fresh proof world. When a
strict reduction is temporarily unavailable, it permits a small replay-certified
neutral stratum at the same dependency profile as discovery scaffolding, then
asks again for a strict reduction. Every promoted result remains replayable from
the original source. A universal bare-variable omission is terminal.
"""

import argparse
from pathlib import Path

MARKER = "    try:\n        # World A: streaming frontier.\n"

PORTAL = r'''    # Developmental dependency ratchet: strict information loss is the
    # progress measure; bounded same-profile laws are only temporary bridges.
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
        # Expansion can leave distinct internal terms with the same observable
        # endpoint. Neither structural nor rendered t=t is informative.
        if recipe.lhs == recipe.rhs:
            return False
        if render_term(recipe.lhs) == render_term(recipe.rhs):
            return False
        return True

    def dependency_snapshot(recipe):
        return {
            "lhs": render_term(recipe.lhs),
            "rhs": render_term(recipe.rhs),
            "profile": list(dependence_profile(recipe)),
            "size": term_size(recipe.lhs) + term_size(recipe.rhs),
            "cost": recipe.cost,
            "terminal": terminal_omission(recipe),
        }

    def replay_candidate(search, candidate):
        nodes, root = search.compile(candidate)
        return replay_dag(
            source, nodes, root,
            maximum_term_size=300, maximum_nodes=60000,
        )

    def discover_improvement(search, expand_recipe, current_profile, generation):
        seen = set()
        strict_replayed = []
        enumerated = 0
        rejected_reflexive = 0
        neutral_replayed_total = 0
        neutral_added_total = 0
        neutral_examples = []
        for local_round in range(4):
            rules = search.rules()
            snapshot = list(rules)
            strict_proposals = []
            neutral_proposals = []
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
                        if profile < current_profile:
                            strict_proposals.append((candidate_rank(candidate), candidate))
                        elif profile == current_profile:
                            neutral_proposals.append((candidate_rank(candidate), candidate))
                    if search.expired():
                        break
                if search.expired():
                    break

            strict_proposals.sort(key=lambda item: item[0])
            for _, candidate in strict_proposals[:96]:
                if replay_candidate(search, candidate):
                    strict_replayed.append(candidate)
                    if terminal_omission(candidate):
                        strict_replayed.sort(key=candidate_rank)
                        return (
                            candidate, strict_replayed, enumerated,
                            rejected_reflexive, neutral_replayed_total,
                            neutral_added_total, neutral_examples,
                        )
            if strict_replayed:
                strict_replayed.sort(key=candidate_rank)
                return (
                    strict_replayed[0], strict_replayed, enumerated,
                    rejected_reflexive, neutral_replayed_total,
                    neutral_added_total, neutral_examples,
                )

            # No strict improvement at this frontier. Admit only a bounded
            # same-profile replayable stratum and recompute critical pairs.
            # These are temporary bridges, not counted as development.
            neutral_proposals.sort(key=lambda item: item[0])
            neutral_added_round = 0
            for _, candidate in neutral_proposals[:96]:
                if not replay_candidate(search, candidate):
                    continue
                neutral_replayed_total += 1
                if len(neutral_examples) < 8:
                    neutral_examples.append(dependency_snapshot(candidate))
                if search.add_clause(candidate):
                    search.superpositions += 1
                    neutral_added_round += 1
                    neutral_added_total += 1
                if neutral_added_round >= 24:
                    break
            if neutral_added_round == 0 or search.expired():
                break

        return (
            None, strict_replayed, enumerated, rejected_reflexive,
            neutral_replayed_total, neutral_added_total, neutral_examples,
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

        (
            selected, replayed, enumerated, rejected_reflexive,
            neutral_replayed, neutral_added, neutral_examples,
        ) = discover_improvement(search, expand_recipe, current_profile, generation)
        record = {
            "generation": generation,
            "start_profile": list(current_profile),
            "promoted_in": len(promoted),
            "promoted_added": promoted_added,
            "enumerated": enumerated,
            "rejected_reflexive": rejected_reflexive,
            "neutral_replayed": neutral_replayed,
            "neutral_added": neutral_added,
            "neutral_examples": neutral_examples,
            "replayable_improvements": len(replayed),
            "replayable_top": [dependency_snapshot(r) for r in replayed[:8]],
            "selected": None,
            "cohort": [],
        }
        if selected is None:
            record["event"] = "plateau-after-neutral-closure"
            ratchet_trace.append(record)
            break

        selected_profile = dependence_profile(selected)
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
