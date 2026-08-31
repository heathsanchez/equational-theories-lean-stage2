#!/usr/bin/env python3
"""Inject bounded target attachment after verifier-certified dependency promotion.

This is deliberately problem-blind: the dependency ratchet first discovers and
replays a strict support-reducing cohort.  Only after that representation change
is attached do we permit a bounded ordinary superposition phase ranked by
structural distance to the incoming target.  Every admitted consequence must
replay from the original source; final success still goes through the normal
Lean judge boundary.
"""

import argparse
from pathlib import Path

NEEDLE = r'''        for law in cohort:
            if search.add_clause(law):
                search.superpositions += 1
        collapse = search.collapse_proof()
'''

REPLACEMENT = r'''        for law in cohort:
            if search.add_clause(law):
                search.superpositions += 1

        # Attachment test: after the representation has genuinely changed,
        # allow consequences that need not reduce support again.  Rank only by
        # target reachability, replay every admitted recipe from the original
        # source, and keep the phase tightly bounded.
        attachment_enumerated = 0
        attachment_replayed = 0
        attachment_added = 0
        attachment_recipe = None
        attachment_seen = set()
        target_left, target_right = target[:2]

        def attachment_rank(recipe):
            forward = (
                structural_distance(recipe.lhs, target_left)
                + structural_distance(recipe.rhs, target_right)
            )
            reverse = (
                structural_distance(recipe.lhs, target_right)
                + structural_distance(recipe.rhs, target_left)
            )
            return (
                min(forward, reverse),
                term_size(recipe.lhs) + term_size(recipe.rhs),
                recipe.cost,
                render_term(recipe.lhs),
                render_term(recipe.rhs),
            )

        for attachment_round in range(3):
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
                        attachment_enumerated += 1
                        if not informative_dependency_law(candidate):
                            continue
                        if not ordinary_variables(candidate):
                            continue
                        key = (
                            search.alpha_signature(candidate.lhs, candidate.rhs),
                            candidate.lhs, candidate.rhs,
                        )
                        if key in attachment_seen:
                            continue
                        attachment_seen.add(key)
                        proposals.append((attachment_rank(candidate), candidate))
                    if search.expired():
                        break
                if search.expired():
                    break

            proposals.sort(key=lambda item: item[0])
            added_round = 0
            for _, candidate in proposals[:128]:
                if not replay_candidate(search, candidate):
                    continue
                attachment_replayed += 1
                if (
                    (candidate.lhs == target_left and candidate.rhs == target_right)
                    or (candidate.lhs == target_right and candidate.rhs == target_left)
                ):
                    attachment_recipe = candidate
                    break
                if search.add_clause(candidate):
                    search.superpositions += 1
                    attachment_added += 1
                    added_round += 1
                if added_round >= 40:
                    break
            if attachment_recipe is not None:
                break
            target_recipe = search.target_proof(search.rules())
            if target_recipe is not None:
                attachment_recipe = target_recipe
                break
            collapse_recipe = search.collapse_proof()
            if collapse_recipe is not None:
                attachment_recipe = collapse_recipe
                break
            if added_round == 0 or search.expired():
                break

        record.update({
            "attachment_enumerated": attachment_enumerated,
            "attachment_replayed": attachment_replayed,
            "attachment_added": attachment_added,
            "attachment_found": attachment_recipe is not None,
        })
        if attachment_recipe is not None:
            final_engine, final_search, final_recipe = engine, search, attachment_recipe
            break

        collapse = search.collapse_proof()
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("solver")
    args = parser.parse_args()
    path = Path(args.solver)
    text = path.read_text()
    count = text.count(NEEDLE)
    if count != 1:
        raise SystemExit(f"expected one attachment marker, found {count}")
    patched = text.replace(NEEDLE, REPLACEMENT, 1)
    compile(patched, str(path), "exec")
    path.write_text(patched)
    print(f"injected dependency attachment saturation into {path}")


if __name__ == "__main__":
    main()
