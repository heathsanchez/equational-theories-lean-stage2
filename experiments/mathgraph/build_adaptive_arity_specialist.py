#!/usr/bin/env python3
"""Build a production Stage 2 solver with residual-triggered adaptive arity.

This layers a bounded arity controller onto the frozen behavioural-future
specialist without modifying that champion builder.  The extra mechanism runs
only after the existing unary behavioural closure fails.  It raises the
representation from clauses to pairs only when a pair has consequences absent
from both unary futures, and raises to triples only when a triple has
consequences absent from every constituent pair projection.

The mechanism is problem-blind and proof-producing: every candidate remains a
Recipe consequence of the source and final success still goes through the
existing replay + official judge path.
"""

import argparse
import tempfile
from pathlib import Path

from build_behavioural_future_specialist import build as build_behavioural

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BASE = ROOT / "submissions/mathgraph/solver.py"

ANCHOR = '''        print(\n            "MATHGRAPH_METRICS " + json.dumps({\n                "portfolio": "behavioural-future-v1",'''

ADAPTIVE = r'''
        # MSI adaptive-arity completion.  Run only when the unary behavioural
        # representation has failed to attach to the target.  Higher arity is
        # admitted only when it creates behaviour absent from every lower-arity
        # projection, preventing combinatorial growth without information gain.
        arity_pair_tests = 0
        arity_pair_states = 0
        arity_pair_max_novelty = 0
        arity_triple_tests = 0
        arity_triple_states = 0
        arity_triple_max_novelty = 0
        arity_promoted = 0
        if target_recipe is None and candidates:
            arity_pool = [q for _, q in candidates[:16]]
            unary_cache = {}

            def unary_future(q):
                key = (
                    frontier.alpha_signature(q.lhs, q.rhs), q.lhs, q.rhs,
                )
                if key not in unary_cache:
                    outs, child, calls = future_signature(q)
                    unary_cache[key] = set(outs)
                    if child is not None:
                        return unary_cache[key], child
                return unary_cache[key], None

            def pair_only(q1, q2, cap=8):
                nonlocal_target = [None]
                out = []
                seen_pair = set()
                base1, child1 = unary_future(q1)
                base2, child2 = unary_future(q2)
                if child1 is not None:
                    nonlocal_target[0] = child1
                    return out, nonlocal_target[0]
                if child2 is not None:
                    nonlocal_target[0] = child2
                    return out, nonlocal_target[0]
                lower = base1 | base2
                for first, second in ((q1, q2), (q2, q1)):
                    for first_reverse in (False, True):
                        a = orient(first, first_reverse)
                        for second_reverse in (False, True):
                            b = orient(second, second_reverse)
                            for path in nonvariable_positions(
                                a.lhs, maximum_depth=8, include_root=True
                            ):
                                child = frontier_pair(a, b, 0, 1, path)
                                if child is None:
                                    continue
                                sig = signature(child)
                                if sig in lower or sig in seen_pair:
                                    continue
                                seen_pair.add(sig)
                                if exact_target(frontier_engine, child):
                                    return out, child
                                out.append(child)
                out.sort(key=frontier.target_score)
                return out[:cap], None

            # Infer whether arity two adds information.  Scan a small target-
            # ordered pool and retain only genuinely relational pair states.
            pair_states = []
            for i in range(len(arity_pool)):
                if target_recipe is not None:
                    break
                for j in range(i + 1, len(arity_pool)):
                    arity_pair_tests += 1
                    novel, child = pair_only(arity_pool[i], arity_pool[j])
                    if child is not None:
                        target_recipe = child
                        target_origin = "adaptive-arity-2-direct"
                        break
                    if novel:
                        arity_pair_states += 1
                        arity_pair_max_novelty = max(
                            arity_pair_max_novelty, len(novel)
                        )
                        pair_states.append((
                            -len(novel),
                            min(frontier.target_score(x) for x in novel),
                            arity_pool[i], arity_pool[j], novel,
                        ))
            pair_states.sort(key=lambda z: (z[0], z[1]))

            # Preserve pair states for one recursive generation.  The children
            # are not flattened into the old scheduler: only pair-only children
            # can form the next product frontier.
            recursive_pairs = []
            if target_recipe is None:
                for _, _, q1, q2, novel in pair_states[:4]:
                    pool2 = novel[:5]
                    for i in range(len(pool2)):
                        for j in range(i + 1, len(pool2)):
                            arity_pair_tests += 1
                            novel2, child = pair_only(pool2[i], pool2[j])
                            if child is not None:
                                target_recipe = child
                                target_origin = "adaptive-arity-2-recursive"
                                break
                            if novel2:
                                arity_pair_states += 1
                                arity_pair_max_novelty = max(
                                    arity_pair_max_novelty, len(novel2)
                                )
                                recursive_pairs.append((
                                    -len(novel2),
                                    min(frontier.target_score(x) for x in novel2),
                                    pool2[i], pool2[j], novel2,
                                ))
                        if target_recipe is not None:
                            break
                    if target_recipe is not None:
                        break
            recursive_pairs.sort(key=lambda z: (z[0], z[1]))

            # Infer arity three only if pair structure exists.  A triple earns
            # promotion only when composing a pair-only child with a third
            # coordinate yields behaviour absent from all three pair
            # projections.  This is the production analogue of the verified
            # MSI interface-shape experiment.
            triple_novel = []
            if target_recipe is None and pair_states:
                triple_base = arity_pool[:8]
                for _, _, q1, q2, pair_children in pair_states[:3]:
                    for q3 in triple_base:
                        if q3 is q1 or q3 is q2:
                            continue
                        arity_triple_tests += 1
                        p12, c12 = pair_only(q1, q2)
                        p13, c13 = pair_only(q1, q3)
                        p23, c23 = pair_only(q2, q3)
                        direct = c12 or c13 or c23
                        if direct is not None:
                            target_recipe = direct
                            target_origin = "adaptive-arity-3-pair-direct"
                            break
                        lower = set(signature(x) for x in p12 + p13 + p23)
                        local = []
                        local_seen = set()
                        for bridge in pair_children[:3]:
                            for first, second in ((bridge, q3), (q3, bridge)):
                                for first_reverse in (False, True):
                                    a = orient(first, first_reverse)
                                    for second_reverse in (False, True):
                                        b = orient(second, second_reverse)
                                        for path in nonvariable_positions(
                                            a.lhs, maximum_depth=8,
                                            include_root=True,
                                        ):
                                            child = frontier_pair(
                                                a, b, 0, 2, path
                                            )
                                            if child is None:
                                                continue
                                            sig = signature(child)
                                            if sig in lower or sig in local_seen:
                                                continue
                                            local_seen.add(sig)
                                            if exact_target(
                                                frontier_engine, child
                                            ):
                                                target_recipe = child
                                                target_origin = (
                                                    "adaptive-arity-3-direct"
                                                )
                                                break
                                            local.append(child)
                                        if target_recipe is not None:
                                            break
                                    if target_recipe is not None:
                                        break
                                if target_recipe is not None:
                                    break
                            if target_recipe is not None:
                                break
                        if target_recipe is not None:
                            break
                        if local:
                            local.sort(key=frontier.target_score)
                            arity_triple_states += 1
                            arity_triple_max_novelty = max(
                                arity_triple_max_novelty, len(local)
                            )
                            triple_novel.extend(local[:3])
                    if target_recipe is not None:
                        break

            # Attachment: promote only a tiny set of proof-bearing consequences
            # created by the earned higher-arity interfaces, then ask the same
            # bounded target search to close.  This retains a single output
            # proof language while using the richer representation for search.
            if target_recipe is None:
                promoted = []
                used = set()
                for record in pair_states[:2] + recursive_pairs[:2]:
                    for q in record[4][:2]:
                        key = (
                            frontier.alpha_signature(q.lhs, q.rhs),
                            q.lhs, q.rhs,
                        )
                        if key not in used:
                            used.add(key)
                            promoted.append(q)
                for q in triple_novel[:4]:
                    key = (
                        frontier.alpha_signature(q.lhs, q.rhs), q.lhs, q.rhs,
                    )
                    if key not in used:
                        used.add(key)
                        promoted.append(q)
                arity_promoted = len(promoted)
                if promoted:
                    # Use the existing proof world so all promoted recipes retain
                    # their provenance.  A short closure tests attachment without
                    # replacing the champion's search budget.
                    for q in promoted:
                        frontier.add_clause(q)
                    for _ in range(2):
                        rules = frontier.rules()
                        proposals = []
                        for q in promoted:
                            for partner in rules[:64]:
                                for first, second in ((q, partner), (partner, q)):
                                    for first_reverse in (False, True):
                                        a = orient(first, first_reverse)
                                        for second_reverse in (False, True):
                                            b = orient(second, second_reverse)
                                            for path in nonvariable_positions(
                                                a.lhs, maximum_depth=10,
                                                include_root=True,
                                            ):
                                                child = frontier_pair(
                                                    a, b, 0, 1, path
                                                )
                                                if child is None:
                                                    continue
                                                if exact_target(
                                                    frontier_engine, child
                                                ):
                                                    target_recipe = child
                                                    target_origin = (
                                                        "adaptive-arity-attachment"
                                                    )
                                                    break
                                                proposals.append((
                                                    frontier.target_score(child),
                                                    child,
                                                ))
                                            if target_recipe is not None:
                                                break
                                        if target_recipe is not None:
                                            break
                                    if target_recipe is not None:
                                        break
                                if target_recipe is not None:
                                    break
                            if target_recipe is not None:
                                break
                        if target_recipe is not None:
                            break
                        proposals.sort(key=lambda z: z[0])
                        promoted = [q for _, q in proposals[:8]]
                        if not promoted:
                            break

        if arity_pair_tests or arity_triple_tests:
            print(
                "MATHGRAPH_ADAPTIVE_ARITY " + json.dumps({
                    "pair_tests": arity_pair_tests,
                    "pair_states": arity_pair_states,
                    "pair_max_novelty": arity_pair_max_novelty,
                    "triple_tests": arity_triple_tests,
                    "triple_states": arity_triple_states,
                    "triple_max_novelty": arity_triple_max_novelty,
                    "promoted": arity_promoted,
                    "found": target_recipe is not None,
                    "target_origin": target_origin,
                }, separators=(",", ":")),
                file=sys.stderr, flush=True,
            )
'''


def build(base: Path, output: Path) -> None:
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td) / "behavioural.py"
        build_behavioural(base, tmp)
        text = tmp.read_text()
    if ANCHOR not in text:
        raise SystemExit("behavioural metrics anchor not found")
    text = text.replace(ANCHOR, ADAPTIVE + "\n" + ANCHOR, 1)
    if len(text.encode("utf-8")) > 500_000:
        raise SystemExit("generated adaptive solver exceeds 500 KB submission cap")
    compile(text, str(output), "exec")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    print(f"built adaptive {output} ({len(text.encode('utf-8'))} bytes)")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default=str(DEFAULT_BASE))
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    build(Path(args.base), Path(args.output))


if __name__ == "__main__":
    main()
