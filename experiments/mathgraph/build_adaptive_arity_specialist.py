#!/usr/bin/env python3
"""Build a non-regressive Stage 2 solver with a separate adaptive-arity phase.

The verified behavioural-future champion is generated first and is left textually
unchanged.  Adaptive arity is compiled as a separate function and is invoked only
after the champion fallback has returned False.  This matters for wall-clock
bounded searches: adding locals/bytecode to the champion function itself can alter
timing-sensitive proof discovery even when the added branch is reached later.
"""

import argparse
import tempfile
from pathlib import Path

from build_behavioural_future_specialist import build as build_behavioural

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BASE = ROOT / "submissions/mathgraph/solver.py"
INSERT_BEFORE = "\ndef run_solo():\n"
CHAMPION_CALL = '''    # Verified developmental fallback: preserve only distinctions that
    # change reachable future proof behaviour, then replay before judging.
    if run_behavioural_future_fallback(source, target, timeout):
        return

'''
ADAPTIVE_CALL = '''    # MSI adaptive-arity fallback.  This is deliberately a second phase:
    # the champion function above executes unchanged and gets first refusal.
    if run_adaptive_arity_fallback(source, target, timeout):
        return

'''

STANDALONE = r'''

# MATHGRAPH_ADAPTIVE_ARITY_V2
# Separate residual-triggered product-state search.  Nothing in this function
# is present in the champion fallback's frame or bytecode.
def run_adaptive_arity_fallback(source, target, timeout):
    base = dict(COMPACT_SUPERPOSITION_PROBE)
    base.update({
        "maximum_term_size": 75,
        "maximum_replay_term_size": 320,
        "maximum_depth": 12,
        "maximum_rules": 896,
        "maximum_rounds": 96,
        "new_clauses_per_round": 64,
        "maximum_clauses": 14000,
        "normalization_steps": 256,
        "maximum_proof_nodes": 70000,
    })

    def setup(seconds):
        limits = dict(base)
        limits["seconds"] = seconds
        engine = TargetGroundedRefutation(
            source, target, time.monotonic() + seconds, limits
        )
        return engine, engine.search

    def orient(q, reverse):
        if not reverse:
            return q
        return Recipe(q.rhs, q.lhs, "symmetry", (q,))

    def exact(engine, q):
        z = engine.inline_recipe(q)
        return ((z.lhs, z.rhs) == target[:2] or
                (z.lhs, z.rhs) == (target[1], target[0]))

    def finish(engine, search, q):
        if q is None:
            return False
        q = engine.inline_recipe(q)
        if (q.lhs, q.rhs) == (target[1], target[0]):
            q = Recipe(q.rhs, q.lhs, "symmetry", (q,))
        if (q.lhs, q.rhs) != target[:2]:
            return False
        nodes, root = search.compile(q)
        if not replay_dag(
            source, nodes, root,
            maximum_term_size=320, maximum_nodes=70000,
        ):
            return False
        code, proof_nodes = make_dag_certificate(target, nodes, root)
        if "_mg_elide_have_types" in globals():
            old_lines = code.splitlines()
            new_lines = _mg_elide_have_types(code).splitlines()
            code = "\n".join(
                old if ":=" in old and old.rstrip().endswith(":= rfl") else new
                for old, new in zip(old_lines, new_lines)
            ) + "\n"
        code_bytes = len(code.encode("utf-8"))
        print(
            "MATHGRAPH_ADAPTIVE_ARITY " + json.dumps({
                "found": True,
                "proof_nodes": proof_nodes,
                "certificate_bytes": code_bytes,
            }, separators=(",", ":")),
            file=sys.stderr, flush=True,
        )
        if code_bytes > 100000:
            return False
        return judge("true", code).get("status") == "accepted"

    try:
        # Build a deterministic structural world.  This is intentionally fresh:
        # the champion has already failed and no mutable state crosses phases.
        engine, search = setup(min(1200.0, max(120.0, timeout / 3.0)))
        pre_trace = []
        for _ in range(3):
            rules = search.rules()
            snapshot = list(rules)
            proposals = []
            proposed = 0
            stop = False
            for oi, outer in enumerate(snapshot):
                if stop:
                    break
                for ii, inner in enumerate(snapshot):
                    if stop:
                        break
                    for path in nonvariable_positions(
                        outer.lhs, maximum_depth=12, include_root=True
                    ):
                        child = search.critical_pair(
                            outer, inner, oi, ii, path
                        )
                        if child is None:
                            continue
                        child = search.interreduce(child, rules)
                        proposals.append((search.target_score(child), child))
                        proposed += 1
                        if exact(engine, child):
                            return finish(engine, search, child)
                        if proposed >= 512:
                            stop = True
                            break
            proposals.sort(key=lambda item: item[0])
            added = 0
            for _, q in proposals:
                if search.add_clause(q):
                    search.superpositions += 1
                    added += 1
                if added >= 64:
                    break
            pre_trace.append((proposed, added, len(search.clauses)))

        rules = search.rules()
        partners = sorted(rules, key=search.target_score)[:12]
        seen = set()
        candidates = []
        for oi, outer in enumerate(rules):
            if len(candidates) >= 64:
                break
            for ii, inner in enumerate(rules):
                if len(candidates) >= 64:
                    break
                for path in nonvariable_positions(
                    outer.lhs, maximum_depth=12, include_root=True
                ):
                    q = search.critical_pair(outer, inner, oi, ii, path)
                    if q is None:
                        continue
                    q = search.interreduce(q, rules)
                    if q.lhs == q.rhs:
                        continue
                    key = (
                        search.alpha_signature(q.lhs, q.rhs), q.lhs, q.rhs,
                    )
                    if key in seen:
                        continue
                    seen.add(key)
                    candidates.append(q)
                    if exact(engine, q):
                        return finish(engine, search, q)
                    if len(candidates) >= 64:
                        break
        candidates = sorted(candidates, key=search.target_score)[:32]

        def sig(q):
            return str(search.alpha_signature(q.lhs, q.rhs))

        individual_calls = 0
        pair_calls = 0
        triple_calls = 0

        def children_with(q, ps, cap=24):
            nonlocal individual_calls
            out = []
            local_seen = set()
            for pi, partner in enumerate(ps):
                for first, second in ((q, partner), (partner, q)):
                    for ar in (False, True):
                        aa = orient(first, ar)
                        for br in (False, True):
                            bb = orient(second, br)
                            for path in nonvariable_positions(
                                aa.lhs, maximum_depth=7, include_root=True
                            ):
                                child = search.critical_pair(
                                    aa, bb, 0, pi, path
                                )
                                if child is None:
                                    continue
                                individual_calls += 1
                                child = search.interreduce(child, rules)
                                key = sig(child)
                                if key in local_seen:
                                    continue
                                local_seen.add(key)
                                if exact(engine, child):
                                    return out, child
                                out.append(child)
            out.sort(key=search.target_score)
            return out[:cap], None

        individual = []
        for q in candidates:
            xs, direct = children_with(q, partners, 24)
            if direct is not None:
                return finish(engine, search, direct)
            individual.append({sig(x) for x in xs})

        # Arity 2: retain only consequences absent from both unary futures.
        pair_states = []
        for i in range(len(candidates)):
            for j in range(i + 1, len(candidates)):
                q1, q2 = candidates[i], candidates[j]
                out = []
                local_seen = set()
                for first, second in ((q1, q2), (q2, q1)):
                    for ar in (False, True):
                        aa = orient(first, ar)
                        for br in (False, True):
                            bb = orient(second, br)
                            for path in nonvariable_positions(
                                aa.lhs, maximum_depth=8, include_root=True
                            ):
                                child = search.critical_pair(
                                    aa, bb, i, j, path
                                )
                                if child is None:
                                    continue
                                pair_calls += 1
                                child = search.interreduce(child, rules)
                                key = sig(child)
                                if key in local_seen:
                                    continue
                                local_seen.add(key)
                                if exact(engine, child):
                                    return finish(engine, search, child)
                                out.append(child)
                lower = individual[i] | individual[j]
                novel = [x for x in out if sig(x) not in lower]
                if novel:
                    novel.sort(key=search.target_score)
                    pair_states.append((
                        -len(novel),
                        min(search.target_score(x) for x in novel),
                        i, j, novel[:6],
                    ))
        pair_states.sort(key=lambda z: (z[0], z[1], z[2], z[3]))

        # One recursive pair generation keeps product structure alive.
        recursive = []
        for _, _, _, _, novel in pair_states[:4]:
            pool2 = novel[:5]
            for i in range(len(pool2)):
                for j in range(i + 1, len(pool2)):
                    q1, q2 = pool2[i], pool2[j]
                    out = []
                    local_seen = set()
                    for first, second in ((q1, q2), (q2, q1)):
                        for ar in (False, True):
                            aa = orient(first, ar)
                            for br in (False, True):
                                bb = orient(second, br)
                                for path in nonvariable_positions(
                                    aa.lhs, maximum_depth=8,
                                    include_root=True,
                                ):
                                    child = search.critical_pair(
                                        aa, bb, i, j, path
                                    )
                                    if child is None:
                                        continue
                                    pair_calls += 1
                                    child = search.interreduce(child, rules)
                                    key = sig(child)
                                    if key in local_seen:
                                        continue
                                    local_seen.add(key)
                                    if exact(engine, child):
                                        return finish(engine, search, child)
                                    out.append(child)
                    if out:
                        out.sort(key=search.target_score)
                        recursive.append((
                            -len(out),
                            min(search.target_score(x) for x in out),
                            out[:5],
                        ))
        recursive.sort(key=lambda z: (z[0], z[1]))

        # Arity 3: a triple earns promotion only when a pair-only bridge
        # interacting with the third coordinate produces a new signature not
        # present in any constituent pair projection.
        triple_novel = []
        for _, _, i, j, p12 in pair_states[:3]:
            q1, q2 = candidates[i], candidates[j]
            for k, q3 in enumerate(candidates[:8]):
                if k == i or k == j:
                    continue
                p13 = []
                p23 = []
                for a, b, bucket in ((q1, q3, p13), (q2, q3, p23)):
                    local_seen = set()
                    for first, second in ((a, b), (b, a)):
                        for ar in (False, True):
                            aa = orient(first, ar)
                            for br in (False, True):
                                bb = orient(second, br)
                                for path in nonvariable_positions(
                                    aa.lhs, maximum_depth=8,
                                    include_root=True,
                                ):
                                    child = search.critical_pair(
                                        aa, bb, 0, 1, path
                                    )
                                    if child is None:
                                        continue
                                    pair_calls += 1
                                    child = search.interreduce(child, rules)
                                    key = sig(child)
                                    if key in local_seen:
                                        continue
                                    local_seen.add(key)
                                    if exact(engine, child):
                                        return finish(engine, search, child)
                                    bucket.append(child)
                lower = {sig(x) for x in p12 + p13 + p23}
                local = []
                local_seen = set()
                for bridge in p12[:3]:
                    for first, second in ((bridge, q3), (q3, bridge)):
                        for ar in (False, True):
                            aa = orient(first, ar)
                            for br in (False, True):
                                bb = orient(second, br)
                                for path in nonvariable_positions(
                                    aa.lhs, maximum_depth=8,
                                    include_root=True,
                                ):
                                    child = search.critical_pair(
                                        aa, bb, 0, 2, path
                                    )
                                    if child is None:
                                        continue
                                    triple_calls += 1
                                    child = search.interreduce(child, rules)
                                    key = sig(child)
                                    if key in lower or key in local_seen:
                                        continue
                                    local_seen.add(key)
                                    if exact(engine, child):
                                        return finish(engine, search, child)
                                    local.append(child)
                local.sort(key=search.target_score)
                triple_novel.extend(local[:3])

        # Attachment is a separate fresh target engine.  Promote only earned
        # higher-arity consequences; final success is still replay + Lean judge.
        promoted = []
        promoted_seen = set()
        for record in pair_states[:3]:
            for q in record[4][:3]:
                key = (search.alpha_signature(q.lhs, q.rhs), q.lhs, q.rhs)
                if key not in promoted_seen:
                    promoted_seen.add(key)
                    promoted.append(q)
        for record in recursive[:2]:
            for q in record[2][:2]:
                key = (search.alpha_signature(q.lhs, q.rhs), q.lhs, q.rhs)
                if key not in promoted_seen:
                    promoted_seen.add(key)
                    promoted.append(q)
        for q in triple_novel[:4]:
            key = (search.alpha_signature(q.lhs, q.rhs), q.lhs, q.rhs)
            if key not in promoted_seen:
                promoted_seen.add(key)
                promoted.append(q)

        print(
            "MATHGRAPH_ADAPTIVE_ARITY " + json.dumps({
                "pre_trace": pre_trace,
                "candidates": len(candidates),
                "partners": len(partners),
                "individual_calls": individual_calls,
                "pair_calls": pair_calls,
                "pair_states": len(pair_states),
                "pair_max_novelty": max([-x[0] for x in pair_states], default=0),
                "triple_calls": triple_calls,
                "triple_novel": len(triple_novel),
                "promoted": len(promoted),
                "found": False,
            }, separators=(",", ":")),
            file=sys.stderr, flush=True,
        )

        if not promoted:
            return False
        attach_engine, attach = setup(min(420.0, max(90.0, timeout / 8.0)))
        for q in promoted:
            attach.add_clause(q)
        target_recipe = (
            attach.collapse_proof() or
            attach.target_proof(attach.rules()) or
            attach.solve()
        )
        return finish(attach_engine, attach, target_recipe)
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError, ValueError,
    ):
        return False
'''


def _champion_function(text: str) -> str:
    start = text.index("def run_behavioural_future_fallback(")
    end = text.index("\ndef run_solo():\n", start)
    return text[start:end]


def build(base: Path, output: Path) -> None:
    with tempfile.TemporaryDirectory() as td:
        champion_path = Path(td) / "champion.py"
        build_behavioural(base, champion_path)
        champion = champion_path.read_text()

    if INSERT_BEFORE not in champion:
        raise SystemExit("run_solo insertion marker not found")
    if CHAMPION_CALL not in champion:
        raise SystemExit("champion call block not found")

    text = champion.replace(INSERT_BEFORE, STANDALONE + INSERT_BEFORE, 1)
    text = text.replace(CHAMPION_CALL, CHAMPION_CALL + ADAPTIVE_CALL, 1)

    # Non-regression invariant: the champion fallback source is literally
    # unchanged.  This prevents a repeat of the 0046 timing regression caused
    # by injecting adaptive locals into the champion function body.
    if _champion_function(text) != _champion_function(champion):
        raise SystemExit("adaptive build modified champion fallback")

    if len(text.encode("utf-8")) > 500_000:
        raise SystemExit("generated adaptive solver exceeds 500 KB submission cap")
    compile(text, str(output), "exec")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    print(f"built isolated adaptive {output} ({len(text.encode('utf-8'))} bytes)")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default=str(DEFAULT_BASE))
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    build(Path(args.base), Path(args.output))


if __name__ == "__main__":
    main()
