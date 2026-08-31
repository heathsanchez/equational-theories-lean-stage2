#!/usr/bin/env python3
"""Add a problem-blind best-first projection/closure specialist to MathGraph.

This builder composes with build_behavioural_future_specialist.py.  The added
route does not contain benchmark IDs, equation IDs, stored certificates, or a
known projection lemma.  It performs a source-only, incremental critical-pair
search ordered by equation weight with a bounded depth penalty.  Any target is
closed only if the discovered source consequences normalize its two sides to
the same term; the resulting Recipe is compiled, independently replayed, and
then sent to the official Lean judge.
"""

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BASE = ROOT / "submissions/mathgraph/solver.py"
BEHAVIOURAL_BUILDER = ROOT / "experiments/mathgraph/build_behavioural_future_specialist.py"
MARKER = "# MATHGRAPH_PROJECTION_CLOSURE_V1"
INSERT_BEFORE = "\n# MATHGRAPH_BEHAVIOURAL_FUTURE_V1\n"
CALL_BEFORE = "    # Verified developmental fallback: preserve only distinctions that\n"

SPECIALIST = r'''

# MATHGRAPH_PROJECTION_CLOSURE_V1
# Source-only best-first completion.  Scheduling is deliberately independent of
# benchmark identity and target similarity: light critical pairs are activated
# first, with derivation depth as a small penalty.  The target is consulted only
# to ask whether the sound source consequences already normalize it to equality.
def run_projection_closure_fallback(source, target, timeout):
    seconds = min(10.0, max(0.5, timeout / 100.0))
    limits = dict(COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        "seconds": seconds,
        "maximum_term_size": 65,
        "maximum_replay_term_size": 5000,
        "maximum_depth": 12,
        "maximum_rules": 1000,
        "maximum_rounds": 128,
        "new_clauses_per_round": 512,
        "maximum_clauses": 12000,
        "normalization_steps": 128,
        "maximum_proof_nodes": 100000,
    })
    deadline = time.monotonic() + seconds
    search = CompactSuperposition(sys.modules[__name__], source, target, deadline, limits)
    active = []
    heap = []
    queued = set()
    serial = 0
    added = 0

    def variants(clause):
        oriented = search.orient(clause)
        if oriented is not None:
            return [oriented]
        out = []
        if clause.lhs[0] != "var":
            out.append(clause)
        if clause.rhs[0] != "var":
            out.append(Recipe(clause.rhs, clause.lhs, "symmetry", (clause,)))
        return out

    def endpoint_key(recipe):
        names = {}
        forward = (
            alpha_canonical_term(recipe.lhs, names),
            alpha_canonical_term(recipe.rhs, names),
        )
        names = {}
        reverse = (
            alpha_canonical_term(recipe.rhs, names),
            alpha_canonical_term(recipe.lhs, names),
        )
        return min(forward, reverse)

    def proposal_weight(recipe, depth):
        return (
            term_size(recipe.lhs) + term_size(recipe.rhs) + 2 * depth,
            recipe.cost,
        )

    def push_pairs(outer, inner, outer_index, inner_index, depth):
        nonlocal serial
        for path in nonvariable_positions(
            outer.lhs, maximum_depth=limits["maximum_depth"], include_root=True
        ):
            if time.monotonic() >= deadline:
                return
            candidate = search.critical_pair(
                outer, inner, outer_index, inner_index, path
            )
            if candidate is None:
                continue
            if max(term_size(candidate.lhs), term_size(candidate.rhs)) > limits[
                "maximum_term_size"
            ]:
                continue
            key = endpoint_key(candidate)
            if key in queued:
                continue
            queued.add(key)
            weight, proof_cost = proposal_weight(candidate, depth)
            serial += 1
            heapq.heappush(
                heap, (weight, proof_cost, serial, depth, key, candidate)
            )
            if len(heap) > 20000:
                # Keep the lightest pending consequences; this is a resource
                # bound, not a semantic pruning rule.
                heap.sort()
                del heap[20000:]
                heapq.heapify(heap)

    def activate(clause, depth):
        new_variants = variants(clause)
        base = len(active)
        active.extend(new_variants)
        for new_index in range(base, len(active)):
            new = active[new_index]
            snapshot = list(active)
            for other_index, other in enumerate(snapshot):
                push_pairs(new, other, new_index, other_index, depth + 1)
                if other_index < base:
                    push_pairs(other, new, other_index, new_index, depth + 1)

    def finish(recipe):
        if recipe is None or (recipe.lhs, recipe.rhs) != target[:2]:
            return False
        try:
            nodes, root = search.compile(recipe)
        except (KeyError, MemoryError, RecursionError, TypeError, ValueError):
            return False
        if not replay_dag(
            source, nodes, root,
            maximum_term_size=limits["maximum_replay_term_size"],
            maximum_nodes=limits["maximum_proof_nodes"],
        ):
            return False
        if (nodes[root].lhs, nodes[root].rhs) != target[:2]:
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
            "MATHGRAPH_METRICS " + json.dumps({
                "portfolio": "projection-closure-v1",
                "found": True,
                "added_clauses": added,
                "proof_nodes": proof_nodes,
                "certificate_bytes": code_bytes,
            }, separators=(",", ":")),
            file=sys.stderr, flush=True,
        )
        if code_bytes > 100000:
            return False
        return judge("true", code).get("status") == "accepted"

    try:
        # The initial source clause is the only seed.  No target-grounding or
        # benchmark-specific bridge is supplied to the completion process.
        activate(search.clauses[0], 0)
        direct = search.target_proof(search.rules())
        if direct is not None and finish(direct):
            return True

        while (
            heap
            and added < 128
            and len(search.clauses) < limits["maximum_clauses"]
            and time.monotonic() < deadline
        ):
            _, _, _, depth, key, candidate = heapq.heappop(heap)
            queued.discard(key)
            candidate = search.interreduce(candidate, list(active))
            if candidate.lhs == candidate.rhs:
                continue
            if not search.add_clause(candidate):
                continue
            added += 1
            clause = search.clauses[-1]
            search.superpositions += 1

            # Ask only whether the now-proven source theory closes the target.
            # This also catches projection, constant, and other simplifying laws
            # without naming or hard-coding any one of them.
            goal = search.target_proof(search.rules())
            if goal is not None and finish(goal):
                return True
            activate(clause, depth)
    except (
        KeyError, IndexError, MemoryError, RecursionError, TypeError, ValueError,
    ):
        return False
    return False
'''

CALL = '''    # Generic lightweight completion before the more expensive
    # behavioural-future representation repair.
    if run_projection_closure_fallback(source, target, timeout):
        return

'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=Path, default=DEFAULT_BASE)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    with tempfile.TemporaryDirectory() as tmp:
        intermediate = Path(tmp) / "behavioural.py"
        subprocess.run(
            [
                sys.executable,
                str(BEHAVIOURAL_BUILDER),
                "--base", str(args.base),
                "--output", str(intermediate),
            ],
            check=True,
        )
        text = intermediate.read_text(encoding="utf-8")

    if MARKER in text:
        raise SystemExit("projection closure specialist already present")
    if text.count(INSERT_BEFORE) != 1:
        raise SystemExit("behavioural insertion marker not unique")
    if text.count(CALL_BEFORE) != 1:
        raise SystemExit("fallback call marker not unique")

    text = text.replace(INSERT_BEFORE, SPECIALIST + INSERT_BEFORE, 1)
    text = text.replace(CALL_BEFORE, CALL + CALL_BEFORE, 1)
    compile(text, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text, encoding="utf-8")
    print(f"built {args.output} ({len(text.encode('utf-8'))} bytes)")


if __name__ == "__main__":
    main()
