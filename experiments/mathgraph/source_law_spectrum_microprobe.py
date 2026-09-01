#!/usr/bin/env python3
"""Infer a replay-certified, target-blind small-law spectrum for every source.

The probe basis is fixed syntactically from two variables and does not inspect
problem ids or real targets.  It asks which small universal identities follow
from the source under a tiny EqualitySearch budget, then reports spectrum
frequencies and the focus rows only after all searches are complete.
"""

import argparse
import importlib.util
import itertools
import json
import time
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions/mathgraph/solver.py"


def load_solver():
    spec = importlib.util.spec_from_file_location("mathgraph_solver", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def source_text(row):
    for key in ("equation1", "source", "eq1"):
        if isinstance(row.get(key), str):
            return row[key]
    raise KeyError("source equation not found")


def truth_label(row):
    value = row.get("answer")
    return value if isinstance(value, bool) else None


def op(a, b):
    return ("op", a, b)


def basis_terms():
    x = ("var", "x")
    y = ("var", "y")
    level1 = [op(x, x), op(x, y), op(y, x), op(y, y)]
    # Deterministic grammar slice: variables, all one-op terms, then a balanced
    # sample of every one-op term composed once with x or y on either side.
    terms = [x, y] + level1
    for t in level1:
        terms.extend([op(t, x), op(t, y), op(x, t), op(y, t)])
    out = []
    seen = set()
    for t in terms:
        if t not in seen:
            seen.add(t)
            out.append(t)
    return out


def target_tuple(left, right):
    vars_ = tuple(sorted({v for t in (left, right) for v in term_vars(t)}))
    return left, right, vars_


def term_vars(term):
    if term[0] == "var":
        return {term[1]}
    return term_vars(term[1]) | term_vars(term[2])


def unpack(search, raw):
    if raw is None or raw is False:
        return None
    if isinstance(raw, int):
        return search.nodes, raw
    if isinstance(raw, tuple) and len(raw) == 2:
        a, b = raw
        if isinstance(a, list) and isinstance(b, int):
            return a, b
        if isinstance(a, int) and isinstance(b, list):
            return b, a
    return None


def proves(module, source, target, seconds):
    direct = module.variable_omission_collapse(source, target)
    if direct is not None:
        nodes, root = direct
        return bool(module.replay_dag(source, nodes, root)), len(nodes), "omission"
    limits = {
        "max_term_size": 11,
        "max_pool_terms": 18,
        "max_core_terms": 5,
        "max_source_attempts": 12000,
        "max_source_edges": 420,
        "max_derivation_nodes": 1400,
        "max_graph_edges": 1100,
        "max_congruence_rounds": 2,
    }
    search = module.EqualitySearch(source, target, time.monotonic() + seconds, limits)
    raw = search.solve()
    got = unpack(search, raw)
    if got is None:
        return False, 0, None
    nodes, root = got
    ok = bool(module.replay_dag(source, nodes, root))
    return ok, len(nodes) if ok else 0, "search" if ok else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("corpus", type=Path)
    ap.add_argument("--seconds", type=float, default=0.05)
    args = ap.parse_args()
    module = load_solver()
    rows = [json.loads(line) for line in args.corpus.read_text().splitlines() if line.strip()]

    terms = basis_terms()
    probes = []
    for i, j in itertools.combinations(range(len(terms)), 2):
        left, right = terms[i], terms[j]
        # Avoid equations whose two sides use disjoint variable sets; these are
        # almost pure collapse tests already covered by the first microprobe.
        if not (term_vars(left) & term_vars(right)):
            continue
        probes.append((i, j, target_tuple(left, right)))
    # Freeze a bounded syntactic prefix for speed, independent of corpus data.
    probes = probes[:96]
    probe_names = [
        module.render_term(t[2][0]) + " = " + module.render_term(t[2][1])
        for t in probes
    ]

    started = time.monotonic()
    spectra = []
    law_counts = defaultdict(Counter)
    for row_index, row in enumerate(rows):
        source = module.parse_equation(source_text(row))
        bits = []
        witnesses = {}
        for pidx, (_, _, target) in enumerate(probes):
            ok, nodes, constructor = proves(module, source, target, args.seconds)
            bits.append(ok)
            if ok:
                witnesses[str(pidx)] = {"nodes": nodes, "constructor": constructor}
        label = truth_label(row)
        for pidx, bit in enumerate(bits):
            if bit:
                law_counts[str(label)][pidx] += 1
        spectra.append({
            "id": row.get("id"),
            "label": label,
            "bits": bits,
            "witnesses": witnesses,
        })

    profiles = defaultdict(list)
    for rec in spectra:
        key = "".join("1" if b else "0" for b in rec["bits"])
        profiles[key].append(rec)

    focus = {}
    for rid in ("order5_normal_0030", "order5_normal_0036"):
        rec = next((r for r in spectra if r["id"] == rid), None)
        if rec is not None:
            active = [i for i, b in enumerate(rec["bits"]) if b]
            key = "".join("1" if b else "0" for b in rec["bits"])
            focus[rid] = {
                "active_count": len(active),
                "active_laws": [probe_names[i] for i in active],
                "profile_class_size": len(profiles[key]),
                "profile_class_ids": [x["id"] for x in profiles[key]],
                "profile_class_labels": [x["label"] for x in profiles[key]],
            }

    discriminative = []
    for i, name in enumerate(probe_names):
        tc = law_counts["True"][i]
        fc = law_counts["False"][i]
        if tc or fc:
            discriminative.append({"index": i, "law": name, "true": tc, "false": fc})
    discriminative.sort(key=lambda r: (r["false"], -r["true"], r["index"]))

    summary = {
        "rows": len(rows),
        "terms": len(terms),
        "probes": len(probes),
        "seconds_per_probe": args.seconds,
        "wall_seconds": round(time.monotonic() - started, 3),
        "unique_profiles": len(profiles),
        "focus": focus,
        "top_target_blind_laws": discriminative[:20],
    }
    print("SOURCE_LAW_SPECTRUM " + json.dumps(summary, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
