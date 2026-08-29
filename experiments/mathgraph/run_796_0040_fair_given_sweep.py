#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"
RATIOS = (4, 5, 6, 7, 8, 10)


def load_solver():
    spec = importlib.util.spec_from_file_location("mg796fair0040", SOLVER)
    m = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = m
    spec.loader.exec_module(m)
    return m


def load_row(path):
    for line in Path(path).read_text().splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        if row.get("id") == "evaluation_normal_0040":
            return row
    raise SystemExit("evaluation_normal_0040 not found")


def oriented_variants(m, clause):
    if clause.lhs == clause.rhs:
        return (clause,)
    return (clause, m.Recipe(clause.rhs, clause.lhs, "symmetry", (clause,)))


def fair_given_recipe(m, search, ratio, maximum_given=1024):
    passive = list(search.clauses)
    active = []
    age = {id(c): i for i, c in enumerate(passive)}
    next_age = len(passive)
    given = age_picks = target_picks = proposals_total = accepted_total = 0

    while passive and given < maximum_given and not search.expired():
        rules = [q for c in active if (q := search.orient(c)) is not None]
        goal = search.target_proof(rules)
        if goal is not None:
            return goal, locals_stats(given, age_picks, target_picks, proposals_total, accepted_total)

        use_age = given > 0 and given % (ratio + 1) == ratio
        if use_age:
            idx = min(range(len(passive)), key=lambda i: age.get(id(passive[i]), 10**18))
            age_picks += 1
        else:
            idx = min(range(len(passive)), key=lambda i: (search.target_score(passive[i]), age.get(id(passive[i]), 10**18)))
            target_picks += 1
        selected = search.interreduce(passive.pop(idx), rules)
        active.append(selected)
        given += 1

        rules = [q for c in active if (q := search.orient(c)) is not None]
        goal = search.target_proof(rules)
        if goal is not None:
            return goal, locals_stats(given, age_picks, target_picks, proposals_total, accepted_total)

        proposals = []
        for oi, other in enumerate(active):
            for bo, bi, a, b in ((selected, other, given, oi), (other, selected, oi, given)):
                for oside, outer in enumerate(oriented_variants(m, bo)):
                    for iside, inner in enumerate(oriented_variants(m, bi)):
                        for path in m.nonvariable_positions(outer.lhs, maximum_depth=search.limits["maximum_depth"], include_root=True):
                            if search.expired():
                                break
                            q = search.critical_pair(outer, inner, a * 2 + oside, b * 2 + iside, path)
                            if q is None:
                                continue
                            qr = search.interreduce(q, rules)
                            proposals.append((search.target_score(qr), qr))
        proposals_total += len(proposals)
        proposals.sort(key=lambda x: x[0])
        for _, q in proposals[:search.limits["new_clauses_per_round"]]:
            if search.add_clause(q):
                passive.append(q)
                age[id(q)] = next_age
                next_age += 1
                accepted_total += 1

        new_passive, seen = [], set()
        for c in passive:
            if search.expired():
                break
            c = search.interreduce(c, rules)
            names = {}
            left = (m.alpha_canonical_term(c.lhs, names), m.alpha_canonical_term(c.rhs, names))
            names = {}
            right = (m.alpha_canonical_term(c.rhs, names), m.alpha_canonical_term(c.lhs, names))
            key = min(left, right)
            if key in seen:
                continue
            seen.add(key)
            new_passive.append(c)
        passive = new_passive

    rules = [q for c in active if (q := search.orient(c)) is not None]
    return search.target_proof(rules), locals_stats(given, age_picks, target_picks, proposals_total, accepted_total)


def locals_stats(given, age_picks, target_picks, proposals, accepted):
    return {"given": given, "age_picks": age_picks, "target_picks": target_picks, "proposals": proposals, "accepted": accepted}


def one(m, row, ratio, seconds):
    source = m.parse_equation(row["equation1"])
    target = m.parse_equation(row["equation2"])
    limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        "seconds": seconds,
        "maximum_term_size": 65,
        "maximum_replay_term_size": 300,
        "maximum_depth": 12,
        "maximum_rules": 1024,
        "maximum_rounds": 96,
        "new_clauses_per_round": 512,
        "maximum_clauses": 16000,
        "normalization_steps": 384,
        "maximum_proof_nodes": 60000,
    })
    started = time.monotonic()
    eng = m.TargetGroundedRefutation(source, target, time.monotonic() + seconds, limits)
    recipe, stats = fair_given_recipe(m, eng.search, ratio, maximum_given=1024)
    out = {"ratio": ratio, "recipe_found": recipe is not None, "inline_ok": False, "compile_ok": False, "replay_ok": False, "proof_nodes": None, **stats}
    if recipe is not None:
        try:
            rr = eng.inline_recipe(recipe)
            out["inline_ok"] = rr is not None
            if rr is not None:
                compiler = m.CompactSuperposition(m, eng.source, eng.target, time.monotonic() + 5.0, eng.search.limits)
                compiled = compiler.compile(rr)
                if compiled is not None:
                    nodes, root = compiled
                    out["compile_ok"] = True
                    out["proof_nodes"] = len(nodes)
                    out["replay_ok"] = bool(m.replay_dag(source, nodes, root))
        except Exception as e:
            out["error"] = type(e).__name__ + ": " + str(e)
    out["seconds"] = round(time.monotonic() - started, 4)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--normal", required=True)
    ap.add_argument("--seconds", type=float, default=20.0)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    m = load_solver()
    row = load_row(args.normal)
    runs = {}
    for ratio in RATIOS:
        rec = one(m, row, ratio, args.seconds)
        runs[str(ratio)] = rec
        print("FAIR0040", json.dumps(rec, sort_keys=True), flush=True)
    out = {"schema": "mathgraph.796-0040-fair-given-sweep.v1", "id": row["id"], "runs": runs, "replay_ratios": [r for r, x in runs.items() if x["replay_ok"]]}
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print("FAIR0040_SUMMARY", json.dumps({"replay_ratios": out["replay_ratios"]}, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
