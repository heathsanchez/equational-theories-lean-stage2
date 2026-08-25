#!/usr/bin/env python3
from __future__ import annotations

import json
import time
from pathlib import Path

import run_residual3_fairness_proof_sweep as base
import run_corridor_aware_continuation as ca

OUT = Path(__file__).parent / "results/multistep-corridor-planner.json"
RATIO = 7
BEAM = 3
HORIZONS = (0, 2, 3)
RESIDUAL = base.RESIDUAL_IDS


def ckey(m, c):
    return ca.ckey(m, c)


def csize(c):
    return ca.clause_size(c)


def score0(search, c):
    s = search.target_score(c)
    return float(s[0] if isinstance(s, tuple) else s)


def children(m, search, active, parent, deadline):
    """Unique reduced one-step children of parent in the frozen current context."""
    rules = [q for c in active if (q := search.orient(c)) is not None]
    pr = search.orient(parent)
    rules2 = rules + ([pr] if pr is not None else [])
    seen = set(); out = []
    for oi, other in enumerate(active + [parent]):
        for bo, bi, a, b in ((parent, other, 9999, oi), (other, parent, oi, 9999)):
            for oside, outer in enumerate(base.oriented_variants(m, bo)):
                for iside, inner in enumerate(base.oriented_variants(m, bi)):
                    for path in m.nonvariable_positions(outer.lhs, maximum_depth=search.limits["maximum_depth"], include_root=True):
                        if time.monotonic() >= deadline or search.expired():
                            return out
                        q = search.critical_pair(outer, inner, a * 2 + oside, b * 2 + iside, path)
                        if q is None:
                            continue
                        qr = search.interreduce(q, rules2); k = ckey(m, qr)
                        if k in seen:
                            continue
                        seen.add(k); out.append(qr)
    return out


def plan_score(m, search, active, root, horizon, deadline):
    """Preserve a beam of moderate-contraction trajectories for horizon steps.

    Returns a lexicographic score: deepest live layer, mean layer occupancy,
    final beam width.  No prover state is mutated.
    """
    if horizon <= 0:
        return (0, 0.0, 0), 0, 0
    beam = [root]
    occupancies = []
    total_generated = 0
    depth = 0
    for step in range(horizon):
        viable = []; generated = 0; moderate = 0
        for parent in beam:
            if time.monotonic() >= deadline or search.expired():
                break
            ps = csize(parent)
            cs = children(m, search, active, parent, deadline)
            generated += len(cs); total_generated += len(cs)
            for ch in cs:
                d = csize(ch) - ps
                if -6 <= d <= 0:
                    moderate += 1
                    viable.append(ch)
        occupancies.append(moderate / generated if generated else 0.0)
        if not viable:
            break
        # Keep several compatible futures alive; target score is only beam pruning.
        viable.sort(key=lambda q: (score0(search, q), csize(q), ckey(m, q)))
        uniq = []; seen = set()
        for q in viable:
            k = ckey(m, q)
            if k in seen:
                continue
            seen.add(k); uniq.append(q)
            if len(uniq) >= BEAM:
                break
        beam = uniq
        depth = step + 1
    mean_occ = sum(occupancies) / len(occupancies) if occupancies else 0.0
    return (depth, mean_occ, len(beam) if depth else 0), total_generated, sum(1 for x in occupancies if x > 0)


def one(m, r, horizon, seconds):
    source = m.parse_equation(r["equation1"]); target = m.parse_equation(r["equation2"])
    limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({"seconds": seconds, "maximum_term_size": 65, "maximum_replay_term_size": 300,
                   "maximum_depth": 12, "maximum_rules": 1024, "maximum_rounds": 96,
                   "new_clauses_per_round": 512, "maximum_clauses": 16000,
                   "normalization_steps": 384, "maximum_proof_nodes": 60000})
    started = time.monotonic(); deadline = started + seconds
    eng = m.TargetGroundedRefutation(source, target, deadline, limits)
    passive = list(eng.search.clauses); active = []
    age = {ckey(m,c): i for i,c in enumerate(passive)}; next_age = len(passive)
    continuation_scores = {}; remaining = 0
    given = age_picks = target_picks = planner_picks = 0
    planner_scored = planner_children = planner_live = 0
    proposals_total = accepted_total = 0; recipe = None

    while passive and given < 1024 and not eng.search.expired():
        rules = [q for c in active if (q := eng.search.orient(c)) is not None]
        recipe = eng.search.target_proof(rules)
        if recipe is not None: break
        cand = [i for i,c in enumerate(passive) if remaining > 0 and ckey(m,c) in continuation_scores]
        use_age = given > 0 and given % (RATIO + 1) == RATIO
        if cand:
            idx = min(cand, key=lambda i: (tuple(-x if isinstance(x,(int,float)) else x for x in continuation_scores[ckey(m,passive[i])]), score0(eng.search,passive[i]), age.get(ckey(m,passive[i]),10**18)))
            planner_picks += 1; remaining -= 1
        elif use_age:
            idx = min(range(len(passive)), key=lambda i: age.get(ckey(m,passive[i]),10**18)); age_picks += 1
        else:
            idx = min(range(len(passive)), key=lambda i: (score0(eng.search,passive[i]), age.get(ckey(m,passive[i]),10**18))); target_picks += 1

        selected = eng.search.interreduce(passive.pop(idx), rules); active.append(selected); given += 1
        selected_was_age = use_age and not cand
        rules = [q for c in active if (q := eng.search.orient(c)) is not None]
        recipe = eng.search.target_proof(rules)
        if recipe is not None: break

        psize = csize(selected); proposals=[]; raw_gate={}
        for oi,other in enumerate(active):
            for bo,bi,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
                for oside,outer in enumerate(base.oriented_variants(m,bo)):
                    for iside,inner in enumerate(base.oriented_variants(m,bi)):
                        for path in m.nonvariable_positions(outer.lhs,maximum_depth=eng.search.limits["maximum_depth"],include_root=True):
                            if eng.search.expired(): break
                            q=eng.search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                            if q is None: continue
                            raw=csize(q); qr=eng.search.interreduce(q,rules); k=ckey(m,qr)
                            raw_gate[k]=raw_gate.get(k,False) or raw <= psize+1
                            proposals.append((score0(eng.search,qr),qr))
        proposals_total += len(proposals); proposals.sort(key=lambda x:x[0]); admitted=[]
        for _,q in proposals[:eng.search.limits["new_clauses_per_round"]]:
            if eng.search.add_clause(q):
                passive.append(q); k=ckey(m,q); age[k]=next_age; next_age+=1; accepted_total+=1
                if raw_gate.get(k,False): admitted.append(q)

        if selected_was_age and horizon > 0 and admitted:
            scored={}
            for q in admitted:
                if eng.search.expired(): break
                ps,nchild,nlive=plan_score(m,eng.search,active,q,horizon,deadline)
                planner_scored += 1; planner_children += nchild; planner_live += nlive
                if ps[0] > 0: scored[ckey(m,q)] = ps
            continuation_scores=scored; remaining=horizon

        new=[]; seen=set(); surviving={}
        for c in passive:
            if eng.search.expired(): break
            c=eng.search.interreduce(c,rules); k=ckey(m,c)
            if k in seen: continue
            seen.add(k); new.append(c)
            if k in continuation_scores: surviving[k]=continuation_scores[k]
        passive=new; continuation_scores=surviving

    if recipe is None:
        rules=[q for c in active if (q:=eng.search.orient(c)) is not None]; recipe=eng.search.target_proof(rules)
    found=recipe is not None; inline_ok=compile_ok=replay_ok=False; nodes_n=None; err=None
    if found:
        try:
            rr=eng.inline_recipe(recipe); inline_ok=rr is not None
            if rr is not None:
                compiler=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+4.0,eng.search.limits)
                compiled=compiler.compile(rr)
                if compiled is not None:
                    nodes,root=compiled; nodes_n=len(nodes); compile_ok=True; replay_ok=bool(m.replay_dag(source,nodes,root))
        except Exception as exc: err=type(exc).__name__+": "+str(exc)
    return {"horizon":horizon,"beam":BEAM,"recipe_found":found,"inline_ok":inline_ok,"compile_ok":compile_ok,"replay_ok":replay_ok,
            "proof_nodes":nodes_n,"seconds":round(time.monotonic()-started,4),"error":err,"given":given,"age_picks":age_picks,
            "target_picks":target_picks,"planner_picks":planner_picks,"planner_scored":planner_scored,"planner_children":planner_children,
            "planner_live_layers":planner_live,"proposals":proposals_total,"accepted":accepted_total}


def main():
    td,m=base.load_solver(); byid=base.rows(); out={"ratio":RATIO,"beam":BEAM,"horizons":HORIZONS,"residuals":[]}
    try:
        for rid in RESIDUAL:
            rec={"id":rid,"runs":{}}
            for h in HORIZONS: rec["runs"][str(h)]=one(m,byid[rid],h,36.0)
            out["residuals"].append(rec); print("MULTISTEP_RESIDUAL",json.dumps(rec,sort_keys=True),flush=True)
        summary={str(h):{"recipes":sum(int(x["runs"][str(h)]["recipe_found"]) for x in out["residuals"]),
                         "replays":sum(int(x["runs"][str(h)]["replay_ok"]) for x in out["residuals"]),
                         "planner_picks":sum(x["runs"][str(h)]["planner_picks"] for x in out["residuals"])} for h in HORIZONS}
        out["summary"]=summary; print("MULTISTEP_SUMMARY",json.dumps(summary,sort_keys=True),flush=True)
    finally: td.cleanup()
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")

if __name__=="__main__": main()
