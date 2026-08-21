#!/usr/bin/env python3
"""Recursive Residual Refactoring (RRR) gate.

Question: can ONE unchanged residual-driven refactoring operator act usefully on
three different object levels?

  L0  operator / representation candidates
  L1  residual representations
  L2  representation-selection strategies (meta-policy)

This is a retrospective reconstruction gate.  It intentionally does NOT claim
prospective autonomous invention.  A later sealed run must freeze the operator
and apply it to unseen episodes.

The core `refactor` function contains no level-specific logic.  It receives
rows with numeric facets plus an externally measured binary response, begins
from one quotient class, and greedily SPLITs only when a facet makes verified
responses more distinguishable.  Leaves with intervention-equivalent response
are then MERGEd.  The exact same function is used at L0/L1/L2.
"""
from __future__ import annotations

import hashlib
import importlib.util
import inspect
import json
import math
import random
import statistics
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RESULTS = HERE / "results"
OUT = RESULTS / "recursive-residual-refactoring-gate.json"
SEED = 20260821


def entropy(y):
    if not y:
        return 0.0
    p = sum(bool(v) for v in y) / len(y)
    if p <= 0.0 or p >= 1.0:
        return 0.0
    return -(p * math.log2(p) + (1-p) * math.log2(1-p))


def candidate_thresholds(vals):
    u = sorted(set(float(v) for v in vals if math.isfinite(float(v))))
    if len(u) < 2:
        return []
    if len(u) <= 10:
        return [(a+b)/2 for a,b in zip(u,u[1:])]
    qs = []
    for q in (0.15,0.25,0.35,0.5,0.65,0.75,0.85):
        i = min(len(u)-2, max(0, int(q*(len(u)-1))))
        qs.append((u[i]+u[i+1])/2)
    return sorted(set(qs))


def best_split(rows, indices, features, min_leaf=3, penalty=0.015):
    base = entropy([rows[i]["y"] for i in indices])
    best = None
    for f in features:
        vals = [rows[i]["x"].get(f,0.0) for i in indices]
        for t in candidate_thresholds(vals):
            a = [i for i in indices if rows[i]["x"].get(f,0.0) <= t]
            b = [i for i in indices if rows[i]["x"].get(f,0.0) > t]
            if len(a) < min_leaf or len(b) < min_leaf:
                continue
            h = (len(a)*entropy([rows[i]["y"] for i in a]) + len(b)*entropy([rows[i]["y"] for i in b]))/len(indices)
            gain = base - h - penalty
            cand = (gain, f, t, a, b)
            if best is None or cand[:3] > best[:3]:
                best = cand
    return best


def refactor(rows, features, max_splits=3, min_leaf=3, penalty=0.015):
    """ONE developmental operator used unchanged at every level.

    Start maximally compressed; SPLIT only when response evidence distinguishes
    a facet; then MERGE leaves whose empirical response is indistinguishable at
    the coarse 0/0.5/1 response code.  Returns a compact partition and rules.
    """
    leaves = [list(range(len(rows)))]
    rules = []
    for _ in range(max_splits):
        winner = None
        for li,idx in enumerate(leaves):
            s = best_split(rows, idx, features, min_leaf=min_leaf, penalty=penalty)
            if s and s[0] > 1e-12:
                cand = (s[0], li, s)
                if winner is None or cand[0] > winner[0]:
                    winner = cand
        if winner is None:
            break
        _, li, s = winner
        gain,f,t,a,b = s
        leaves[li:li+1] = [a,b]
        rules.append({"op":"SPLIT","feature":f,"threshold":t,"gain":gain})

    # MERGE only response-equivalent leaves.  The coarse code prevents tiny
    # sample-frequency noise from manufacturing distinctions.
    def code(idx):
        p = sum(rows[i]["y"] for i in idx)/len(idx)
        return 0 if p < .25 else 1 if p > .75 else .5
    merged=[]
    for leaf in leaves:
        c=code(leaf)
        hit=None
        for j,(mc,midx) in enumerate(merged):
            if mc==c:
                hit=j;break
        if hit is None:
            merged.append((c,list(leaf)))
        else:
            merged[hit][1].extend(leaf)
            rules.append({"op":"MERGE","response_code":c})
    leaves=[idx for _,idx in merged]

    models=[]
    for idx in leaves:
        p=sum(rows[i]["y"] for i in idx)/len(idx)
        models.append({"indices":idx,"p":p,"pred":p>=.5})
    return {"rules":rules,"leaves":models}


def assign_from_rules(row, model, train_rows):
    # Reconstruct split path by applying the recorded SPLIT sequence as a tiny
    # decision list.  For robustness with merges, prediction is nearest leaf
    # centroid in the selected split coordinates.
    fs=[]
    for r in model["rules"]:
        if r["op"]=="SPLIT" and r["feature"] not in fs:
            fs.append(r["feature"])
    if not fs:
        p=sum(r["y"] for r in train_rows)/len(train_rows)
        return p>=.5
    best=None
    for leaf in model["leaves"]:
        pts=[train_rows[i] for i in leaf["indices"]]
        centroid={f:statistics.mean(p["x"].get(f,0.0) for p in pts) for f in fs}
        scales={f:max(1e-9,statistics.pstdev([p["x"].get(f,0.0) for p in train_rows])) for f in fs}
        d=sum(((row["x"].get(f,0.0)-centroid[f])/scales[f])**2 for f in fs)
        cand=(d,leaf["pred"])
        if best is None or cand[0]<best[0]:best=cand
    return best[1]


def bacc(y,p):
    pos=sum(bool(v) for v in y); neg=len(y)-pos
    if not pos or not neg:return .5
    tp=sum(bool(a) and bool(b) for a,b in zip(y,p)); tn=sum((not bool(a)) and (not bool(b)) for a,b in zip(y,p))
    return .5*(tp/pos+tn/neg)


def stable_split(rows, key="id"):
    tr=[];te=[]
    for r in rows:
        h=int(hashlib.sha256(str(r[key]).encode()).hexdigest()[:8],16)%5
        (te if h==0 else tr).append(r)
    return tr,te


def evaluate(rows, features, max_splits=3):
    train,test=stable_split(rows)
    m=refactor(train,features,max_splits=max_splits)
    pred=[assign_from_rules(r,m,train) for r in test]
    y=[r["y"] for r in test]
    base=max(sum(y),len(y)-sum(y))/len(y) if y else 0.0
    # deterministic shuffled-label falsifier
    sh=[dict(r,y=train[(i*37+11)%len(train)]["y"]) for i,r in enumerate(train)]
    sm=refactor(sh,features,max_splits=max_splits)
    sp=[assign_from_rules(r,sm,sh) for r in test]
    return {"n":len(rows),"train":len(train),"test":len(test),"positive":sum(r["y"] for r in rows),
            "heldout_bacc":bacc(y,pred),"majority_accuracy":base,"shuffled_bacc":bacc(y,sp),
            "model":{"rules":m["rules"],"leaf_count":len(m["leaves"])} }


def load_module(path,name):
    spec=importlib.util.spec_from_file_location(name,path);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod


def ensure_reification():
    p=RESULTS/"missing-subterm-reification-gate.json"
    if not p.exists():
        subprocess.run([sys.executable,str(HERE/"run_missing_subterm_reification_gate.py")],check=True)
    return json.loads(p.read_text())


def level0():
    d=ensure_reification()
    rows=[]
    # We deliberately use only numeric properties of the produced equality,
    # never arm identity.  y is the externally measured target-structure hit.
    for arm in ("top_B","top_C"):
        for j,z in enumerate(d.get(arm,[])):
            lhs,rhs=z["lhs"],z["rhs"]
            s=lhs+" = "+rhs
            x={
              "activation":float(z.get("activation",0)),
              "lhs_len":len(lhs),"rhs_len":len(rhs),"paren_count":s.count("("),
              "x_count":s.count("x"),"y_count":s.count("y"),"z_count":s.count("z"),
              "side_len_gap":abs(len(lhs)-len(rhs)),
            }
            rows.append({"id":f"{arm}:{j}:{hashlib.sha1(s.encode()).hexdigest()[:8]}","x":x,"y":int(z.get("missing_hits",0)>0)})
    features=sorted(rows[0]["x"]) if rows else []
    return evaluate(rows,features,max_splits=3)


def level1():
    rrt=load_module(HERE/"run_residual_representation_tournament.py","rrt_rrr")
    fp=RESULTS/"contextual_development_frozen/sample_200_development.json"
    dp=RESULTS/"contextual_development_all/sample_200_development.json"
    f={r["id"]:r for r in json.loads(fp.read_text())}; d={r["id"]:r for r in json.loads(dp.read_text())}
    rows=[]
    for rid in sorted(set(f)&set(d)):
        x,fm,dm=rrt.feat(f[rid],d[rid])
        # Prospective/static residual facets only; verdict and post-intervention diffs excluded.
        sx={k:float(v) for k,v in x.items() if k.startswith("static.") and k!="static.true_problem" and isinstance(v,(int,float,bool))}
        y=int(any(m.get("portfolio")=="target-narrowing" for m in dm))
        rows.append({"id":rid,"x":sx,"y":y})
    return evaluate(rows,sorted(rows[0]["x"]),max_splits=3)


def level2():
    p=RESULTS/"residual-factorization-optimum.json"
    if not p.exists():subprocess.run([sys.executable,str(HERE/"run_residual_factorization_optimum.py")],check=True)
    d=json.loads(p.read_text()); rows=[]
    for track,t in d.get("tracks",{}).items():
        entries=t.get("top10",[])+t.get("best_by_k",[])
        # dedupe strategy configurations
        seen=set(); vals=[float(e.get("symmetric_transfer_bacc",.5)) for e in entries]
        med=statistics.median(vals) if vals else .5
        for e in entries:
            key=(track,e.get("process"),e.get("k"),tuple(e.get("context_factors",[])))
            if key in seen:continue
            seen.add(key)
            fs=e.get("context_factors",[])
            x={
              "k":float(e.get("k",0)),
              "process_signal":float(e.get("process")=="signal"),
              "process_diverse":float(e.get("process")=="diverse"),
              "process_split":float(e.get("process")=="split"),
              "structural_factor_count":float(sum(not any(w in f for w in ("elapsed","persistence","replay_seconds","certificate_bytes")) for f in fs)),
              "operational_factor_count":float(sum(any(w in f for w in ("elapsed","persistence","replay_seconds","certificate_bytes")) for f in fs)),
            }
            # Outcome is cross-lineage transfer quality, not objective/factor-jaccard.
            y=int(float(e.get("symmetric_transfer_bacc",.5))>=med)
            rows.append({"id":"|".join(map(str,key[:3]))+"|"+hashlib.sha1(str(key[3]).encode()).hexdigest()[:8],"x":x,"y":y})
    return evaluate(rows,sorted(rows[0]["x"]),max_splits=3)


def main():
    core_hash=hashlib.sha256(inspect.getsource(refactor).encode()).hexdigest()
    levels={"L0_operator_representation":level0(),"L1_residual_representation":level1(),"L2_representation_selection_strategy":level2()}
    # Conservative retrospective gate: useful held-out discrimination at every
    # level, above shuffled control. This is NOT the final prospective gate.
    passes={k:(v["heldout_bacc"]>=.65 and v["heldout_bacc"]>=v["shuffled_bacc"]+.05) for k,v in levels.items()}
    out={"schema":"mathgraph.recursive-residual-refactoring.v1","protocol":{"retrospective_reconstruction":True,"same_refactor_function_all_levels":True,"level_specific_logic_inside_refactor":False,"core_refactor_sha256":core_hash,"max_splits":3,"heldout_hash_split":True,"shuffled_label_falsifier":True},"levels":levels,"level_pass":passes,"decision":"RETROSPECTIVE_PASS" if all(passes.values()) else "PARTIAL_OR_FAIL","next_required":"Freeze the exact core refactor hash and run prospective problem-disjoint episodes at all three levels with causal ablations."}
    RESULTS.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n");print(json.dumps(out,indent=2,sort_keys=True))

if __name__=="__main__":main()
