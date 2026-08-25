#!/usr/bin/env python3
"""Measure one-step continuation-corridor shape on the frozen 8-vs-5 residual.

Candidate admission is exactly the earlier normalized raw-size residual:
raw_size(candidate) <= size(rescued_parent)+1.  No prover policy changes.
We augment each candidate with distributional properties of all unique legal
one-step children, then test scalar separators over the same 8 positives and
5 negatives used by the validated lookahead run.
"""
from __future__ import annotations
import json, math, statistics
from pathlib import Path
import run_residual3_lookahead_separator as base

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'experiments/mathgraph/results/residual3-corridor-separator.json'


def raw_gate(qraw, qred, parent):
    return base.size(qraw) <= base.size(parent) + 1


def corridor_child_stats(m, search, active, parent, later, next_key):
    rules=[q for x in active if (q:=search.orient(x)) is not None]
    pr=search.orient(parent)
    rules2=rules+([pr] if pr is not None else [])
    seen=set(); deltas=[]; target_deltas=[]; passing=0; later_hits=0; next_hits=0
    psize=base.size(parent); pscore=base.score0(search,parent)
    for oi,other in enumerate(active+[parent]):
        for bo,bi,a,b in ((parent,other,9999,oi),(other,parent,oi,9999)):
            for oside,outer in enumerate(base.fp.oriented_variants(m,bo)):
                for iside,inner in enumerate(base.fp.oriented_variants(m,bi)):
                    for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                        if search.expired(): break
                        q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                        if q is None: continue
                        qr=search.interreduce(q,rules2); k=base.fp.clause_key(qr)
                        if k in seen: continue
                        seen.add(k)
                        d=base.size(qr)-psize; td=base.score0(search,qr)-pscore
                        deltas.append(float(d)); target_deltas.append(float(td))
                        if raw_gate(q,qr,parent): passing+=1
                        if k in later: later_hits+=1
                        if next_key is not None and k==next_key: next_hits+=1
    n=len(deltas)
    if not n:
        return {k:999.0 for k in ('best_child_delta_size','best_child_target_delta','mean_child_delta_size','median_child_delta_size','stdev_child_delta_size','child_delta_span','mean_child_target_delta','median_child_target_delta')} | {
            'legal_children':0,'gate_children':0,'later_path_children':0,'next_path_children':0,
            'has_later_path_child':0,'has_next_path_child':0,'rawgate_fraction':0.0,'target_improving_fraction':0.0,
            'moderate_contraction_fraction':0.0,'nonextreme_fraction':0.0,'later_path_fraction':0.0}
    mean_d=statistics.fmean(deltas); med_d=statistics.median(deltas)
    sd_d=statistics.pstdev(deltas) if n>1 else 0.0
    mean_t=statistics.fmean(target_deltas); med_t=statistics.median(target_deltas)
    return {
        'legal_children':n,'gate_children':passing,
        'best_child_delta_size':min(deltas),'best_child_target_delta':min(target_deltas),
        'later_path_children':later_hits,'next_path_children':next_hits,
        'has_later_path_child':int(later_hits>0),'has_next_path_child':int(next_hits>0),
        'mean_child_delta_size':mean_d,'median_child_delta_size':float(med_d),
        'stdev_child_delta_size':sd_d,'child_delta_span':max(deltas)-min(deltas),
        'mean_child_target_delta':mean_t,'median_child_target_delta':float(med_t),
        'rawgate_fraction':passing/n,
        'target_improving_fraction':sum(x<0 for x in target_deltas)/n,
        # Broad, source-independent corridor summaries.  -6..0 contains the
        # productive one-step contraction scale observed in both residuals;
        # >-7 is the prior pooled best-child boundary, measured here as a
        # population fraction rather than an extremum.
        'moderate_contraction_fraction':sum(-6 <= x <= 0 for x in deltas)/n,
        'nonextreme_fraction':sum(x > -7 for x in deltas)/n,
        'later_path_fraction':later_hits/n,
    }


def main():
    base.gate=raw_gate
    base.child_stats=corridor_child_stats
    td,m=base.fp.load_solver(); byid={r['id']:r for r in base.fp.rows()}; out=[]
    try:
        for rid in base.IDS:
            rec=base.census_one(m,byid[rid]); out.append(rec)
            print('CORRIDOR_SEPARATOR',json.dumps(rec,sort_keys=True),flush=True)
    finally:
        td.cleanup()
    pooled=[x for rec in out if rec.get('status')=='COMPLETE' for x in rec['rows']]
    keys=['legal_children','gate_children','best_child_delta_size','best_child_target_delta',
          'later_path_children','next_path_children','mean_child_delta_size','median_child_delta_size',
          'stdev_child_delta_size','child_delta_span','mean_child_target_delta','median_child_target_delta',
          'rawgate_fraction','target_improving_fraction','moderate_contraction_fraction','nonextreme_fraction',
          'later_path_fraction']
    seps=[base.best_numeric(pooled,k) for k in keys] if pooled else []
    seps=[x for x in seps if x]
    seps.sort(key=lambda z:(z['balanced_accuracy'],z['precision'],z['recall'],-z['fp']),reverse=True)
    pool={'candidates':len(pooled),'positives':sum(x['positive'] for x in pooled),
          'negatives':sum(not x['positive'] for x in pooled),'best_corridor_separators':seps[:24]}
    result={'rows':out,'pooled':pool}; OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('CORRIDOR_SEPARATOR_POOLED',json.dumps(pool,sort_keys=True),flush=True)

if __name__=='__main__': main()
