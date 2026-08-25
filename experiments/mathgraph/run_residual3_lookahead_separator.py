#!/usr/bin/env python3
"""One-step future-action separator inside the validated structural residual.

For hard1_0067 and hard3_0208, reproduce the exact rescued-clause census,
retain only candidates satisfying the validated local gate, and measure what
each candidate enables in one further legal superposition step. Measurement
only: no prover policy is changed here.
"""
from __future__ import annotations
import json, time
from pathlib import Path
import run_residual3_fullpath_lifecycle as fp
import run_residual3_continuation_separator_census as c

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'experiments/mathgraph/results/residual3-lookahead-separator.json'
IDS=('hard1_0067','hard3_0208')


def score0(search,q):
    z=search.target_score(q)
    return float(z[0] if isinstance(z,tuple) else z)


def distinct_vars(q):
    return len(c.vars_of(q.lhs)|c.vars_of(q.rhs))


def size(q):
    return c.term_size(q.lhs)+c.term_size(q.rhs)


def gate(qraw,qred,parent):
    return size(qraw) <= size(parent)+1 and distinct_vars(qred) <= 3 and size(qred) < size(parent)


def confusion(rows,key,direction,cut):
    tp=fpn=tn=fn=0
    for r in rows:
        v=float(r['lookahead'][key]); pred=v<=cut if direction=='le' else v>cut; y=r['positive']
        if pred and y: tp+=1
        elif pred: fpn+=1
        elif y: fn+=1
        else: tn+=1
    rec=tp/(tp+fn) if tp+fn else 0.0; spec=tn/(tn+fpn) if tn+fpn else 0.0
    prec=tp/(tp+fpn) if tp+fpn else 0.0
    return {'feature':key,'direction':direction,'cut':cut,'tp':tp,'fp':fpn,'tn':tn,'fn':fn,
            'recall':rec,'specificity':spec,'precision':prec,'balanced_accuracy':(rec+spec)/2}


def best_numeric(rows,key):
    vals=sorted(set(float(r['lookahead'][key]) for r in rows))
    if not vals: return None
    cuts=[vals[0]-1e-9]+[(a+b)/2 for a,b in zip(vals,vals[1:])]+[vals[-1]+1e-9]
    cand=[confusion(rows,key,d,cut) for cut in cuts for d in ('le','gt')]
    return max(cand,key=lambda z:(z['balanced_accuracy'],z['precision'],z['recall'],-z['fp']))


def prepare(m,r):
    source,target,vpath=fp.vampire_path(m,r)
    hits,_=fp.trace_all(m,source,target,{x['key'] for x in vpath},seconds=20.0)
    first_i=next((i for i,x in enumerate(vpath) if fp.status(hits[x['key']])!='selected'),None)
    if first_i is None: return None,{'id':r['id'],'status':'NO_STARVED_VAMPIRE_STEP'}
    rescue_key=vpath[first_i]['key']; later=[x['key'] for x in vpath[first_i+1:]]
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':28.0,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,
                   'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,
                   'maximum_clauses':16000,'normalization_steps':384,'maximum_proof_nodes':60000})
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+28.0,limits); search=eng.search
    passive=list(search.clauses); active=[]; age={id(x):i for i,x in enumerate(passive)}; next_age=len(passive); given=0
    rescued=None
    while passive and given<1024 and not search.expired():
        rescue_idx=next((i for i,x in enumerate(passive) if fp.clause_key(x)==rescue_key),None)
        if rescue_idx is not None: idx=rescue_idx
        else:
            idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
        rules=[q for x in active if (q:=search.orient(x)) is not None]
        selected=search.interreduce(passive.pop(idx),rules); active.append(selected); given+=1
        if fp.clause_key(selected)==rescue_key: rescued=selected; break
        rules=[q for x in active if (q:=search.orient(x)) is not None]; proposals=[]
        for oi,other in enumerate(active):
            for bo,bi,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
                for oside,outer in enumerate(fp.oriented_variants(m,bo)):
                    for iside,inner in enumerate(fp.oriented_variants(m,bi)):
                        for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                            if search.expired(): break
                            q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                            if q is not None:
                                qr=search.interreduce(q,rules); proposals.append((search.target_score(qr),qr))
        proposals.sort(key=lambda z:z[0])
        for _,q in proposals[:search.limits['new_clauses_per_round']]:
            if search.add_clause(q): passive.append(q); age[id(q)]=next_age; next_age+=1
        new=[]; seen=set()
        for x in passive:
            if search.expired(): break
            x=search.interreduce(x,rules); k=fp.clause_key(x)
            if k not in seen: seen.add(k); new.append(x)
        passive=new
    if rescued is None:
        return None,{'id':r['id'],'status':'RESCUE_NOT_REACHED','first_vampire_path_index':first_i}
    return (eng,search,active,rescued,given,later,vpath,first_i),None


def child_stats(m,search,active,parent,later,next_key):
    rules=[q for x in active if (q:=search.orient(x)) is not None]
    # Include the candidate itself as a potential rewrite rule where orientable.
    pr=search.orient(parent)
    rules2=rules+([pr] if pr is not None else [])
    seen=set(); legal=passing=0; best_delta=10**9; best_target_delta=10**9
    later_hits=next_hits=0; psize=size(parent); pscore=score0(search,parent)
    for oi,other in enumerate(active+[parent]):
        for bo,bi,a,b in ((parent,other,9999,oi),(other,parent,oi,9999)):
            for oside,outer in enumerate(fp.oriented_variants(m,bo)):
                for iside,inner in enumerate(fp.oriented_variants(m,bi)):
                    for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                        if search.expired(): break
                        q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                        if q is None: continue
                        qr=search.interreduce(q,rules2); k=fp.clause_key(qr)
                        if k in seen: continue
                        seen.add(k); legal+=1
                        d=size(qr)-psize; td=score0(search,qr)-pscore
                        best_delta=min(best_delta,d); best_target_delta=min(best_target_delta,td)
                        if gate(q,qr,parent): passing+=1
                        if k in later: later_hits+=1
                        if next_key is not None and k==next_key: next_hits+=1
    return {'legal_children':legal,'gate_children':passing,
            'best_child_delta_size':best_delta if legal else 999.0,
            'best_child_target_delta':best_target_delta if legal else 999.0,
            'later_path_children':later_hits,'next_path_children':next_hits,
            'has_later_path_child':int(later_hits>0),'has_next_path_child':int(next_hits>0)}


def census_one(m,r):
    state,err=prepare(m,r)
    if err: return err
    eng,search,active,rescued,given,later,vpath,first_i=state
    rules=[q for x in active if (q:=search.orient(x)) is not None]
    rows=[]; seen=set(); next_key=later[0] if later else None
    for oi,other in enumerate(active):
        for parent_outer,bo,bi,a,b in ((True,rescued,other,given,oi),(False,other,rescued,oi,given)):
            for oside,outer in enumerate(fp.oriented_variants(m,bo)):
                for iside,inner in enumerate(fp.oriented_variants(m,bi)):
                    for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                        if search.expired(): break
                        q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                        if q is None: continue
                        qr=search.interreduce(q,rules); k=fp.clause_key(qr); sig=(k,parent_outer,oside,iside,tuple(path))
                        if sig in seen: continue
                        seen.add(sig)
                        if not gate(q,qr,rescued): continue
                        rows.append({'positive':k in set(later),'formula_key':str(k),
                                     'local':{'raw_size':size(q),'reduced_size':size(qr),'distinct_vars':distinct_vars(qr)},
                                     'lookahead':child_stats(m,search,active,qr,set(later),next_key)})
    keys=['legal_children','gate_children','best_child_delta_size','best_child_target_delta',
          'later_path_children','next_path_children','has_later_path_child','has_next_path_child']
    seps=[best_numeric(rows,k) for k in keys]; seps=[x for x in seps if x]
    seps.sort(key=lambda z:(z['balanced_accuracy'],z['precision'],z['recall'],-z['fp']),reverse=True)
    return {'id':r['id'],'status':'COMPLETE','first_vampire_path_index':first_i,'rescue_formula':vpath[first_i]['formula'],
            'candidates':len(rows),'positives':sum(x['positive'] for x in rows),'negatives':sum(not x['positive'] for x in rows),
            'best_lookahead_separators':seps[:12],'rows':rows}


def main():
    td,m=fp.load_solver(); byid={r['id']:r for r in fp.rows()}; out=[]
    try:
        for rid in IDS:
            rec=census_one(m,byid[rid]); out.append(rec)
            print('LOOKAHEAD_SEPARATOR',json.dumps(rec,sort_keys=True),flush=True)
    finally: td.cleanup()
    pooled=[x for rec in out if rec.get('status')=='COMPLETE' for x in rec['rows']]
    keys=['legal_children','gate_children','best_child_delta_size','best_child_target_delta',
          'later_path_children','next_path_children','has_later_path_child','has_next_path_child']
    seps=[best_numeric(pooled,k) for k in keys] if pooled else []; seps=[x for x in seps if x]
    seps.sort(key=lambda z:(z['balanced_accuracy'],z['precision'],z['recall'],-z['fp']),reverse=True)
    pool={'candidates':len(pooled),'positives':sum(x['positive'] for x in pooled),'negatives':sum(not x['positive'] for x in pooled),
          'best_lookahead_separators':seps[:16]}
    result={'rows':out,'pooled':pool}; OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('LOOKAHEAD_SEPARATOR_POOLED',json.dumps(pool,sort_keys=True),flush=True)

if __name__=='__main__': main()
