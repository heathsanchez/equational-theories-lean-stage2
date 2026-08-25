#!/usr/bin/env python3
"""Separator census for productive continuations after the rescued Vampire clause.

For hard1_0067 and hard3_0208:
  * recover the genuine Vampire-derived equality path;
  * identify the first path equality that target-only 796 leaves passive;
  * replay target-only search until that equality is available, then oracle-select it;
  * enumerate every legal side-complete critical-pair proposal involving it;
  * label a proposal positive iff its post-interreduce equality matches a *later*
    genuine Vampire-derived equality (a later-path match, not asserted direct ancestry);
  * compare structural features and report the best one-dimensional threshold/
    categorical separators.

This is measurement-only. It does not alter the solver policy.
"""
from __future__ import annotations
import json, math, time
from pathlib import Path
import run_residual3_fullpath_lifecycle as fp

ROOT=Path(__file__).resolve().parents[2]
IDS=('hard1_0067','hard3_0208')
OUT=ROOT/'experiments/mathgraph/results/residual3-continuation-separator-census.json'


def term_size(t):
    if getattr(t,'is_var',False): return 1
    if isinstance(t,tuple):
        if t and t[0] in ('var','v'): return 1
        if len(t)>=3: return 1+term_size(t[1])+term_size(t[2])
    # 796 terms are dataclasses in some lineage revisions.
    for lr in (('left','right'),('lhs','rhs')):
        if hasattr(t,lr[0]) and hasattr(t,lr[1]):
            return 1+term_size(getattr(t,lr[0]))+term_size(getattr(t,lr[1]))
    if hasattr(t,'args'):
        return 1+sum(term_size(x) for x in t.args)
    return 1


def vars_of(t,out=None):
    if out is None: out=set()
    if isinstance(t,tuple):
        if t and t[0] in ('var','v'):
            out.add(str(t[1])); return out
        for x in t[1:]: vars_of(x,out)
        return out
    if getattr(t,'is_var',False): out.add(str(getattr(t,'name',t))); return out
    if hasattr(t,'args'):
        for x in t.args: vars_of(x,out)
    else:
        for a in ('left','right'):
            if hasattr(t,a): vars_of(getattr(t,a),out)
    return out


def features(search,qraw,qred,parent,path,parent_outer,oside,iside):
    raw_size=term_size(qraw.lhs)+term_size(qraw.rhs)
    red_size=term_size(qred.lhs)+term_size(qred.rhs)
    psize=term_size(parent.lhs)+term_size(parent.rhs)
    v=vars_of(qred.lhs)|vars_of(qred.rhs)
    return {
        'target_score': float(search.target_score(qred)),
        'delta_target_score': float(search.target_score(qred)-search.target_score(parent)),
        'raw_size': raw_size,
        'reduced_size': red_size,
        'delta_size': red_size-psize,
        'interreduce_contraction': raw_size-red_size,
        'overlap_depth': len(path),
        'root_overlap': int(len(path)==0),
        'parent_outer': int(parent_outer),
        'outer_side': int(oside),
        'inner_side': int(iside),
        'distinct_vars': len(v),
        'lhs_size': term_size(qred.lhs),
        'rhs_size': term_size(qred.rhs),
    }


def best_numeric(rows,key):
    vals=sorted(set(float(r['features'][key]) for r in rows))
    if not vals: return None
    cuts=[vals[0]-1e-9]+[(a+b)/2 for a,b in zip(vals,vals[1:])]+[vals[-1]+1e-9]
    best=None
    for cut in cuts:
        for direction in ('le','gt'):
            tp=tn=fpn=fn=0
            for r in rows:
                pred=(r['features'][key] <= cut) if direction=='le' else (r['features'][key] > cut)
                y=r['positive']
                if pred and y: tp+=1
                elif pred and not y: fpn+=1
                elif not pred and y: fn+=1
                else: tn+=1
            tpr=tp/(tp+fn) if tp+fn else 0.0
            tnr=tn/(tn+fpn) if tn+fpn else 0.0
            bal=(tpr+tnr)/2
            precision=tp/(tp+fpn) if tp+fpn else 0.0
            rec={'feature':key,'kind':'threshold','direction':direction,'cut':cut,'balanced_accuracy':bal,'precision':precision,'recall':tpr,'tp':tp,'fp':fpn,'tn':tn,'fn':fn}
            if best is None or (bal,precision)>(best['balanced_accuracy'],best['precision']): best=rec
    return best


def best_categorical(rows,key):
    vals=sorted(set(r['features'][key] for r in rows),key=str); best=None
    for val in vals:
        for equal in (True,False):
            tp=tn=fpn=fn=0
            for r in rows:
                pred=(r['features'][key]==val) if equal else (r['features'][key]!=val)
                y=r['positive']
                if pred and y: tp+=1
                elif pred and not y: fpn+=1
                elif not pred and y: fn+=1
                else: tn+=1
            tpr=tp/(tp+fn) if tp+fn else 0.0; tnr=tn/(tn+fpn) if tn+fpn else 0.0
            bal=(tpr+tnr)/2; precision=tp/(tp+fpn) if tp+fpn else 0.0
            rec={'feature':key,'kind':'categorical','op':'eq' if equal else 'ne','value':val,'balanced_accuracy':bal,'precision':precision,'recall':tpr,'tp':tp,'fp':fpn,'tn':tn,'fn':fn}
            if best is None or (bal,precision)>(best['balanced_accuracy'],best['precision']): best=rec
    return best


def census_one(m,r):
    source,target,vpath=fp.vampire_path(m,r)
    hits,_=fp.trace_all(m,source,target,{x['key'] for x in vpath},seconds=20.0)
    first_i=None
    for i,x in enumerate(vpath):
        if fp.status(hits[x['key']])!='selected': first_i=i; break
    if first_i is None:
        return {'id':r['id'],'status':'NO_STARVED_VAMPIRE_STEP'}
    rescue_key=vpath[first_i]['key']; later={x['key'] for x in vpath[first_i+1:]}

    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':20.0,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,'maximum_clauses':16000,'normalization_steps':384,'maximum_proof_nodes':60000})
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+20.0,limits); search=eng.search
    passive=list(search.clauses); active=[]; age={id(c):i for i,c in enumerate(passive)}; next_age=len(passive); given=0
    rescued=None
    # Reproduce target-only lifecycle until rescued clause appears, then select it.
    while passive and given<1024 and not search.expired():
        rescue_idx=next((i for i,c in enumerate(passive) if fp.clause_key(c)==rescue_key),None)
        if rescue_idx is not None:
            idx=rescue_idx; rescued=passive[idx]
        else:
            rules=[q for c in active if (q:=search.orient(c)) is not None]
            idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
        selected=passive.pop(idx)
        rules=[q for c in active if (q:=search.orient(c)) is not None]
        selected=search.interreduce(selected,rules); active.append(selected); given+=1
        if fp.clause_key(selected)==rescue_key:
            rescued=selected; break
        rules=[q for c in active if (q:=search.orient(c)) is not None]
        proposals=[]
        for oi,other in enumerate(active):
            for bo,bi,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
                for oside,outer in enumerate(fp.oriented_variants(m,bo)):
                    for iside,inner in enumerate(fp.oriented_variants(m,bi)):
                        for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                            if search.expired(): break
                            q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                            if q is None: continue
                            qr=search.interreduce(q,rules); proposals.append((search.target_score(qr),qr))
        proposals.sort(key=lambda z:z[0])
        for _,q in proposals[:search.limits['new_clauses_per_round']]:
            if search.add_clause(q): passive.append(q); age[id(q)]=next_age; next_age+=1
        new=[]; seen=set()
        for c in passive:
            if search.expired(): break
            c=search.interreduce(c,rules); k=fp.clause_key(c)
            if k in seen: continue
            seen.add(k); new.append(c)
        passive=new
    if rescued is None or fp.clause_key(rescued)!=rescue_key:
        return {'id':r['id'],'status':'RESCUE_NOT_REACHED','first_vampire_path_index':first_i}

    rules=[q for c in active if (q:=search.orient(c)) is not None]
    rows=[]; seen=set()
    # Enumerate exactly proposals in which rescued equality participates.
    for oi,other in enumerate(active):
        for parent_outer,bo,bi,a,b in ((True,rescued,other,given,oi),(False,other,rescued,oi,given)):
            for oside,outer in enumerate(fp.oriented_variants(m,bo)):
                for iside,inner in enumerate(fp.oriented_variants(m,bi)):
                    for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                        if search.expired(): break
                        q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                        if q is None: continue
                        qr=search.interreduce(q,rules); k=fp.clause_key(qr)
                        sig=(k,parent_outer,oside,iside,tuple(path))
                        if sig in seen: continue
                        seen.add(sig)
                        rows.append({'positive':k in later,'later_path_match':k in later,'features':features(search,q,qr,rescued,path,parent_outer,oside,iside)})
    pos=sum(rw['positive'] for rw in rows); neg=len(rows)-pos
    numeric=['target_score','delta_target_score','raw_size','reduced_size','delta_size','interreduce_contraction','overlap_depth','distinct_vars','lhs_size','rhs_size']
    categorical=['root_overlap','parent_outer','outer_side','inner_side']
    seps=[x for k in numeric if (x:=best_numeric(rows,k)) is not None]+[x for k in categorical if (x:=best_categorical(rows,k)) is not None]
    seps.sort(key=lambda x:(x['balanced_accuracy'],x['precision'],x['recall']),reverse=True)
    return {
        'id':r['id'],'status':'COMPLETE','first_vampire_path_index':first_i,
        'rescue_formula':vpath[first_i]['formula'],'later_vampire_equalities':len(later),
        'candidates':len(rows),'positive_later_path_matches':pos,'negative_candidates':neg,
        'best_separators':seps[:12],
        'positive_feature_rows':[rw['features'] for rw in rows if rw['positive']][:20],
    }


def main():
    td,m=fp.load_solver(); byid={r['id']:r for r in fp.rows()}; out=[]
    try:
        for rid in IDS:
            rec=census_one(m,byid[rid]); out.append(rec)
            print('SEPARATOR_CENSUS',json.dumps(rec,sort_keys=True),flush=True)
    finally: td.cleanup()
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps({'rows':out},indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()
