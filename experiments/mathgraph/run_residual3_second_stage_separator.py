#!/usr/bin/env python3
"""Second-stage separator census inside the validated normalized-size gate.

Measurement only. Reuses the exact residual-3 continuation census and captures
its candidate rows without altering candidate generation or Vampire labels.
We then restrict to raw_size - parent_size <= 1 and seek the cheapest second
separator, including simple two-predicate conjunctions.
"""
from __future__ import annotations
import json
from pathlib import Path
import run_residual3_continuation_separator_census as c

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'experiments/mathgraph/results/residual3-second-stage-separator.json'


def confusion(rows,pred):
    tp=fp=tn=fn=0
    for r in rows:
        p=bool(pred(r)); y=bool(r['positive'])
        if p and y: tp+=1
        elif p and not y: fp+=1
        elif not p and y: fn+=1
        else: tn+=1
    recall=tp/(tp+fn) if tp+fn else 0.0
    specificity=tn/(tn+fp) if tn+fp else 0.0
    precision=tp/(tp+fp) if tp+fp else 0.0
    return {'tp':tp,'fp':fp,'tn':tn,'fn':fn,'recall':recall,'specificity':specificity,
            'precision':precision,'balanced_accuracy':(recall+specificity)/2}


def primitive_predicates(rows):
    numeric=['target_score','delta_target_score','raw_size','reduced_size','delta_size',
             'interreduce_contraction','overlap_depth','distinct_vars','lhs_size','rhs_size',
             'raw_delta_from_parent','raw_ratio_to_parent']
    categorical=['root_overlap','parent_outer','outer_side','inner_side']
    out=[]
    for key in numeric:
        vals=sorted(set(float(r['features'][key]) for r in rows))
        cuts=[(a+b)/2 for a,b in zip(vals,vals[1:])]
        if vals: cuts=[vals[0]-1e-9]+cuts+[vals[-1]+1e-9]
        for cut in cuts:
            out.append((f'{key}<={cut:g}',lambda r,k=key,t=cut: float(r['features'][k])<=t))
            out.append((f'{key}>{cut:g}',lambda r,k=key,t=cut: float(r['features'][k])>t))
    for key in categorical:
        for val in sorted(set(r['features'][key] for r in rows),key=str):
            out.append((f'{key}=={val}',lambda r,k=key,v=val: r['features'][k]==v))
            out.append((f'{key}!={val}',lambda r,k=key,v=val: r['features'][k]!=v))
    return out


def rank_record(name,metrics,kind):
    return {'name':name,'kind':kind,**metrics}


def second_stage(rows):
    gated=[r for r in rows if r['features']['raw_delta_from_parent']<=1]
    prim=primitive_predicates(gated)
    singles=[]
    for name,p in prim:
        singles.append(rank_record(name,confusion(gated,p),'single'))
    singles.sort(key=lambda z:(z['balanced_accuracy'],z['precision'],z['recall'],-z['fp']),reverse=True)

    # Only combine the strongest 40 primitive predicates: bounded, interpretable,
    # and enough to decide whether a simple conjunction closes the 8-vs-5 residual.
    top=prim[:]
    scored=[]
    for name,p in top:
        m=confusion(gated,p)
        scored.append((m['balanced_accuracy'],m['precision'],name,p))
    scored.sort(reverse=True,key=lambda x:(x[0],x[1]))
    top=scored[:40]
    pairs=[]
    for i,(_,_,na,pa) in enumerate(top):
        for _,_,nb,pb in top[i+1:]:
            m=confusion(gated,lambda r,a=pa,b=pb: a(r) and b(r))
            pairs.append(rank_record(f'({na}) AND ({nb})',m,'pair'))
    pairs.sort(key=lambda z:(z['balanced_accuracy'],z['precision'],z['recall'],-z['fp']),reverse=True)
    return {
        'gate':'raw_size - parent_size <= 1',
        'candidates':len(gated),
        'positives':sum(r['positive'] for r in gated),
        'negatives':sum(not r['positive'] for r in gated),
        'best_singles':singles[:15],
        'best_pairs':pairs[:20],
        'gated_rows':[{'positive':r['positive'],'features':r['features']} for r in gated],
    }


def main():
    captured={}
    original_features=c.features
    original_numeric=c.best_numeric
    original_cat=c.best_categorical

    def features(search,qraw,qred,parent,path,parent_outer,oside,iside):
        f=original_features(search,qraw,qred,parent,path,parent_outer,oside,iside)
        psize=c.term_size(parent.lhs)+c.term_size(parent.rhs)
        f['parent_size']=psize
        f['raw_delta_from_parent']=f['raw_size']-psize
        f['raw_ratio_to_parent']=f['raw_size']/psize if psize else 999.0
        return f

    current=[None]
    def best_numeric(rows,key):
        if current[0] is not None and current[0] not in captured:
            captured[current[0]]=rows
        return original_numeric(rows,key)
    def best_categorical(rows,key):
        if current[0] is not None and current[0] not in captured:
            captured[current[0]]=rows
        return original_cat(rows,key)

    c.features=features; c.best_numeric=best_numeric; c.best_categorical=best_categorical
    td,m=c.fp.load_solver(); byid={r['id']:r for r in c.fp.rows()}; results=[]
    try:
        for rid in c.IDS:
            current[0]=rid
            base=c.census_one(m,byid[rid])
            rows=captured.get(rid,[])
            rec={'id':rid,'base_status':base.get('status'),'base_candidates':base.get('candidates'),
                 'base_positives':base.get('positive_later_path_matches'),'second_stage':second_stage(rows) if rows else None}
            results.append(rec)
            print('SECOND_STAGE_SEPARATOR',json.dumps(rec,sort_keys=True),flush=True)
    finally:
        td.cleanup()
    pooled=[]
    for rid in c.IDS: pooled.extend(captured.get(rid,[]))
    pooled_rec=second_stage(pooled) if pooled else None
    out={'rows':results,'pooled':pooled_rec}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SECOND_STAGE_SEPARATOR_POOLED',json.dumps(pooled_rec,sort_keys=True),flush=True)

if __name__=='__main__': main()
