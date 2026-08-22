#!/usr/bin/env python3
import json, sys
from pathlib import Path
from datasets import load_dataset

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path: sys.path.insert(0,str(HERE))
import run_methodology_0036_cut_ranking_tournament_v1 as tour

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-cut-ranking-prefix-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-cut-ranking-prefix-v1.json'
RID='evaluation_normal_0036'

def traj(m,source,target,cfg,ranking,budgets):
    rows=[]
    for k in budgets:
        sel=ranking[:k]
        arm=tour.apply_arm(m,source,target,cfg,sel)
        rows.append({
            'k':k,
            'selected':len(sel),
            'post_cross_distance':arm['post_cross_distance'],
            'connected':arm['connected'],
            'replayable_closure':arm['replayable_closure'],
            'added':arm['added']
        })
    return rows

def first_contract(rows):
    for r in rows:
        d=0 if r['connected'] else r['post_cross_distance']
        if d is not None and d<10: return r['k']
    return None

def score(r):
    return (0 if r['connected'] else r['post_cross_distance'], 0 if r['replayable_closure'] else 1)

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] and RID not in p['sealed_transfer_ids']
    m=tour.cut.load_hist()
    row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    s,old,new,admitted,edges,st=tour.frozen_state(m,source,target,cfg)
    candidates,anchors,fills=tour.make_pool(m,s,source,target,st,p['parent_evidence']['candidate_pool_count'])
    A=tour.select(candidates,len(candidates),'target'); B=tour.select(candidates,len(candidates),'cut')
    ok=(s.max_term_size==19 and len(old)==45 and admitted==9 and edges==9 and st is not None and st.get('cross_distance')==10 and st.get('lhs_size')==4 and st.get('rhs_size')==19 and len(candidates)==35 and sum(c['predicted_cut_distance']<10 for c in candidates)==15)
    budgets=p['prefix_budgets']
    ta=traj(m,source,target,cfg,A,budgets) if ok else []
    tb=traj(m,source,target,cfg,B,budgets) if ok else []
    for ra,rb in zip(ta,tb):
        ra['prefix_overlap']=len({c['key'] for c in A[:ra['k']]} & {c['key'] for c in B[:rb['k']]})
        rb['prefix_overlap']=ra['prefix_overlap']
    fa=first_contract(ta); fb=first_contract(tb)
    if not ok: decision='MEASUREMENT_FAILURE'
    elif fb is not None and (fa is None or fb<fa): decision='EARLY_CUT_ADVANTAGE'
    elif fb is not None and fa==fb:
        byk={r['k']:r for r in tb}; ayk={r['k']:r for r in ta}
        if any(score(byk[k])<score(ayk[k]) for k in budgets): decision='EARLY_CUT_ADVANTAGE'
        elif all(score(byk[k])==score(ayk[k]) for k in budgets): decision='RANKINGS_EFFECTIVELY_EQUIVALENT'
        else: decision='PREDICTED_DISTANCE_NONCAUSAL'
    elif fb is None and fa is not None: decision='PREDICTED_DISTANCE_NONCAUSAL'
    else: decision='PREDICTED_DISTANCE_NONCAUSAL'
    out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':ok,'first_contraction_k':{'A_TARGET_COVERAGE':fa,'B_CUT_CONTRACTION':fb},'trajectory':{'A_TARGET_COVERAGE':ta,'B_CUT_CONTRACTION':tb},'pool':{'count':len(candidates),'contractors':sum(c['predicted_cut_distance']<10 for c in candidates),'A_first':[tour.public_candidate(m,c) for c in A[:4]],'B_first':[tour.public_candidate(m,c) for c in B[:4]]},'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
