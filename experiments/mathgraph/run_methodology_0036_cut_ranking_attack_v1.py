#!/usr/bin/env python3
import json, sys
from pathlib import Path
from datasets import load_dataset

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path: sys.path.insert(0,str(HERE))
import run_methodology_0036_cut_ranking_tournament_v1 as tour

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-cut-ranking-attack-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-cut-ranking-attack-v1.json'
RID='evaluation_normal_0036'

def ranking(candidates,mode):
    if mode=='target': return sorted(candidates,key=lambda c:(-c['target_coverage'],c['key']))
    if mode=='cut': return sorted(candidates,key=lambda c:(c['predicted_cut_distance'],c['key']))
    if mode=='wrong': return sorted(candidates,key=lambda c:(-c['predicted_cut_distance'],c['key']))
    raise ValueError(mode)

def run_traj(m,source,target,cfg,ranked,budgets):
    out=[]
    for k in budgets:
        selected=ranked[:k]
        arm=tour.apply_arm(m,source,target,cfg,selected)
        out.append({
            'k':k,
            'post_cross_distance':arm['post_cross_distance'],
            'connected':arm['connected'],
            'replayable_closure':arm['replayable_closure'],
            'added':arm['added'],
            'contractors_selected':sum(c['predicted_cut_distance']<10 for c in selected)
        })
    return out

def first(rows):
    for r in rows:
        d=0 if r['connected'] else r['post_cross_distance']
        if d is not None and d<10:return r['k']
    return None

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] and RID not in p['sealed_transfer_ids']
    m=tour.cut.load_hist(); row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    s,old,new,admitted,edges,st=tour.frozen_state(m,source,target,cfg)
    candidates,anchors,fills=tour.make_pool(m,s,source,target,st,20000)
    A=ranking(candidates,'target'); B=ranking(candidates,'cut'); C=ranking(candidates,'wrong'); budgets=p['prefix_budgets']
    ok=(s.max_term_size==19 and len(old)==45 and admitted==9 and edges==9 and st is not None and st.get('cross_distance')==10 and st.get('lhs_size')==4 and st.get('rhs_size')==19 and len(candidates)==35 and sum(c['predicted_cut_distance']<10 for c in candidates)==15)
    ta=run_traj(m,source,target,cfg,A,budgets) if ok else []; tb=run_traj(m,source,target,cfg,B,budgets) if ok else []; tc=run_traj(m,source,target,cfg,C,budgets) if ok else []
    fa,fb,fc=first(ta),first(tb),first(tc)
    if not ok: decision='MEASUREMENT_FAILURE'
    elif fb is not None and (fa is None or fb<fa) and (fc is None or fb<fc): decision='CUT_SIGNAL_CAUSAL'
    elif fb==fc or all((0 if b['connected'] else b['post_cross_distance'])==(0 if c['connected'] else c['post_cross_distance']) for b,c in zip(tb,tc)): decision='ORDERING_CONFOUND'
    else: decision='CUT_SIGNAL_WEAK'
    def head(rank): return [tour.public_candidate(m,c) for c in rank[:5]]
    out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':ok,'first_contraction_k':{'A_CUT_BLIND_TARGET':fa,'B_CUT_AWARE':fb,'C_WRONG_DIRECTION_CUT':fc},'trajectory':{'A_CUT_BLIND_TARGET':ta,'B_CUT_AWARE':tb,'C_WRONG_DIRECTION_CUT':tc},'ranking_heads':{'A':head(A),'B':head(B),'C':head(C)},'pool':{'count':len(candidates),'contractors':sum(c['predicted_cut_distance']<10 for c in candidates)},'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
