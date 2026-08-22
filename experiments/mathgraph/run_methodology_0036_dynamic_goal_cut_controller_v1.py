#!/usr/bin/env python3
import json, sys
from pathlib import Path
from datasets import load_dataset

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path: sys.path.insert(0,str(HERE))
import run_methodology_0036_cut_ranking_tournament_v1 as tour
import run_methodology_0036_goal_cut_descaffold_v1 as desc

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-dynamic-goal-cut-controller-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-dynamic-goal-cut-controller-v1.json'
RID='evaluation_normal_0036'

def state_distance(m,s,target):
    st=tour.cut.component_state(m,s,target,40)
    if st is None:return None,None
    return (0 if st.get('connected') else st.get('cross_distance')),st

def select_raw(m,s,target,cands):
    current,_=state_distance(m,s,target)
    scored=[]
    for c in cands:
        d=desc.simulate_goal_separation(m,s,target,c)
        scored.append((999999 if d is None else d,c['key'],c))
    scored.sort(key=lambda x:(x[0],x[1]))
    strict=sum(1 for d,_,_ in scored if current is not None and d<current)
    return scored[0][2],scored[0][0],strict

def select_target(cands,current):
    ranked=sorted(cands,key=lambda c:(-c['target_coverage'],c['key']))
    return ranked[0],ranked[0]['predicted_cut_distance'],sum(1 for c in cands if c['predicted_cut_distance']<current)

def run_arm(m,source,target,cfg,mode,max_steps,pool_limit):
    s,old,new,admitted,edges,initial_st=tour.frozen_state(m,source,target,cfg)
    rows=[]; best=0 if initial_st.get('connected') else initial_st['cross_distance']; closure_step=None; stall=False
    for step in range(1,max_steps+1):
        pre_st=tour.cut.component_state(m,s,target,40)
        if pre_st is None:
            stall=True; break
        pre_d=0 if pre_st.get('connected') else pre_st['cross_distance']
        if pre_st.get('connected'):
            closure_step=step-1; break
        cands,anchors,fills=tour.make_pool(m,s,source,target,pre_st,pool_limit)
        if not cands:
            stall=True; rows.append({'step':step,'pre_distance':pre_d,'post_distance':pre_d,'candidate_pool':0,'strict_contractors':0,'status':'NO_CANDIDATES'}); break
        if mode=='raw': chosen,pred,strict=select_raw(m,s,target,cands)
        else: chosen,pred,strict=select_target(cands,pre_d)
        nid=s.ensure_source_mapping(chosen['mapping'],False,'dynamic-goal-cut-controller',step)
        added=nid is not None
        post_st=tour.cut.component_state(m,s,target,40)
        post_d=None if post_st is None else (0 if post_st.get('connected') else post_st['cross_distance'])
        root=s.shortest_path(); replay=False
        if root is not None: replay=m.replay_dag(source,s.nodes,root,maximum_term_size=19)
        rows.append({'step':step,'pre_distance':pre_d,'post_distance':post_d,'candidate_pool':len(cands),'strict_contractors':strict,'predicted_selected_distance':pred,'selected_added':added,'selected':tour.public_candidate(m,chosen),'lhs_component_size':None if post_st is None else post_st.get('lhs_size'),'rhs_component_size':None if post_st is None else post_st.get('rhs_size'),'connected':bool(post_st and post_st.get('connected')),'replayable_closure':replay})
        if post_d is not None: best=min(best,post_d)
        if replay:
            closure_step=step; break
        if strict==0 or post_d is None or post_d>=pre_d:
            stall=True; break
    return {'rows':rows,'best_distance':best,'closure_step':closure_step,'stalled':stall,'admitted_reentries':admitted,'reentry_edges':edges,'initial_lhs_size':initial_st.get('lhs_size'),'initial_rhs_size':initial_st.get('rhs_size'),'initial_distance':0 if initial_st.get('connected') else initial_st.get('cross_distance')}

def first_distance(rows,d):
    for r in rows:
        if r.get('post_distance') is not None and r['post_distance']<=d:return r['step']
    return None

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] and RID not in p['sealed_transfer_ids']
    m=tour.cut.load_hist(); row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    s0,old0,new0,adm0,ed0,st0=tour.frozen_state(m,source,target,cfg)
    ok=(s0.max_term_size==19 and len(old0)==45 and adm0==9 and ed0==9 and st0 is not None and st0.get('cross_distance')==10 and st0.get('lhs_size')==4 and st0.get('rhs_size')==19)
    A=run_arm(m,source,target,cfg,'raw',p['maximum_steps'],p['fixed_limits']['candidate_pool_limit']) if ok else None
    B=run_arm(m,source,target,cfg,'target',p['maximum_steps'],p['fixed_limits']['candidate_pool_limit']) if ok else None
    matched=bool(ok and A and B and A['initial_distance']==B['initial_distance']==10 and A['reentry_edges']==B['reentry_edges']==9)
    if not matched: decision='MEASUREMENT_FAILURE'
    elif A['closure_step'] is not None and (B['closure_step'] is None or A['closure_step']<=B['closure_step']): decision='DYNAMIC_RAW_GOAL_CLOSES'
    elif A['best_distance']<B['best_distance']: decision='DYNAMIC_RAW_GOAL_ADVANTAGE'
    elif A['best_distance']==B['best_distance']:
        da=first_distance(A['rows'],A['best_distance']); db=first_distance(B['rows'],B['best_distance'])
        if da is not None and (db is None or da<db): decision='DYNAMIC_RAW_GOAL_ADVANTAGE'
        elif A['stalled'] and A['closure_step'] is None: decision='DYNAMIC_RAW_GOAL_STALLS'
        else: decision='CONTROL_EQUIVALENT_OR_BETTER'
    elif A['stalled'] and A['closure_step'] is None: decision='DYNAMIC_RAW_GOAL_STALLS'
    else: decision='CONTROL_EQUIVALENT_OR_BETTER'
    out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':matched,'A_DYNAMIC_RAW_GOAL':A,'B_DYNAMIC_TARGET_COVERAGE':B,'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
