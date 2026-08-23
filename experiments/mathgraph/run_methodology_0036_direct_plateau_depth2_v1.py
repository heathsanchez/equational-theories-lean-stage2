#!/usr/bin/env python3
import copy, json, sys
from pathlib import Path
from datasets import load_dataset

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path: sys.path.insert(0,str(HERE))
import run_methodology_0036_cut_ranking_tournament_v1 as tour
import run_methodology_0036_goal_cut_descaffold_v1 as desc
import run_methodology_0036_postcontractor_factorization_v1 as post

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-direct-plateau-depth2-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-direct-plateau-depth2-v1.json'
RID='evaluation_normal_0036'

def relaxed_pool(m,s,source,target,st,cap=19,limit=100000):
    anchors,fills=post.l1_terms(m,s,target,st)
    cands,_=post.enumerate_candidates(m,s,source,target,st,anchors,fills,cap,limit)
    return cands,anchors,fills

def score_candidate(m,s,target,c):
    return desc.simulate_goal_separation(m,s,target,c)

def apply_direct(s,c,step):
    return s.ensure_source_mapping(c['mapping'],False,'direct-plateau-depth2',step)

def public(m,c,d):
    return {
        'lhs':m.render_term(c['lhs']),
        'rhs':m.render_term(c['rhs']),
        'post_separation':d,
        'max_term_size':c.get('max_term_size',max(m.term_size(c['lhs']),m.term_size(c['rhs'])))
    }

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] and RID not in p['sealed_transfer_ids']
    m=tour.cut.load_hist()
    row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    base,old,new,admitted,edges,first,nid,st=post.reconstruct_post_step(m,source,target,cfg)
    pool,anchors,fills=relaxed_pool(m,base,source,target,st,19,p['search']['maximum_second_pool']) if st is not None else ([],[],[])
    scored=[(score_candidate(m,base,target,c),c) for c in pool]
    strict0=[(d,c) for d,c in scored if d is not None and d<8]
    admissible=sorted([(d,c) for d,c in scored if d is not None and d<=8],key=lambda x:(x[0],x[1]['key']))[:p['search']['maximum_first_steps']]
    ok=(base.max_term_size==19 and len(old)==45 and admitted==9 and edges==9 and nid is not None and st is not None and not st.get('connected') and st.get('cross_distance')==8 and len(pool)==34 and len(strict0)==0)
    witness=None; best=8; exposing=0; explored=[]
    if ok:
        for i,(d1,c1) in enumerate(admissible):
            s=copy.deepcopy(base)
            n1=apply_direct(s,c1,2)
            if n1 is None:
                explored.append({'first':public(m,c1,d1),'second_pool':0,'strict_second':0,'status':'FIRST_NOT_ADDED'})
                continue
            st1=tour.cut.component_state(m,s,target,40)
            if st1 is None:
                explored.append({'first':public(m,c1,d1),'second_pool':0,'strict_second':0,'status':'NO_STATE'})
                continue
            current=0 if st1.get('connected') else st1.get('cross_distance')
            if current is not None: best=min(best,current)
            if st1.get('connected'):
                root=s.shortest_path(); replay=bool(root is not None and m.replay_dag(source,s.nodes,root,maximum_term_size=19))
                witness={'first':public(m,c1,d1),'second':None,'post_separation':0,'connected':True,'replayable_closure':replay}
                exposing+=1; break
            pool2,_,_=relaxed_pool(m,s,source,target,st1,19,p['search']['maximum_second_pool'])
            scored2=sorted([(score_candidate(m,s,target,c2),c2) for c2 in pool2],key=lambda x:(999999 if x[0] is None else x[0],x[1]['key']))
            strict2=[(d,c) for d,c in scored2 if d is not None and d<8]
            if strict2:
                exposing+=1
                d2,c2=strict2[0]
                best=min(best,d2)
                s2=copy.deepcopy(s); n2=apply_direct(s2,c2,3)
                post2=tour.cut.component_state(m,s2,target,40) if n2 is not None else None
                root=s2.shortest_path() if n2 is not None else None
                replay=bool(root is not None and m.replay_dag(source,s2.nodes,root,maximum_term_size=19))
                witness={'first':public(m,c1,d1),'second':public(m,c2,d2),'post_separation':None if post2 is None else (0 if post2.get('connected') else post2.get('cross_distance')),'connected':bool(post2 and post2.get('connected')),'replayable_closure':replay,'second_pool_count':len(pool2),'strict_second_count':len(strict2)}
                explored.append({'first':public(m,c1,d1),'second_pool':len(pool2),'strict_second':len(strict2),'best_second_separation':d2})
                break
            explored.append({'first':public(m,c1,d1),'second_pool':len(pool2),'strict_second':0,'best_second_separation':scored2[0][0] if scored2 else None})
    if not ok: decision='MEASUREMENT_FAILURE'
    elif witness is not None: decision='GREEDY_PLATEAU_CONFIRMED'
    else: decision='DIRECT_CONSTRUCTOR_DEPTH2_EXHAUSTED'
    out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':ok,'parent':{'cross_distance':None if st is None else st.get('cross_distance'),'relaxed_pool_count':len(pool),'strict_one_step_contractors':len(strict0),'nonworsening_first_moves':len(admissible),'anchor_count':len(anchors),'fill_count':len(fills)},'depth2':{'first_moves_explored':len(explored),'first_moves_exposing_strict_second':exposing,'best_reachable_separation':best,'witness':witness,'explored':explored},'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
