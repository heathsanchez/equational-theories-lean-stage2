#!/usr/bin/env python3
import json, sys, time
from pathlib import Path
from datasets import load_dataset

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path: sys.path.insert(0,str(HERE))
import run_methodology_0036_component_cut_factorization_v1 as cut

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-cut-ranking-tournament-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-cut-ranking-tournament-v1.json'
RID='evaluation_normal_0036'

def uniq_terms(xs):
    out=[]; seen=set()
    for x in xs:
        if x in seen: continue
        seen.add(x); out.append(x)
    return out

def edge_exists(s,a,b):
    return any(n==b for n,_,_ in s.adjacency.get(a,())) or any(n==a for n,_,_ in s.adjacency.get(b,()))

def frozen_state(m,source,target,cfg):
    s,old=cut.make_search(m,source,target,cfg)
    admitted,edges,new=cut.add_reentry(m,s,source,target,old)
    st=cut.component_state(m,s,target,40)
    return s,old,new,admitted,edges,st

def make_pool(m,s,source,target,st,limit):
    comps=st['component_map']; tl,tr=target[:2]; lc,rc=comps[tl],comps[tr]
    L=st['lhs_members']; R=st['rhs_members']
    anchors=sorted(uniq_terms([t for t in L+R if m.term_size(t)<=9]),key=s.term_key)
    vars_=[('var',v) for v in target[2]]
    proper=[]
    for side in target[:2]:
        for t in m.walk_subterms(side):
            if t!=side and m.term_size(t)<=5: proper.append(t)
    small=[t for t in L+R if m.term_size(t)<=5]
    fills=sorted(uniq_terms(vars_+small+proper),key=s.term_key)[:16]
    b=cut.basis(m,target); candidates=[]; seen=set()
    for anchor in anchors:
        c=comps.get(anchor)
        if c not in (lc,rc): continue
        opposite=R if c==lc else L
        side='L' if c==lc else 'R'
        for y in fills:
            for z in fills:
                mapping={'x':anchor,'y':y,'z':z}
                lhs=m.substitute(source[0],mapping); rhs=m.substitute(source[1],mapping)
                if lhs==rhs or max(m.term_size(lhs),m.term_size(rhs))>19: continue
                key=frozenset((lhs,rhs))
                if key in seen or edge_exists(s,lhs,rhs): continue
                seen.add(key)
                d=min(m.structural_distance(rhs,o) for o in opposite)
                tc=len(cut.cov(m,rhs,b))
                candidates.append({'mapping':mapping,'lhs':lhs,'rhs':rhs,'anchor_side':side,'predicted_cut_distance':d,'target_coverage':tc,'key':(m.render_term(lhs),m.render_term(rhs))})
                if len(candidates)>=limit: return candidates,anchors,fills
    return candidates,anchors,fills

def select(candidates,k,mode):
    if mode=='target':
        return sorted(candidates,key=lambda c:(-c['target_coverage'],c['key']))[:k]
    return sorted(candidates,key=lambda c:(c['predicted_cut_distance'],c['key']))[:k]

def apply_arm(m,source,target,cfg,selected):
    s,old,new,admitted,edges,pre=frozen_state(m,source,target,cfg)
    added=0
    for c in selected:
        nid=s.ensure_source_mapping(c['mapping'],False,'cut-ranking-tournament',1)
        if nid is not None: added+=1
    post=cut.component_state(m,s,target,40)
    root=s.shortest_path(); replay=False
    if root is not None:
        replay=m.replay_dag(source,s.nodes,root,maximum_term_size=19)
    return {'added':added,'pre_cross_distance':None if pre is None else pre.get('cross_distance'),'post_cross_distance':None if post is None else post.get('cross_distance',0),'connected':bool(post and post.get('connected')),'root':root,'replayable_closure':replay,'post_lhs_size':None if post is None else post.get('lhs_size'),'post_rhs_size':None if post is None else post.get('rhs_size')}

def public_candidate(m,c):
    return {'lhs':m.render_term(c['lhs']),'rhs':m.render_term(c['rhs']),'anchor_side':c['anchor_side'],'predicted_cut_distance':c['predicted_cut_distance'],'target_coverage':c['target_coverage']}

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] and RID not in p['sealed_transfer_ids']
    m=cut.load_hist(); row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    s,old,new,admitted,edges,st=frozen_state(m,source,target,cfg)
    ok=(s.max_term_size==19 and len(old)==45 and admitted==9 and edges==9 and st is not None and not st.get('connected') and st.get('lhs_size')==4 and st.get('rhs_size')==19 and st.get('cross_distance')==10)
    candidates,anchors,fills=make_pool(m,s,source,target,st,p['candidate_family']['maximum_pool']) if ok else ([],[],[])
    contractors=[c for c in candidates if c['predicted_cut_distance']<10]
    k=min(24,len(candidates))
    A=select(candidates,k,'target'); B=select(candidates,k,'cut')
    armA=apply_arm(m,source,target,cfg,A) if ok and k else None
    armB=apply_arm(m,source,target,cfg,B) if ok and k else None
    matched=bool(ok and k and armA and armB and len(A)==len(B)==k and armA['added']==armB['added'])
    if not matched: decision='MEASUREMENT_FAILURE'
    elif not contractors: decision='NO_ONE_STEP_CUT_CONTRACTOR'
    else:
        a=(0 if armA['connected'] else armA['post_cross_distance']); b=(0 if armB['connected'] else armB['post_cross_distance'])
        if b<a or (armB['replayable_closure'] and not armA['replayable_closure']): decision='CUT_CONTRACTOR_CAUSAL'
        elif a<=b and armA['connected']>=armB['connected'] and armA['replayable_closure']>=armB['replayable_closure']: decision='TARGET_RANKING_EQUIVALENT'
        else: decision='CONTRACTOR_PREDICTION_FAILS'
    aset={c['key'] for c in A}; bset={c['key'] for c in B}
    out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':matched,'frozen':{'cross_distance':None if st is None else st.get('cross_distance'),'lhs_size':None if st is None else st.get('lhs_size'),'rhs_size':None if st is None else st.get('rhs_size'),'reentry_edges':edges},'candidate_pool':{'count':len(candidates),'anchor_count':len(anchors),'fill_count':len(fills),'predicted_contractors':len(contractors),'best_predicted_distance':min((c['predicted_cut_distance'] for c in candidates),default=None)},'selection':{'k':k,'overlap_count':len(aset&bset),'A_top':[public_candidate(m,c) for c in A[:8]],'B_top':[public_candidate(m,c) for c in B[:8]]},'arm_A_target_coverage':armA,'arm_B_cut_contraction':armB,'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
