#!/usr/bin/env python3
import json, sys
from pathlib import Path
from itertools import product
from datasets import load_dataset

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path: sys.path.insert(0,str(HERE))
import run_methodology_0036_cut_ranking_tournament_v1 as tour
import run_methodology_0036_goal_cut_descaffold_v1 as desc

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-postcontractor-factorization-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-postcontractor-factorization-v1.json'
RID='evaluation_normal_0036'

def uniq(xs):
    out=[]; seen=set()
    for x in xs:
        if x in seen: continue
        seen.add(x); out.append(x)
    return out

def edge_exists(s,a,b):
    return any(n==b for n,_,_ in s.adjacency.get(a,())) or any(n==a for n,_,_ in s.adjacency.get(b,()))

def reconstruct_post_step(m,source,target,cfg):
    s,old,new,admitted,edges,st=tour.frozen_state(m,source,target,cfg)
    cands,_,_=tour.make_pool(m,s,source,target,st,20000)
    ranked,_=desc.rank_descaffolded(m,s,target,cands)
    first=ranked[0]
    nid=s.ensure_source_mapping(first['mapping'],False,'postcontractor-parent-replay',1)
    post=tour.cut.component_state(m,s,target,40)
    return s,old,new,admitted,edges,first,nid,post

def l0_terms(m,s,target,st):
    comps=st['component_map']; tl,tr=target[:2]; lc,rc=comps[tl],comps[tr]
    live=st['lhs_members']+st['rhs_members']
    anchors=sorted(uniq([t for t in live if m.term_size(t)<=9]),key=s.term_key)
    vars_=[('var',v) for v in target[2]]
    proper=[]
    for side in target[:2]:
        for t in m.walk_subterms(side):
            if t!=side and m.term_size(t)<=5: proper.append(t)
    small=[t for t in live if m.term_size(t)<=5]
    fills=sorted(uniq(vars_+small+proper),key=s.term_key)[:16]
    return anchors,fills

def l1_terms(m,s,target,st):
    live=st['lhs_members']+st['rhs_members']
    anchors=sorted(uniq([t for t in live if m.term_size(t)<=19]),key=s.term_key)
    vars_=[('var',v) for v in target[2]]
    target_terms=[]
    for side in target[:2]:
        target_terms.extend([t for t in m.walk_subterms(side) if m.term_size(t)<=9])
    fills=sorted(uniq(vars_+live+target_terms),key=s.term_key)
    return anchors,fills

def enumerate_candidates(m,s,source,target,st,anchors,fills,cap,limit=100000):
    comps=st['component_map']; tl,tr=target[:2]; lc,rc=comps[tl],comps[tr]
    out=[]; seen=set(); rejected_size=0
    for anchor in anchors:
        if comps.get(anchor) not in (lc,rc): continue
        for y,z in product(fills,repeat=2):
            mapping={'x':anchor,'y':y,'z':z}
            lhs=m.substitute(source[0],mapping); rhs=m.substitute(source[1],mapping)
            if lhs==rhs: continue
            mx=max(m.term_size(lhs),m.term_size(rhs))
            if mx>cap:
                rejected_size+=1; continue
            key=frozenset((lhs,rhs))
            if key in seen or edge_exists(s,lhs,rhs): continue
            seen.add(key)
            c={'mapping':mapping,'lhs':lhs,'rhs':rhs,'anchor':anchor,'y':y,'z':z,'key':(m.render_term(lhs),m.render_term(rhs)),'max_term_size':mx}
            d=desc.simulate_goal_separation(m,s,target,c)
            c['post_separation']=d
            out.append(c)
            if len(out)>=limit:return out,rejected_size
    return out,rejected_size

def summarize(m,cands,l0_anchor_set,l0_fill_set,current=8):
    strict=[c for c in cands if c['post_separation'] is not None and c['post_separation']<current]
    best=min((c['post_separation'] for c in cands if c['post_separation'] is not None),default=None)
    minsize=min((c['max_term_size'] for c in strict),default=None)
    excluded=sum(1 for c in strict if c['anchor'] not in l0_anchor_set or c['y'] not in l0_fill_set or c['z'] not in l0_fill_set)
    examples=[]
    for c in sorted(strict,key=lambda x:(x['post_separation'],x['max_term_size'],x['key']))[:10]:
        examples.append({'lhs':m.render_term(c['lhs']),'rhs':m.render_term(c['rhs']),'post_separation':c['post_separation'],'max_term_size':c['max_term_size'],'anchor_excluded_L0':c['anchor'] not in l0_anchor_set,'y_excluded_L0':c['y'] not in l0_fill_set,'z_excluded_L0':c['z'] not in l0_fill_set})
    return {'candidate_count':len(cands),'strict_contractor_count':len(strict),'best_post_separation':best,'minimum_contractor_max_term_size':minsize,'contractors_using_L0_excluded_terms':excluded,'examples':examples}

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] and RID not in p['sealed_transfer_ids']
    m=tour.cut.load_hist(); row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    s,old,new,admitted,edges,first,nid,st=reconstruct_post_step(m,source,target,cfg)
    ok=(s.max_term_size==19 and len(old)==45 and admitted==9 and edges==9 and nid is not None and st is not None and not st.get('connected') and st.get('cross_distance')==8 and m.render_term(first['lhs'])=='x')
    if not ok:
        out={'schema':p['schema'],'id':RID,'decision':'MEASUREMENT_FAILURE','measurement_ok':False,'sealed_transfer_ids_loaded':[]}
    else:
        a0,f0=l0_terms(m,s,target,st); a1,f1=l1_terms(m,s,target,st)
        c0,r0=enumerate_candidates(m,s,source,target,st,a0,f0,19)
        c1,r1=enumerate_candidates(m,s,source,target,st,a1,f1,19)
        c2,r2=enumerate_candidates(m,s,source,target,st,a1,f1,23)
        c3,r3=enumerate_candidates(m,s,source,target,st,a1,f1,27)
        A0,F0=set(a0),set(f0)
        sums={
          'L0_FROZEN':summarize(m,c0,A0,F0),
          'L1_RELAX_POOL':summarize(m,c1,A0,F0),
          'L2_CAP23':summarize(m,c2,A0,F0),
          'L3_CAP27':summarize(m,c3,A0,F0)
        }
        sums['L0_FROZEN']['size_rejections']=r0; sums['L1_RELAX_POOL']['size_rejections']=r1; sums['L2_CAP23']['size_rejections']=r2; sums['L3_CAP27']['size_rejections']=r3
        if sums['L0_FROZEN']['strict_contractor_count']!=0:
            decision='MEASUREMENT_FAILURE'
        elif sums['L1_RELAX_POOL']['strict_contractor_count']>0:
            decision='POOL_TRUNCATION_OBSTRUCTION'
        elif sums['L2_CAP23']['strict_contractor_count']>0 or sums['L3_CAP27']['strict_contractor_count']>0:
            decision='TERM_CAP_OBSTRUCTION'
        else:
            decision='DIRECT_CONSTRUCTOR_EXHAUSTED'
        out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':decision!='MEASUREMENT_FAILURE','post_step':{'cross_distance':st.get('cross_distance'),'lhs_size':st.get('lhs_size'),'rhs_size':st.get('rhs_size'),'first_move':tour.public_candidate(m,first)},'pool_geometry':{'L0_anchor_count':len(a0),'L0_fill_count':len(f0),'L1_anchor_count':len(a1),'L1_fill_count':len(f1)},'ladder':sums,'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
