#!/usr/bin/env python3
"""O5-0014 next residual: both target endpoints are live but components remain separated.

Freeze the successful semantic-JOIN endpoint representation. Then ask the strongest
possible question first: is there a direct replay-valid source-law instance whose
bare endpoint lies in one live target component and whose structured side lies in
the opposite component? If not, synthesize component-anchored instances using the
already residual-derived multisubstitution mappings and rank them only by verified
cross-component distance reduction.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py';MS=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
JOIN=ROOT/'experiments/mathgraph/run_0014_semantic_join_endpoint_multisub_gate.py'
OUT=ROOT/'experiments/mathgraph/results/0014-component-bridge-unification-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def canon(m,t):return m.alpha_canonical_term(t,{})
class UF:
 def __init__(self):self.p={}
 def find(self,x):
  self.p.setdefault(x,x)
  if self.p[x]!=x:self.p[x]=self.find(self.p[x])
  return self.p[x]
 def union(self,a,b):
  a=self.find(a);b=self.find(b)
  if a!=b:self.p[b]=a
def components(m,target,nodes):
 uf=UF();terms={}
 for n in nodes:
  a=canon(m,n.lhs);b=canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 lk,rk=canon(m,target[0]),canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 L=[t for k,t in terms.items() if uf.find(k)==lr];R=[t for k,t in terms.items() if uf.find(k)==rr]
 return uf,terms,L,R,lr,rr
def state(m,sym,source,target,items,seconds=30):
 started=time.monotonic();Norm=sym.make_normalizer(m);cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=seconds,candidate_equalities=9000,overlap_candidates=8500,selected_rules=1200,replayed_rules=5000,maximum_term_size=130,maximum_proof_nodes=150000);s=Norm(source,target,started+seconds,cfg)
 for it in items:
  ns,r=it['proof'];off=len(s.nodes)
  for n in ns:s.nodes.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or 'component-bridge-seed',derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 s.solve();return s
def make(m,source,target,mp,tag):
 if any(v not in mp for v in source[2]):return None
 a=m.substitute(source[0],mp);b=m.substitute(source[1],mp)
 if max(m.term_size(a),m.term_size(b))>180:return None
 n=m.EqualityNode(a,b,'source instance',substitution=tuple((v,mp[v]) for v in source[2]),orientation=False,constructor=tag)
 if not m.replay_dag(source,[n],0,maximum_term_size=220,maximum_nodes=8):return None
 sch=(a,b,tuple(sorted(m.term_variables(a)|m.term_variables(b))))
 return {'schema':sch,'proof':([n],0),'name':tag,'activation':selfm.activation(m,sch,target),'mapping':mp}
def main():
 global selfm
 m=load(SOLVER,'mg_cb');sym=load(SYM,'sym_cb');selfm=load(SELF,'self_cb');op=load(OPC,'op_cb');op.selfmod=selfm;miss=load(MISS,'miss_cb');ms=load(MS,'ms_cb');ms.selfmod=selfm;j=load(JOIN,'join_cb');j.selfm=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 ep=j.endpoint_vars(source)[0]
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfm.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));base=g1[:32]+g2[:128]
 _,_,fterms=miss.frontier(m,sym,source,target,base,10.0);missing=miss.target_missing(m,target,fterms);multi=ms.synthesize(m,source,target,missing)
 maps=[]
 for it in multi:
  mp=dict(it['proof'][0][it['proof'][1]].substitution or ())
  if mp and all(v in mp for v in source[2]):maps.append(mp)
 join=[];seen=set()
 for bmp in maps:
  for side in target[:2]:
   mp=dict(bmp);mp[ep]=side;x=make(m,source,target,mp,'frozen-semantic-join')
   if x:
    k=(canon(m,x['schema'][0]),canon(m,x['schema'][1]));
    if k not in seen:seen.add(k);join.append(x)
 join.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 common=g1[:24]+g2[:56];frozen=common+join[:64];s=state(m,sym,source,target,frozen,35);uf,terms,L,R,lr,rr=components(m,target,s.nodes)
 # Exact source-law bridge by unification with opposite live component.
 bare_left=source[0][0]=='var' and source[0][1]==ep;pattern=source[1] if bare_left else source[0]
 exact=[]
 for A,B in ((L,R),(R,L)):
  for a in sorted(A,key=lambda t:(m.term_size(t),m.render_term(t)))[:180]:
   for b in sorted(B,key=lambda t:(m.term_size(t),m.render_term(t)))[:180]:
    env={ep:a}
    if not m.match_term(pattern,b,env) or any(v not in env for v in source[2]):continue
    x=make(m,source,target,env,'exact-live-component-bridge')
    if x:exact.append(x)
 # If exact bridge absent, anchor endpoint in each component while preserving residual multisub y/z maps.
 cand=[];seen=set()
 for bmp in maps:
  for side_name,A,B in (('L',L,R),('R',R,L)):
   Bs=sorted(B,key=lambda t:(m.term_size(t),m.render_term(t)))[:120]
   for a in sorted(A,key=lambda t:(m.term_size(t),m.render_term(t)))[:80]:
    mp=dict(bmp);mp[ep]=a;x=make(m,source,target,mp,'component-anchored-multisub')
    if not x:continue
    other=x['schema'][1] if bare_left else x['schema'][0]
    dist=min((m.structural_distance(other,b) for b in Bs),default=999)
    k=(canon(m,x['schema'][0]),canon(m,x['schema'][1]))
    if k in seen:continue
    seen.add(k);x['cross_distance']=dist;x['anchor_side']=side_name;cand.append(x)
 cand.sort(key=lambda x:(x['cross_distance'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 A=j.run(m,sym,source,target,frozen,35,'A_frozen_join_geometry')
 C=j.run(m,sym,source,target,common+(exact[:32] if exact else cand[:96]),45,'C_component_bridge')
 out={'schema':'mathgraph.0014-component-bridge-unification.v1','id':RID,'frozen_residual':{'lhs_component':len(L),'rhs_component':len(R),'cross_distance':A.get('cross_distance')},'counts':{'exact_source_bridges':len(exact),'component_anchored_candidates':len(cand),'distance_lt_frozen':sum(x['cross_distance']<(A.get('cross_distance') or 999) for x in cand)},'arms':{'A':A,'C':C},'best_candidates':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'cross_distance':x.get('cross_distance'),'activation':x['activation'],'anchor_side':x.get('anchor_side')} for x in cand[:20]],'protocol':{'semantic_join_state_frozen':True,'exact_bridge_tested_before_approximation':True,'all_candidates_direct_source_instances_replay_verified':True,'no_external_proof_trace':True,'no_answer_label':True},'decision':'PASS_CLOSURE' if C.get('closure') and not A.get('closure') else 'EXACT_BRIDGE_FOUND_NO_CLOSURE' if exact else 'DISTANCE_REDUCED' if C.get('cross_distance') is not None and A.get('cross_distance') is not None and C['cross_distance']<A['cross_distance'] else 'MINIMAL_BRIDGE_RESIDUAL'}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
