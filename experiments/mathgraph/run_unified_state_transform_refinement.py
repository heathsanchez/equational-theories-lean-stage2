#!/usr/bin/env python3
"""Strong unification gate for O5-0014.

One carrier: finite replay-verified equality interventions.
One cost: proof-object complexity.
One effect-signature type.
One refine() implementation called twice.
"""
from __future__ import annotations
import importlib.util, json, sys, time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
MS=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
JOIN=ROOT/'experiments/mathgraph/run_0014_semantic_join_endpoint_multisub_gate.py'
BRIDGE=ROOT/'experiments/mathgraph/run_0014_component_bridge_unification_gate.py'
ATT=ROOT/'experiments/mathgraph/run_residual_active_continuation_attachment_gate.py'
OUT=ROOT/'experiments/mathgraph/results/unified-state-transform-refinement.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def canon(m,t): return m.alpha_canonical_term(t,{})
def eqkey(m,a,b): return min((canon(m,a),canon(m,b)),(canon(m,b),canon(m,a)))

@dataclass
class Intervention:
 name: str
 item: dict

@dataclass
class Effect:
 replay_valid: bool
 introduced_required: int
 lhs_present: bool
 rhs_present: bool
 joined: bool
 cross_distance: int|None

@dataclass
class ResidualSpec:
 name: str
 predicate: Callable[[Effect],bool]

class UF:
 def __init__(self): self.p={}
 def find(self,x):
  self.p.setdefault(x,x)
  if self.p[x]!=x:self.p[x]=self.find(self.p[x])
  return self.p[x]
 def union(self,a,b):
  a=self.find(a);b=self.find(b)
  if a!=b:self.p[b]=a

def proof_cost(m,d:Intervention):
 ns,r=d.item['proof'];root=ns[r]
 depth=getattr(root,'derivation_depth',0) or 0
 return (len(ns),m.term_size(d.item['schema'][0])+m.term_size(d.item['schema'][1]),depth)

def replay_ok(m,source,d:Intervention):
 try:return bool(m.replay_dag(source,d.item['proof'][0],d.item['proof'][1],maximum_term_size=260,maximum_nodes=70000))
 except Exception:return False

def dedup_interventions(m,source,items,tag,limit=220):
 out=[];seen=set()
 for x in items:
  d=Intervention(tag,x)
  if not replay_ok(m,source,d):continue
  k=eqkey(m,*x['schema'][:2])
  if k in seen:continue
  seen.add(k);out.append(d)
  if len(out)>=limit:break
 return out

def build_state(m,bridge,sym,source,target,installed,seconds=24):
 items=[d.item for d in installed]
 s=bridge.state(m,sym,source,target,items,seconds)
 return {'installed':list(installed),'nodes':s.nodes}

def geometry(m,target,nodes,extra=None):
 uf=UF();terms={}
 for n in nodes:
  a=canon(m,n.lhs);b=canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 if extra is not None:
  a,b=extra.item['schema'][:2];ka,kb=canon(m,a),canon(m,b);terms[ka]=a;terms[kb]=b;uf.union(ka,kb)
 lk,rk=canon(m,target[0]),canon(m,target[1]);lp=lk in terms;rp=rk in terms
 joined=bool(lp and rp and uf.find(lk)==uf.find(rk));dist=None
 if lp and rp and not joined:
  lr,rr=uf.find(lk),uf.find(rk)
  L=[t for k,t in terms.items() if uf.find(k)==lr]
  R=[t for k,t in terms.items() if uf.find(k)==rr]
  L=sorted(L,key=lambda t:(m.term_size(t),m.render_term(t)))[:180]
  R=sorted(R,key=lambda t:(m.term_size(t),m.render_term(t)))[:180]
  if L and R:dist=min(m.structural_distance(a,b) for a in L for b in R)
 return {'lhs_present':lp,'rhs_present':rp,'joined':joined,'cross_distance':dist}

def effect(m,source,target,state,d,required_keys):
 ok=replay_ok(m,source,d)
 hits=set()
 if ok:
  for side in d.item['schema'][:2]:
   for u in m.walk_subterms(side):
    k=canon(m,u)
    if k in required_keys:hits.add(k)
 g=geometry(m,target,state['nodes'],d if ok else None)
 return Effect(ok,len(hits),g['lhs_present'],g['rhs_present'],g['joined'],g['cross_distance'])

def refine(m,source,target,state,residual,candidates,required_keys):
 admissible=[]
 for d in candidates:
  e=effect(m,source,target,state,d,required_keys)
  if e.replay_valid and residual.predicate(e):admissible.append((proof_cost(m,d),d,e))
 admissible.sort(key=lambda z:z[0])
 return (admissible[0] if admissible else None),admissible

def full_closure(m,j,sym,source,target,installed,seconds,tag):
 return j.run(m,sym,source,target,[d.item for d in installed],seconds,tag)

def make_stage1_candidates(m,sym,source,target,required,missing,g1,g2,reify,ms,j,bridge):
 common=g1[:24]+g2[:56]
 R=dedup_interventions(m,source,reify.generate_instances(m,source,target,required,'unified-R',520),'R',180)
 M=dedup_interventions(m,source,ms.synthesize(m,source,target,missing),'M',180)
 # Endpoint-promoted M instances.
 Jraw=[];eps=j.endpoint_vars(source)
 if eps:
  ep=eps[0]
  for d in M:
   node=d.item['proof'][0][d.item['proof'][1]];mp=dict(node.substitution or ())
   if not mp or any(v not in mp for v in source[2]):continue
   for side in target[:2]:
    q=dict(mp);q[ep]=side;x=j.make(m,source,target,q,'unified-J')
    if x:Jraw.append(x)
 J=dedup_interventions(m,source,Jraw,'J',180)
 # Component anchors are generated from the live J geometry but remain the same Intervention type.
 Craw=[]
 if eps:
  s=bridge.state(m,sym,source,target,common+[d.item for d in J[:48]],18)
  _,_,L,Rc,_,_=bridge.components(m,target,s.nodes);ep=eps[0]
  maps=[]
  for d in M:
   mp=dict(d.item['proof'][0][d.item['proof'][1]].substitution or ())
   if mp and all(v in mp for v in source[2]):maps.append(mp)
  for bmp in maps[:36]:
   for comp in (L,Rc):
    for a in sorted(comp,key=lambda t:(m.term_size(t),m.render_term(t)))[:24]:
     q=dict(bmp);q[ep]=a;x=bridge.make(m,source,target,q,'unified-C')
     if x:Craw.append(x)
     if len(Craw)>=180:break
    if len(Craw)>=180:break
   if len(Craw)>=180:break
 C=dedup_interventions(m,source,Craw,'C',180)
 return R+M+J+C,{'R':len(R),'M':len(M),'J':len(J),'C':len(C)}

def stage2_candidates(m,source,target,state,winner,att,bridge,j,ms_items):
 raw=[]
 # Context-lifts of the chosen intervention.
 try:raw.extend(att.attachments(m,source,target,[winner.item],limit=160))
 except Exception:pass
 # Component-anchor direct source instances from the updated state.
 eps=j.endpoint_vars(source)
 if eps:
  ep=eps[0];dummy=type('Dummy',(object,),{})()
  dummy.nodes=state['nodes']
  _,_,L,R,_,_=bridge.components(m,target,state['nodes'])
  maps=[]
  for d in ms_items:
   mp=dict(d.item['proof'][0][d.item['proof'][1]].substitution or ())
   if mp and all(v in mp for v in source[2]):maps.append(mp)
  for bmp in maps[:36]:
   for comp in (L,R):
    for a in sorted(comp,key=lambda t:(m.term_size(t),m.render_term(t)))[:32]:
     q=dict(bmp);q[ep]=a;x=bridge.make(m,source,target,q,'unified-attachment-anchor')
     if x:raw.append(x)
     if len(raw)>=220:break
    if len(raw)>=220:break
   if len(raw)>=220:break
 return dedup_interventions(m,source,raw,'ATTACH',220)

def main():
 global selfm
 m=load(SOLVER,'mg_unified');sym=load(SYM,'sym_unified');selfm=load(SELF,'self_unified');op=load(OPC,'op_unified');op.selfmod=selfm
 miss=load(MISS,'miss_unified');reify=load(REIFY,'reify_unified');reify.selfm=selfm
 ms=load(MS,'ms_unified');ms.selfmod=selfm;j=load(JOIN,'join_unified');j.selfm=selfm
 bridge=load(BRIDGE,'bridge_unified');bridge.selfm=selfm;att=load(ATT,'att_unified');att.selfm=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfm.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base_items=[Intervention('BASE',x) for x in (g1[:32]+g2[:128]) if replay_ok(m,source,Intervention('BASE',x))]
 # Residual 1 from the actual frozen frontier.
 _,_,fterms=miss.frontier(m,sym,source,target,[d.item for d in base_items],10.0)
 missing=reify.target_missing(m,target,fterms);proper=reify.proper_missing(m,target,missing);required=proper or missing
 required_keys={canon(m,t) for t in required}
 S0=build_state(m,bridge,sym,source,target,base_items,24)
 A=full_closure(m,j,sym,source,target,base_items,24,'A_frozen')
 candidates1,fcounts=make_stage1_candidates(m,sym,source,target,required,missing,g1,g2,reify,ms,j,bridge)
 K1=ResidualSpec('motif-first-introduction',lambda e:e.introduced_required>0)
 win1,adm1=refine(m,source,target,S0,K1,candidates1,required_keys)
 if not win1:
  out={'schema':'mathgraph.unified-state-transform-refinement.v1','id':RID,'identity':{'carrier':'Intervention[replay-verified equality proof DAG]','cost':'(proof_nodes,total_term_size,root_derivation_depth)','effect_type':'Effect','refine_function':'same Python function for all stages'},'family_counts':fcounts,'stage1':{'admissible':0},'arms':{'A':A},'decision':'NO_STAGE1_REFINEMENT'}
  OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True));return
 cost1,d1,e1=win1
 installed1=base_items+[d1]
 S1=build_state(m,bridge,sym,source,target,installed1,28)
 C1=full_closure(m,j,sym,source,target,installed1,28,'C_stage1')
 g1state=geometry(m,target,S1['nodes']);baseline_dist=g1state['cross_distance'];baseline_present=(g1state['lhs_present'],g1state['rhs_present'])
 # Build M interventions only for state-conditioned attachment proposer.
 Mitems=dedup_interventions(m,source,ms.synthesize(m,source,target,missing),'M',180)
 candidates2=stage2_candidates(m,source,target,S1,d1,att,bridge,j,Mitems)
 if g1state['lhs_present'] and g1state['rhs_present'] and not g1state['joined']:
  K2=ResidualSpec('component-disconnection',lambda e:e.joined or (baseline_dist is not None and e.cross_distance is not None and e.cross_distance<baseline_dist))
  residual2='component-disconnection'
 else:
  # If the shared minimal cost does not reproduce the expected residual sequence, record that honestly.
  K2=ResidualSpec('endpoint-addressability',lambda e:(e.lhs_present and e.rhs_present) and not (baseline_present[0] and baseline_present[1]))
  residual2='endpoint-addressability'
 win2,adm2=refine(m,source,target,S1,K2,candidates2,required_keys)
 if not win2:
  out={'schema':'mathgraph.unified-state-transform-refinement.v1','id':RID,'identity':{'carrier':'Intervention[replay-verified equality proof DAG]','cost':'(proof_nodes,total_term_size,root_derivation_depth)','effect_type':'Effect','refine_function':'same Python function for all stages'},'family_counts':fcounts,'stage1':{'winner':d1.name,'cost':cost1,'effect':e1.__dict__,'admissible':len(adm1)},'post_stage1_geometry':g1state,'stage2_residual':residual2,'stage2':{'candidates':len(candidates2),'admissible':0},'arms':{'A':A,'C1':C1},'decision':'STAGE1_ONLY'}
  OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True));return
 cost2,d2,e2=win2
 installed2=installed1+[d2]
 D=full_closure(m,j,sym,source,target,installed2,38,'D_stage2')
 Abl=full_closure(m,j,sym,source,target,installed1,38,'D_stage2_ablation')
 strong=bool(D.get('closure') and not A.get('closure') and not C1.get('closure') and not Abl.get('closure'))
 predicted=bool(e2.joined or (baseline_dist is not None and e2.cross_distance is not None and e2.cross_distance<baseline_dist) or (e2.lhs_present and e2.rhs_present and not all(baseline_present)))
 decision='PASS_STRONG_UNIFIED_CLOSURE' if strong else 'PASS_UNIFIED_PROGRESS' if predicted else 'UNIFIED_OPERATOR_NO_PREDICTED_EFFECT'
 out={'schema':'mathgraph.unified-state-transform-refinement.v1','id':RID,
  'identity':{'carrier':'Intervention[replay-verified equality proof DAG]','same_carrier_both_calls':True,'cost':'(proof_nodes,total_term_size,root_derivation_depth)','same_cost_both_calls':True,'effect_type':'Effect(replay_valid,introduced_required,lhs_present,rhs_present,joined,cross_distance)','same_effect_type_both_calls':True,'admissibility_form':'ResidualSpec.predicate(Effect)','same_admissibility_form_both_calls':True,'refine_function':'refine','same_refine_code_path_both_calls':True},
  'required':[m.render_term(t) for t in required],'family_counts':fcounts,
  'stage1':{'residual':'motif-first-introduction','candidate_count':len(candidates1),'admissible':len(adm1),'winner':d1.name,'cost':cost1,'effect':e1.__dict__},
  'post_stage1_geometry':g1state,
  'stage2':{'residual':residual2,'candidate_count':len(candidates2),'admissible':len(adm2),'winner':d2.name,'cost':cost2,'effect':e2.__dict__},
  'arms':{'A_frozen':A,'C_stage1':C1,'D_stage2':D,'D_stage2_ablation':Abl},
  'protocol':{'same_intervention_dataclass':True,'same_proof_cost_function':True,'same_effect_function':True,'same_refine_function':True,'stateful_iteration_allowed':True,'all_interventions_replay_to_source':True,'no_external_proof_trace':True,'no_answer_label':True},
  'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
