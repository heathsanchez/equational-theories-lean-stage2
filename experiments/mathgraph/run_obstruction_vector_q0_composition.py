#!/usr/bin/env python3
"""Bounded obstruction-vector diagnostic for O5-0014 after unified Stage 2.

No global non-existence/necessity claims. Q0 is bounded over Phi_B. Q1 is bounded
over H_B. Q4 tests bounded two-step synergy. Multiple implicated refinements are
reported non-exclusively; no synthetic joint carrier is assumed.
"""
import importlib.util,json,sys,time,itertools
from pathlib import Path
from dataclasses import dataclass
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'; SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'; OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py'; REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
MS=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'; JOIN=ROOT/'experiments/mathgraph/run_0014_semantic_join_endpoint_multisub_gate.py'
BRIDGE=ROOT/'experiments/mathgraph/run_0014_component_bridge_unification_gate.py'; ATT=ROOT/'experiments/mathgraph/run_residual_active_continuation_attachment_gate.py'
UNI=ROOT/'experiments/mathgraph/run_unified_state_transform_refinement.py'; OUT=ROOT/'experiments/mathgraph/results/obstruction-vector-q0-composition.json'; RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def canon(m,t):return m.alpha_canonical_term(t,{})
def eqkey(m,a,b):return min((canon(m,a),canon(m,b)),(canon(m,b),canon(m,a)))
def replay(m,source,it):
 try:return bool(m.replay_dag(source,it['proof'][0],it['proof'][1],maximum_term_size=240,maximum_nodes=60000))
 except Exception:return False
class UF:
 def __init__(self):self.p={}
 def find(self,x):
  self.p.setdefault(x,x)
  if self.p[x]!=x:self.p[x]=self.find(self.p[x])
  return self.p[x]
 def union(self,a,b):
  a=self.find(a);b=self.find(b)
  if a!=b:self.p[b]=a
def geometry(m,target,nodes):
 uf=UF();terms={}
 for n in nodes:
  a=canon(m,n.lhs);b=canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 lk,rk=canon(m,target[0]),canon(m,target[1]);lp=lk in terms;rp=rk in terms;L=[];R=[];joined=False
 if lp:
  lr=uf.find(lk);L=[t for k,t in terms.items() if uf.find(k)==lr]
 if rp:
  rr=uf.find(rk);R=[t for k,t in terms.items() if uf.find(k)==rr]
 if lp and rp:joined=uf.find(lk)==uf.find(rk)
 cross=None
 if L and R and not joined:
  LL=sorted(L,key=m.term_size)[:160];RR=sorted(R,key=m.term_size)[:160]
  cross=min(m.structural_distance(a,b) for a in LL for b in RR)
 return {'lhs_present':lp,'rhs_present':rp,'joined':joined,'cross_distance':cross,'L':L,'R':R,'terms':terms}
def boundary_features(m,target,g,nodes,required_keys):
 L,R=g['L'],g['R'];pairs=0
 for a in sorted(L,key=m.term_size)[:80]:
  for b in sorted(R,key=m.term_size)[:80]:
   env={}
   if m.match_term(a,b,env) or m.match_term(b,a,env):pairs+=1
 ctx=0
 tkeys={canon(m,target[0]),canon(m,target[1])}
 for n in nodes:
  for side in (n.lhs,n.rhs):
   for u in m.walk_subterms(side):
    if canon(m,u) in tkeys:ctx+=1
 motifs=0
 for n in nodes:
  for side in (n.lhs,n.rhs):
   motifs+=sum(canon(m,u) in required_keys for u in m.walk_subterms(side))
 return {'boundary_terms':len(L)+len(R),'unifiable_cross_pairs':pairs,'target_context_occurrences':ctx,'required_motif_occurrences':motifs}
def state(m,sym,source,target,items,seconds=18):
 started=time.monotonic();Norm=sym.make_normalizer(m);cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=seconds,candidate_equalities=8000,overlap_candidates=7500,selected_rules=1100,replayed_rules=4500,maximum_term_size=130,maximum_proof_nodes=140000);s=Norm(source,target,started+seconds,cfg)
 for it in items:
  ns,r=it['proof'];off=len(s.nodes)
  for n in ns:s.nodes.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or 'obstruction-vector',derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 found=s.solve();ok=False
 if found:
  ns,r=found;ok=bool(m.replay_dag(source,ns,r,maximum_term_size=180,maximum_nodes=160000))
 return s,ok
def build_atomic(m,sym,source,target,selfm,op,miss,reify,ms,j,bridge,att):
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfm.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));base=g1[:32]+g2[:128];common=g1[:24]+g2[:56]
 _,_,fterms=reify.frontier(m,sym,source,target,base,10.0);missing=reify.target_missing(m,target,fterms);proper=reify.proper_missing(m,target,missing);req=proper or missing;keys={canon(m,t) for t in req}
 R=reify.generate_instances(m,source,target,req,'OV-R',160);M=ms.synthesize(m,source,target,missing)[:160]
 for xs in (R,M):xs[:]=[x for x in xs if replay(m,source,x)]
 eps=j.endpoint_vars(source);J=[]
 if eps:
  ep=eps[0];seen=set()
  for it in M:
   mp=dict(it['proof'][0][it['proof'][1]].substitution or ())
   if not mp or any(v not in mp for v in source[2]):continue
   for side in target[:2]:
    q=dict(mp);q[ep]=side;x=j.make(m,source,target,q,'OV-J')
    if x and replay(m,source,x):
     k=eqkey(m,*x['schema'][:2]);
     if k not in seen:seen.add(k);J.append(x)
 # reproduce Stage1 minimum: cheapest replay-valid motif introducer
 def intro(x):
  return any(canon(m,u) in keys for side in x['schema'][:2] for u in m.walk_subterms(side))
 atoms=[]
 for name,xs in [('R',R),('M',M),('J',J)]:
  for x in xs:x=dict(x);x['family']=name;atoms.append(x)
 stage1=min((x for x in atoms if intro(x)),key=lambda x:(len(x['proof'][0]),m.term_size(x['schema'][0])+m.term_size(x['schema'][1]),x['proof'][0][x['proof'][1]].derivation_depth),default=None)
 installed1=common+([stage1] if stage1 else [])
 s1,_=state(m,sym,source,target,installed1,20);g=geometry(m,target,s1.nodes)
 # attachments from all replay-valid atoms against actual S1/target contexts
 A=att.attachments(m,source,target,atoms,limit=128)
 for x in A:x['family']='ATTACH'
 A=[x for x in A if replay(m,source,x)]
 # choose stage2 as cheapest intervention making rhs present (historical residual)
 pool2=atoms+A
 stage2=None
 for x in sorted(pool2,key=lambda x:(len(x['proof'][0]),m.term_size(x['schema'][0])+m.term_size(x['schema'][1]),x['proof'][0][x['proof'][1]].derivation_depth)):
  ss,_=state(m,sym,source,target,installed1+[x],8);gg=geometry(m,target,ss.nodes)
  if gg['rhs_present']:
   stage2=x;break
 installed2=installed1+([stage2] if stage2 else [])
 return base,common,req,keys,atoms,A,stage1,stage2,installed2
def main():
 global selfm
 m=load(SOLVER,'ov_m');sym=load(SYM,'ov_sym');selfm=load(SELF,'ov_self');op=load(OPC,'ov_op');op.selfmod=selfm;miss=load(MISS,'ov_miss');reify=load(REIFY,'ov_reify');reify.selfm=selfm;ms=load(MS,'ov_ms');ms.selfmod=selfm;j=load(JOIN,'ov_j');j.selfm=selfm;bridge=load(BRIDGE,'ov_b');bridge.selfm=selfm;att=load(ATT,'ov_att');att.selfm=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 base,common,req,rkeys,atoms,attachments,s1w,s2w,S2items=build_atomic(m,sym,source,target,selfm,op,miss,reify,ms,j,bridge,att)
 s2,closed2=state(m,sym,source,target,S2items,28);g2=geometry(m,target,s2.nodes);f2=boundary_features(m,target,g2,s2.nodes,rkeys);baseline={**{k:g2[k] for k in ('lhs_present','rhs_present','joined','cross_distance')},**f2}
 # Phi_B/H_B: all frozen atomic interventions + attachments, deduped, capped.
 HB=[];seen=set()
 for x in atoms+attachments:
  k=eqkey(m,*x['schema'][:2]);
  if k in seen:continue
  seen.add(k);HB.append(x)
 HB=HB[:220]
 probes=[];admiss=[];q0_counter=[]
 def K3(e):return e['replay_valid'] and (e['joined'] or (e['cross_distance'] is not None and e['cross_distance']<12))
 for x in HB:
  ss,cl=state(m,sym,source,target,S2items+[x],7);gg=geometry(m,target,ss.nodes);ff=boundary_features(m,target,gg,ss.nodes,rkeys);e={'replay_valid':replay(m,source,x),**{k:gg[k] for k in ('lhs_present','rhs_present','joined','cross_distance')},**ff};adm=K3(e)
  if adm:admiss.append((x,e))
  nond=[k for k in ('boundary_terms','unifiable_cross_pairs','target_context_occurrences','required_motif_occurrences') if e[k]>baseline[k]]
  worsened_all=all(e[k]<baseline[k] for k in ('boundary_terms','unifiable_cross_pairs','target_context_occurrences','required_motif_occurrences'))
  if (not adm) and nond and not worsened_all:q0_counter.append((x,e,nond))
  probes.append((x,e,adm))
 # Q2 family coverage
 fam={}
 for x,e,a in probes:
  fam.setdefault(x.get('family','unknown'),{'count':0,'K3':0,'rhs_present':0,'joined':0})
  z=fam[x.get('family','unknown')];z['count']+=1;z['K3']+=int(a);z['rhs_present']+=int(e['rhs_present']);z['joined']+=int(e['joined'])
 # Q3 bounded addressability evidence: exact live-component source instances available?
 exact=0
 eps=j.endpoint_vars(source)
 if eps:
  ep=eps[0];bare_left=source[0][0]=='var' and source[0][1]==ep;pattern=source[1] if bare_left else source[0]
  for A,B in ((g2['L'],g2['R']),(g2['R'],g2['L'])):
   for a in sorted(A,key=m.term_size)[:80]:
    for b in sorted(B,key=m.term_size)[:80]:
     env={ep:a}
     if m.match_term(pattern,b,env) and all(v in env for v in source[2]):exact+=1
 # Q4 bounded synergy: cheapest first 24 atoms by proof cost, ordered pairs, individual K3 false only.
 non=[(x,e) for x,e,a in probes if not a]
 non.sort(key=lambda z:(len(z[0]['proof'][0]),m.term_size(z[0]['schema'][0])+m.term_size(z[0]['schema'][1])))
 synergy=[]
 for (x,e1),(y,e2) in itertools.permutations(non[:24],2):
  ss,cl=state(m,sym,source,target,S2items+[x,y],8);gg=geometry(m,target,ss.nodes);ff=boundary_features(m,target,gg,ss.nodes,rkeys);ee={'replay_valid':True,**{k:gg[k] for k in ('lhs_present','rhs_present','joined','cross_distance')},**ff}
  if K3(ee):synergy.append({'first':x.get('family'),'second':y.get('family'),'effect':ee});break
 # composition ordering only if bounded addressability evidence and bounded synergy both implicated.
 composition=None
 if exact==0 and synergy:
  composition={'classification':'ONLY_ONE_ORDER_WELL_TYPED_OR_UNRESOLVED','note':'addressability refinement is not yet represented as a common carrier element; no synthetic joint intervention was constructed. Both orders require separately defined refinement operators before execution.'}
 vector={'specification':('COUNTEREXAMPLE_IN_PHI_B' if q0_counter else 'SURVIVED_PHI_B'),'bounded_atomic':('NONEMPTY' if admiss else 'EMPTY'),'representation':('FAMILY_COVERAGE_GAP' if not admiss else 'K3_REPRESENTED'),'addressability':('NO_EXACT_LIVE_COMPONENT_SOURCE_BRIDGE_IN_BOUND' if exact==0 else 'EXACT_BRIDGE_ADDRESSABLE'),'atomicity':('BOUNDED_SYNERGY_FOUND' if synergy else 'NO_BOUNDED_SYNERGY_FOUND')}
 out={'schema':'mathgraph.obstruction-vector-q0-composition.v1','id':RID,'baseline_S2':baseline,'bounds':{'H_B':len(HB),'Phi_B':len(probes),'pair_prefix':min(24,len(non))},'Q0':{'decision':'K3_COUNTEREXAMPLE_IN_PHI_B' if q0_counter else 'K3_SURVIVED_PHI_B','counterexamples':len(q0_counter),'examples':[{'family':x.get('family'),'improved':n,'effect':e} for x,e,n in q0_counter[:8]]},'Q1':{'decision':'K3_INTERSECTION_NONEMPTY_IN_H_B' if admiss else 'K3_INTERSECTION_EMPTY_IN_H_B','admissible':len(admiss)},'Q2':{'family_effect_coverage':fam},'Q3':{'exact_live_component_source_bridges':exact,'decision':'ADDRESSABILITY_OBSTRUCTION_IN_BOUND' if exact==0 else 'ADDRESSABLE_BRIDGE_EXISTS_IN_BOUND'},'Q4':{'decision':'ATOMICITY_OBSTRUCTION_IN_BOUND' if synergy else 'NO_BOUNDED_SYNERGY_FOUND','synergy':synergy[:1]},'obstruction_vector':vector,'composition':composition,'protocol':{'q0_bounded_only':True,'q1_bounded_only':True,'nonexclusive_vector':True,'no_global_nonexistence_claim':True,'no_global_necessity_claim':True,'no_joint_carrier_assumed':True,'ordering_required_before_joint_claim':True,'all_installed_interventions_replay_to_source':True},'decision':'DIAGNOSTIC_COMPLETE'}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
