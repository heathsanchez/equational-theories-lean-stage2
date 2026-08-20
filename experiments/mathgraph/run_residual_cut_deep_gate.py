#!/usr/bin/env python3
"""Deep verification of the residual-induced cut with the smallest component gap.

Selection is theorem-agnostic: a cheap replay-gated component expansion is run
for every frozen residual and the residual with minimum cross-component
structural distance is selected.  Only then do we spend a serious proof budget
on the top locally-factored bridge obligations.  Any promoted cut must replay
from the original source axiom before it is installed into a fresh target
search. No external proof trace or answer label is used.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
CUT=ROOT/'experiments/mathgraph/run_residual_cut_induction_gate.py'
BIDIR=ROOT/'experiments/mathgraph/run_bidirectional_proof_operator_gate.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
SCHEMA=ROOT/'experiments/mathgraph/run_verified_schema_induction_gate.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
GIVEN=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-cut-deep-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def components(m,b,op,se,source,target,seconds,rounds,cap):
 rules,g1,g2=b.library(m,se,op,source,target);dl=time.monotonic()+seconds
 L,le=cut.expand_component(m,b,rules,source,target,target[0],dl,rounds,cap)
 R,re=cut.expand_component(m,b,rules,source,target,target[1],dl,rounds,cap)
 obs=cut.closest_obligations(m,L,R,target,8)
 return rules,g1,g2,L,R,le,re,obs

def main():
 m=load(SOLVER,'mg_cutdeep');cut=load(CUT,'cutdeep');b=load(BIDIR,'bidir_cutdeep');se=load(SELF,'self_cutdeep');op=load(OPC,'op_cutdeep');op.selfmod=se;sc=load(SCHEMA,'schema_cutdeep');sy=load(SYM,'sym_cutdeep');gv=load(GIVEN,'given_cutdeep');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 ranking=[]
 for rid in IDS:
  src=m.parse_equation(rows[rid]['equation1']);tgt=m.parse_equation(rows[rid]['equation2'])
  _,_,_,L,R,_,_,obs=components(m,b,op,se,src,tgt,4.5,1,120)
  d=obs[0][0][0] if obs else 10**9
  ranking.append({'id':rid,'cross_distance':d,'left_states':len(L),'right_states':len(R)})
 ranking.sort(key=lambda x:(x['cross_distance'],x['id']));winner=ranking[0]['id'];row=rows[winner]
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);started=time.monotonic()
 rules,g1,g2,L,R,le,re,obs=components(m,b,op,se,source,target,22.0,3,420)
 proved=[];screen=[]
 for score,a,bb,path,bridge in obs[:4]:
  proof,st=sc.prove_schema(m,gv,source,bridge,12.0)
  rec={'lhs':m.render_term(bridge[0]),'rhs':m.render_term(bridge[1]),'context_depth':len(path),'cross_distance':score[0],'proved':proof is not None,'given':st.get('given',0),'generated':st.get('generated',0)}
  screen.append(rec)
  if proof is not None:proved.append((bridge,proof,rec))
 Norm=sy.make_normalizer(m);cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=22.0,candidate_equalities=5000,overlap_candidates=4200,selected_rules=600,replayed_rules=2200,maximum_term_size=55,maximum_proof_nodes=90000)
 s=Norm(source,target,time.monotonic()+22.0,cfg);roots=[]
 for bridge,proof,_ in proved:roots.append(sc.append_proof(m,s.nodes,proof,'residual-induced-cut-deep'))
 found=s.solve();ok=False;cert=None;pn=None
 if found is not None:
  nodes,root=found;ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=90000))
  if ok:code,pn=m.make_dag_certificate(target,nodes,root);cert=len(code.encode())
 out={'schema':'mathgraph.residual-cut-deep.v1','ranking':ranking,'selected':winner,'selected_distance':ranking[0]['cross_distance'],'left_states':len(L),'right_states':len(R),'left_replayed':le,'right_replayed':re,'exact_component_intersection':len(set(L)&set(R)),'cuts_screened':len(screen),'cuts_proved':len(proved),'screen':screen,'proved_cuts':[x[2] for x in proved],'closure':ok,'certificate_bytes':cert,'proof_nodes':pn,'symbolic_rules':len(s.rules),'selected_rules':len(s.selected_rules),'left_steps':s.left_steps,'right_steps':s.right_steps,'seconds':round(time.monotonic()-started,6)}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
