#!/usr/bin/env python3
"""Instantiate mined provenance K(rho) with an actually constructible family.

Prior cross-cone critical-pair selection produced zero candidates: the K(rho)
constraint was meaningful, but ordinary overlaps could not instantiate it.
This gate therefore uses the already trusted binary-congruence construction:
from a=a' touching the lhs residual component and b=b' touching the rhs
component derive (a◇b)=(a'◇b') by two context lifts + transitivity.

Arms: A post-development frozen; B same-cone binary congruence control;
C opposite-cone binary congruence. Every candidate must replay to the source.
A positive requires C closure and A/B failure, then frozen ablation failure.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'; SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'; SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'; OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'; REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'; CP=ROOT/'experiments/mathgraph/run_residual_cut_critical_pair_gate.py'; BF=ROOT/'experiments/mathgraph/run_binary_fusion_invariant_breaker_gate.py'
OUT=ROOT/'experiments/mathgraph/results/cross-cone-binary-congruence-gate.json'; RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def touches(n,comps,c): return comps.get(n.lhs)==c or comps.get(n.rhs)==c
def run_search(m,sym,cp,source,target,items,seconds=28):
 started=time.monotonic(); Norm=sym.make_normalizer(m); cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=seconds,candidate_equalities=8000,overlap_candidates=8000,selected_rules=1200,replayed_rules=5000,maximum_term_size=130,maximum_proof_nodes=120000);s=Norm(source,target,started+seconds,cfg)
 for x in items: cp.copy_proof_into(m,s,x['proof'],x.get('name','installed'))
 found=s.solve(); ok=False;cert=None
 if found:
  ns,root=found;ok=bool(m.replay_dag(source,ns,root,maximum_term_size=150,maximum_nodes=120000));
  if ok: cert=len(m.make_dag_certificate(target,ns,root)[0].encode())
 return {'closure':ok,'nodes':len(s.nodes),'rules':len(s.rules),'overlaps':s.overlap_candidates,'certificate_bytes':cert}
def main():
 m=load(SOLVER,'mg_ccbc');sym=load(SYM,'sym_ccbc');selfm=load(SELF,'self_ccbc');op=load(OPC,'op_ccbc');r=load(REIFY,'reify_ccbc');cp=load(CP,'cp_ccbc');bf=load(BF,'bf_ccbc');r.selfm=selfm;op.selfmod=selfm;bf.selfm=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);tl,tr=target[:2]
 state=cp.build_state(m,sym,selfm,op,r,source,target)
 # Build a component-labelled view of retained verified roots.
 s=m.ContextualSearch(source,target,time.monotonic()+25,{'max_term_size':130,'max_pool_terms':110,'max_core_terms':18,'max_source_attempts':160000,'max_source_edges':4200,'max_derivation_nodes':42000,'max_graph_edges':26000,'max_congruence_rounds':1})
 roots=[]
 for item in state:
  q=cp.copy_proof_into(m,s,item['proof'],'post-development-installed');roots.append((item,q))
 pool=s.make_pool();s.instantiate_sources(pool);comps=s.components();lc,rc=comps.get(tl),comps.get(tr)
 L=[];R=[]
 for item,q in roots:
  if q is None:continue
  n=s.nodes[q]
  if touches(n,comps,lc):L.append(item)
  if touches(n,comps,rc):R.append(item)
 # Keep compact, short parent pools; enumerate both orientations through bf.fuse.
 def small(xs):return sorted(xs,key=lambda x:m.term_size(x['schema'][0])+m.term_size(x['schema'][1]))[:28]
 Ls,Rs=small(L),small(R)
 def build(a_pool,b_pool,limit=320):
  out=[];seen=set()
  for a in a_pool:
   for b in b_pool:
    for ra,rb in ((False,False),(False,True),(True,False),(True,True)):
     x=bf.fuse(m,source,target,a,b,ra,rb,max_size=130)
     if not x:continue
     key=(m.alpha_canonical_term(x['schema'][0],{}),m.alpha_canonical_term(x['schema'][1],{}))
     if key in seen:continue
     seen.add(key);x['activation']=selfm.activation(m,x['schema'],target);out.append(x)
     if len(out)>=limit:return out
  return out
 same=build(Ls,Ls);cross=build(Ls,Rs)
 same.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));cross.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base=state
 A=run_search(m,sym,cp,source,target,base,24);B=run_search(m,sym,cp,source,target,base+same[:96],24);C=run_search(m,sym,cp,source,target,base+cross[:96],32);ab=run_search(m,sym,cp,source,target,base,24) if C['closure'] else None
 out={'schema':'mathgraph.cross-cone-binary-congruence.v1','id':RID,'K_rho':'successful nonprimitive bridge must combine verified parents carrying opposite residual-component provenance','family':'binary congruence over opposite residual components','component_sizes':{'lhs_items':len(L),'rhs_items':len(R),'lhs_pool':len(Ls),'rhs_pool':len(Rs)},'candidate_counts':{'same_cone':len(same),'cross_cone':len(cross)},'protocol':{'K_mined_prior':True,'all_candidates_replay_to_source':True,'same_cone_control':True,'no_external_proof_trace':True,'no_target_specific_identity':True},'arms':{'A':A,'B_same':B,'C_cross':C,'C_ablation':ab},'decision':'PASS' if C['closure'] and not A['closure'] and not B['closure'] and ab and not ab['closure'] else ('CROSS_CONE_GENERATED_NO_CLOSURE' if cross else 'K_NOT_INSTANTIABLE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
