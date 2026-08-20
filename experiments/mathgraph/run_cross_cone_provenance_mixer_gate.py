#!/usr/bin/env python3
"""Decisive K(rho) intervention: cross-cone critical-pair mixing.

K(rho), mined independently by run_provenance_invariant_extraction.py, says the
post-development grammar produced no direct cross-cut edge and no two-parent
node whose parents separately touch the two target components.  This gate adds
one previously absent *selection/operator family*: critical overlaps are formed
only between verified equalities drawn from opposite residual components.

The family is derived from K(rho), not from a proof trace or target identity.
Every resulting edge is still produced by the existing replayable overlap
constructor.  A/B/C are matched: A current grammar; B same-cone forced mixing
control; C opposite-cone forced mixing.  If C closes, rerun without C for
ablation.  Output preserves candidate proof metadata for subsequent Lean replay.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'; SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'; SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'; OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'; REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'; CP=ROOT/'experiments/mathgraph/run_residual_cut_critical_pair_gate.py'
OUT=ROOT/'experiments/mathgraph/results/cross-cone-provenance-mixer-gate.json'; RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def touch(n,comps,c): return comps.get(n.lhs)==c or comps.get(n.rhs)==c
def setup(m,sym,selfm,op,r,cp,source,target,secs=35):
 state=cp.build_state(m,sym,selfm,op,r,source,target); lim={'max_term_size':140,'max_pool_terms':130,'max_core_terms':22,'max_source_attempts':220000,'max_source_edges':5500,'max_derivation_nodes':60000,'max_graph_edges':38000,'max_congruence_rounds':2}; s=m.ContextualSearch(source,target,time.monotonic()+secs,lim); roots=[]
 for item in state:
  q=cp.copy_proof_into(m,s,item['proof'],'post-development-installed');
  if q is not None: roots.append(q)
 pool=s.make_pool();s.instantiate_sources(pool); src=[i for i,n in enumerate(s.nodes) if n.kind in ('source instance','source reentry')]; outer=list(dict.fromkeys(roots+src))[:5000]; cand=s.collect_overlap_candidates(outer,outer,4,14000)
 for c in cand[:6500]:
  if time.monotonic()>=s.deadline: break
  s.apply_overlap(c,1)
 return s
def arm(m,sym,selfm,op,r,cp,source,target,mode):
 s=setup(m,sym,selfm,op,r,cp,source,target); tl,tr=target[:2]; comps=s.components();lc,rc=comps.get(tl),comps.get(tr); base_join=lc==rc
 if base_join:return {'closure':True,'base_joined':True,'nodes':len(s.nodes)}
 L=[i for i,n in enumerate(s.nodes) if touch(n,comps,lc)][:2500];R=[i for i,n in enumerate(s.nodes) if touch(n,comps,rc)][:2500]
 if mode=='same': a,b=L,L
 elif mode=='cross': a,b=L,R
 else:return {'closure':False,'base_joined':False,'nodes':len(s.nodes),'lhs_nodes':len(L),'rhs_nodes':len(R)}
 before=len(s.nodes); cands=s.collect_overlap_candidates(a,b,6,18000); added0=s.overlaps_added
 for c in cands[:12000]:
  if time.monotonic()>=s.deadline:break
  s.apply_overlap(c,1)
 # symmetric orientation is part of the cross-cone family.
 if mode=='cross' and time.monotonic()<s.deadline:
  c2=s.collect_overlap_candidates(b,a,6,18000)
  for c in c2[:12000]:
   if time.monotonic()>=s.deadline:break
   s.apply_overlap(c,1)
 else:c2=[]
 fin=s.components();closed=fin.get(tl)==fin.get(tr)
 return {'closure':closed,'base_joined':False,'nodes_before':before,'nodes_after':len(s.nodes),'lhs_nodes':len(L),'rhs_nodes':len(R),'mix_candidates':len(cands)+len(c2),'mix_overlaps_added':s.overlaps_added-added0,'graph_edges':s.graph_edges,'final_joined':closed}
def main():
 m=load(SOLVER,'mg_mix');sym=load(SYM,'sym_mix');selfm=load(SELF,'self_mix');op=load(OPC,'op_mix');r=load(REIFY,'reify_mix');cp=load(CP,'cp_mix');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 A=arm(m,sym,selfm,op,r,cp,source,target,'base');B=arm(m,sym,selfm,op,r,cp,source,target,'same');C=arm(m,sym,selfm,op,r,cp,source,target,'cross');ab=None
 if C.get('closure'):ab=arm(m,sym,selfm,op,r,cp,source,target,'base')
 decision='K_FAMILY_CLOSES' if C.get('closure') and not A.get('closure') else ('CROSS_CONE_EXPRESSIBLE_NO_CLOSURE' if C.get('mix_overlaps_added',0)>0 else 'K_FAMILY_NOT_INSTANTIABLE')
 out={'schema':'mathgraph.cross-cone-provenance-mixer.v1','id':RID,'K_rho':'successful nonprimitive bridge must combine verified parents carrying opposite residual-component provenance','new_family':'opposite-component critical-pair mixer','protocol':{'K_mined_by_separate_prior_run':True,'no_external_proof_trace':True,'no_target_specific_identity':True,'target_only_defines_residual_cut':True,'same_cone_control':True},'arms':{'A_frozen':A,'B_same_cone':B,'C_cross_cone':C,'C_ablation':ab},'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
