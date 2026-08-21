#!/usr/bin/env python3
"""Fast K2 diagnostic for evaluation_order5_0014.

K1 (opposite-cone provenance mixing) was instantiable but insufficient: 320
cross-cone binary-congruence operators produced no closure. This audit asks the
next exact topological question: do those derived equality endpoints actually
attach to the frozen lhs/rhs target components, or do they form new detached
components despite mixed parent provenance?
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'; SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'; SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'; OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'; REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'; CP=ROOT/'experiments/mathgraph/run_residual_cut_critical_pair_gate.py'; BF=ROOT/'experiments/mathgraph/run_binary_fusion_invariant_breaker_gate.py'
OUT=ROOT/'experiments/mathgraph/results/cut-attachment-audit.json'; RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def touches(n,comps,c): return comps.get(n.lhs)==c or comps.get(n.rhs)==c
def subs(m,t): return list(m.walk_subterms(t))
def main():
 m=load(SOLVER,'mg_ca');sym=load(SYM,'sym_ca');selfm=load(SELF,'self_ca');op=load(OPC,'op_ca');r=load(REIFY,'reify_ca');cp=load(CP,'cp_ca');bf=load(BF,'bf_ca');r.selfm=selfm;op.selfmod=selfm;bf.selfm=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);tl,tr=target[:2]
 state=cp.build_state(m,sym,selfm,op,r,source,target)
 s=m.ContextualSearch(source,target,time.monotonic()+30,{'max_term_size':130,'max_pool_terms':110,'max_core_terms':18,'max_source_attempts':160000,'max_source_edges':4200,'max_derivation_nodes':42000,'max_graph_edges':26000,'max_congruence_rounds':1})
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
 def small(xs):return sorted(xs,key=lambda x:m.term_size(x['schema'][0])+m.term_size(x['schema'][1]))[:28]
 Ls,Rs=small(L),small(R);out=[];seen=set()
 for a in Ls:
  for b in Rs:
   for ra,rb in ((False,False),(False,True),(True,False),(True,True)):
    x=bf.fuse(m,source,target,a,b,ra,rb,max_size=130)
    if not x:continue
    u,v,_=x['schema'];k=(m.alpha_canonical_term(u,{}),m.alpha_canonical_term(v,{}))
    if k in seen:continue
    seen.add(k);out.append(x)
    if len(out)>=320:break
   if len(out)>=320:break
  if len(out)>=320:break
 def c(t): return comps.get(t)
 exact=one_l=one_r=detached=0;sub_lr=0;rows=[]
 for x in out:
  u,v,_=x['schema'];cu,cv=c(u),c(v)
  bridge=(cu==lc and cv==rc) or (cu==rc and cv==lc)
  if bridge: exact+=1
  elif cu==lc or cv==lc: one_l+=1
  elif cu==rc or cv==rc: one_r+=1
  else: detached+=1
  su={c(z) for z in subs(m,u)};sv={c(z) for z in subs(m,v)}
  smix=((lc in su and rc in sv) or (rc in su and lc in sv) or (lc in su and rc in su) or (lc in sv and rc in sv))
  if smix: sub_lr+=1
  if bridge or smix:
   rows.append({'lhs':m.render_term(u),'rhs':m.render_term(v),'lhs_component':cu,'rhs_component':cv,'exact_cut_bridge':bridge,'subterm_mixes_cut':smix})
 decision='EXACT_CUT_EDGE_EXISTS' if exact else ('OUTPUTS_DETACHED_DESPITE_PROVENANCE_MIX' if detached==len(out) else 'PARTIAL_ATTACHMENT_NO_BRIDGE')
 result={'schema':'mathgraph.cut-attachment-audit.v1','id':RID,'K1':'combine opposite residual provenance','candidate_count':len(out),'target_components':{'lhs':lc,'rhs':rc},'component_parent_pools':{'lhs':len(Ls),'rhs':len(Rs)},'attachment':{'exact_lhs_rhs_edges':exact,'lhs_only':one_l,'rhs_only':one_r,'detached':detached,'subterm_cut_mix':sub_lr},'decision':decision,'examples':rows[:20],'protocol':{'diagnostic_only':True,'all_candidates_replay_to_source':True,'no_external_proof_trace':True,'target_only_defines_cut':True}}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
