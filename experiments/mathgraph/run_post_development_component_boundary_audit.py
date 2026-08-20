#!/usr/bin/env python3
"""Diagnose the smallest structural mismatch across the post-development target cut."""
import importlib.util,json,sys
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py';CC=ROOT/'experiments/mathgraph/run_residual_cut_congruence_completion_gate.py'
OUT=ROOT/'experiments/mathgraph/results/post-development-component-boundary-audit.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def diffs(a,b,path=()):
 if a==b:return []
 if a[0]!=b[0]:return [{'path':path,'a':a,'b':b,'kind':'node-kind'}]
 if a[0]=='var':return [{'path':path,'a':a,'b':b,'kind':'variable'}]
 out=[]
 if a[1]!=b[1]:out.extend(diffs(a[1],b[1],path+('L',)))
 if a[2]!=b[2]:out.extend(diffs(a[2],b[2],path+('R',)))
 return out

def main():
 m=load(SOLVER,'mg_baudit');sym=load(SYM,'sym_baudit');selfm=load(SELF,'self_baudit');op=load(OPC,'op_baudit');r=load(REIFY,'reify_baudit');cc=load(CC,'cc_baudit');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 state=cc.build_state(m,sym,selfm,op,r,source,target);s,_,_=r.frontier(m,sym,source,target,state,20.0);uf,adj,terms=cc.graph(m,r,s.nodes)
 lk=r.canon(m,target[0]);rk=r.canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 L=[t for k,t in terms.items() if uf.find(k)==lr];R=[t for k,t in terms.items() if uf.find(k)==rr]
 best=[];bestd=10**9
 for a in L:
  for b in R:
   d=m.structural_distance(a,b)
   if d<bestd:bestd=d;best=[(a,b)]
   elif d==bestd and len(best)<20:best.append((a,b))
 diag=[]
 for a,b in best[:10]:
  ds=diffs(a,b)
  diag.append({'a':m.render_term(a),'b':m.render_term(b),'size_a':m.term_size(a),'size_b':m.term_size(b),'distance':bestd,'diffs':[{'path':list(x['path']),'a':m.render_term(x['a']),'b':m.render_term(x['b']),'kind':x['kind'],'a_component':str(uf.find(r.canon(m,x['a']))),'b_component':str(uf.find(r.canon(m,x['b']))),'same_component':uf.find(r.canon(m,x['a']))==uf.find(r.canon(m,x['b']))} for x in ds]})
 out={'schema':'mathgraph.post-development-component-boundary-audit.v1','id':RID,'component_state':{'lhs_component_size':len(L),'rhs_component_size':len(R),'nodes':len(s.nodes),'rules':len(s.rules),'overlaps':s.overlap_candidates},'minimum_structural_distance':bestd,'minimum_pairs':diag,'protocol':{'post_development_cut_recomputed':True,'diagnostic_only':True,'no_external_proof_trace':True}}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
