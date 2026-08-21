#!/usr/bin/env python3
"""Locate replay-valid derived universal bare-variable collapse laws for O5-0014.

Diagnostic only: no theorem is installed.  We run the existing normalizer at
progressively larger verified bounds and inspect its proof DAG for an equality
V = C (either orientation) where V is a variable absent from C.  Such a node is
exactly the activation object for the previously promoted variable-omission
collapse constructor.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2];SOLVER=ROOT/'submissions/mathgraph/solver.py';OUT=ROOT/'experiments/mathgraph/results/order5-0014-derived-collapse-scan.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def candidates(m,nodes,source,maxsize):
 out=[]
 for i,n in enumerate(nodes):
  for rev,(vside,body) in enumerate(((n.lhs,n.rhs),(n.rhs,n.lhs))):
   if vside[0]!='var' or vside[1] in m.term_variables(body):continue
   ok=bool(m.replay_dag(source,nodes,i,maximum_term_size=maxsize))
   out.append({'node':i,'reverse':bool(rev),'variable':vside[1],'body':m.render_term(body),'body_size':m.term_size(body),'kind':n.kind,'replay':ok,'constructor':n.constructor})
 return out
def arm(m,source,target,seconds,portfolio):
 st=time.monotonic();cfg=dict(m.NORMALIZATION_PORTFOLIO[portfolio]);cfg['seconds']=seconds
 n=m.EquationalNormalizer(source,target,st+seconds,cfg);n.generate_consequences();n.orient();n.select_rulebook();cs=candidates(m,n.nodes,source,cfg['maximum_term_size']);return {'portfolio':portfolio,'seconds':seconds,'elapsed':round(time.monotonic()-st,6),'nodes':len(n.nodes),'rules':len(n.rules),'overlaps':getattr(n,'overlap_candidates',None),'collapse_candidates':len(cs),'replay_valid':sum(x['replay'] for x in cs),'top':sorted(cs,key=lambda x:(not x['replay'],x['body_size'],x['node']))[:12]}
def main():
 m=load(SOLVER,'mg_cscan');row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);arms=[]
 for sec,p in [(5.0,1),(10.0,2),(20.0,3)]:
  r=arm(m,source,target,sec,p);arms.append(r);print(json.dumps(r,sort_keys=True),flush=True)
  if r['replay_valid']:break
 out={'schema':'mathgraph.order5-0014-derived-collapse-scan.v1','id':RID,'protocol':{'diagnostic_only':True,'original_source_replay_required':True,'progressive_bounds_after_negative_only':True,'activation_matches_promoted_variable_omission_constructor':True},'arms':arms,'decision':'DERIVED_COLLAPSE_PRESENT' if any(x['replay_valid'] for x in arms) else 'NO_DERIVED_COLLAPSE'};OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
