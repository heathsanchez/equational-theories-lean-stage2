#!/usr/bin/env python3
"""Inspect the four frozen residual frontiers for generic derived structural triggers.
No external proof traces or theorem-specific identities are used.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';GATE=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-derived-structure-probe.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def main():
 m=load(SOLVER,'mg_struct');gate=load(GATE,'gate_struct');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.residual-derived-structure.v1','records':[]}
 for rid in IDS:
  row=rows[rid];src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
  limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':12.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':50000})
  eng=m.TargetGroundedRefutation(src,tgt,time.monotonic()+12.0,limits);recipe,stats=gate.solve_given(m,eng.search)
  candidates=[]
  for i,c in enumerate(eng.search.clauses):
   lhs,rhs=c.lhs,c.rhs;vl=set(m.term_variables(lhs));vr=set(m.term_variables(rhs));bare_l=lhs[0]=='var';bare_r=rhs[0]=='var'
   omitted=(bare_l and lhs[1] not in vr) or (bare_r and rhs[1] not in vl)
   subset_lr=vr<=vl;subset_rl=vl<=vr
   candidates.append({'index':i,'lhs':m.render_term(lhs),'rhs':m.render_term(rhs),'vars_l':sorted(vl),'vars_r':sorted(vr),'bare_l':bare_l,'bare_r':bare_r,'variable_omission':omitted,'vars_subset':subset_lr or subset_rl,'size':m.term_size(lhs)+m.term_size(rhs),'cost':getattr(c,'cost',None),'kind':getattr(c,'kind',None)})
  candidates.sort(key=lambda x:(0 if x['variable_omission'] else 1,0 if (x['bare_l'] or x['bare_r']) else 1,0 if x['vars_subset'] else 1,x['size'],x['cost'] if isinstance(x['cost'],int) else 10**9))
  rec={'id':rid,'closure':recipe is not None,'stats':stats,'clause_count':len(candidates),'variable_omission_count':sum(x['variable_omission'] for x in candidates),'bare_side_count':sum(x['bare_l'] or x['bare_r'] for x in candidates),'vars_subset_count':sum(x['vars_subset'] for x in candidates),'top':candidates[:20]}
  out['records'].append(rec);print(json.dumps({k:rec[k] for k in ['id','closure','clause_count','variable_omission_count','bare_side_count','vars_subset_count']},sort_keys=True),flush=True)
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
if __name__=='__main__':main()
