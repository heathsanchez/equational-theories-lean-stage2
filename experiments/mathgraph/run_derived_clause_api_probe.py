#!/usr/bin/env python3
import importlib.util,inspect,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2];SOLVER=ROOT/'submissions/mathgraph/solver.py';GATE=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py';OUT=ROOT/'experiments/mathgraph/results/derived-clause-api-probe.json'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
m=load(SOLVER,'mg_api');gate=load(GATE,'gate_api')
row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']=='evaluation_order5_0014')
src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':5.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':50000})
eng=m.TargetGroundedRefutation(src,tgt,time.monotonic()+5,limits);gate.solve_given(m,eng.search)
cand=None
for c in eng.search.clauses:
 vl=set(m.term_variables(c.lhs));vr=set(m.term_variables(c.rhs));
 if (c.lhs[0]=='var' and c.lhs[1] not in vr) or (c.rhs[0]=='var' and c.rhs[1] not in vl):cand=c;break
rec={'clause_type':type(cand).__name__ if cand else None,'clause_dict':{k:repr(v)[:1500] for k,v in vars(cand).items()} if cand and hasattr(cand,'__dict__') else {},'lhs':m.render_term(cand.lhs) if cand else None,'rhs':m.render_term(cand.rhs) if cand else None,'search_methods':{}}
for name in ['instantiate','compile','interreduce','target_proof','normalize','add_clause']:
 f=getattr(eng.search,name,None)
 if callable(f):
  try: rec['search_methods'][name]={'signature':str(inspect.signature(f)),'source':inspect.getsource(f)[:6000]}
  except Exception as e: rec['search_methods'][name]={'signature':str(inspect.signature(f)),'error':repr(e)}
rec['eng_methods']={}
for name in ['inline_recipe']:
 f=getattr(eng,name,None)
 if callable(f):rec['eng_methods'][name]={'signature':str(inspect.signature(f)),'source':inspect.getsource(f)[:6000]}
print(json.dumps(rec,indent=2,sort_keys=True));OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
