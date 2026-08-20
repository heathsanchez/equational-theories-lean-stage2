#!/usr/bin/env python3
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
OUT=ROOT/'experiments/mathgraph/results/given-clause-official-lean-gate.json'
RID='evaluation_hard_0196'

sys.path.insert(0,str(ROOT))
from judge.verify import verify_answer


def load_module(path,name):
 spec=importlib.util.spec_from_file_location(name,path)
 mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod;spec.loader.exec_module(mod);return mod


def main():
 m=load_module(SOLVER,'mg_given_official')
 gate=load_module(ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py','given_gate')
 row=None
 for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_hard',split='train'):
  if raw.get('id')==RID: row=dict(raw);break
 if row is None: raise SystemExit('missing target row')
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 eng=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits)
 recipe,stats=gate.solve_given(m,eng.search)
 if recipe is None:
  result={'id':RID,'closure':False,'official_status':'NO_RECIPE','stats':stats}
 else:
  rr=eng.inline_recipe(recipe)
  cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+3.0,eng.search.limits)
  nodes,root=cc.compile(rr)
  replay=bool(nodes[root].lhs==target[0] and nodes[root].rhs==target[1] and m.replay_dag(source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes']))
  code,proof_nodes=m.make_dag_certificate(target,nodes,root)
  answer=json.dumps({'verdict':'true','code':code})
  judged=verify_answer(row,answer)
  result={'id':RID,'closure':replay,'proof_nodes':proof_nodes,'certificate_bytes':len(code.encode()),'official_status':judged.get('status'),'official_error_code':judged.get('error_code'),'official_message':judged.get('message'),'direct_declarations':judged.get('direct_declarations',[]),'axioms':judged.get('axioms',[]),'stats':stats}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result,indent=2,sort_keys=True))
 if not (result.get('closure') and result.get('official_status')=='accepted'):
  raise SystemExit(1)

if __name__=='__main__':main()
