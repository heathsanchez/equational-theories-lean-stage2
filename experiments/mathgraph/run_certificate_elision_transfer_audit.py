#!/usr/bin/env python3
"""Source-distinct audit of the generic inferred-type certificate compiler law."""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from judge.verify import verify_answer

SOLVER=ROOT/'submissions/mathgraph/solver.py'
GATE=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/certificate-elision-transfer-audit.json'
KNOWN={'evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196','evaluation_order5_0014','evaluation_order5_0042'}
CONFIGS=['evaluation_normal','evaluation_hard','evaluation_extra_hard','evaluation_order5']
SECONDS=3.0

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def compact(code):
 out=[];n=0
 for line in code.splitlines():
  s=line.lstrip()
  if s.startswith('have ') and ' : ' in line and ' := ' in line:
   left,expr=line.split(' := ',1);name,typ=left.split(' : ',1)
   if name.strip().startswith('have ') and typ:
    line=name+' := '+expr;n+=1
  out.append(line)
 return '\n'.join(out)+'\n',n

def derive(m,gate,row):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':SECONDS,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':256,'maximum_clauses':6000,'normalization_steps':256,'maximum_proof_nodes':50000})
 eng=m.TargetGroundedRefutation(src,tgt,time.monotonic()+SECONDS,limits)
 recipe,stats=gate.solve_given(m,eng.search)
 if recipe is None:return None,stats
 try:
  rr=eng.inline_recipe(recipe);cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+1.0,eng.search.limits);nodes,root=cc.compile(rr)
  ok=(nodes[root].lhs==tgt[0] and nodes[root].rhs==tgt[1] and m.replay_dag(src,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes']))
  if not ok:return None,stats
  raw,pn=m.make_dag_certificate(tgt,nodes,root);return (raw,pn),stats
 except Exception as e:
  return None,{**stats,'compile_exception':type(e).__name__}

def main():
 m=load(SOLVER,'mg_elision_transfer');gate=load(GATE,'given_gate_elision_transfer')
 rows=[]
 for cfg in CONFIGS:
  true=[dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train') if bool(r.get('answer')) and r.get('id') not in KNOWN]
  for i in (17,73):
   if i<len(true):rows.append(true[i])
 records=[]
 for row in rows:
  found,stats=derive(m,gate,row)
  if found is None:
   rec={'id':row['id'],'closure':False,'stats':stats}
  else:
   raw,pn=found;code,n=compact(raw);judged=verify_answer(row,json.dumps({'verdict':'true','code':code}))
   rec={'id':row['id'],'closure':True,'proof_nodes':pn,'raw_bytes':len(raw.encode()),'compact_bytes':len(code.encode()),'elided':n,'compression_ratio':round(len(code.encode())/len(raw.encode()),6),'official_status':judged.get('status'),'official_error_code':judged.get('error_code'),'axioms':judged.get('axioms',[]),'direct_declarations':judged.get('direct_declarations',[]),'stats':stats}
  records.append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 closed=[r for r in records if r.get('closure')]
 summary={'n':len(records),'closures':len(closed),'official_accepted':sum(r.get('official_status')=='accepted' for r in closed),'failures':[r['id'] for r in closed if r.get('official_status')!='accepted']}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps({'schema':'mathgraph.certificate-elision-transfer.v1','rows':records,'summary':summary},indent=2,sort_keys=True)+'\n')
 print(json.dumps(summary,indent=2,sort_keys=True))
 if summary['failures']:raise SystemExit(1)

if __name__=='__main__':main()
