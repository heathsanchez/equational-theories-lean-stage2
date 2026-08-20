#!/usr/bin/env python3
"""Compositional representation gate: quotient-derived verified equalities -> normalizer rules.

The quotient matcher and EquationalNormalizer share one proof-DAG list. The
existing quotient route uses newly derived equalities only as equality-class
edges. This gate asks whether recompiling those same replay-verified derived
edges into the normalizer's rule language creates new capability.

No Vampire proof bodies, residual-specific identities, or answer labels are
used. Positive credit requires replay to the original source law.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
QM=ROOT/'experiments/mathgraph/run_quotient_matcher_research.py'
OUT=ROOT/'experiments/mathgraph/results/quotient-recompile-composition-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def run(m,qm,row,generations,instances,seconds):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);started=time.monotonic()
 try:
  q=qm.QuotientMatcher(m,src,tgt,started+seconds,edge_cap=384)
  initial_nodes=len(q.nodes)
  added=[]
  for g in range(generations):
   if time.monotonic()>=q.deadline:break
   q.generations=g+1;added.extend(q.one_generation(instances))
  derived_nodes=len(q.nodes)-initial_nodes
  # Critical composition: compile the newly verified quotient derivations into
  # the already-shared normalizer's rewrite/rule representation, then solve.
  found=q.normalizer.solve()
  ok=False;cert=None;proof_nodes=None
  if found is not None:
   nodes,root=found
   ok=bool(m.replay_dag(src,nodes,root,maximum_term_size=max(q.maximum_term_size,31),maximum_nodes=20000))
   if ok:
    code,proof_nodes=m.make_dag_certificate(tgt,nodes,root);cert=len(code.encode())
  return {'closure':ok,'seconds':round(time.monotonic()-started,6),'quotient_generations':q.generations,'quotient_matches':q.matches,'quotient_only':q.quotient_only,'quotient_instances':q.instances,'quotient_replay_failures':q.replay_failures,'derived_nodes_before_recompile':derived_nodes,'normalizer_nodes_after':len(q.normalizer.nodes),'normalizer_rules':len(q.normalizer.rules),'selected_rules':len(q.normalizer.selected_rules),'left_steps':q.normalizer.left_steps,'right_steps':q.normalizer.right_steps,'normalizer_replay_failures':q.normalizer.replay_failures,'certificate_bytes':cert,'proof_nodes':proof_nodes}
 except Exception as e:
  return {'closure':False,'seconds':round(time.monotonic()-started,6),'error':repr(e)}

def main():
 m=load(SOLVER,'mg_qrc');qm=load(QM,'qm_qrc');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 arms=[('q1_recompile',1,128,6.0),('q2_recompile',2,192,8.0),('q3_recompile',3,256,10.0)]
 out={'schema':'mathgraph.quotient-recompile-composition.v1','records':[]}
 for rid in IDS:
  for name,g,i,s in arms:
   rec={'id':rid,'arm':name,**run(m,qm,rows[rid],g,i,s)};out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['gains']=[{'id':r['id'],'arm':r['arm']} for r in out['records'] if r.get('closure')]
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains']},indent=2))
if __name__=='__main__':main()
