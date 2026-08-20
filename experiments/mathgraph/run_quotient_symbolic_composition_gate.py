#!/usr/bin/env python3
"""Second-order composition gate: quotient-derived equalities -> symbolic superposition.

Stage 1 derives replay-verified equality-class matches. Stage 2 installs that
proof DAG as the substrate of the independently developed symbolic critical-pair
normalizer, allowing derived facts to compose with each other before target
normalization. No Vampire proof bodies, residual-specific identities, or answer
labels are used. Any positive must replay to the original source law.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
QM=ROOT/'experiments/mathgraph/run_quotient_matcher_research.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
OUT=ROOT/'experiments/mathgraph/results/quotient-symbolic-composition-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def run(m,qm,sym,row,generations,instances,seconds):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);started=time.monotonic();stage1=min(seconds*0.55,6.0)
 try:
  q=qm.QuotientMatcher(m,src,tgt,started+stage1,edge_cap=384)
  initial=len(q.nodes)
  for g in range(generations):
   if time.monotonic()>=q.deadline:break
   q.generations=g+1;q.one_generation(instances)
  quotient_nodes=len(q.nodes)-initial
  # Second-order promotion: use the quotient proof DAG as the initial theorem
  # language for symbolic critical-pair generation.
  Norm=sym.make_normalizer(m)
  cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=max(0.5,seconds-(time.monotonic()-started)),candidate_equalities=2400,overlap_candidates=2000,selected_rules=256,replayed_rules=1000,maximum_term_size=35,maximum_proof_nodes=20000)
  s=Norm(src,tgt,started+seconds,cfg)
  s.nodes=q.nodes
  before_symbolic=len(s.nodes)
  found=s.solve()
  ok=False;cert=None;proof_nodes=None
  if found is not None:
   nodes,root=found;ok=bool(m.replay_dag(src,nodes,root,maximum_term_size=35,maximum_nodes=20000))
   if ok:
    code,proof_nodes=m.make_dag_certificate(tgt,nodes,root);cert=len(code.encode())
  return {'closure':ok,'seconds':round(time.monotonic()-started,6),'quotient_generations':q.generations,'quotient_matches':q.matches,'quotient_only':q.quotient_only,'quotient_instances':q.instances,'quotient_replay_failures':q.replay_failures,'quotient_derived_nodes':quotient_nodes,'symbolic_input_nodes':before_symbolic,'symbolic_nodes_after':len(s.nodes),'symbolic_new_nodes':len(s.nodes)-before_symbolic,'symbolic_overlaps':s.overlap_candidates,'symbolic_rules':len(s.rules),'symbolic_selected_rules':len(s.selected_rules),'symbolic_replay_failures':s.replay_failures,'left_steps':s.left_steps,'right_steps':s.right_steps,'certificate_bytes':cert,'proof_nodes':proof_nodes}
 except Exception as e:return {'closure':False,'seconds':round(time.monotonic()-started,6),'error':repr(e)}

def main():
 m=load(SOLVER,'mg_qsym');qm=load(QM,'qm_qsym');sym=load(SYM,'sym_qsym');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 arms=[('q1_symbolic',1,128,8.0),('q2_symbolic',2,192,12.0),('q3_symbolic',3,256,16.0)]
 out={'schema':'mathgraph.quotient-symbolic-composition.v1','records':[]}
 for rid in IDS:
  for name,g,i,s in arms:
   rec={'id':rid,'arm':name,**run(m,qm,sym,rows[rid],g,i,s)};out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['gains']=[{'id':r['id'],'arm':r['arm']} for r in out['records'] if r.get('closure')]
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains']},indent=2))
if __name__=='__main__':main()
