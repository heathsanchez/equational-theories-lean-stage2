#!/usr/bin/env python3
"""Orthogonal language swarm v2 on the four post-hard0196 residuals.

All constructors predate this gate: symbolic superposition, BridgeIR, and
variable-omission collapse. Candidate construction uses no Vampire proof body
or residual-specific identity. Positive credit requires replay.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYMBOLIC=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
COLLAPSE=ROOT/'experiments/mathgraph/run_collapse_context_research.py'
OUT=ROOT/'experiments/mathgraph/results/inference-language-swarm-v2.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def symbolic(m,sym,row,seconds=5.0):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);Norm=sym.make_normalizer(m);cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=seconds,candidate_equalities=1600,overlap_candidates=1200,selected_rules=192,replayed_rules=600,maximum_term_size=31,maximum_proof_nodes=6000);t=time.monotonic();s=Norm(src,tgt,t+seconds,cfg);found=s.solve();ok=False;cert=None
 if found is not None:
  nodes,root=found;ok=bool(m.replay_dag(src,nodes,root,maximum_term_size=31));
  if ok:code,_=m.make_dag_certificate(tgt,nodes,root);cert=len(code.encode())
 return {'closure':ok,'seconds':round(time.monotonic()-t,6),'consequences':len(s.nodes),'overlaps':s.overlap_candidates,'rules':len(s.rules),'selected_rules':len(s.selected_rules),'replay_failures':s.replay_failures,'certificate_bytes':cert}

def bridge(m,row,variant,portfolio_index):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);cfg=dict(m.BRIDGE_IR_PORTFOLIO[portfolio_index]);cfg.update(ranking=variant,seconds=6.0,maximum_proof_nodes=max(cfg.get('maximum_proof_nodes',0),6000));t=time.monotonic();s=m.BridgeIR(src,tgt,t+6.0,cfg);found=s.solve();ok=False;cert=None
 if found is not None:
  nodes,root=found;limit=s.normalizer.configuration['maximum_term_size'];ok=bool(m.replay_dag(src,nodes,root,maximum_term_size=limit,maximum_nodes=cfg['maximum_proof_nodes']));
  if ok:code,_=m.make_dag_certificate(tgt,nodes,root);cert=len(code.encode())
 return {'closure':ok,'seconds':round(time.monotonic()-t,6),'variant':variant,'bridge_candidates':s.bridge_equality_candidates,'replayed_bridges':s.replayed_bridge_equalities,'matches_attempted':s.bridge_matches_attempted,'states_created':s.bridge_states_created,'no_match_activations':s.no_match_activations,'shared_normal_form_hits':s.shared_normal_form_hits,'exhaustion':s.exhaustion,'certificate_bytes':cert}

def collapse(m,col,row):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);t=time.monotonic();found=col.variable_omission_proof(m,src,tgt);ok=False;cert=None
 if found is not None:
  nodes,root=found;ok=bool(m.replay_dag(src,nodes,root));
  if ok:code,_=m.make_dag_certificate(tgt,nodes,root);cert=len(code.encode())
 return {'closure':ok,'seconds':round(time.monotonic()-t,6),'certificate_bytes':cert}

def main():
 m=load(SOLVER,'mg_swarm2');sym=load(SYMBOLIC,'sym_swarm2');col=load(COLLAPSE,'collapse_swarm2');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 arms=[('symbolic',lambda r:symbolic(m,sym,r)),('bridge_activation_p0',lambda r:bridge(m,r,'activation',0)),('bridge_distance_p0',lambda r:bridge(m,r,'distance',0)),('bridge_activation_p1',lambda r:bridge(m,r,'activation',min(1,len(m.BRIDGE_IR_PORTFOLIO)-1))),('collapse',lambda r:collapse(m,col,r))]
 out={'schema':'mathgraph.inference-language-swarm.v2','records':[]}
 for rid in IDS:
  for name,fn in arms:
   try:rec={'id':rid,'arm':name,**fn(rows[rid])}
   except Exception as e:rec={'id':rid,'arm':name,'closure':False,'error':repr(e)}
   out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['gains']=[{'id':r['id'],'arm':r['arm']} for r in out['records'] if r.get('closure')]
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains']},indent=2))
if __name__=='__main__':main()
