#!/usr/bin/env python3
"""Frozen inference-language genome sweep on the four post-hard0196 residuals.

Mutation alphabet predates this gate: quotient matching, source re-entry, and
contextual overlap. No Vampire proof bodies, target-specific identities, or
answer labels are used to construct candidates. Every positive must replay.
"""
import importlib.util, json, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
QM=ROOT/'experiments/mathgraph/run_quotient_matcher_research.py'
OUT=ROOT/'experiments/mathgraph/results/inference-language-genome-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def replay(m,source,found,limit=None):
 if found is None:return False
 try:
  nodes,root=found
  return bool(m.replay_dag(source,nodes,root,maximum_term_size=limit))
 except Exception:return False

def quotient(m,qm,row,seconds,generations,instances,edge_cap):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);t=time.monotonic()
 try:
  s=qm.QuotientMatcher(m,src,tgt,t+seconds,edge_cap=edge_cap);found=s.solve(generations,instances);ok=replay(m,src,found,s.maximum_term_size)
  rec={'closure':ok,'seconds':round(time.monotonic()-t,6),'matches':s.matches,'quotient_only':s.quotient_only,'instances':s.instances,'generations':s.generations,'replay_failures':s.replay_failures}
  if ok:
   nodes,root=found;code,_=m.make_dag_certificate(tgt,nodes,root);rec['certificate_bytes']=len(code.encode())
  return rec
 except Exception as e:return {'closure':False,'seconds':round(time.monotonic()-t,6),'error':repr(e)}

def reentry(m,row,seconds,cfg_index):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);cfg=m.REENTRY_PORTFOLIO[cfg_index];t=time.monotonic()
 limits=dict(cfg['limits']);s=m.EqualitySearch(src,tgt,t+seconds,limits);base=s.solve()
 if base is not None:return {'closure':replay(m,src,base,limits.get('max_term_size')),'seconds':round(time.monotonic()-t,6),'base_closed':True}
 s.deadline=t+seconds;s.max_term_size=cfg['reentry_term_size'];s.max_derivation_nodes=cfg['reentry_nodes'];s.max_graph_edges=cfg['reentry_edges'];s.exhaustion=None
 found=s.solve_reentry(cfg['generations'],cfg['new_terms'],cfg['instances'],targeted=cfg['targeted']);ok=replay(m,src,found,s.max_term_size)
 return {'closure':ok,'seconds':round(time.monotonic()-t,6),'base_closed':False,'generations_completed':s.generations_completed,'graph_edges':s.graph_edges,'reentry_terms':len(s.reentry_terms_used),'exhaustion':s.exhaustion}

def contextual(m,row,seconds,cfg_index):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);cfg=m.CONTEXTUAL_PORTFOLIO[cfg_index];t=time.monotonic();limits=dict(cfg['limits']);s=m.ContextualSearch(src,tgt,t+seconds,limits)
 found=s.solve_contextual_overlap(cfg['maximum_overlap_depth'],cfg['maximum_context_depth'],cfg['maximum_source_instances'],cfg['maximum_candidates'],cfg['maximum_new_nodes']);ok=replay(m,src,found,limits.get('max_term_size'))
 return {'closure':ok,'seconds':round(time.monotonic()-t,6),'overlap_candidates':s.overlap_candidates,'overlaps_added':s.overlaps_added,'components_joined':s.components_joined,'missing_target_introduced':s.missing_target_introduced,'graph_edges':s.graph_edges,'exhaustion':s.exhaustion}

def main():
 m=load(SOLVER,'mg_genome');qm=load(QM,'qm_genome');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 genomes=[
  ('quotient_q1',lambda r:quotient(m,qm,r,8.0,1,96,128)),
  ('quotient_q2',lambda r:quotient(m,qm,r,8.0,2,128,256)),
  ('quotient_q3',lambda r:quotient(m,qm,r,8.0,3,192,384)),
  ('reentry_r0',lambda r:reentry(m,r,8.0,0)),
  ('reentry_r1',lambda r:reentry(m,r,8.0,min(1,len(m.REENTRY_PORTFOLIO)-1))),
  ('context_c0',lambda r:contextual(m,r,8.0,0)),
  ('context_c2',lambda r:contextual(m,r,8.0,min(2,len(m.CONTEXTUAL_PORTFOLIO)-1))),
 ]
 out={'schema':'mathgraph.inference-language-genome.v1','ids':IDS,'genomes':[g for g,_ in genomes],'records':[]}
 for rid in IDS:
  for name,fn in genomes:
   rec={'id':rid,'genome':name,**fn(rows[rid])};out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['gains']=[{'id':r['id'],'genome':r['genome']} for r in out['records'] if r.get('closure')]
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains']},indent=2))
if __name__=='__main__':main()
