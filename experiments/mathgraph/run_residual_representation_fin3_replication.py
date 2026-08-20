#!/usr/bin/env python3
import json,hashlib,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; R=ROOT/'experiments/mathgraph/results'; HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('rrt',HERE/'run_residual_representation_tournament.py'); M=importlib.util.module_from_spec(spec); spec.loader.exec_module(M)
FROZEN=R/'fin3_development_frozen/sample_200_development.json'; DEV=R/'fin3_development_all/sample_200_development.json'; PRIMARY=R/'residual-representation-tournament.json'; OUT=R/'residual-representation-fin3-replication.json'
def build(pathf,pathd):
 F={r['id']:r for r in json.loads(pathf.read_text())}; D={r['id']:r for r in json.loads(pathd.read_text())}; base=[]
 for i in sorted(set(F)&set(D)):
  x,fm,dm=M.feat(F[i],D[i]); pf=[m.get('portfolio') for m in fm]; pd=[m.get('portfolio') for m in dm]
  labels={'new_portfolio':any(p not in pf for p in pd),'target_narrowing':any(m.get('portfolio')=='target-narrowing' for m in dm),'target_structure_introduced':any(M.num(m.get('missing_target_introduced'))>0 for m in dm),'residual_trajectory_changed':pd!=pf or any(x[k]!=0 for k in ('diff.nodes','diff.source_total','diff.components_joined','diff.narrowing_successors','diff.overlaps_added'))}
  base.append({'id':i,'x':x,'labels':labels,'frozen_solved':bool(F[i].get('solved')),'dev_solved':bool(D[i].get('solved'))})
 return base
def main():
 base=build(FROZEN,DEV); static=[k for k in base[0]['x'] if k.startswith('static.')]; response=[k for k in base[0]['x'] if k.startswith('diff.') or k.startswith('rel.')]; out={'schema':'mathgraph.residual-representation-fin3-replication.v1','paired_cases':len(base),'frozen_solved':sum(r['frozen_solved'] for r in base),'developed_solved':sum(r['dev_solved'] for r in base),'unique_solve_gains':sum(r['dev_solved'] and not r['frozen_solved'] for r in base),'tracks':{}}
 for target in base[0]['labels']:
  rows=[{'id':r['id'],'x':r['x'],'y':r['labels'][target]} for r in base]; n=sum(r['y'] for r in rows); tr={'positives':n,'negatives':len(rows)-n}
  if n>=3 and len(rows)-n>=3:
   tr['prospective_static']=M.sweep(rows,static,20260831); tr['retrospective_response']=M.sweep(rows,response,20260832); recur={}
   for rep in range(20):
    sub=[r for r in rows if int(hashlib.sha256((r['id']+'fin3'+str(rep)).encode()).hexdigest(),16)%2==0]
    if sum(r['y'] for r in sub)<2 or sum(not r['y'] for r in sub)<2: continue
    for z in M.sweep(sub,static,20260831+rep,5): recur[z['signature']]=recur.get(z['signature'],0)+1
   tr['canonical_static_recurrence']=[{'signature':k,'half_sample_top5_count':v} for k,v in sorted(recur.items(),key=lambda kv:(-kv[1],kv[0]))[:12]]
  out['tracks'][target]=tr
 if PRIMARY.exists():
  p=json.loads(PRIMARY.read_text()); comp={}
  for target,tr in out['tracks'].items():
   if 'prospective_static' not in tr or target not in p.get('tracks',{}): continue
   a={z['signature'] for z in tr['prospective_static'][:5]}; b={z['signature'] for z in p['tracks'][target].get('prospective_static',[])[:5]}; comp[target]={'primary_top5':sorted(b),'fin3_top5':sorted(a),'intersection':sorted(a&b),'jaccard':round(len(a&b)/max(1,len(a|b)),4)}
  out['primary_vs_fin3']=comp
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
