#!/usr/bin/env python3
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; R=ROOT/'experiments/mathgraph/results'; OUT=R/'residual-atlas-inventory.json'
def walk(x,path='',acc=None):
 if acc is None: acc={'keys':{},'decisions':{},'strings':{}}
 if isinstance(x,dict):
  for k,v in x.items():
   acc['keys'][k]=acc['keys'].get(k,0)+1
   if k in ('decision','status','verdict','schema','outcome','result') and isinstance(v,(str,bool,int,float)):
    s=str(v); acc['strings'][f'{k}={s}']=acc['strings'].get(f'{k}={s}',0)+1
   walk(v,path+'.'+k,acc)
 elif isinstance(x,list):
  for v in x: walk(v,path+'[]',acc)
 return acc
def summarize(p):
 try:x=json.loads(p.read_text())
 except Exception as e:return {'path':str(p.relative_to(R)),'error':str(e)}
 a=walk(x); o={'path':str(p.relative_to(R)),'bytes':p.stat().st_size,'top_type':type(x).__name__,'top_keys':sorted(x.keys()) if isinstance(x,dict) else [],'rows':len(x) if isinstance(x,list) else None,'signals':sorted(a['strings'].items(),key=lambda kv:(-kv[1],kv[0]))[:20],'frequent_keys':sorted(a['keys'].items(),key=lambda kv:(-kv[1],kv[0]))[:25]}
 if isinstance(x,list) and x and all(isinstance(r,dict) for r in x):
  o['solved_true']=sum(r.get('solved') is True for r in x); o['solved_false']=sum(r.get('solved') is False for r in x); o['true_unsolved']=sum(r.get('verdict')=='true' and r.get('solved') is False for r in x)
 return o
def main():
 files=sorted(R.rglob('*.json')); inv=[summarize(p) for p in files if p.name not in {OUT.name,'residual-representation-tournament.json','residual-atlas-external-validation.json'}]
 candidates=[]
 for z in inv:
  text=' '.join(k for k,_ in z.get('signals',[])).lower(); keys={k for k,_ in z.get('frequent_keys',[])}
  score=0
  for needle in ('gain','promot','closure','introduced','verified','success','solved','causal','ablation'): score += 2 if needle in text else 0
  score += int(bool(keys & {'A','B','C','ablation','baseline','intervention','decision','solved','promotion'}))
  if score:candidates.append({'path':z['path'],'score':score,'rows':z.get('rows'),'signals':z.get('signals',[])[:8],'top_keys':z.get('top_keys',[])})
 out={'schema':'mathgraph.residual-atlas-inventory.v1','json_files':len(inv),'files':inv,'candidate_experiments':sorted(candidates,key=lambda z:(-z['score'],z['path']))[:40]}
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps({'schema':out['schema'],'json_files':out['json_files'],'candidate_experiments':out['candidate_experiments']},indent=2))
if __name__=='__main__':main()
