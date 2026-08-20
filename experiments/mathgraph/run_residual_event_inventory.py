#!/usr/bin/env python3
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; R=ROOT/'experiments/mathgraph/results'; OUT=R/'residual-event-inventory.json'
PAT=re.compile(r'MATHGRAPH_METRICS\s+(\{.*?\})(?:\n|$)')
def metrics(row):
 out=[]
 for e in row.get('log',[]):
  if not isinstance(e,dict) or e.get('type')!='solver_stderr': continue
  for z in PAT.finditer(e.get('tail','')):
   try: out.append(json.loads(z.group(1)))
   except: pass
 return out
def summarize(p):
 try:x=json.loads(p.read_text())
 except:return None
 if not isinstance(x,list) or not x or not all(isinstance(r,dict) for r in x): return None
 rows=[]
 for r in x:
  ms=metrics(r)
  if not ms: continue
  rows.append({'id':r.get('id'),'target_structure':any((m.get('missing_target_introduced') or 0)>0 for m in ms),'target_narrowing':any(m.get('portfolio')=='target-narrowing' for m in ms),'components_joined':any((m.get('components_joined') or 0)>0 for m in ms),'narrowing':any((m.get('narrowing_successors') or 0)>0 for m in ms),'multi_portfolio':len(ms)>1,'solved':bool(r.get('solved'))})
 if not rows:return None
 return {'path':str(p.relative_to(R)),'rows':len(x),'metric_rows':len(rows),'target_structure_rows':sum(r['target_structure'] for r in rows),'target_narrowing_rows':sum(r['target_narrowing'] for r in rows),'components_joined_rows':sum(r['components_joined'] for r in rows),'narrowing_rows':sum(r['narrowing'] for r in rows),'multi_portfolio_rows':sum(r['multi_portfolio'] for r in rows),'solved_rows':sum(r['solved'] for r in rows),'target_structure_ids':[r['id'] for r in rows if r['target_structure']][:30]}
def main():
 found=[]
 for p in sorted(R.rglob('*.json')):
  if p.name.startswith('residual-'): continue
  s=summarize(p)
  if s:found.append(s)
 ranked=sorted(found,key=lambda z:(-z['target_structure_rows'],-z['target_narrowing_rows'],-z['components_joined_rows'],-z['multi_portfolio_rows'],z['path']))
 out={'schema':'mathgraph.residual-event-inventory.v1','datasets_with_metrics':len(found),'datasets_with_target_structure':sum(z['target_structure_rows']>0 for z in found),'datasets_with_target_narrowing':sum(z['target_narrowing_rows']>0 for z in found),'datasets':ranked}
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps({'schema':out['schema'],'datasets_with_metrics':out['datasets_with_metrics'],'datasets_with_target_structure':out['datasets_with_target_structure'],'datasets_with_target_narrowing':out['datasets_with_target_narrowing'],'top_datasets':ranked[:25]},indent=2))
if __name__=='__main__':main()
