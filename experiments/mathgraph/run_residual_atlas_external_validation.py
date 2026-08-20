#!/usr/bin/env python3
import json,re,math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; R=ROOT/'experiments/mathgraph/results'
H=R/'contextual_frozen/sample_200_holdout.json'; F=R/'contextual_final/sample_200.json'; OUT=R/'residual-atlas-external-validation.json'
PAT=re.compile(r'MATHGRAPH_METRICS\s+(\{.*?\})(?:\n|$)')
def metrics(row):
 out=[]
 for e in row.get('log',[]):
  if e.get('type')!='solver_stderr': continue
  for z in PAT.finditer(e.get('tail','')):
   try: out.append(json.loads(z.group(1)))
   except: pass
 return out
def first(ms,n='initial-chain'): return next((m for m in ms if m.get('portfolio')==n),{})
def num(x): return float(x) if isinstance(x,(int,float,bool)) else 0.0
def vals(m): return [float(v) for v in m.get('source_instances',{}).values() if isinstance(v,(int,float))]
def static(row):
 m=first(metrics(row)); s=sum(vals(m)); nodes=num(m.get('equality_nodes')); sat=nodes/4000.; dens=s/(1+nodes); elapsed=num(row.get('elapsed_seconds'))
 return {'nodes':nodes,'source_total':s,'node_saturation':sat,'source_density':dens,'search_persistence':elapsed*(1+sat),'dense_saturation':dens*sat,'elapsed':elapsed}
def confusion(rows,pred,label):
 tp=sum(pred(r) and label(r) for r in rows); fp=sum(pred(r) and not label(r) for r in rows); fn=sum((not pred(r)) and label(r) for r in rows); tn=sum((not pred(r)) and not label(r) for r in rows)
 pos=tp+fn; neg=fp+tn
 return {'tp':tp,'fp':fp,'fn':fn,'tn':tn,'support':tp+fp,'positives':pos,'precision':round(tp/max(1,tp+fp),4),'recall':round(tp/max(1,pos),4),'balanced_accuracy':round(.5*(tp/max(1,pos)+tn/max(1,neg)),4),'prevalence':round(pos/max(1,len(rows)),4),'selected_rate':round((tp+fp)/max(1,len(rows)),4),'lift':round((tp/max(1,tp+fp))/max(1e-12,pos/max(1,len(rows))),4) if tp+fp else 0.0}
def main():
 h={r['id']:r for r in json.loads(H.read_text())}; f={r['id']:r for r in json.loads(F.read_text())}; ids=sorted(set(h)&set(f)); rows=[]
 for i in ids:
  hr,fr=h[i],f[i]; x=static(hr)
  rows.append({'id':i,'x':x,'holdout_solved':bool(hr.get('solved')),'final_solved':bool(fr.get('solved')),'verdict':hr.get('verdict')})
 rules={
  'PERSIST_DENSE':lambda r:r['x']['search_persistence']>=2.3405 and r['x']['source_density']>=0.23844,
  'PERSIST_TOTAL':lambda r:r['x']['search_persistence']>=2.3405 and r['x']['source_total']>=693,
  'PERSIST_DENSE_TOTAL':lambda r:r['x']['search_persistence']>=2.3405 and r['x']['source_density']>=0.23844 and r['x']['source_total']>=693,
  'PERSIST_DENSE_SAT':lambda r:r['x']['search_persistence']>=2.3405 and r['x']['dense_saturation']>=0.182205,
 }
 labels={
  'frozen_to_final_gain':lambda r:r['final_solved'] and not r['holdout_solved'],
  'frozen_unresolved_true':lambda r:r['verdict']=='true' and not r['holdout_solved'],
  'final_unresolved_true':lambda r:r['verdict']=='true' and not r['final_solved'],
 }
 out={'schema':'mathgraph.residual-atlas-external-validation.v1','protocol':{'thresholds_frozen_before_external_outcome_evaluation':True,'source':'v3 target_structure_introduced full-data rules','no_refit_on_external':True},'holdout_rows':len(h),'final_rows':len(f),'paired_ids':len(rows),'holdout_solved':sum(r['holdout_solved'] for r in rows),'final_solved':sum(r['final_solved'] for r in rows),'labels':{},'rules':{}}
 for n,lab in labels.items(): out['labels'][n]=sum(lab(r) for r in rows)
 for n,p in rules.items():
  out['rules'][n]={'thresholds':{'search_persistence_min':2.3405,**({'source_density_min':0.23844} if 'DENSE' in n else {}),**({'source_total_min':693} if 'TOTAL' in n else {}),**({'dense_saturation_min':0.182205} if n=='PERSIST_DENSE_SAT' else {})},'evaluations':{k:confusion(rows,p,lab) for k,lab in labels.items()},'selected_ids':[r['id'] for r in rows if p(r)]}
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
