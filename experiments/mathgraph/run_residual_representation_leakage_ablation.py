#!/usr/bin/env python3
import json,hashlib,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; R=ROOT/'experiments/mathgraph/results'; HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('rrt',HERE/'run_residual_representation_tournament.py'); M=importlib.util.module_from_spec(spec); spec.loader.exec_module(M)
OUT=R/'residual-representation-leakage-ablation.json'
LINEAGES={
 'primary':(R/'contextual_development_frozen/sample_200_development.json',R/'contextual_development_all/sample_200_development.json'),
 'fin3':(R/'fin3_development_frozen/sample_200_development.json',R/'fin3_development_all/sample_200_development.json'),
}
STRUCTURAL=['static.nodes','static.edges','static.source_total','static.source_families','static.source_entropy','static.source_max_share','static.generations','static.max_term_size','static.edge_node_gap','static.node_saturation','static.source_density','static.dense_saturation']
OPERATIONAL=['static.elapsed','static.term_budget_exhausted','static.replay_seconds','static.certificate_bytes','static.search_persistence']
def build(a,b):
 F={r['id']:r for r in json.loads(a.read_text())}; D={r['id']:r for r in json.loads(b.read_text())}; rows=[]
 for i in sorted(set(F)&set(D)):
  x,fm,dm=M.feat(F[i],D[i]); pf=[m.get('portfolio') for m in fm]; pd=[m.get('portfolio') for m in dm]
  labels={'new_portfolio':any(p not in pf for p in pd),'residual_trajectory_changed':pd!=pf or any(x[k]!=0 for k in ('diff.nodes','diff.source_total','diff.components_joined','diff.narrowing_successors','diff.overlaps_added')),'target_narrowing':any(m.get('portfolio')=='target-narrowing' for m in dm),'target_structure_introduced':any(M.num(m.get('missing_target_introduced'))>0 for m in dm)}
  rows.append({'id':i,'x':x,'labels':labels})
 return rows
def main():
 out={'schema':'mathgraph.residual-representation-leakage-ablation.v1','protocol':{'verdict_derived_features_excluded':True,'structural_features':STRUCTURAL,'operational_features':OPERATIONAL,'combined_clean_features':STRUCTURAL+OPERATIONAL},'lineages':{},'cross_lineage':{}}
 tops={}
 for lname,(a,b) in LINEAGES.items():
  base=build(a,b); lo={'paired_cases':len(base),'targets':{}}
  for target in base[0]['labels']:
   rows=[{'id':r['id'],'x':r['x'],'y':r['labels'][target]} for r in base]; n=sum(r['y'] for r in rows); tr={'positives':n,'negatives':len(rows)-n}
   if n>=3 and len(rows)-n>=3:
    fams={'structural_only':STRUCTURAL,'operational_only':OPERATIONAL,'combined_clean':STRUCTURAL+OPERATIONAL}
    tr['families']={f:M.sweep(rows,fs,20260910+ix,10) for ix,(f,fs) in enumerate(fams.items())}
    tops[(lname,target)]={f:{z['signature'] for z in tr['families'][f][:5]} for f in fams}
   lo['targets'][target]=tr
  out['lineages'][lname]=lo
 for target in ('new_portfolio','residual_trajectory_changed','target_narrowing','target_structure_introduced'):
  if ('primary',target) not in tops or ('fin3',target) not in tops: continue
  out['cross_lineage'][target]={}
  for fam in ('structural_only','operational_only','combined_clean'):
   a=tops[('primary',target)][fam]; b=tops[('fin3',target)][fam]
   out['cross_lineage'][target][fam]={'primary_top5':sorted(a),'fin3_top5':sorted(b),'intersection':sorted(a&b),'jaccard':round(len(a&b)/max(1,len(a|b)),4)}
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
