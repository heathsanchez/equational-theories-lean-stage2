#!/usr/bin/env python3
import json, math, statistics, importlib.util
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
RESULTS=HERE/'results'
OUT=RESULTS/'residual-factorization-optimum.json'

spec=importlib.util.spec_from_file_location('rrt', HERE/'run_residual_representation_tournament.py')
rrt=importlib.util.module_from_spec(spec); spec.loader.exec_module(rrt)

DATASETS={
 'contextual':(
  RESULTS/'contextual_development_frozen/sample_200_development.json',
  RESULTS/'contextual_development_all/sample_200_development.json'),
 'fin3':(
  RESULTS/'fin3_development_frozen/sample_200_development.json',
  RESULTS/'fin3_development_all/sample_200_development.json'),
}

def load_pair(paths):
 f={r['id']:r for r in json.loads(paths[0].read_text())}; d={r['id']:r for r in json.loads(paths[1].read_text())}
 rows=[]
 for i in sorted(set(f)&set(d)):
  x,fm,dm=rrt.feat(f[i],d[i]); pf=[m.get('portfolio') for m in fm]; pd=[m.get('portfolio') for m in dm]
  labels={
   'new_portfolio':any(p not in pf for p in pd),
   'target_narrowing':any(m.get('portfolio')=='target-narrowing' for m in dm),
   'residual_trajectory_changed':pd!=pf or any(x[k]!=0 for k in ('diff.nodes','diff.source_total','diff.components_joined','diff.narrowing_successors','diff.overlaps_added')),
  }
  rows.append({'id':i,'x':x,'labels':labels})
 return rows

def bacc(y,p):
 pos=sum(y); neg=len(y)-pos
 if not pos or not neg:return .5
 tp=sum(a and b for a,b in zip(y,p)); tn=sum((not a) and (not b) for a,b in zip(y,p))
 return .5*(tp/pos+tn/neg)

def mean(xs): return sum(xs)/len(xs) if xs else 0.0

def stdev(xs):
 if len(xs)<2:return 1.0
 s=statistics.pstdev(xs); return s if s>1e-12 else 1.0

def corr(rows,a,b):
 xa=[r['x'][a] for r in rows]; xb=[r['x'][b] for r in rows]; ma,mb=mean(xa),mean(xb); sa,sb=stdev(xa),stdev(xb)
 return mean([(u-ma)*(v-mb)/(sa*sb) for u,v in zip(xa,xb)])

def effect(rows,f,target):
 p=[r['x'][f] for r in rows if r['labels'][target]]; n=[r['x'][f] for r in rows if not r['labels'][target]]
 if not p or not n:return 0.0
 allv=p+n; return abs(mean(p)-mean(n))/stdev(allv)

def fit_centroid(rows,features,target):
 stats={}
 for f in features:
  vals=[r['x'][f] for r in rows]; m=mean(vals); s=stdev(vals)
  zp=[(r['x'][f]-m)/s for r in rows if r['labels'][target]]; zn=[(r['x'][f]-m)/s for r in rows if not r['labels'][target]]
  stats[f]=(m,s,mean(zp),mean(zn))
 return stats

def predict(row,stats):
 dp=dn=0.0
 for f,(m,s,cp,cn) in stats.items():
  z=(row['x'][f]-m)/s; dp+=(z-cp)**2; dn+=(z-cn)**2
 return dp<=dn

def eval_model(train,test,features,target):
 stats=fit_centroid(train,features,target)
 return bacc([r['labels'][target] for r in test],[predict(r,stats) for r in test])

def select(rows,features,target,k,mode):
 selected=[]; remaining=list(features)
 while remaining and len(selected)<k:
  best=None
  for f in remaining:
   sig=effect(rows,f,target)
   if mode=='signal': score=sig
   elif mode=='diverse':
    red=max([abs(corr(rows,f,g)) for g in selected],default=0.0); score=sig-0.45*red
   else: # split: reward features that improve in-sample centroid discrimination
    trial=selected+[f]; score=eval_model(rows,rows,trial,target)-0.01*len(trial)
   cand=(score,f)
   if best is None or cand>best: best=cand
  selected.append(best[1]); remaining.remove(best[1])
 return selected

def main():
 ds={k:load_pair(v) for k,v in DATASETS.items()}
 # Strictly prospective residual facets. Remove verdict-derived true_problem and post-intervention diffs.
 base_features=[f for f in ds['contextual'][0]['x'] if f.startswith('static.') and f!='static.true_problem']
 structural=[f for f in base_features if f not in ('static.elapsed','static.search_persistence','static.replay_seconds','static.certificate_bytes')]
 tracks={}
 for feature_family,features in [('all_static',base_features),('structural_only',structural)]:
  for target in ('new_portfolio','target_narrowing','residual_trajectory_changed'):
   if any(sum(r['labels'][target] for r in rows)<3 or sum(not r['labels'][target] for r in rows)<3 for rows in ds.values()): continue
   key=f'{feature_family}:{target}'; entries=[]
   for mode in ('signal','diverse','split'):
    for k in range(1,min(12,len(features))+1):
     fwd=select(ds['contextual'],features,target,k,mode); rev=select(ds['fin3'],features,target,k,mode)
     a=eval_model(ds['contextual'],ds['fin3'],fwd,target); b=eval_model(ds['fin3'],ds['contextual'],rev,target)
     transfer=(a+b)/2; overlap=len(set(fwd)&set(rev))/max(1,len(set(fwd)|set(rev)))
     # Optimum balances transfer, recurrence of chosen factors, and representational simplicity.
     objective=transfer+0.05*overlap-0.0125*(k-1)
     entries.append({'process':mode,'k':k,'context_to_fin3_bacc':round(a,4),'fin3_to_context_bacc':round(b,4),'symmetric_transfer_bacc':round(transfer,4),'factor_jaccard':round(overlap,4),'objective':round(objective,4),'context_factors':fwd,'fin3_factors':rev})
   entries.sort(key=lambda z:(-z['objective'],-z['symmetric_transfer_bacc'],z['k']))
   best_by_k=[]
   for k in sorted({e['k'] for e in entries}): best_by_k.append(max((e for e in entries if e['k']==k),key=lambda z:z['objective']))
   tracks[key]={'winner':entries[0],'top10':entries[:10],'best_by_k':best_by_k}
 winners=[{'track':k,**v['winner']} for k,v in tracks.items()]
 # Consensus optimum: median winning k, and process recurrence.
 ks=[w['k'] for w in winners]; processes={m:sum(w['process']==m for w in winners) for m in ('signal','diverse','split')}
 out={'schema':'mathgraph.residual-factorization-optimum.v1','datasets':{k:len(v) for k,v in ds.items()},'objective':'symmetric cross-lineage balanced accuracy + 0.05 factor recurrence - 0.0125 per extra factor','tracks':tracks,'winners':winners,'consensus':{'winning_k_values':ks,'median_winning_k':statistics.median(ks) if ks else None,'process_win_counts':processes}}
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__': main()
