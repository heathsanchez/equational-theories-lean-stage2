#!/usr/bin/env python3
import json,re,statistics,hashlib,random
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];R=ROOT/'experiments/mathgraph/results';OUT=R/'residual-factorization-id-holdout-closure.json'
P=R/'contextual_development_all/sample_200_development.json'
PAT=re.compile(r'MATHGRAPH_METRICS\s+(\{.*?\})(?:\n|$)')
def num(x):return float(x) if isinstance(x,(int,float,bool)) else 0.0
def metrics(r):
 o=[]
 for e in r.get('log',[]):
  if not isinstance(e,dict) or e.get('type')!='solver_stderr':continue
  for z in PAT.finditer(e.get('tail','')):
   try:o.append(json.loads(z.group(1)))
   except:pass
 return o
def src(m):return [float(v) for v in m.get('source_instances',{}).values() if isinstance(v,(int,float))]
def mean(a):return sum(a)/len(a) if a else 0.0
def sd(a):
 if len(a)<2:return 1.0
 q=statistics.pstdev(a);return q if q>1e-12 else 1.0
def entropy(v):
 import math
 s=sum(v);return -sum((x/s)*math.log(x/s+1e-15) for x in v if x>0) if s>0 else 0.0
def action(ms):
 t={k:sum(num(m.get(k)) for m in ms) for k in ('components_joined','missing_target_introduced','narrowing_successors','overlaps_added')}
 if t['components_joined']>0:return 'COMPONENT_BRIDGE'
 if t['missing_target_introduced']>0:return 'TARGET_STRUCTURE'
 if t['narrowing_successors']>0:return 'NARROWING'
 if t['overlaps_added']>0:return 'OVERLAP'
 return 'NO_PRODUCTIVE_OPERATOR'
def feat(r):
 ms=metrics(r)
 if not ms:return None
 a=next((m for m in ms if m.get('portfolio')=='initial-chain'),ms[0]);v=src(a);st=sum(v)
 x={'nodes':num(a.get('equality_nodes')),'edges':num(a.get('graph_edges')),'source_total':st,'source_families':len(v),'source_entropy':entropy(v),'source_max_share':max(v)/max(1,st) if v else 0.0,'generations':num(a.get('generations')),'max_term_size':num(a.get('max_term_size')),'term_budget_exhausted':float(a.get('exhaustion')=='term budget exhausted'),'edge_node_gap':num(a.get('graph_edges'))-num(a.get('equality_nodes'))}
 x['node_saturation']=x['nodes']/4000.;x['source_density']=x['source_total']/(1+x['nodes']);x['dense_saturation']=x['source_density']*x['node_saturation']
 return {'id':str(r.get('id')),'x':x,'y':action(ms)}
def fit(rows,fs):
 base={f:(mean([r['x'][f] for r in rows]),sd([r['x'][f] for r in rows])) for f in fs};pri=Counter(r['y'] for r in rows);cen={}
 for y in pri:
  rr=[r for r in rows if r['y']==y];cen[y]={f:mean([(r['x'][f]-base[f][0])/base[f][1] for r in rr]) for f in fs}
 return base,pri,cen
def pred(r,m):
 base,pri,cen=m;return min(((sum(((r['x'][f]-mu)/s-c[f])**2 for f,(mu,s) in base.items()),-pri[y],y) for y,c in cen.items()))[2]
def macro(rows,ps):
 labs=sorted(set(r['y'] for r in rows));return mean([sum(ps[i]==y for i,r in enumerate(rows) if r['y']==y)/sum(r['y']==y for r in rows) for y in labs]) if labs else 0.0
def ev(tr,te,fs):return macro(te,[pred(r,fit(tr,fs)) for r in te])
def fold(r,n=5):return int(hashlib.sha256(r['id'].encode()).hexdigest(),16)%n
def cv(rows,fs):
 z=[]
 for k in range(5):
  tr=[r for r in rows if fold(r)!=k];te=[r for r in rows if fold(r)==k]
  if tr and te:z.append(ev(tr,te,fs))
 return mean(z)
def adaptive(rows,fs,g=.015,merge=.005,maxk=5):
 sc,f=max((cv(rows,[f]),f) for f in fs);sel=[f];rem=[q for q in fs if q!=f];hist=[['seed',f,round(sc,4)]]
 while rem and len(sel)<maxk:
  ns,nf=max((cv(rows,sel+[q]),q) for q in rem);gain=ns-sc
  if gain<g:hist.append(['stop',nf,round(gain,4)]);break
  sel.append(nf);rem.remove(nf);sc=ns;hist.append(['split',nf,round(gain,4)])
  changed=True
  while changed and len(sel)>1:
   changed=False
   for q in list(sel):
    t=[f for f in sel if f!=q];s=cv(rows,t)
    if sc-s<=merge:sel=t;rem.append(q);sc=s;hist.append(['merge',q,round(sc-s,4)]);changed=True;break
 return sel,hist
def hsplit(rows,seed):
 tr=[];te=[]
 for r in rows:
  v=int(hashlib.sha256((r['id']+'|'+str(seed)).encode()).hexdigest(),16)%10
  (tr if v<6 else te).append(r)
 return tr,te
def shuffled(rows,seed):
 q=[dict(r) for r in rows];labs=[r['y'] for r in q];random.Random(seed).shuffle(labs)
 for r,y in zip(q,labs):r['y']=y
 return q
def main():
 raw=json.loads(P.read_text());rows=[z for r in raw if (z:=feat(r))]
 counts=Counter(r['y'] for r in rows);keep={y for y,n in counts.items() if n>=5};rows=[r for r in rows if r['y'] in keep]
 fs=list(rows[0]['x']);runs=[]
 for seed in range(30):
  tr,te=hsplit(rows,seed);labs=set(r['y'] for r in tr)&set(r['y'] for r in te)
  if len(labs)<2:continue
  tr=[r for r in tr if r['y'] in labs];te=[r for r in te if r['y'] in labs]
  if min(Counter(r['y'] for r in tr).values())<2 or min(Counter(r['y'] for r in te).values())<2:continue
  sel,h=adaptive(tr,fs);score=ev(tr,te,sel);one,_=adaptive(tr,fs,maxk=1);one_score=ev(tr,te,one)
  sh=shuffled(tr,1000+seed);ssel,_=adaptive(sh,fs);shuffle_score=ev(sh,te,ssel)
  runs.append({'seed':seed,'n_train':len(tr),'n_test':len(te),'actions':sorted(labs),'factors':sel,'k':len(sel),'history':h,'macro':round(score,4),'k1_macro':round(one_score,4),'shuffle_macro':round(shuffle_score,4),'gain_k1':round(score-one_score,4),'shuffle_gap':round(score-shuffle_score,4),'id_overlap':len(set(r['id'] for r in tr)&set(r['id'] for r in te))})
 med=lambda key:statistics.median([r[key] for r in runs]) if runs else 0
 out={'schema':'mathgraph.residual-factorization-id-holdout-closure.v1','rows':len(rows),'action_counts':dict(counts),'valid_splits':len(runs),'median_macro':round(med('macro'),4),'median_k':med('k'),'median_gain_k1':round(med('gain_k1'),4),'median_shuffle_gap':round(med('shuffle_gap'),4),'all_id_disjoint':all(r['id_overlap']==0 for r in runs),'sparse_rate':round(mean([r['k']<=4 for r in runs]),4) if runs else 0,'runs':runs}
 out['gates']={'G1_at_least_20_splits':len(runs)>=20,'G2_problem_disjoint':out['all_id_disjoint'],'G3_macro_ge_060':out['median_macro']>=.60,'G4_sparse':out['sparse_rate']>=.9,'G5_beats_k1':out['median_gain_k1']>0,'G6_shuffle_gap':out['median_shuffle_gap']>=.10};out['closure_pass']=all(out['gates'].values())
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='runs'},indent=2,sort_keys=True))
if __name__=='__main__':main()
