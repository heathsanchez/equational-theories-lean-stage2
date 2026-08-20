#!/usr/bin/env python3
import json, re, statistics, hashlib, itertools, importlib.util
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; R=ROOT/'experiments/mathgraph/results'; OUT=R/'adaptive-residual-archive-closure.json'
PAT=re.compile(r'MATHGRAPH_METRICS\s+(\{.*?\})(?:\n|$)')

def metrics(row):
 out=[]
 for e in row.get('log',[]):
  if not isinstance(e,dict) or e.get('type')!='solver_stderr':continue
  for z in PAT.finditer(e.get('tail','')):
   try:out.append(json.loads(z.group(1)))
   except:pass
 return out

def src(m):return [float(v) for v in m.get('source_instances',{}).values() if isinstance(v,(int,float))]
def st(m):return sum(src(m))
def entropy(v):
 s=sum(v)
 if s<=0:return 0.0
 return -sum((x/s)*__import__('math').log(x/s+1e-15) for x in v if x>0)
def num(x):return float(x) if isinstance(x,(int,float,bool)) else 0.0

def feat(row):
 ms=metrics(row)
 if not ms:return None
 a=next((m for m in ms if m.get('portfolio')=='initial-chain'),ms[0]); av=src(a)
 x={'nodes':num(a.get('equality_nodes')),'edges':num(a.get('graph_edges')),'source_total':st(a),'source_families':len(av),'source_entropy':entropy(av),'source_max_share':max(av)/max(1.0,sum(av)) if av else 0.0,'generations':num(a.get('generations')),'max_term_size':num(a.get('max_term_size')),'term_budget_exhausted':float(a.get('exhaustion')=='term budget exhausted'),'elapsed':num(row.get('elapsed_seconds')),'edge_node_gap':num(a.get('graph_edges'))-num(a.get('equality_nodes')),'replay_seconds':num(a.get('replay_seconds')),'certificate_bytes':num(a.get('certificate_bytes'))}
 x['node_saturation']=x['nodes']/4000.;x['source_density']=x['source_total']/(1+x['nodes']);x['search_persistence']=x['elapsed']*(1+x['node_saturation']);x['dense_saturation']=x['source_density']*x['node_saturation']
 return x,ms

def action(ms):
 t={k:sum(num(m.get(k)) for m in ms) for k in ('components_joined','missing_target_introduced','narrowing_successors','overlaps_added')}
 if t['components_joined']>0:return 'COMPONENT_BRIDGE'
 if t['missing_target_introduced']>0:return 'TARGET_STRUCTURE'
 if t['narrowing_successors']>0:return 'NARROWING'
 if t['overlaps_added']>0:return 'OVERLAP'
 return 'NO_PRODUCTIVE_OPERATOR'

def load_dataset(p):
 try:q=json.loads(p.read_text())
 except:return []
 if not isinstance(q,list):return []
 out=[]
 for r in q:
  if not isinstance(r,dict):continue
  fm=feat(r)
  if fm:
   x,ms=fm;out.append({'id':str(r.get('id')),'x':x,'y':action(ms)})
 return out

def mean(a):return sum(a)/len(a) if a else 0.0
def sd(a):
 if len(a)<2:return 1.0
 q=statistics.pstdev(a);return q if q>1e-12 else 1.0

def fit(rows,fs):
 labs=sorted(set(r['y'] for r in rows));base={f:(mean([r['x'][f] for r in rows]),sd([r['x'][f] for r in rows])) for f in fs};pri=Counter(r['y'] for r in rows);cen={}
 for y in labs:
  rr=[r for r in rows if r['y']==y];cen[y]={f:mean([(r['x'][f]-base[f][0])/base[f][1] for r in rr]) for f in fs}
 return base,pri,cen

def pred(r,mod):
 base,pri,cen=mod;best=None
 for y,c in cen.items():
  d=sum(((r['x'][f]-m)/s-c[f])**2 for f,(m,s) in base.items());q=(d,-pri[y],y)
  if best is None or q<best:best=q
 return best[2]

def macro(test,ps):
 labs=sorted(set(r['y'] for r in test));return mean([sum(ps[i]==y for i,r in enumerate(test) if r['y']==y)/sum(r['y']==y for r in test) for y in labs])
def ev(train,test,fs):return macro(test,[pred(r,fit(train,fs)) for r in test])
def fold(r,n=5):return int(hashlib.sha256(r['id'].encode()).hexdigest(),16)%n
def cv(rows,fs):
 z=[]
 for k in range(5):
  tr=[r for r in rows if fold(r)!=k];te=[r for r in rows if fold(r)==k]
  if tr and te:z.append(ev(tr,te,fs))
 return mean(z)

def adaptive(rows,fs,gain=.015,merge=.005,maxk=6):
 one=max((cv(rows,[f]),f) for f in fs);sel=[one[1]];cur=one[0];rem=[f for f in fs if f not in sel];hist=[['seed',sel[0],round(cur,4)]]
 while rem and len(sel)<maxk:
  sc,f=max((cv(rows,sel+[q]),q) for q in rem);g=sc-cur
  if g<gain:hist.append(['stop',f,round(g,4)]);break
  sel.append(f);rem.remove(f);cur=sc;hist.append(['split',f,round(g,4)])
  changed=True
  while changed and len(sel)>1:
   changed=False
   for q in list(sel):
    t=[f for f in sel if f!=q];s=cv(rows,t);loss=cur-s
    if loss<=merge:
     sel=t;rem.append(q);cur=s;hist.append(['merge',q,round(loss,4)]);changed=True;break
 return sel,hist

def main():
 sets={}
 for p in sorted(R.rglob('*.json')):
  if p.name.startswith(('residual-','adaptive-residual-')):continue
  rows=load_dataset(p)
  if len(rows)>=20:sets[str(p.relative_to(R))]=rows
 elig=[]
 for a,b in itertools.combinations(sorted(sets),2):
  ca=Counter(r['y'] for r in sets[a]);cb=Counter(r['y'] for r in sets[b]);common=sorted(y for y in set(ca)&set(cb) if ca[y]>=3 and cb[y]>=3)
  productive=[y for y in common if y!='NO_PRODUCTIVE_OPERATOR']
  if len(common)>=2 and productive:elig.append((a,b,common))
 fs=list(next(iter(sets.values()))[0]['x']) if sets else []
 structural=[f for f in fs if f not in ('elapsed','search_persistence','replay_seconds','certificate_bytes')]
 records=[]
 for a,b,common in elig:
  ra=[r for r in sets[a] if r['y'] in common];rb=[r for r in sets[b] if r['y'] in common]
  for fam,features in [('all',fs),('structural',structural)]:
   sa,ha=adaptive(ra,features);sb,hb=adaptive(rb,features);ab=ev(ra,rb,sa);ba=ev(rb,ra,sb);j=len(set(sa)&set(sb))/max(1,len(set(sa)|set(sb)))
   records.append({'a':a,'b':b,'family':fam,'common_actions':common,'n_a':len(ra),'n_b':len(rb),'factors_a':sa,'factors_b':sb,'k_a':len(sa),'k_b':len(sb),'history_a':ha,'history_b':hb,'a_to_b_macro':round(ab,4),'b_to_a_macro':round(ba,4),'symmetric_macro':round((ab+ba)/2,4),'jaccard':round(j,4)})
 structural_records=[r for r in records if r['family']=='structural']
 passes=[r for r in structural_records if r['k_a']<=4 and r['k_b']<=4 and r['jaccard']>=.25 and r['symmetric_macro']>=.60]
 out={'schema':'mathgraph.adaptive-residual-archive-closure.v1','datasets_scanned':len(sets),'eligible_pairs':len(elig),'records':records,'structural_pairs':len(structural_records),'structural_pass_pairs':len(passes),'pass_rate':round(len(passes)/max(1,len(structural_records)),4),'closure_pass':len(structural_records)>=3 and len(passes)/max(1,len(structural_records))>=.67,'top_structural':sorted(structural_records,key=lambda r:-r['symmetric_macro'])[:12]}
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2,sort_keys=True))
if __name__=='__main__':main()
