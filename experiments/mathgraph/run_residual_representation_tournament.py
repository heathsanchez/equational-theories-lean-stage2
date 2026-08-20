#!/usr/bin/env python3
# v2 mechanism-change tournament; trigger-only comment 20260821
import json,re,random,hashlib,itertools
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; R=ROOT/'experiments/mathgraph/results'
FROZEN=R/'contextual_development_frozen/sample_200_development.json'; DEV=R/'contextual_development_all/sample_200_development.json'; OUT=R/'residual-representation-tournament.json'
PAT=re.compile(r'MATHGRAPH_METRICS\s+(\{.*?\})(?:\n|$)')
def metrics(row):
 out=[]
 for e in row.get('log',[]):
  if e.get('type')!='solver_stderr': continue
  for z in PAT.finditer(e.get('tail','')):
   try: out.append(json.loads(z.group(1)))
   except: pass
 return out
def first(ms,n): return next((m for m in ms if m.get('portfolio')==n),{})
def num(x): return float(x) if isinstance(x,(int,float,bool)) else 0.0
def st(m): return sum(v for v in m.get('source_instances',{}).values() if isinstance(v,(int,float)))
def feat(fr,dr):
 fm,dm=metrics(fr),metrics(dr); a,b=first(fm,'initial-chain'),first(dm,'initial-chain')
 x={'static.nodes':num(a.get('equality_nodes')),'static.edges':num(a.get('graph_edges')),'static.source_total':st(a),'static.generations':num(a.get('generations')),'static.max_term_size':num(a.get('max_term_size')),'static.term_budget_exhausted':float(a.get('exhaustion')=='term budget exhausted'),'static.elapsed':num(fr.get('elapsed_seconds')),'static.true_problem':float(fr.get('verdict')=='true')}
 x['static.node_saturation']=x['static.nodes']/4000.; x['static.source_density']=x['static.source_total']/(1+x['static.nodes'])
 x.update({'diff.nodes':num(b.get('equality_nodes'))-num(a.get('equality_nodes')),'diff.source_total':st(b)-st(a),'diff.elapsed':num(dr.get('elapsed_seconds'))-num(fr.get('elapsed_seconds')),'diff.portfolios_seen':len(dm)-len(fm),'diff.components_joined':sum(num(m.get('components_joined')) for m in dm),'diff.narrowing_successors':sum(num(m.get('narrowing_successors')) for m in dm),'diff.overlaps_added':sum(num(m.get('overlaps_added')) for m in dm)})
 x['rel.dev_to_frozen_node_ratio']=(1+num(b.get('equality_nodes')))/(1+num(a.get('equality_nodes'))); x['rel.extra_portfolio_per_node']=x['diff.portfolios_seen']/(1+x['static.nodes']); x['rel.narrowing_per_node']=x['diff.narrowing_successors']/(1+x['static.nodes']); x['rel.overlap_per_source']=x['diff.overlaps_added']/(1+x['static.source_total'])
 return x,fm,dm
def bacc(rows,rule):
 pos=[r for r in rows if r['y']]; neg=[r for r in rows if not r['y']]
 if not pos or not neg:return .5,0,0,0
 hit=lambda r: all((r['x'][f]>=t if d=='ge' else r['x'][f]<=t) for f,d,t in rule)
 tp=sum(hit(r) for r in pos); fp=sum(hit(r) for r in neg); sup=tp+fp
 return .5*(tp/len(pos)+(len(neg)-fp)/len(neg)),tp/max(1,sup),tp/len(pos),sup
def preds(rows,fs):
 o=[]
 for f in fs:
  v=sorted({r['x'][f] for r in rows})
  if len(v)<2: continue
  for q in (.1,.25,.5,.75,.9):
   t=v[min(len(v)-1,int(q*(len(v)-1)))]; o += [(f,'ge',t),(f,'le',t)]
 return list(dict.fromkeys(o))
def fmt(rule): return ' AND '.join(f'{f} {">=" if d=="ge" else "<="} {t:.6g}' for f,d,t in rule)
def sweep(rows,fs,seed):
 ps=preds(rows,fs); ss=sorted(((bacc(rows,(p,))[0],p) for p in ps),reverse=True)[:28]; base=[p for _,p in ss]; cand=[]
 for k in (1,2,3):
  for rule in itertools.combinations(base,k):
   if len({p[0] for p in rule})<k: continue
   s=bacc(rows,rule); cand.append((s[0]-.01*(k-1),s,rule))
 cand=sorted(cand,reverse=True)[:30]; rng=random.Random(seed); stab={fmt(r):0 for _,_,r in cand[:15]}
 for _ in range(80):
  boot=[rows[rng.randrange(len(rows))] for _ in rows]; ranked=[]
  for _,_,r in cand[:15]: ranked.append((bacc(boot,r)[0]-.01*(len(r)-1),fmt(r)))
  for _,n in sorted(ranked,reverse=True)[:5]: stab[n]+=1
 return [{'rule':fmt(r),'balanced_accuracy':round(s[0],4),'precision':round(s[1],4),'recall':round(s[2],4),'support':s[3],'bootstrap_top5_rate':round(stab.get(fmt(r),0)/80,4),'complexity':len(r),'objective':round(o,4)} for o,s,r in cand[:12]]
def main():
 F={r['id']:r for r in json.loads(FROZEN.read_text())}; D={r['id']:r for r in json.loads(DEV.read_text())}; ids=sorted(set(F)&set(D)); base=[]
 for i in ids:
  x,fm,dm=feat(F[i],D[i]); portsF=[m.get('portfolio') for m in fm]; portsD=[m.get('portfolio') for m in dm]
  labels={'new_portfolio':any(p not in portsF for p in portsD),'target_narrowing':any(m.get('portfolio')=='target-narrowing' for m in dm),'target_structure_introduced':any(num(m.get('missing_target_introduced'))>0 for m in dm),'residual_trajectory_changed':portsD!=portsF or any(x[k]!=0 for k in ('diff.nodes','diff.source_total','diff.components_joined','diff.narrowing_successors','diff.overlaps_added'))}
  base.append({'id':i,'x':x,'labels':labels})
 static=[k for k in base[0]['x'] if k.startswith('static.')]; response=[k for k in base[0]['x'] if k.startswith('diff.') or k.startswith('rel.')]
 out={'schema':'mathgraph.residual-representation-tournament.v2','paired_cases':len(base),'tracks':{}}
 for target in base[0]['labels']:
  rows=[{'id':r['id'],'x':r['x'],'y':r['labels'][target]} for r in base]; n=sum(r['y'] for r in rows); track={'positives':n,'negatives':len(rows)-n}
  if n>=3 and len(rows)-n>=3:
   track['prospective_static']=sweep(rows,static,20260821); track['retrospective_response']=sweep(rows,response,20260822); recur={}
   for rep in range(12):
    sub=[r for r in rows if int(hashlib.sha256((r['id']+str(rep)).encode()).hexdigest(),16)%2==0]
    if sum(r['y'] for r in sub)<2 or sum(not r['y'] for r in sub)<2: continue
    for z in sweep(sub,static,20260821+rep)[:5]: recur[z['rule']]=recur.get(z['rule'],0)+1
   track['static_recurrence']=[{'rule':k,'half_sample_top5_count':v} for k,v in sorted(recur.items(),key=lambda kv:(-kv[1],kv[0]))[:15]]
  out['tracks'][target]=track
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
