#!/usr/bin/env python3
import json,re,random,hashlib,itertools,math
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
def src(m): return [float(v) for v in m.get('source_instances',{}).values() if isinstance(v,(int,float))]
def st(m): return sum(src(m))
def entropy(vs):
 s=sum(vs)
 if s<=0:return 0.0
 ps=[v/s for v in vs if v>0]
 return -sum(p*math.log(p+1e-15) for p in ps)
def feat(fr,dr):
 fm,dm=metrics(fr),metrics(dr); a,b=first(fm,'initial-chain'),first(dm,'initial-chain'); av=src(a)
 x={'static.nodes':num(a.get('equality_nodes')),'static.edges':num(a.get('graph_edges')),'static.source_total':st(a),'static.source_families':len(av),'static.source_entropy':entropy(av),'static.source_max_share':max(av)/max(1.0,sum(av)) if av else 0.0,'static.generations':num(a.get('generations')),'static.max_term_size':num(a.get('max_term_size')),'static.term_budget_exhausted':float(a.get('exhaustion')=='term budget exhausted'),'static.elapsed':num(fr.get('elapsed_seconds')),'static.true_problem':float(fr.get('verdict')=='true'),'static.edge_node_gap':num(a.get('graph_edges'))-num(a.get('equality_nodes')),'static.replay_seconds':num(a.get('replay_seconds')),'static.certificate_bytes':num(a.get('certificate_bytes'))}
 x['static.node_saturation']=x['static.nodes']/4000.; x['static.source_density']=x['static.source_total']/(1+x['static.nodes']); x['static.search_persistence']=x['static.elapsed']*(1+x['static.node_saturation']); x['static.dense_saturation']=x['static.source_density']*x['static.node_saturation']
 def sm(k): return sum(num(m.get(k)) for m in dm)
 x.update({'diff.nodes':num(b.get('equality_nodes'))-num(a.get('equality_nodes')),'diff.source_total':st(b)-st(a),'diff.elapsed':num(dr.get('elapsed_seconds'))-num(fr.get('elapsed_seconds')),'diff.portfolios_seen':len(dm)-len(fm),'diff.components_joined':sm('components_joined'),'diff.narrowing_successors':sm('narrowing_successors'),'diff.overlaps_added':sm('overlaps_added'),'diff.overlap_candidates':sm('overlap_candidates'),'diff.term_size_rejections':sm('term_size_rejections'),'diff.variable_overlap_suppressed':sm('variable_overlap_suppressed'),'diff.missing_target_introduced':sm('missing_target_introduced')})
 x['rel.dev_to_frozen_node_ratio']=(1+num(b.get('equality_nodes')))/(1+num(a.get('equality_nodes'))); x['rel.extra_portfolio_per_node']=x['diff.portfolios_seen']/(1+x['static.nodes']); x['rel.narrowing_per_node']=x['diff.narrowing_successors']/(1+x['static.nodes']); x['rel.overlap_per_source']=x['diff.overlaps_added']/(1+x['static.source_total']); x['rel.rejection_per_narrowing']=x['diff.term_size_rejections']/(1+x['diff.narrowing_successors']); x['rel.overlap_candidate_yield']=x['diff.overlaps_added']/(1+x['diff.overlap_candidates'])
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
  for q in (.1,.2,.35,.5,.65,.8,.9):
   t=v[min(len(v)-1,int(q*(len(v)-1)))]; o += [(f,'ge',t),(f,'le',t)]
 return list(dict.fromkeys(o))
def fmt(rule): return ' AND '.join(f'{f} {">=" if d=="ge" else "<="} {t:.6g}' for f,d,t in rule)
def sig(rule): return ' & '.join(sorted(f'{f}:{"high" if d=="ge" else "low"}' for f,d,_ in rule))
def sweep(rows,fs,seed,topn=14):
 ps=preds(rows,fs); ss=sorted(((bacc(rows,(p,))[0],p) for p in ps),reverse=True)[:36]; base=[p for _,p in ss]; cand=[]
 for k in (1,2,3):
  for rule in itertools.combinations(base,k):
   if len({p[0] for p in rule})<k: continue
   s=bacc(rows,rule); cand.append((s[0]-.01*(k-1),s,rule))
 cand=sorted(cand,reverse=True)[:50]; rng=random.Random(seed); stab={sig(r):0 for _,_,r in cand[:25]}
 for _ in range(100):
  boot=[rows[rng.randrange(len(rows))] for _ in rows]; ranked=[]
  for _,_,r in cand[:25]: ranked.append((bacc(boot,r)[0]-.01*(len(r)-1),sig(r)))
  seen=set()
  for _,n in sorted(ranked,reverse=True):
   if n in seen: continue
   stab[n]=stab.get(n,0)+1; seen.add(n)
   if len(seen)>=5: break
 out=[]; used=set()
 for o,s,r in cand:
  sg=sig(r)
  if sg in used: continue
  used.add(sg); out.append({'signature':sg,'rule':fmt(r),'balanced_accuracy':round(s[0],4),'precision':round(s[1],4),'recall':round(s[2],4),'support':s[3],'bootstrap_signature_top5_rate':round(stab.get(sg,0)/100,4),'complexity':len(r),'objective':round(o,4)})
  if len(out)>=topn: break
 return out
def main():
 F={r['id']:r for r in json.loads(FROZEN.read_text())}; D={r['id']:r for r in json.loads(DEV.read_text())}; ids=sorted(set(F)&set(D)); base=[]
 for i in ids:
  x,fm,dm=feat(F[i],D[i]); pf=[m.get('portfolio') for m in fm]; pd=[m.get('portfolio') for m in dm]
  labels={'new_portfolio':any(p not in pf for p in pd),'target_narrowing':any(m.get('portfolio')=='target-narrowing' for m in dm),'target_structure_introduced':any(num(m.get('missing_target_introduced'))>0 for m in dm),'residual_trajectory_changed':pd!=pf or any(x[k]!=0 for k in ('diff.nodes','diff.source_total','diff.components_joined','diff.narrowing_successors','diff.overlaps_added'))}
  base.append({'id':i,'x':x,'labels':labels})
 static=[k for k in base[0]['x'] if k.startswith('static.')]; response=[k for k in base[0]['x'] if k.startswith('diff.') or k.startswith('rel.')]; out={'schema':'mathgraph.residual-representation-tournament.v3','paired_cases':len(base),'static_feature_count':len(static),'response_feature_count':len(response),'tracks':{}}
 cross={}
 for target in base[0]['labels']:
  rows=[{'id':r['id'],'x':r['x'],'y':r['labels'][target]} for r in base]; n=sum(r['y'] for r in rows); tr={'positives':n,'negatives':len(rows)-n}
  if n>=3 and len(rows)-n>=3:
   tr['prospective_static']=sweep(rows,static,20260821); tr['retrospective_response']=sweep(rows,response,20260822); recur={}; thresholds={}
   for rep in range(20):
    sub=[r for r in rows if int(hashlib.sha256((r['id']+str(rep)).encode()).hexdigest(),16)%2==0]
    if sum(r['y'] for r in sub)<2 or sum(not r['y'] for r in sub)<2: continue
    for z in sweep(sub,static,20260821+rep,5):
     sg=z['signature']; recur[sg]=recur.get(sg,0)+1; thresholds.setdefault(sg,[]).append(z['rule'])
   tr['canonical_static_recurrence']=[{'signature':k,'half_sample_top5_count':v,'examples':thresholds[k][:3]} for k,v in sorted(recur.items(),key=lambda kv:(-kv[1],kv[0]))[:12]]
   for z in tr['prospective_static'][:5]: cross[z['signature']]=cross.get(z['signature'],0)+1
  out['tracks'][target]=tr
 out['cross_target_static_signatures']=[{'signature':k,'target_top5_count':v} for k,v in sorted(cross.items(),key=lambda kv:(-kv[1],kv[0]))]
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
