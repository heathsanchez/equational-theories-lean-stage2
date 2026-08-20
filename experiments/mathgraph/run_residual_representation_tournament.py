#!/usr/bin/env python3
import json,re,math,random,hashlib,itertools
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
R=ROOT/'experiments/mathgraph/results'
FROZEN=R/'contextual_development_frozen/sample_200_development.json'
DEV=R/'contextual_development_all/sample_200_development.json'
OUT=R/'residual-representation-tournament.json'
PAT=re.compile(r'MATHGRAPH_METRICS\s+(\{.*?\})(?:\n|$)')

def metrics(row):
 out=[]
 for e in row.get('log',[]):
  if e.get('type')!='solver_stderr': continue
  for m in PAT.finditer(e.get('tail','')):
   try: out.append(json.loads(m.group(1)))
   except Exception: pass
 return out

def first_port(ms,name):
 for m in ms:
  if m.get('portfolio')==name:return m
 return {}

def num(x):
 return float(x) if isinstance(x,(int,float,bool)) else 0.0

def source_total(m):
 s=m.get('source_instances',{})
 return float(sum(v for v in s.values() if isinstance(v,(int,float))))

def build_features(fr,dr):
 fm=metrics(fr); dm=metrics(dr)
 fi=first_port(fm,'initial-chain'); di=first_port(dm,'initial-chain')
 feats={
  'static.nodes':num(fi.get('equality_nodes')),
  'static.edges':num(fi.get('graph_edges')),
  'static.source_total':source_total(fi),
  'static.generations':num(fi.get('generations')),
  'static.max_term_size':num(fi.get('max_term_size')),
  'static.term_budget_exhausted':1.0 if fi.get('exhaustion')=='term budget exhausted' else 0.0,
  'static.elapsed':num(fr.get('elapsed_seconds')),
  'static.true_problem':1.0 if fr.get('verdict')=='true' else 0.0,
  'static.node_saturation':num(fi.get('equality_nodes'))/4000.0,
  'static.source_density':source_total(fi)/(1.0+num(fi.get('equality_nodes'))),
 }
 # Intervention-response / differential traits.
 feats.update({
  'diff.nodes':num(di.get('equality_nodes'))-num(fi.get('equality_nodes')),
  'diff.source_total':source_total(di)-source_total(fi),
  'diff.elapsed':num(dr.get('elapsed_seconds'))-num(fr.get('elapsed_seconds')),
  'diff.portfolios_seen':float(len(dm)-len(fm)),
  'diff.any_target_narrowing':1.0 if any(m.get('portfolio')=='target-narrowing' for m in dm) else 0.0,
  'diff.any_medium':1.0 if any(m.get('portfolio')=='medium' for m in dm) else 0.0,
  'diff.missing_target_introduced':sum(num(m.get('missing_target_introduced')) for m in dm),
  'diff.components_joined':sum(num(m.get('components_joined')) for m in dm),
  'diff.narrowing_successors':sum(num(m.get('narrowing_successors')) for m in dm),
  'diff.overlaps_added':sum(num(m.get('overlaps_added')) for m in dm),
 })
 # Derived relational-style phenotype coordinates.
 feats['rel.dev_to_frozen_node_ratio']=(1+num(di.get('equality_nodes')))/(1+num(fi.get('equality_nodes')))
 feats['rel.dev_extra_portfolio_per_static_node']=feats['diff.portfolios_seen']/(1+feats['static.nodes'])
 feats['rel.target_intro_per_source']=feats['diff.missing_target_introduced']/(1+feats['static.source_total'])
 feats['rel.narrowing_per_static_node']=feats['diff.narrowing_successors']/(1+feats['static.nodes'])
 return feats

def bal_acc(y,p):
 pos=[i for i,v in enumerate(y) if v]; neg=[i for i,v in enumerate(y) if not v]
 if not pos or not neg:return 0.5
 return 0.5*(sum(p[i] for i in pos)/len(pos)+sum(1-p[i] for i in neg)/len(neg))

def predicates(rows,features):
 preds=[]
 for f in features:
  vals=sorted({r['x'][f] for r in rows})
  if len(vals)<2: continue
  qs=[]
  for q in (.1,.25,.5,.75,.9): qs.append(vals[min(len(vals)-1,int(q*(len(vals)-1)))])
  for t in sorted(set(qs)):
   for d in ('ge','le'):
    preds.append((f,d,t))
 return preds

def apply_pred(r,p):
 f,d,t=p;v=r['x'][f]
 return v>=t if d=='ge' else v<=t

def rule_pred(r,rule):return all(apply_pred(r,p) for p in rule)

def score_rule(rows,rule):
 y=[r['y'] for r in rows];p=[1 if rule_pred(r,rule) else 0 for r in rows]
 b=bal_acc(y,p); support=sum(p); positives=sum(y)
 precision=sum(yi and pi for yi,pi in zip(y,p))/max(1,support)
 recall=sum(yi and pi for yi,pi in zip(y,p))/max(1,positives)
 return b,precision,recall,support

def fmt(rule):return ' AND '.join(f'{f} {">=" if d=="ge" else "<="} {t:.6g}' for f,d,t in rule)

def tournament(rows,fams,seed=20260821):
 rng=random.Random(seed); allout={}
 for fam,features in fams.items():
  ps=predicates(rows,features)
  singles=sorted(((score_rule(rows,(p,))[0],(p,)) for p in ps),reverse=True)[:24]
  base=[r for _,rule in singles for r in rule]
  cand=[]
  for k in (1,2,3):
   for rule in itertools.combinations(base,k):
    if len({p[0] for p in rule})<k: continue
    s=score_rule(rows,rule)
    # complexity penalty is deliberately small but nonzero.
    obj=s[0]-0.01*(k-1)
    cand.append((obj,s,rule))
  cand=sorted(cand,reverse=True)[:40]
  # repeated bootstrap stability: how often a rule family remains top-5.
  stability={fmt(rule):0 for _,_,rule in cand[:20]}
  for _ in range(60):
   boot=[rows[rng.randrange(len(rows))] for _ in rows]
   ranked=[]
   for _,_,rule in cand[:20]: ranked.append((score_rule(boot,rule)[0]-0.01*(len(rule)-1),fmt(rule)))
   for _,name in sorted(ranked,reverse=True)[:5]: stability[name]+=1
  top=[]
  for obj,s,rule in cand[:15]:
   name=fmt(rule); top.append({'rule':name,'balanced_accuracy':round(s[0],4),'precision':round(s[1],4),'recall':round(s[2],4),'support':s[3],'bootstrap_top5_rate':round(stability.get(name,0)/60,4),'complexity':len(rule),'objective':round(obj,4)})
  allout[fam]=top
 return allout

def main():
 frozen={r['id']:r for r in json.loads(FROZEN.read_text())}; dev={r['id']:r for r in json.loads(DEV.read_text())}
 ids=sorted(set(frozen)&set(dev));rows=[]
 for i in ids:
  fr,dr=frozen[i],dev[i]
  # clean causal label: development succeeds where frozen did not.
  y=bool(dr.get('solved')) and not bool(fr.get('solved'))
  rows.append({'id':i,'y':y,'x':build_features(fr,dr)})
 features=list(rows[0]['x'])
 fams={
  'static':[f for f in features if f.startswith('static.')],
  'differential':[f for f in features if f.startswith('diff.')],
  'relational':[f for f in features if f.startswith('rel.')],
  'combined':features,
 }
 results=tournament(rows,fams)
 # A second recurrence sweep over deterministic half-samples.
 recurrence={}
 for rep in range(8):
  sub=[r for r in rows if int(hashlib.sha256((r['id']+str(rep)).encode()).hexdigest(),16)%2==0]
  if sum(r['y'] for r in sub)<2 or sum(not r['y'] for r in sub)<2: continue
  rr=tournament(sub,{'combined':features},seed=20260821+rep)['combined'][:5]
  for x in rr: recurrence[x['rule']]=recurrence.get(x['rule'],0)+1
 out={
  'schema':'mathgraph.residual-representation-tournament.v1',
  'paired_cases':len(rows),'development_unique_gains':sum(r['y'] for r in rows),'frozen_solved':sum(bool(frozen[i].get('solved')) for i in ids),'developed_solved':sum(bool(dev[i].get('solved')) for i in ids),
  'feature_count':len(features),'families':{k:len(v) for k,v in fams.items()},'results':results,
  'recurrent_rules':[{'rule':k,'half_sample_top5_count':v} for k,v in sorted(recurrence.items(),key=lambda kv:(-kv[1],kv[0]))[:20]],
  'note':'Primary label is matched causal gain: development solved while frozen did not. Differential/relational families are retrospective diagnostic representations; static family is prospective.'
 }
 OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
