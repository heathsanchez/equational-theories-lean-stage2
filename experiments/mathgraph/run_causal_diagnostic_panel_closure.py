#!/usr/bin/env python3
"""Problem-disjoint causal diagnostic-panel closure gate.

Every case receives the same matched short probes before any routing decision:
  B0 = ordinary compact superposition
  G0 = given-clause saturation
The label is determined only by matched longer-budget arms. We then test whether
short intervention responses improve unseen-ID routing over static residual state.
No theorem IDs, external proof traces, answer-specific rules, or labels enter the router.

Full routing closure additionally requires genuine arm divergence: BOTH vs NEITHER
is useful solvability prediction, but is not evidence that the residual selects
between interventions.
"""
import importlib.util,json,sys,time,hashlib,statistics,math
from collections import Counter
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
GATE=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/causal-diagnostic-panel-closure.json'
CONFIGS=['evaluation_normal','evaluation_hard','evaluation_extra_hard','evaluation_order5']
SHORT=1.5; LONG=6.0; PER_CFG=10

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def replay(m,e,r):
 if r is None:return False
 try:
  rr=e.inline_recipe(r);c=m.CompactSuperposition(m,e.source,e.target,time.monotonic()+1.5,e.search.limits);nodes,root=c.compile(rr)
  return bool(nodes[root].lhs==e.target[0] and nodes[root].rhs==e.target[1] and m.replay_dag(e.source,nodes,root,maximum_term_size=e.search.limits['maximum_replay_term_size'],maximum_nodes=e.search.limits['maximum_proof_nodes']))
 except Exception:return False

def engine(m,row,seconds):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);lim=dict(m.COMPACT_SUPERPOSITION_PROBE)
 lim.update({'seconds':seconds,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 return m.TargetGroundedRefutation(src,tgt,time.monotonic()+seconds,lim)

def barm(m,row,seconds):
 e=engine(m,row,seconds);t=time.monotonic();r=e.search.solve();ok=replay(m,e,r);s=e.search
 stats={'closure':float(ok),'elapsed':time.monotonic()-t,'clauses':len(getattr(s,'clauses',[])),'rules':len(getattr(s,'rules',[])) if not callable(getattr(s,'rules',None)) else len(list(s.rules())),'superpositions':float(getattr(s,'superpositions',0) or 0),'overlap_candidates':float(getattr(s,'overlap_candidates',0) or 0),'left_steps':float(getattr(s,'left_steps',0) or 0),'right_steps':float(getattr(s,'right_steps',0) or 0)}
 return ok,stats

def garm(m,gate,row,seconds):
 e=engine(m,row,seconds);t=time.monotonic();r,s=gate.solve_given(m,e.search);ok=replay(m,e,r);out={'closure':float(ok),'elapsed':time.monotonic()-t}
 for k,v in (s or {}).items():
  if isinstance(v,(int,float,bool)):out[k]=float(v)
 return ok,out

def static(m,row):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
 def ts(t):return m.term_size(t)
 def vars(t):
  if t[0]=='var':return {t[1]}
  return vars(t[1])|vars(t[2])
 return {'src_lhs_size':ts(src[0]),'src_rhs_size':ts(src[1]),'tgt_lhs_size':ts(tgt[0]),'tgt_rhs_size':ts(tgt[1]),'src_size_gap':abs(ts(src[0])-ts(src[1])),'tgt_size_gap':abs(ts(tgt[0])-ts(tgt[1])),'src_vars':len(vars(src[0])|vars(src[1])),'tgt_vars':len(vars(tgt[0])|vars(tgt[1]))}
def flatten(prefix,d):return {prefix+k:float(v) for k,v in d.items() if isinstance(v,(int,float,bool))}
def mean(a):return sum(a)/len(a) if a else 0.0
def sd(a):
 if len(a)<2:return 1.0
 q=statistics.pstdev(a);return q if q>1e-12 else 1.0
def fit(rows,fs):
 base={f:(mean([r['x'].get(f,0) for r in rows]),sd([r['x'].get(f,0) for r in rows])) for f in fs};pri=Counter(r['y'] for r in rows);cen={}
 for y in pri:
  q=[r for r in rows if r['y']==y];cen[y]={f:mean([(r['x'].get(f,0)-base[f][0])/base[f][1] for r in q]) for f in fs}
 return base,pri,cen
def predict(r,model):
 base,pri,cen=model;best=None
 for y,c in cen.items():
  d=sum(((r['x'].get(f,0)-mu)/s-c[f])**2 for f,(mu,s) in base.items());z=(d,-pri[y],y)
  if best is None or z<best:best=z
 return best[2]
def macro(rows,ps):
 labs=sorted(set(r['y'] for r in rows));return mean([sum(ps[i]==y for i,r in enumerate(rows) if r['y']==y)/sum(r['y']==y for r in rows) for y in labs]) if labs else 0.0
def evaluate(tr,te,fs):return macro(te,[predict(r,fit(tr,fs)) for r in te])
def split(rows,seed):
 tr=[];te=[]
 for r in rows:
  z=int(hashlib.sha256((r['id']+'|'+str(seed)).encode()).hexdigest(),16)%10;(tr if z<6 else te).append(r)
 return tr,te

def main():
 m=load(SOLVER,'mg_diag_panel');gate=load(GATE,'given_diag_panel');selected=[]
 for cfg in CONFIGS:
  ds=[dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train') if bool(r.get('answer'))]
  if not ds:continue
  idx=sorted(set(min(len(ds)-1,round(i*(len(ds)-1)/max(1,PER_CFG-1))) for i in range(PER_CFG)))
  for i in idx:selected.append((cfg,ds[i]))
 records=[]
 for cfg,row in selected:
  t0=time.monotonic();s=static(m,row);bs,bshort=barm(m,row,SHORT);gs,gshort=garm(m,gate,row,SHORT);bl,blong=barm(m,row,LONG);gl,glong=garm(m,gate,row,LONG)
  if bl and not gl:y='BASELINE'
  elif gl and not bl:y='GIVEN'
  elif bl and gl:y='BOTH'
  else:y='NEITHER'
  x={**flatten('s.',s),**flatten('b.',bshort),**flatten('g.',gshort)}
  rec={'id':row['id'],'config':cfg,'y':y,'x':x,'short_baseline':bs,'short_given':gs,'long_baseline':bl,'long_given':gl,'seconds':round(time.monotonic()-t0,3)};records.append(rec);print(json.dumps({k:v for k,v in rec.items() if k!='x'},sort_keys=True),flush=True)
 counts=Counter(r['y'] for r in records);keep={y for y,n in counts.items() if n>=4};rows=[r for r in records if r['y'] in keep]
 static_fs=sorted(f for f in rows[0]['x'] if f.startswith('s.')) if rows else [];panel_fs=sorted(rows[0]['x']) if rows else [];runs=[]
 for seed in range(30):
  tr,te=split(rows,seed);labs=set(r['y'] for r in tr)&set(r['y'] for r in te)
  if len(labs)<2:continue
  tr=[r for r in tr if r['y'] in labs];te=[r for r in te if r['y'] in labs]
  if min(Counter(r['y'] for r in tr).values())<2 or min(Counter(r['y'] for r in te).values())<2:continue
  st=evaluate(tr,te,static_fs);pa=evaluate(tr,te,panel_fs);runs.append({'seed':seed,'labels':sorted(labs),'n_train':len(tr),'n_test':len(te),'static_macro':round(st,4),'panel_macro':round(pa,4),'gain':round(pa-st,4),'id_overlap':len(set(r['id'] for r in tr)&set(r['id'] for r in te))})
 med=lambda k:statistics.median([r[k] for r in runs]) if runs else 0.0
 arm_specific=counts.get('BASELINE',0)+counts.get('GIVEN',0);arm_labels=sum(counts.get(x,0)>=4 for x in ('BASELINE','GIVEN'))
 out={'schema':'mathgraph.causal-diagnostic-panel-closure.v2','protocol':{'short_seconds':SHORT,'long_seconds':LONG,'teacher_forced_long_arms':True,'no_external_proof_trace':True,'problem_disjoint':True,'requires_arm_specific_divergence':True},'cases':len(records),'label_counts':dict(counts),'kept_labels':sorted(keep),'arm_specific_cases':arm_specific,'arm_specific_labels_with_support':arm_labels,'valid_splits':len(runs),'median_static_macro':round(med('static_macro'),4),'median_panel_macro':round(med('panel_macro'),4),'median_gain':round(med('gain'),4),'all_id_disjoint':all(r['id_overlap']==0 for r in runs),'records':records,'runs':runs}
 out['gates']={'G1_two_or_more_labels':len(keep)>=2,'G2_at_least_15_valid_splits':len(runs)>=15,'G3_disjoint':out['all_id_disjoint'],'G4_panel_macro_ge_060':out['median_panel_macro']>=.60,'G5_panel_gain_ge_010':out['median_gain']>=.10,'G6_arm_specific_divergence':arm_specific>=8 and arm_labels>=1};out['closure_pass']=all(out['gates'].values())
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ('records','runs')},indent=2,sort_keys=True))
if __name__=='__main__':main()
