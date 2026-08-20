#!/usr/bin/env python3
"""Residual-directed saturation for recursive collapse intermediates on O5-0014.

No external proof clause is supplied. The generic score prefers equalities with a
bare variable on one side; among them it prefers exactly one occurrence of that
same variable in the opposite context, then smaller contexts. Search uses only
existing superposition/demodulation machinery, both overlap orientations, and
must compile/replay from the original source. Matched control uses target score.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2];SOLVER=ROOT/'submissions/mathgraph/solver.py';OUT=ROOT/'experiments/mathgraph/results/order5-0014-recursive-collapse-directed-gate.json';RID='evaluation_order5_0014';SECONDS=20.0;MAX_GIVEN=768

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def occurrences(t,v):
 if t[0]=='var':return int(t[1]==v)
 return occurrences(t[1],v)+occurrences(t[2],v)

def collapse_features(m,c):
 best=None
 for vs,body in ((c.lhs,c.rhs),(c.rhs,c.lhs)):
  if vs[0]!='var':continue
  o=occurrences(body,vs[1]);feat=(0 if o==0 else 1,abs(o-1),o,m.term_size(body),len(m.term_variables(body)),m.render_term(body))
  if best is None or feat<best:best=feat
 return best if best is not None else (2,99,99,m.term_size(c.lhs)+m.term_size(c.rhs),len(m.term_variables(c.lhs)|m.term_variables(c.rhs)),m.render_term(c.lhs))

def orientations(m,c):
 if c.lhs==c.rhs:return (c,)
 return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))

def active_rules(search,active):
 out=[]
 for c in active:
  r=search.orient(c)
  if r is not None:out.append(r)
 return out

def canon(m,c):
 def p(a,b):
  names={};return (m.alpha_canonical_term(a,names),m.alpha_canonical_term(b,names))
 return min(p(c.lhs,c.rhs),p(c.rhs,c.lhs))

def replay(m,e,r):
 if r is None:return False
 try:
  rr=e.inline_recipe(r);cc=m.CompactSuperposition(m,e.source,e.target,time.monotonic()+4,e.search.limits);nodes,root=cc.compile(rr);return bool(nodes[root].lhs==e.target[0] and nodes[root].rhs==e.target[1] and m.replay_dag(e.source,nodes,root,maximum_term_size=e.search.limits['maximum_replay_term_size'],maximum_nodes=e.search.limits['maximum_proof_nodes']))
 except Exception:return False

def solve(m,search,mode):
 passive=list(search.clauses);active=[];age={id(c):i for i,c in enumerate(passive)};nextage=len(passive);stats={'given':0,'generated':0,'pair_attempts':0,'recursive_seen':0,'omission_seen':0,'best_recursive':None}
 def score(c):return (collapse_features(m,c),age.get(id(c),10**18)) if mode=='collapse' else (search.target_score(c),age.get(id(c),10**18))
 while passive and stats['given']<MAX_GIVEN and not search.expired():
  rules=active_rules(search,active);goal=search.target_proof(rules)
  if goal is not None:return goal,stats
  i=min(range(len(passive)),key=lambda j:score(passive[j]));sel=passive.pop(i);sel=search.interreduce(sel,rules);active.append(sel);stats['given']+=1
  feat=collapse_features(m,sel)
  if feat[0]==0:stats['omission_seen']+=1
  elif feat[0]==1:
   stats['recursive_seen']+=1
   if stats['best_recursive'] is None or feat<tuple(stats['best_recursive']):stats['best_recursive']=list(feat)
  rules=active_rules(search,active);goal=search.target_proof(rules)
  if goal is not None:return goal,stats
  props=[]
  for oi,other in enumerate(active):
   sviews=orientations(m,sel) if mode=='collapse' else (sel,);oviews=orientations(m,other) if mode=='collapse' else (other,)
   for sv in sviews:
    for ov in oviews:
     for outer,inner,a,b in ((sv,ov,stats['given'],oi),(ov,sv,oi,stats['given'])):
      for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
       if search.expired():break
       stats['pair_attempts']+=1;q=search.critical_pair(outer,inner,a,b,path)
       if q is None:continue
       q=search.interreduce(q,rules);props.append((collapse_features(m,q) if mode=='collapse' else search.target_score(q),q))
  props.sort(key=lambda x:x[0])
  for _,q in props[:search.limits['new_clauses_per_round']]:
   if search.add_clause(q):passive.append(q);age[id(q)]=nextage;nextage+=1;stats['generated']+=1;search.superpositions+=1
  new=[];seen=set()
  for c in passive:
   if search.expired():break
   r=search.interreduce(c,rules);c=r;k=canon(m,c)
   if k in seen:continue
   seen.add(k);new.append(c)
  passive=new
 return search.target_proof(active_rules(search,active)),stats

def run(m,row,mode):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);lim=dict(m.COMPACT_SUPERPOSITION_PROBE);lim.update(seconds=SECONDS,maximum_term_size=75,maximum_replay_term_size=300,maximum_depth=14,maximum_rules=1200,maximum_rounds=128,new_clauses_per_round=512,maximum_clauses=16000,normalization_steps=320,maximum_proof_nodes=120000);e=m.TargetGroundedRefutation(src,tgt,time.monotonic()+SECONDS,lim);st=time.monotonic();r,s=solve(m,e.search,mode);return {'mode':mode,'closure':replay(m,e,r),'elapsed':round(time.monotonic()-st,6),'clauses':len(e.search.clauses),'superpositions':e.search.superpositions,'reductions':e.search.reductions,**s}
def main():
 m=load(SOLVER,'mg_rcollapse');row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);A=run(m,row,'target');C=run(m,row,'collapse');out={'schema':'mathgraph.order5-0014-recursive-collapse-directed.v1','id':RID,'protocol':{'matched_seconds':SECONDS,'same_inference_language':True,'collapse_score_generic_no_external_clause':True,'bidirectional_views_only_in_intervention':True,'full_source_replay_required':True},'A':A,'C':C,'decision':'PASS' if C['closure'] and not A['closure'] else 'BOTH_CLOSE' if C['closure'] and A['closure'] else 'NO_GAIN'};OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
