#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'
CORRIDOR=('f95','f123','f148','f150','f196','f217','f229','f231','f244','f258','f259')

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); sys.modules[name]=m; s.loader.exec_module(m); return m

def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
 m=load(SOLVER,'mg_priority_audit'); h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'h_priority_audit')
 row=h.load_row(a.input,RID); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
 lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'seconds':45.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 warm_deadline=time.monotonic()+6.0; warm_lim=dict(lim); warm_lim['seconds']=6.0
 e=m.TargetGroundedRefutation(source,target,warm_deadline,warm_lim); warm=e.solve(); r=m.RigidSuperpositionModule()
 proof=next(x['proof'] for x in json.load(urllib.request.urlopen(TRACE_URL))['rows'] if x['id']==RID)
 W=h.extract_wanted(proof,target[2],m,CORRIDOR)
 def alpha_pair(a,b):
  n={}; x=r.alpha_canonical_term(a,n); y=r.alpha_canonical_term(b,n); return min((x,y),(y,x))
 wanted={k:alpha_pair(*v) for k,v in W.items()}
 deadline=time.monotonic()+45.0; e.deadline=deadline
 if hasattr(e.search,'deadline'): e.search.deadline=deadline
 if hasattr(e.search,'seconds'): e.search.seconds=45.0
 target_terms=[]
 for side in target[:2]: target_terms.extend(m.walk_subterms(side))
 def inline_clause(c): return h.inline_engine_names(c.lhs,e.reverse_constants),h.inline_engine_names(c.rhs,e.reverse_constants)
 def key_clause(c):
  x,y=inline_clause(c); return alpha_pair(x,y)
 def labels(seq):
  ks={key_clause(c) for c in seq}; return [name for name in CORRIDOR if wanted[name] in ks]
 def score(c):
  x,y=inline_clause(c); d=min([m.structural_distance(x,t) for t in target_terms]+[m.structural_distance(y,t) for t in target_terms])
  return (d,max(m.term_size(x),m.term_size(y)),m.term_size(x)+m.term_size(y),m.render_term(x),m.render_term(y))
 def orientations(c): return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
 def cps(a0,b0,cap=32):
  made=[]
  for aa in orientations(a0):
   for bb in orientations(b0):
    for outer,inner in ((aa,bb),(bb,aa)):
     for path in r.nonvariable_positions(outer.lhs,maximum_depth=lim['maximum_depth'],include_root=True):
      p=e.search.critical_pair(outer,inner,0,1,path)
      if p is not None: made.append(p)
      if len(made)>=cap: return made
  return made
 retained=list(e.search.clauses)
 out={'id':RID,'warm_found':bool(warm),'initial_clauses':len(retained),'initial_corridor':labels(retained),'rounds':[],'diagnostic_oracle_only':True,'scheduler_oracle_free':True}
 candidates=[]
 for c in list(retained):
  if time.monotonic()>=deadline: break
  candidates.extend(cps(c,c,cap=12))
 ranked=sorted(candidates,key=score)
 rank0={}
 for i,c in enumerate(ranked,1):
  k=key_clause(c)
  for name in CORRIDOR:
   if wanted[name]==k and name not in rank0: rank0[name]=i
 selected=ranked[:256]; frontier=[]
 for p in selected:
  if e.search.add_clause(p): frontier.append(p); retained.append(p)
 out['bootstrap']={'raw':len(candidates),'selected':len(selected),'added':len(frontier),'raw_corridor':labels(candidates),'selected_corridor':labels(selected),'added_corridor':labels(frontier),'corridor_ranks':rank0}
 for rnd in range(1,9):
  if time.monotonic()>=deadline or not frontier: break
  bank=sorted(retained,key=score)[:320]; raw=[]; pair_attempts=0
  for f in sorted(frontier,key=score)[:96]:
   for b in bank:
    if time.monotonic()>=deadline: break
    raw.extend(cps(f,b,cap=8)); pair_attempts+=1
    if pair_attempts>=12000 or len(raw)>=5000: break
   if pair_attempts>=12000 or len(raw)>=5000 or time.monotonic()>=deadline: break
  ranked=sorted(raw,key=score); rankmap={}
  for i,c in enumerate(ranked,1):
   k=key_clause(c)
   for name in CORRIDOR:
    if wanted[name]==k and name not in rankmap: rankmap[name]=i
  selected=ranked[:512]; new=[]
  for p in selected:
   if e.search.add_clause(p): new.append(p); retained.append(p)
  out['rounds'].append({'round':rnd,'frontier_in':len(frontier),'pair_attempts':pair_attempts,'raw':len(raw),'selected':len(selected),'added':len(new),'raw_corridor':labels(raw),'selected_corridor':labels(selected),'added_corridor':labels(new),'retained_corridor':labels(retained),'corridor_ranks':rankmap})
  frontier=new
 out['final_clauses']=len(retained); out['final_corridor']=labels(retained)
 Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print('NORMAL0040_PRIORITY_AUDIT',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
