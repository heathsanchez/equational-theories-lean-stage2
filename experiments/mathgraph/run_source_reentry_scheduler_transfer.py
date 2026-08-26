#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
CASES=('evaluation_normal_0040','evaluation_normal_0036','evaluation_hard_0196')

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); sys.modules[name]=m; s.loader.exec_module(m); return m

def run_one(rid,path,m,h):
 row=h.load_row(path,rid); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
 lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'seconds':45.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 warm_deadline=time.monotonic()+6.0; e=m.TargetGroundedRefutation(source,target,warm_deadline,dict(lim,seconds=6.0)); warm=e.solve(); r=m.RigidSuperpositionModule()
 out={'id':rid,'policy':'pair-fair-plus-narrow-source-reentry','warm_found':bool(warm),'oracle_free':True}
 if warm:
  nodes,root=warm; out.update(found=True,phase='warm',proof_nodes=len(m.proof_node_ids(nodes,root)),replay_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000))); return out
 deadline=time.monotonic()+45.0; e.deadline=deadline
 if hasattr(e.search,'deadline'): e.search.deadline=deadline
 if hasattr(e.search,'seconds'): e.search.seconds=45.0
 target_terms=[]
 for side in target[:2]: target_terms.extend(m.walk_subterms(side))
 def inline(t): return h.inline_engine_names(t,e.reverse_constants)
 def score(c):
  x,y=inline(c.lhs),inline(c.rhs); d=min([m.structural_distance(x,t) for t in target_terms]+[m.structural_distance(y,t) for t in target_terms])
  return (d,max(m.term_size(x),m.term_size(y)),m.term_size(x)+m.term_size(y),m.render_term(x),m.render_term(y))
 def ori(c): return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
 def cps(a0,b0,cap=1):
  made=[]
  for aa in ori(a0):
   for bb in ori(b0):
    for outer,inner in ((aa,bb),(bb,aa)):
     for path0 in r.nonvariable_positions(outer.lhs,maximum_depth=lim['maximum_depth'],include_root=True):
      p=e.search.critical_pair(outer,inner,0,1,path0)
      if p is not None: made.append(p)
      if len(made)>=cap: return made
  return made
 def directed_outer(outer0,inner0,cap=2):
  made=[]
  for outer in ori(outer0):
   for inner in ori(inner0):
    for path0 in r.nonvariable_positions(outer.lhs,maximum_depth=lim['maximum_depth'],include_root=True):
     p=e.search.critical_pair(outer,inner,0,1,path0)
     if p is not None: made.append(p)
     if len(made)>=cap: return made
  return made
 retained=list(e.search.clauses); initial=list(retained)
 # Oracle-free schema recognition: clauses whose inlined equality is an instance/renaming of the input source law.
 source_schemas=[]
 for c in initial:
  try:
   if m.source_instance(source,(inline(c.lhs),inline(c.rhs),source[2])) is not None: source_schemas.append(c)
  except Exception: pass
 out['source_schema_count']=len(source_schemas); out['initial_clauses']=len(initial)
 candidates=[]
 for c in initial:
  if time.monotonic()>=deadline: break
  candidates.extend(cps(c,c,cap=12))
 candidates=sorted(candidates,key=score)[:256]; frontier=[]
 for p in candidates:
  if e.search.add_clause(p): frontier.append(p); retained.append(p)
 out['bootstrap']={'selected':len(candidates),'added':len(frontier)}; out['round_stats']=[]
 for rnd in range(1,9):
  if time.monotonic()>=deadline or not frontier: break
  fs=sorted(frontier,key=score)[:96]; bank=sorted(retained,key=score)[:320]; raw=[]; pair_attempts=0; fair_complete=True
  for f in fs:
   for b in bank:
    if time.monotonic()>=deadline: fair_complete=False; break
    raw.extend(cps(f,b,cap=1)); pair_attempts+=1
   if not fair_complete: break
  # Narrow lane: preserve proven fair-pair behavior; add only source-schema-as-outer results over the active frontier.
  reentry_raw=[]; reentry_attempts=0
  if fair_complete:
   for f in fs:
    for s in source_schemas[:8]:
     if time.monotonic()>=deadline: break
     reentry_raw.extend(directed_outer(s,f,cap=2)); reentry_attempts+=1
    if time.monotonic()>=deadline: break
  raw.extend(reentry_raw)
  expansion_attempts=0
  if fair_complete:
   for f in fs:
    for b in bank:
     if time.monotonic()>=deadline or len(raw)>=12000: break
     more=cps(f,b,cap=4)
     if len(more)>1: raw.extend(more[1:])
     expansion_attempts+=1
    if time.monotonic()>=deadline or len(raw)>=12000: break
  ranked=sorted(raw,key=score)[:1024]; new=[]
  for p in ranked:
   if e.search.add_clause(p): new.append(p); retained.append(p)
  out['round_stats'].append({'round':rnd,'frontier_in':len(frontier),'bank':len(bank),'fair_complete':fair_complete,'pair_attempts':pair_attempts,'source_reentry_attempts':reentry_attempts,'source_reentry_raw':len(reentry_raw),'raw':len(raw),'selected':len(ranked),'added':len(new),'clauses':len(e.search.clauses)})
  frontier=new
 finish=time.monotonic()+10.0; e.deadline=finish
 if hasattr(e.search,'deadline'): e.search.deadline=finish
 if hasattr(e.search,'seconds'): e.search.seconds=10.0
 found=e.solve()
 if found:
  nodes,root=found; out.update(found=True,phase='finish',proof_nodes=len(m.proof_node_ids(nodes,root)),replay_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)))
 else: out.update(found=False,phase='finish',replay_ok=False)
 return out

def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--normal-input',required=True); ap.add_argument('--hard-input',required=True); ap.add_argument('--output',required=True); args=ap.parse_args()
 m=load(SOLVER,'mg_source_reentry'); h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'h_source_reentry'); rows=[]
 for rid in CASES:
  path=args.normal_input if 'normal_' in rid else args.hard_input; res=run_one(rid,path,m,h); rows.append(res); print('SOURCE_REENTRY_CASE',json.dumps(res,sort_keys=True),flush=True)
 out={'policy':'pair-fair-plus-narrow-source-reentry','rows':rows,'solved':sum(bool(x.get('found')) for x in rows),'intervention_solved':sum(bool(x.get('found')) and x.get('phase')=='finish' for x in rows),'replay_ok':sum(bool(x.get('replay_ok')) for x in rows)}
 Path(args.output).parent.mkdir(parents=True,exist_ok=True); Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('SOURCE_REENTRY_SUMMARY',json.dumps({k:out[k] for k in ('solved','intervention_solved','replay_ok')},sort_keys=True),flush=True)
if __name__=='__main__': main()
