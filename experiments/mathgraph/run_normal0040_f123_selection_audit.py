#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); sys.modules[name]=m; s.loader.exec_module(m); return m

def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
 m=load(SOLVER,'mg_f123_sel'); h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'h_f123_sel')
 row=h.load_row(a.input,RID); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
 lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'seconds':30.0,'maximum_term_size':65,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 e=m.TargetGroundedRefutation(source,target,time.monotonic()+6.0,{**lim,'seconds':6.0}); warm=e.solve(); r=m.RigidSuperpositionModule()
 proof=next(x['proof'] for x in json.load(urllib.request.urlopen(TRACE_URL))['rows'] if x['id']==RID)
 W=h.extract_wanted(proof,target[2],m,('f27','f81','f95','f123'))
 deadline=time.monotonic()+30.0; e.deadline=deadline
 if hasattr(e.search,'deadline'): e.search.deadline=deadline
 def alpha(a,b):
  n={}; x=r.alpha_canonical_term(a,n); y=r.alpha_canonical_term(b,n); return min((x,y),(y,x))
 wanted={k:alpha(*v) for k,v in W.items()}
 target_terms=[t for side in target[:2] for t in m.walk_subterms(side)]
 def inline(c): return h.inline_engine_names(c.lhs,e.reverse_constants),h.inline_engine_names(c.rhs,e.reverse_constants)
 def key(c): return alpha(*inline(c))
 def score(c):
  x,y=inline(c); d=min([m.structural_distance(x,t) for t in target_terms]+[m.structural_distance(y,t) for t in target_terms])
  return (d,max(m.term_size(x),m.term_size(y)),m.term_size(x)+m.term_size(y),m.render_term(x),m.render_term(y))
 def orientations(c): return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
 def cps(a0,b0,cap):
  made=[]
  for aa in orientations(a0):
   for bb in orientations(b0):
    for outer,inner in ((aa,bb),(bb,aa)):
     for path in r.nonvariable_positions(outer.lhs,maximum_depth=lim['maximum_depth'],include_root=True):
      p=e.search.critical_pair(outer,inner,0,1,path)
      if p is not None: made.append(p)
      if len(made)>=cap: return made
  return made
 def covers(c,eq):
  x,y=inline(c)
  for rev,(u,v) in enumerate(((x,y),(y,x))):
   s={}
   if r.match_term(u,eq[0],s) and r.match_term(v,eq[1],s): return True
  return False
 retained=list(e.search.clauses)
 candidates=[]
 for c in list(retained): candidates.extend(cps(c,c,12))
 selected=sorted(candidates,key=score)[:256]; frontier=[]
 for p in selected:
  if e.search.add_clause(p): frontier.append(p); retained.append(p)
 front_ranked=sorted(frontier,key=score); active=front_ranked[:96]
 bank_ranked=sorted(retained,key=score); bank=bank_ranked[:320]
 def exact_rank(seq,name):
  for i,c in enumerate(seq,1):
   if key(c)==wanted[name]: return i
  return None
 def cover_rank(seq,name):
  for i,c in enumerate(seq,1):
   if covers(c,W[name]): return i
  return None
 f95=next((c for c in frontier if key(c)==wanted['f95']),None)
 c27=next((c for c in retained if covers(c,W['f27'])),None)
 direct8=cps(f95,c27,8) if f95 and c27 else []
 direct256=cps(f95,c27,256) if f95 and c27 else []
 out={
  'id':RID,'warm_found':bool(warm),'bootstrap_added':len(frontier),
  'f95_frontier_rank':exact_rank(front_ranked,'f95'),'f95_active_top96':any(key(c)==wanted['f95'] for c in active),
  'f27_best_retained_rank':cover_rank(bank_ranked,'f27'),'f27_in_bank_top320':any(covers(c,W['f27']) for c in bank),
  'direct_cap8_count':len(direct8),'f123_in_direct_cap8':any(key(c)==wanted['f123'] for c in direct8),
  'direct_cap256_count':len(direct256),'f123_in_direct_cap256':any(key(c)==wanted['f123'] for c in direct256),
 }
 # Reproduce round-1 iteration and record whether the productive parent pair is actually visited before global raw cap.
 raw=[]; attempts=0; productive_attempted=False; productive_raw=False
 for f in active:
  for b in bank:
   if time.monotonic()>=deadline: break
   ispair=(key(f)==wanted['f95'] and covers(b,W['f27'])) or (covers(f,W['f27']) and key(b)==wanted['f95'])
   ps=cps(f,b,8); attempts+=1
   if ispair: productive_attempted=True
   if any(key(p)==wanted['f123'] for p in ps): productive_raw=True
   raw.extend(ps)
   if attempts>=12000 or len(raw)>=5000: break
  if attempts>=12000 or len(raw)>=5000 or time.monotonic()>=deadline: break
 out.update({'round1_pair_attempts':attempts,'round1_raw':len(raw),'productive_pair_attempted':productive_attempted,'f123_generated_round1':productive_raw})
 Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print('NORMAL0040_F123_SELECTION_AUDIT',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
