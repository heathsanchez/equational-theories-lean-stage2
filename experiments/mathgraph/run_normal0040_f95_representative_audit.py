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
 m=load(SOLVER,'mg_f95_rep'); h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'h_f95_rep')
 row=h.load_row(a.input,RID); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
 lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'seconds':30.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 e=m.TargetGroundedRefutation(source,target,time.monotonic()+6.0,{**lim,'seconds':6.0}); warm=e.solve(); r=m.RigidSuperpositionModule()
 proof=next(x['proof'] for x in json.load(urllib.request.urlopen(TRACE_URL))['rows'] if x['id']==RID)
 W=h.extract_wanted(proof,target[2],m,('f27','f81','f95','f123'))
 def alpha(a,b):
  n={}; x=r.alpha_canonical_term(a,n); y=r.alpha_canonical_term(b,n); return min((x,y),(y,x))
 wanted={k:alpha(*v) for k,v in W.items()}
 def inline(c): return h.inline_engine_names(c.lhs,e.reverse_constants),h.inline_engine_names(c.rhs,e.reverse_constants)
 def key(c): return alpha(*inline(c))
 target_terms=[]
 for side in target[:2]: target_terms.extend(m.walk_subterms(side))
 def score(c):
  x,y=inline(c); d=min([m.structural_distance(x,t) for t in target_terms]+[m.structural_distance(y,t) for t in target_terms])
  return (d,max(m.term_size(x),m.term_size(y)),m.term_size(x)+m.term_size(y),m.render_term(x),m.render_term(y))
 def orientations(c): return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
 def cps(a0,b0,cap=512):
  made=[]
  for aa in orientations(a0):
   for bb in orientations(b0):
    for outer,inner in ((aa,bb),(bb,aa)):
     for path in r.nonvariable_positions(outer.lhs,maximum_depth=lim['maximum_depth'],include_root=True):
      p=e.search.critical_pair(outer,inner,0,1,path)
      if p is not None: made.append(p)
      if len(made)>=cap: return made
  return made
 retained0=list(e.search.clauses)
 f27s=[c for c in retained0 if key(c)==wanted['f27']]
 f81s=[c for c in retained0 if key(c)==wanted['f81']]
 raw=[]
 for c in retained0: raw.extend(cps(c,c,cap=12))
 ranked=sorted(raw,key=score); selected=ranked[:256]
 f95_raw=[c for c in raw if key(c)==wanted['f95']]
 f95_selected=[c for c in selected if key(c)==wanted['f95']]
 added=[]
 for p in selected:
  if e.search.add_clause(p): added.append(p)
 f95_added=[c for c in added if key(c)==wanted['f95']]
 exact95=[]
 for c in f81s:
  exact95.extend([p for p in cps(c,c,cap=512) if key(p)==wanted['f95']])
 def describe(c):
  x,y=inline(c); return {'lhs':m.render_term(x),'rhs':m.render_term(y),'reason':getattr(c,'reason',None)}
 def test95(c):
  hits=[]; total=0
  for d in f27s:
   ps=cps(d,c,cap=512); total+=len(ps)
   hits.extend([p for p in ps if key(p)==wanted['f123']])
  return {'repr':describe(c),'cp_count':total,'f123_hits':len(hits),'f123_examples':[describe(p) for p in hits[:3]]}
 out={'id':RID,'warm_found':bool(warm),'f27_representatives':len(f27s),'f81_representatives':len(f81s),'f95_raw_count':len(f95_raw),'f95_selected_count':len(f95_selected),'f95_added_count':len(f95_added),'f95_exact_from_f81_count':len(exact95),'selected_f95_tests':[test95(c) for c in f95_selected[:20]],'added_f95_tests':[test95(c) for c in f95_added[:20]],'exact_f95_tests':[test95(c) for c in exact95[:20]]}
 Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print('NORMAL0040_F95_REPRESENTATIVE_AUDIT',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
