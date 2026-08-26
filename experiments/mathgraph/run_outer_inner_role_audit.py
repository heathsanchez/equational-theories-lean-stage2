#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
CASES={
 'evaluation_normal_0036':('f6','f35','f38'),
 'evaluation_hard_0196':('f6','f27','f30'),
}

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); sys.modules[name]=m; s.loader.exec_module(m); return m

def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--normal-input',required=True); ap.add_argument('--hard-input',required=True); ap.add_argument('--output',required=True); opts=ap.parse_args()
 m=load(SOLVER,'mg_role_audit'); h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'h_role_audit'); r=m.RigidSuperpositionModule()
 trace=json.load(urllib.request.urlopen(TRACE_URL)); proofs={x['id']:x['proof'] for x in trace['rows']}
 rows=[]
 for rid,(src_id,bridge_id,want_id) in CASES.items():
  inp=opts.normal_input if 'normal_' in rid else opts.hard_input; row=h.load_row(inp,rid); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
  lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'seconds':20.0,'maximum_term_size':65,'maximum_depth':12,'maximum_rules':768,'maximum_clauses':12000})
  deadline=time.monotonic()+6.0; e=m.TargetGroundedRefutation(source,target,deadline,dict(lim,seconds=6.0)); e.solve()
  wanted=h.extract_wanted(proofs[rid],target[2],m,[src_id,bridge_id,want_id])
  def alpha_pair(x0,y0):
   n={}; x=r.alpha_canonical_term(x0,n); y=r.alpha_canonical_term(y0,n); return min((x,y),(y,x))
  def inline(t): return h.inline_engine_names(t,e.reverse_constants)
  def key(c): return alpha_pair(inline(c.lhs),inline(c.rhs))
  keys={fid:alpha_pair(*eq) for fid,eq in wanted.items()}
  matches={fid:[c for c in e.search.clauses if key(c)==k] for fid,k in keys.items()}
  def oriented(c): return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
  def directed(outer0,inner0):
   made=[]
   for outer in oriented(outer0):
    for inner in oriented(inner0):
     for path in r.nonvariable_positions(outer.lhs,maximum_depth=lim['maximum_depth'],include_root=True):
      p=e.search.critical_pair(outer,inner,0,1,path)
      if p is not None: made.append(p)
   return made
  out={'id':rid,'source_matches':len(matches.get(src_id,[])),'bridge_matches':len(matches.get(bridge_id,[])),'want_present_initial':bool(matches.get(want_id,[]))}
  hits_outer=[]; hits_reverse=[]; source_total=0; bridge_total=0
  for s in matches.get(src_id,[]):
   for b in matches.get(bridge_id,[]):
    source_cps=directed(s,b); bridge_cps=directed(b,s)
    source_total += len(source_cps); bridge_total += len(bridge_cps)
    hits_outer += [p for p in source_cps if key(p)==keys.get(want_id)]
    hits_reverse += [p for p in bridge_cps if key(p)==keys.get(want_id)]
  out.update(source_outer_hits=len(hits_outer),bridge_outer_hits=len(hits_reverse),source_outer_total=source_total,bridge_outer_total=bridge_total)
  rows.append(out); print('OUTER_INNER_ROLE_AUDIT',json.dumps(out,sort_keys=True),flush=True)
 Path(opts.output).parent.mkdir(parents=True,exist_ok=True); Path(opts.output).write_text(json.dumps({'rows':rows},indent=2,sort_keys=True)+'\n')
if __name__=='__main__': main()
