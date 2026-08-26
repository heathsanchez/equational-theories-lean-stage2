#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'; RID='evaluation_normal_0040'
def load(path,name):
 s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); sys.modules[name]=m; s.loader.exec_module(m); return m
def alpha(r,a,b):
 n={}; x=r.alpha_canonical_term(a,n); y=r.alpha_canonical_term(b,n); return min((x,y),(y,x))
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
 m=load(SOLVER,'mg217'); h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'h217')
 row=h.load_row(a.input,RID); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
 lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 e=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,lim); base=e.solve(); r=m.RigidSuperpositionModule()
 proof=next(x['proof'] for x in json.load(urllib.request.urlopen(TRACE_URL))['rows'] if x['id']==RID)
 W=h.extract_wanted(proof,target[2],m,('f19','f20','f27','f81','f95','f123','f126','f130','f148','f150','f196','f217'))
 def cover(eq):
  for c in e.search.clauses:
   x=h.inline_engine_names(c.lhs,e.reverse_constants); y=h.inline_engine_names(c.rhs,e.reverse_constants)
   for rev,(u,v) in enumerate(((x,y),(y,x))):
    s={}
    if r.match_term(u,eq[0],s) and r.match_term(v,eq[1],s):
     b=c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,)); return e.search.instantiate(b,s)
  return None
 def cp(a0,b0,goal):
  for aa in (a0,m.Recipe(a0.rhs,a0.lhs,'symmetry',(a0,))):
   for bb in (b0,m.Recipe(b0.rhs,b0.lhs,'symmetry',(b0,))):
    for outer,inner in ((aa,bb),(bb,aa)):
     for path in r.nonvariable_positions(outer.lhs,maximum_depth=lim['maximum_depth'],include_root=True):
      p=e.search.critical_pair(outer,inner,0,1,path)
      if p:
       x=h.inline_engine_names(p.lhs,e.reverse_constants); y=h.inline_engine_names(p.rhs,e.reverse_constants)
       if alpha(r,x,y)==alpha(r,*goal): return p
  return None
 out={'id':RID,'baseline_found':bool(base)}
 c81=cover(W['f81']); out['f81_cover']=bool(c81); s95=cp(c81,c81,W['f95']) if c81 else None; out['f95_generated']=bool(s95)
 if s95: e.search.add_clause(s95)
 c27=cover(W['f27']); out['f27_cover']=bool(c27); s123=cp(c27,s95,W['f123']) if c27 and s95 else None; out['f123_generated']=bool(s123)
 if s123: e.search.add_clause(s123)
 c20=cover(W['f20']); c126=cover(W['f126']); out['f20_cover']=bool(c20); out['f126_cover']=bool(c126); s148=cp(c20,c126,W['f148']) if c20 and c126 else None; out['f148_generated']=bool(s148)
 if s148: e.search.add_clause(s148)
 c130=cover(W['f130']); out['f130_cover']=bool(c130); s150=cp(c130,c130,W['f150']) if c130 else None; out['f150_generated']=bool(s150)
 if s150: e.search.add_clause(s150)
 s196=cp(s148,s150,W['f196']) if s148 and s150 else None; out['f196_generated']=bool(s196)
 if s196: e.search.add_clause(s196)
 c19=cover(W['f19']); out['f19_cover']=bool(c19); s217=cp(c19,s196,W['f217']) if c19 and s196 else None; out['f217_generated']=bool(s217); out['f217_seed_added']=False
 if s217: out['f217_seed_added']=bool(e.search.add_clause(s217))
 found=e.solve() if s217 else None; out['seeded_found']=bool(found); out['seeded_replay_ok']=False; out['proof_nodes']=None
 if found:
  nodes,root=found; out['proof_nodes']=len(m.proof_node_ids(nodes,root)); out['seeded_replay_ok']=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000) and (nodes[root].lhs,nodes[root].rhs)==target[:2])
 Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('NORMAL0040_F217_ATTACHMENT',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
