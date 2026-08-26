#!/usr/bin/env python3
import argparse, importlib.util, json, re, sys, time, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'; RID='evaluation_normal_0040'
def load(path,name):
 s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); sys.modules[name]=m; s.loader.exec_module(m); return m
def alpha(r,a,b):
 n={}; x=r.alpha_canonical_term(a,n); y=r.alpha_canonical_term(b,n); return min((x,y),(y,x))
def covers(r,sa,sb,ta,tb):
 for x,y in ((sa,sb),(sb,sa)):
  s={}
  if r.match_term(x,ta,s) and r.match_term(y,tb,s): return True
 return False
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
 m=load(SOLVER,'mgpost229'); h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'hpost229')
 row=h.load_row(a.input,RID); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
 lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 e=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,lim); e.solve(); r=m.RigidSuperpositionModule()
 proof=next(x['proof'] for x in json.load(urllib.request.urlopen(TRACE_URL))['rows'] if x['id']==RID)
 W=h.extract_wanted(proof,target[2],m,('f18','f19','f20','f27','f81','f95','f123','f126','f130','f148','f150','f196','f217','f229'))
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
 c81=cover(W['f81']); s95=cp(c81,c81,W['f95']) if c81 else None
 if s95: e.search.add_clause(s95)
 c27=cover(W['f27']); s123=cp(c27,s95,W['f123']) if c27 and s95 else None
 if s123: e.search.add_clause(s123)
 c20=cover(W['f20']); c126=cover(W['f126']); s148=cp(c20,c126,W['f148']) if c20 and c126 else None
 if s148: e.search.add_clause(s148)
 c130=cover(W['f130']); s150=cp(c130,c130,W['f150']) if c130 else None
 if s150: e.search.add_clause(s150)
 s196=cp(s148,s150,W['f196']) if s148 and s150 else None
 if s196: e.search.add_clause(s196)
 c19=cover(W['f19']); s217=cp(c19,s196,W['f217']) if c19 and s196 else None
 if s217: e.search.add_clause(s217)
 c18=cover(W['f18']); s229=cp(c18,s217,W['f229']) if c18 and s217 else None
 if s229: e.search.add_clause(s229)
 student=[(h.inline_engine_names(c.lhs,e.reverse_constants),h.inline_engine_names(c.rhs,e.reverse_constants)) for c in e.search.clauses]
 defs={}; after=False; audited=[]; first=None
 for block in h.fof_blocks(proof):
  q=h.parse_fof(block)
  if not q: continue
  fid,kind,formula,tail=q
  try: eq=h.formula_equality(formula)
  except Exception: eq=None
  if eq is None: continue
  x,y=eq
  if kind=='definition':
   if x[0]=='var' and x[1].startswith('sF'): defs[x[1]]=y
   elif y[0]=='var' and y[1].startswith('sF'): defs[y[1]]=x
   continue
  if fid=='f229': after=True; continue
  if not after: continue
  mi=re.search(r'inference\(([^,\]]+)',','.join(tail)); inf=mi.group(1) if mi else ''
  if inf not in ('superposition','forward_demodulation'): continue
  aa=h.map_rigids(h.inline_defs(x,defs),target[2]); bb=h.map_rigids(h.inline_defs(y,defs),target[2])
  exact=any(alpha(r,aa,bb)==alpha(r,sa,sb) for sa,sb in student); present=exact or any(covers(r,sa,sb,aa,bb) for sa,sb in student)
  rec={'id':fid,'inference':inf,'present':present,'exact':exact,'lhs':m.render_term(aa),'rhs':m.render_term(bb)}; audited.append(rec)
  if first is None and not present: first=rec
 out={'id':RID,'f95_seeded':s95 is not None,'f123_seeded':s123 is not None,'f148_seeded':s148 is not None,'f150_seeded':s150 is not None,'f196_seeded':s196 is not None,'f217_seeded':s217 is not None,'f229_seeded':s229 is not None,'clauses_after_seeds':len(e.search.clauses),'audited_after_f229':len(audited),'present_after_f229':sum(x['present'] for x in audited),'first_missing_after_f229':first,'first_steps':audited[:8]}
 Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('NORMAL0040_POSTF229_DIVERGENCE',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
