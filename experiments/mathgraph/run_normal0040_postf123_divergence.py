#!/usr/bin/env python3
import argparse, importlib.util, json, re, sys, time, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'; RID='evaluation_normal_0040'
def load_mod(path,name):
 spec=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(spec); sys.modules[name]=m; spec.loader.exec_module(m); return m
def alpha_sig(rigid,a,b):
 names={}; x=rigid.alpha_canonical_term(a,names); y=rigid.alpha_canonical_term(b,names); return min((x,y),(y,x))
def covers(rigid,sa,sb,ta,tb):
 for x,y in ((sa,sb),(sb,sa)):
  subst={}
  if rigid.match_term(x,ta,subst) and rigid.match_term(y,tb,subst): return True
 return False
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
 m=load_mod(SOLVER,'mg_postf123_solver'); h=load_mod(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'mg_postf123_helpers')
 row=h.load_row(a.input,RID); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 engine=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits); engine.solve(); rigid=m.RigidSuperpositionModule()
 trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
 wanted=h.extract_wanted(proof,target[2],m,('f27','f81','f95','f123'))
 def find_cover(eq):
  for c in engine.search.clauses:
   x=h.inline_engine_names(c.lhs,engine.reverse_constants); y=h.inline_engine_names(c.rhs,engine.reverse_constants)
   for rev,(u,v) in enumerate(((x,y),(y,x))):
    subst={}
    if rigid.match_term(u,eq[0],subst) and rigid.match_term(v,eq[1],subst): return c,subst,bool(rev)
  return None
 c81=find_cover(wanted['f81']); seed95=None; seed123=None
 if c81:
  c,subst,rev=c81; base=c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,)); mat=engine.search.instantiate(base,subst); goal=alpha_sig(rigid,*wanted['f95'])
  for path in rigid.nonvariable_positions(mat.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
   p=engine.search.critical_pair(mat,mat,0,0,path)
   if p is None: continue
   x=h.inline_engine_names(p.lhs,engine.reverse_constants); y=h.inline_engine_names(p.rhs,engine.reverse_constants)
   if alpha_sig(rigid,x,y)==goal: seed95=p; engine.search.add_clause(p); break
 if seed95:
  c27=find_cover(wanted['f27'])
  if c27:
   c,subst,rev=c27; base=c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,)); mat27=engine.search.instantiate(base,subst); goal=alpha_sig(rigid,*wanted['f123'])
   for a0 in (mat27,m.Recipe(mat27.rhs,mat27.lhs,'symmetry',(mat27,))):
    for b0 in (seed95,m.Recipe(seed95.rhs,seed95.lhs,'symmetry',(seed95,))):
     for outer,inner in ((a0,b0),(b0,a0)):
      for path in rigid.nonvariable_positions(outer.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
       p=engine.search.critical_pair(outer,inner,0,1,path)
       if p is None: continue
       x=h.inline_engine_names(p.lhs,engine.reverse_constants); y=h.inline_engine_names(p.rhs,engine.reverse_constants)
       if alpha_sig(rigid,x,y)==goal: seed123=p; engine.search.add_clause(p); break
      if seed123: break
     if seed123: break
    if seed123: break
 student=[(h.inline_engine_names(c.lhs,engine.reverse_constants),h.inline_engine_names(c.rhs,engine.reverse_constants)) for c in engine.search.clauses]
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
  if fid=='f123': after=True; continue
  if not after: continue
  mi=re.search(r'inference\(([^,\]]+)',','.join(tail)); inf=mi.group(1) if mi else ''
  if inf not in ('superposition','forward_demodulation'): continue
  aa=h.map_rigids(h.inline_defs(x,defs),target[2]); bb=h.map_rigids(h.inline_defs(y,defs),target[2])
  exact=any(alpha_sig(rigid,aa,bb)==alpha_sig(rigid,sa,sb) for sa,sb in student)
  present=exact or any(covers(rigid,sa,sb,aa,bb) for sa,sb in student)
  rec={'id':fid,'inference':inf,'present':present,'exact':exact,'lhs':m.render_term(aa),'rhs':m.render_term(bb)}; audited.append(rec)
  if first is None and not present: first=rec
 out={'id':RID,'f95_seeded':seed95 is not None,'f123_seeded':seed123 is not None,'clauses_after_seeds':len(engine.search.clauses),'audited_after_f123':len(audited),'present_after_f123':sum(r['present'] for r in audited),'first_missing_after_f123':first,'first_steps':audited[:8]}
 Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('NORMAL0040_POSTF123_DIVERGENCE',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
