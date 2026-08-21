#!/usr/bin/env python3
"""Prospective distance-2 frontier characterization for evaluation_normal_0040.

The protocol is frozen before this executable.  Reconstruct the verified 3->2
state, compute the exact terms attaining the distance-2 cut, and enumerate a
finite current source-derived one-step continuation closure over that shell.
Selection is effect-level only: whether a replay-valid candidate lowers the
opposite-component structural distance below 2.
"""
import importlib.util,itertools,json,sys
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py'
EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py'
CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-distance2-frontier-v1.json'
OUT=ROOT/'experiments/mathgraph/results/normal0040-distance2-frontier-gate.json'
RID='evaluation_normal_0040'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def canon(m,t):return m.alpha_canonical_term(t,{})

def mindist(m,t,others):
 return min((m.structural_distance(t,u) for u in others),default=999)

def finite_basis(m,ep,source,L,R,shellL,shellR,limit=18):
 vals={canon(m,t):t for t in ep.source_atoms(m,source)}
 # The current finite continuation language is allowed to use already-live
 # frontier structure, but nothing from a teacher trace or target proof.
 seeds=list(shellL)+list(shellR)
 # Also expose the closest live terms on either side so the one-step closure is
 # not artificially restricted to source atoms alone.
 for t in sorted(L,key=lambda x:(mindist(m,x,R),m.term_size(x),m.render_term(x)))[:12]:seeds.append(t)
 for t in sorted(R,key=lambda x:(mindist(m,x,L),m.term_size(x),m.render_term(x)))[:12]:seeds.append(t)
 for t in seeds:
  for u in [t,*list(m.walk_subterms(t))]:
   if m.term_size(u)<=15:vals.setdefault(canon(m,u),u)
 return sorted(vals.values(),key=lambda t:(m.term_size(t),m.render_term(t)))[:limit]

def enumerate_shell(m,selfm,ep,source,target,L,R,shellL,shellR,base_dist=2):
 eps=ep.endpoint_variables(source)
 if not eps:raise SystemExit('no distinguished source endpoint variable')
 ev=eps[0]
 bare_left=(source[0][0]=='var' and source[0][1]==ev)
 bare_right=(source[1][0]=='var' and source[1][1]==ev)
 if not (bare_left or bare_right):raise SystemExit('endpoint variable not a bare source side')
 basis=finite_basis(m,ep,source,L,R,shellL,shellR)
 others=[v for v in source[2] if v!=ev]
 rows=[];seen=set()
 for side,shell,opposite in [('L',shellL,R),('R',shellR,L)]:
  for anchor in sorted(shell,key=lambda t:(m.term_size(t),m.render_term(t))):
   for vals in itertools.product(basis,repeat=len(others)):
    mp={ev:anchor};mp.update(zip(others,vals))
    x=ep.make_instance(m,selfm,source,target,mp,'normal0040-distance2-frontier')
    if not x:continue
    other=x['schema'][1] if bare_left else x['schema'][0]
    d=mindist(m,other,opposite)
    k=ep.eqkey(m,x['schema'][0],x['schema'][1])
    if k in seen:continue
    seen.add(k);x['frontier_side']=side;x['effect_distance']=d;x['satisfies_K']=d<base_dist;rows.append(x)
 rows.sort(key=lambda x:(x['effect_distance'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 return rows,basis

def show(m,xs,k=30):
 return [{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'frontier_side':x['frontier_side'],'effect_distance':x['effect_distance'],'activation':x['activation']} for x in xs[:k]]

def main():
 p=json.loads(PROTO.read_text())
 if not p.get('frozen_before_execution') or p.get('teacher_trace_used'):raise SystemExit('protocol invariant failed')
 m=load(SOLVER,'mg0040d2');sym=load(SYM,'sym0040d2');selfm=load(SELF,'self0040d2');op=load(OPC,'op0040d2');op.selfmod=selfm
 rhs=load(RHS,'rhs0040d2');rhs.selfm=selfm;ep=load(EP,'ep0040d2');cut=load(CUT,'cut0040d2')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])

 # Reconstruct the validated endpoint-addressable distance-3 state.
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target)
 s3,_=ep.frontier(m,sym,source,target,frozen,20.0)
 uf3,terms3,L3,R3,lr3,rr3,d3=cut.components(m,target,s3.nodes)
 if d3!=3:raise SystemExit(f'expected frozen distance 3, got {d3}')

 # Recompute the previously discovered lawful 3->2 contractor from geometry,
 # not by theorem/case dispatch, and install only its unique best effect class.
 c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3)
 good3=[x for x in c3 if x['cross_distance']<3]
 if not good3:raise SystemExit('validated 3->2 contractor no longer reconstructs')
 bestd=min(x['cross_distance'] for x in good3)
 step3=[x for x in good3 if x['cross_distance']==bestd]
 # The prior experiment found a unique member. Preserve that fact as an
 # invariant; fail loud if the reconstructed geometry changes.
 if bestd!=2 or len(step3)!=1:raise SystemExit(f'expected unique distance-2 contractor, got d={bestd}, n={len(step3)}')
 prior=frozen+[step3[0]]
 s2,_=ep.frontier(m,sym,source,target,prior,25.0)
 uf2,terms2,L2,R2,lr2,rr2,d2=cut.components(m,target,s2.nodes)
 if d2!=2:raise SystemExit(f'expected post-contractor distance 2, got {d2}')

 # Exact shell: all live endpoints attaining the verified minimum distance 2.
 shellL=[t for t in L2 if mindist(m,t,R2)==2]
 shellR=[t for t in R2 if mindist(m,t,L2)==2]
 if not shellL and not shellR:raise SystemExit('distance-2 shell unexpectedly empty')
 rows,basis=enumerate_shell(m,selfm,ep,source,target,L2,R2,shellL,shellR,2)
 good=[x for x in rows if x['satisfies_K']]
 bad=[x for x in rows if not x['satisfies_K']]
 exact=[x for x in rows if x['effect_distance']==0]
 d1=[x for x in rows if x['effect_distance']==1]

 A=ep.run_arm(m,sym,source,target,prior,30.0,'A_frozen_distance2')
 B=None;C=None;abl=None
 if good:
  n=min(96,len(good),len(bad)) if bad else min(96,len(good))
  if bad:B=ep.run_arm(m,sym,source,target,prior+bad[:n],30.0,'B_frontier_noncontracting')
  C=ep.run_arm(m,sym,source,target,prior+good[:n],30.0,'C_frontier_K_2to1')
  # Ablation is an explicit fresh reconstruction without the acquired K member.
  if C.get('closure') or (C.get('cross_distance') is not None and C['cross_distance']<2):
   abl=ep.run_arm(m,sym,source,target,prior,30.0,'C_ablation')
  causal=bool(C and C.get('cross_distance') is not None and C['cross_distance']<2 and abl and abl.get('cross_distance')==2 and (not B or B.get('cross_distance',2)>=2))
  strong=bool(C and C.get('closure') and abl and not abl.get('closure') and (not B or not B.get('closure')))
  decision='PASS_STRONG_CLOSURE' if strong else 'PASS_2_TO_1_CAUSAL' if causal else 'PREDICTED_K_FAILED_INSTALLATION'
 else:
  n=0
  # No member of the declared finite current continuation closure satisfies K.
  decision='GRAMMAR_OBSTRUCTION_K_EMPTY'

 out={
  'schema':'mathgraph.normal0040-distance2-frontier-gate.v1','id':RID,
  'J':p['J'],'K_rho':p['K_rho'],'prediction':p['prediction'],
  'prior_transition':{'distance_3':d3,'unique_3_to_2_contractors':len(step3),'best_prior_effect':bestd,'prior_contractor':show(m,step3,1)},
  'frozen_residual':{'cross_distance':d2,'lhs_component_size':len(L2),'rhs_component_size':len(R2),'lhs_shell_size':len(shellL),'rhs_shell_size':len(shellR),'lhs_shell':[m.render_term(t) for t in sorted(shellL,key=lambda t:(m.term_size(t),m.render_term(t)))[:40]],'rhs_shell':[m.render_term(t) for t in sorted(shellR,key=lambda t:(m.term_size(t),m.render_term(t)))[:40]]},
  'declared_constructor_closure':{'kind':'finite replay-valid source-derived one-step closure over exact distance-2 shell','basis_size':len(basis),'basis':[m.render_term(t) for t in basis],'all_candidates':len(rows),'K_2to1_members':len(good),'distance1_members':len(d1),'exact_bridge_members':len(exact),'nonmembers':len(bad),'installed_per_arm':n},
  'arms':{'A':A,'B':B,'C':C,'C_ablation':abl},
  'best_K_members':show(m,good),'best_nonmembers':show(m,bad),
  'decision':decision
 }
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
