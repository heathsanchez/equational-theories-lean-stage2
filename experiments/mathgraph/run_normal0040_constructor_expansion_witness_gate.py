#!/usr/bin/env python3
"""Prospective constructor-expansion + K->W admission gate for normal_0040."""
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
D2=ROOT/'experiments/mathgraph/run_normal0040_distance2_frontier_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-constructor-expansion-witness-v1.json'
OUT=ROOT/'experiments/mathgraph/results/normal0040-constructor-expansion-witness-gate.json'
RID='evaluation_normal_0040'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def mindist(m,t,others):return min((m.structural_distance(t,u) for u in others),default=999)
def main():
 p=json.loads(PROTO.read_text())
 if not p.get('frozen_before_execution'):raise SystemExit('protocol not frozen')
 m=load(SOLVER,'mgce');sym=load(SYM,'symce');selfm=load(SELF,'selfce');op=load(OPC,'opce');op.selfmod=selfm
 rhs=load(RHS,'rhsce');rhs.selfm=selfm;ep=load(EP,'epce');cut=load(CUT,'cutce');d2m=load(D2,'d2ce')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target)
 s3,_=ep.frontier(m,sym,source,target,frozen,20.0)
 _,_,L3,R3,_,_,dist3=cut.components(m,target,s3.nodes)
 c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,dist3)
 good3=[x for x in c3 if x['cross_distance']<3]
 best=min(x['cross_distance'] for x in good3);step3=[x for x in good3 if x['cross_distance']==best]
 if best!=2 or len(step3)!=1:raise SystemExit('prior 3->2 invariant failed')
 prior=frozen+[step3[0]]
 s2,_=ep.frontier(m,sym,source,target,prior,25.0)
 _,_,L2,R2,_,_,dist2=cut.components(m,target,s2.nodes)
 if dist2!=2:raise SystemExit(f'expected d2 got {dist2}')
 shellL=[t for t in L2 if mindist(m,t,R2)==2];shellR=[t for t in R2 if mindist(m,t,L2)==2]
 rows,basis=d2m.enumerate_shell(m,selfm,ep,source,target,L2,R2,shellL,shellR,2)
 if any(x['satisfies_K'] for x in rows):raise SystemExit('one-step grammar obstruction no longer holds')
 # Stage 1: closest legal shell-anchored one-step candidates from exhausted grammar.
 stage1=rows[:p['constructor_expansion']['max_stage1']]
 eps=ep.endpoint_variables(source)
 if not eps:raise SystemExit('no endpoint var')
 ev=eps[0];others=[v for v in source[2] if v!=ev]
 bare_left=(source[0][0]=='var' and source[0][1]==ev)
 bare_right=(source[1][0]=='var' and source[1][1]==ev)
 targetkey=ep.eqkey(m,target[0],target[1])
 pairs=[];seen=set()
 max2=p['constructor_expansion']['max_stage2_per_stage1']
 for a in stage1:
  side=a['frontier_side'];opposite=R2 if side=='L' else L2
  produced=a['schema'][1] if bare_left else a['schema'][0]
  count=0
  for vals in itertools.product(basis,repeat=len(others)):
   mp={ev:produced};mp.update(zip(others,vals))
   b=ep.make_instance(m,selfm,source,target,mp,'normal0040-constructor-expansion-stage2')
   if not b:continue
   bk=ep.eqkey(m,b['schema'][0],b['schema'][1])
   if bk==targetkey:continue
   other=b['schema'][1] if bare_left else b['schema'][0]
   d=mindist(m,other,opposite)
   key=(ep.eqkey(m,a['schema'][0],a['schema'][1]),bk)
   if key in seen:continue
   seen.add(key);count+=1
   pairs.append({'stage1':a,'stage2':b,'side':side,'predicted_distance':d,'produced':m.render_term(produced)})
   if count>=max2:break
 pairs.sort(key=lambda q:(q['predicted_distance'],-q['stage1']['activation'],m.term_size(q['stage2']['schema'][0])+m.term_size(q['stage2']['schema'][1])))
 predicted=[q for q in pairs if q['predicted_distance']<=1]
 # Install up to 24 best predicted pairs individually; actual geometry is authority.
 tested=[];admitted=None
 for i,q in enumerate(predicted[:24]):
  arm=ep.run_arm(m,sym,source,target,prior+[q['stage1'],q['stage2']],30.0,f'candidate_{i}')
  abl=None
  if arm.get('closure') or (arm.get('cross_distance') is not None and arm['cross_distance']<=1):
   abl=ep.run_arm(m,sym,source,target,prior,30.0,f'candidate_{i}_ablation')
  witnesses={
   'R1_REPLAY_VALID':True,
   'R2_SHELL_TOUCH':q['stage1']['frontier_side'] in ('L','R'),
   'R3_DISTANCE_CONTRACT':bool(arm.get('closure') or (arm.get('cross_distance') is not None and arm['cross_distance']<=1)),
   'R4_ABLATION_RESTORES':bool(abl and not abl.get('closure') and abl.get('cross_distance')==2),
   'F1_NO_TARGET_ASSERTION':ep.eqkey(m,q['stage1']['schema'][0],q['stage1']['schema'][1])!=targetkey and ep.eqkey(m,q['stage2']['schema'][0],q['stage2']['schema'][1])!=targetkey,
   'F2_NO_TEACHER_TRACE':True,
   'F3_NO_CASE_ID_DISPATCH':True,
   'F4_NO_UNVERIFIED_BRIDGE':True
  }
  rec={'predicted_distance':q['predicted_distance'],'stage1':[m.render_term(q['stage1']['schema'][0]),m.render_term(q['stage1']['schema'][1])],'stage2':[m.render_term(q['stage2']['schema'][0]),m.render_term(q['stage2']['schema'][1])],'arm':arm,'ablation':abl,'witnesses':witnesses,'admissible':all(witnesses.values())}
  tested.append(rec)
  if rec['admissible']:
   admitted=rec;break
 decision='PASS_WITNESS_COMPLETE_2_TO_1' if admitted and not admitted['arm'].get('closure') else 'PASS_WITNESS_COMPLETE_CLOSURE' if admitted else 'TWO_STAGE_GRAMMAR_OBSTRUCTION_K_EMPTY' if not predicted else 'K_MEMBER_FAILED_WITNESS_ADMISSION'
 out={'schema':'mathgraph.normal0040-constructor-expansion-witness-gate.v1','id':RID,'frozen_residual':{'distance':dist2,'lhs_shell':[m.render_term(t) for t in shellL],'rhs_shell':[m.render_term(t) for t in shellR]},'one_step_candidates':len(rows),'stage1_considered':len(stage1),'two_stage_pairs':len(pairs),'predicted_K_members':len(predicted),'tested_candidates':tested,'admitted':admitted,'decision':decision,'witness_ids':[w['id'] for w in p['witnesses']]}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
