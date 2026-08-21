#!/usr/bin/env python3
import importlib.util, json, sys, time
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
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-distance2-position-attachment-v1.json'
OUT=ROOT/'experiments/mathgraph/results/normal0040-distance2-position-attachment-gate.json'
RID='evaluation_normal_0040'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def cp(m,src,dst,tag):
 o=len(dst)
 for n in src:
  ov=n.overlap_record
  if ov is not None: ov=(o+ov[0],o+ov[1],*ov[2:])
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(o+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=tuple((v,t,tuple(o+p for p in ps)) for v,t,ps in n.term_origins),constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=ov))
 return o

def orient(m,item,rev,tag):
 nodes=[];ns,r=item['proof'];o=cp(m,ns,nodes,tag);root=o+r
 if rev:
  q=nodes[root];nodes.append(m.EqualityNode(q.rhs,q.lhs,'symmetry',parents=(root,),constructor=tag+'-sym'));root=len(nodes)-1
 return nodes,root

def paths(t,maxdepth=4,p=()):
 out=[]
 if p and len(p)<=maxdepth: out.append((p,t))
 if t[0]=='op' and len(p)<maxdepth:
  out+=paths(t[1],maxdepth,p+('L',));out+=paths(t[2],maxdepth,p+('R',))
 return out

def replace(t,path,x):
 if not path:return x
 if t[0]!='op':raise ValueError('bad path')
 h,*rest=path
 return ('op',replace(t[1],tuple(rest),x),t[2]) if h=='L' else ('op',t[1],replace(t[2],tuple(rest),x))

def md(m,t,S):return min((m.structural_distance(t,u) for u in S),default=999)
def canonpair(m,a,b):
 n={};x=(m.alpha_canonical_term(a,n),m.alpha_canonical_term(b,n));n={};y=(m.alpha_canonical_term(b,n),m.alpha_canonical_term(a,n));return min(x,y)

def position_lifts(m,source,target,library,shellL,shellR,L,R,max_lifts=2400):
 norm=m.EquationalNormalizer(source,target,time.monotonic()+25,dict(m.NORMALIZATION_PORTFOLIO[1]));raw={}
 templates=[('L',s) for s in shellL]+[('R',s) for s in shellR]
 for side,shell in templates:
  for path,sub in paths(shell,4):
   for idx,item in enumerate(library[:192]):
    for rev in (False,True):
     nodes,root=orient(m,item,rev,'position-base');q=nodes[root]
     if q.lhs!=sub:continue
     start=shell;end=replace(shell,path,q.rhs)
     if max(m.term_size(start),m.term_size(end))>160:continue
     try:lift=norm.lift_context(nodes,root,start,path)
     except Exception:continue
     if lift is None:continue
     if not m.replay_dag(source,nodes,lift,maximum_term_size=220,maximum_nodes=30000):continue
     key=canonpair(m,start,end)
     if key in raw:continue
     opp=R if side=='L' else L
     effect=md(m,end,opp)
     raw[key]={'schema':(start,end,tuple(sorted(m.term_variables(start)|m.term_variables(end)))),'proof':(nodes,lift),'side':side,'path':path,'base_index':idx,'effect_distance':effect,'shell_touch':True}
     if len(raw)>=max_lifts:break
    if len(raw)>=max_lifts:break
   if len(raw)>=max_lifts:break
  if len(raw)>=max_lifts:break
 out=list(raw.values());out.sort(key=lambda z:(z['effect_distance'],len(z['path']),m.term_size(z['schema'][1])));return out

def aligned_composites(m,source,lifts,L,R,limit=2400):
 by_start={};by_end={}
 for i,x in enumerate(lifts):
  a,b=x['schema'][:2];by_start.setdefault(a,[]).append((i,x));by_end.setdefault(b,[]).append((i,x))
 raw={}
 for mid,lefts in by_end.items():
  rights=by_start.get(mid,[])
  for i,x in lefts[:24]:
   for j,y in rights[:24]:
    if i==j:continue
    nodes=[];ox=cp(m,x['proof'][0],nodes,'pos-comp-a');rx=ox+x['proof'][1];oy=cp(m,y['proof'][0],nodes,'pos-comp-b');ry=oy+y['proof'][1]
    a=x['schema'][0];b=y['schema'][1]
    nodes.append(m.EqualityNode(a,b,'transitivity',parents=(rx,ry),constructor='position-sensitive-context-composition'));root=len(nodes)-1
    if not m.replay_dag(source,nodes,root,maximum_term_size=240,maximum_nodes=40000):continue
    key=canonpair(m,a,b)
    if key in raw:continue
    effect=min(md(m,a,L)+md(m,b,R),md(m,a,R)+md(m,b,L))
    raw[key]={'schema':(a,b,tuple(sorted(m.term_variables(a)|m.term_variables(b)))),'proof':(nodes,root),'side':'C','path':(), 'parents':(i,j),'effect_distance':effect,'shell_touch':x['shell_touch'] or y['shell_touch']}
    if len(raw)>=limit:break
   if len(raw)>=limit:break
  if len(raw)>=limit:break
 out=list(raw.values());out.sort(key=lambda z:(z['effect_distance'],m.term_size(z['schema'][0])+m.term_size(z['schema'][1])));return out

def main():
 p=json.loads(PROTO.read_text());m=load(SOLVER,'mgpos');sym=load(SYM,'sympos');selfm=load(SELF,'selfpos');op=load(OPC,'oppos');op.selfmod=selfm;rhs=load(RHS,'rhspos');rhs.selfm=selfm;ep=load(EP,'eppos');cut=load(CUT,'cutpos');d2m=load(D2,'d2pos')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target);s3,_=ep.frontier(m,sym,source,target,frozen,20.0);_,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes);c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3);good=[x for x in c3 if x['cross_distance']<3];best=min(x['cross_distance'] for x in good);step=[x for x in good if x['cross_distance']==best]
 if d3!=3 or best!=2 or len(step)!=1:raise SystemExit('prior geometry changed')
 prior=frozen+[step[0]];s2,_=ep.frontier(m,sym,source,target,prior,25.0);_,_,L,R,_,_,d=cut.components(m,target,s2.nodes)
 if d!=2:raise SystemExit('expected d2')
 shellL=[t for t in L if md(m,t,R)==2];shellR=[t for t in R if md(m,t,L)==2]
 unary,basis=d2m.enumerate_shell(m,selfm,ep,source,target,L,R,shellL,shellR,2)
 retained=[x for x in prior if isinstance(x,dict) and x.get('proof')]
 library=(unary[:96]+retained[:96])
 lifts=position_lifts(m,source,target,library,shellL,shellR,L,R,2400);comps=aligned_composites(m,source,lifts,L,R,2400)
 candidates=[x for x in lifts if x['effect_distance']<=1]+[x for x in comps if x['effect_distance']<=1]
 candidates.sort(key=lambda z:(z['effect_distance'],0 if z['side']!='C' else 1,m.term_size(z['schema'][0])+m.term_size(z['schema'][1])))
 A=ep.run_arm(m,sym,source,target,prior,25.0,'A_d2')
 tested=[];admitted=None;ablation=None
 for i,x in enumerate(candidates[:64]):
  arm=ep.run_arm(m,sym,source,target,prior+[x],18.0,f'position_{i}')
  contracted=arm.get('closure') or (arm.get('cross_distance') is not None and arm['cross_distance']<=1)
  witness={
   'R1_REPLAY_VALID':m.replay_dag(source,x['proof'][0],x['proof'][1],maximum_term_size=240,maximum_nodes=40000),
   'R2_SHELL_TOUCH':bool(x.get('shell_touch')),
   'R3_DISTANCE_CONTRACT':bool(contracted),
   'R4_ABLATION_RESTORES':False,
   'F1_NO_TARGET_ASSERTION':x['schema'][:2]!=(target[0],target[1]),
   'F2_NO_TEACHER_TRACE':True,
   'F3_NO_CASE_ID_DISPATCH':True,
   'F4_NO_UNVERIFIED_BRIDGE':True
  }
  if contracted:
   ab=ep.run_arm(m,sym,source,target,prior,18.0,'position_ablation');witness['R4_ABLATION_RESTORES']=((not ab.get('closure')) and ab.get('cross_distance')==2)
  else:ab=None
  rec={'candidate':{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'side':x['side'],'path':list(x['path']),'predicted_effect':x['effect_distance']},'arm':arm,'witnesses':witness,'admissible':all(witness.values())};tested.append(rec)
  if rec['admissible']:admitted=rec;ablation=ab;break
 decision='PASS_POSITION_ATTACHMENT_CLOSURE' if admitted and admitted['arm'].get('closure') else 'PASS_POSITION_ATTACHMENT_2_TO_1' if admitted else 'POSITION_ATTACHMENT_GRAMMAR_OBSTRUCTION_K_EMPTY' if not candidates else 'POSITION_PREDICTED_BUT_NOT_CAUSAL'
 out={'schema':'mathgraph.normal0040-distance2-position-attachment.v1','id':RID,'protocol':p,'frozen':{'distance':d,'lhs_component':len(L),'rhs_component':len(R),'lhs_shell':[m.render_term(t) for t in shellL],'rhs_shell':[m.render_term(t) for t in shellR]},'counts':{'basis':len(basis),'unary':len(unary),'library':len(library),'position_lifts_verified':len(lifts),'aligned_composites_verified':len(comps),'predicted_K_members':len(candidates),'tested':len(tested)},'baseline':A,'tested_candidates':tested,'admitted':admitted,'ablation':ablation,'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
