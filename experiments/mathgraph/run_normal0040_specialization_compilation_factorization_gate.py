#!/usr/bin/env python3
import importlib.util,itertools,json,sys
from collections import defaultdict
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py';EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py';CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py';ROU=ROOT/'experiments/mathgraph/run_normal0040_router_overlap_unification_gate.py';QR=ROOT/'experiments/mathgraph/run_normal0040_substitution_quotient_rival_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-specialization-compilation-factorization-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-specialization-compilation-factorization-gate.json';RID='evaluation_normal_0040'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def canon(m,t):return repr(m.alpha_canonical_term(t,{}))
def md(m,t,S):return min((m.structural_distance(t,u) for u in S),default=999)
def bucket(d):return 0 if d<=0 else 1 if d==1 else 2 if d==2 else 3 if d<=4 else 5
def pathshape(p):return ''.join(p) if p else 'ROOT'
def subst_pattern(m,mp,vars_):
 vals=[canon(m,mp[v]) for v in vars_ if v in mp];ids={};out=[]
 for x in vals:
  if x not in ids:ids[x]=len(ids)
  out.append(ids[x])
 return tuple(out)
def shared_nontrivial(m,t,shell):
 a={canon(m,x) for x in m.walk_subterms(t) if m.term_size(x)>=2};b={canon(m,x) for x in m.walk_subterms(shell) if m.term_size(x)>=2};return bool(a&b)
def apply_theta(t,theta):
 if not theta:return t
 if t[0]=='var':
  if t[1] not in theta:return t
  u=theta[t[1]]
  return t if u==t else apply_theta(u,theta)
 if t[0]=='op':return ('op',apply_theta(t[1],theta),apply_theta(t[2],theta))
 return t
def main():
 p=json.loads(PROTO.read_text());m=load(SOLVER,'mgcf');sym=load(SYM,'symcf');selfm=load(SELF,'selfcf');op=load(OPC,'opcf');op.selfmod=selfm;rhs=load(RHS,'rhscf');rhs.selfm=selfm;ep=load(EP,'epcf');cut=load(CUT,'cutcf');rou=load(ROU,'roucf');rou.epmod=ep;qr=load(QR,'qrcf')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target);s3,_=ep.frontier(m,sym,source,target,frozen,20.0);_,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes);c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3);good=[x for x in c3 if x['cross_distance']<3];best=min(x['cross_distance'] for x in good);step=[x for x in good if x['cross_distance']==best];assert d3==3 and best==2 and len(step)==1
 prior=frozen+[step[0]];s2,_=ep.frontier(m,sym,source,target,prior,25.0);_,_,L,R,_,_,d=cut.components(m,target,s2.nodes);assert d==2
 shellL=[t for t in L if md(m,t,R)==2];shellR=[t for t in R if md(m,t,L)==2];assert len(shellL)==len(shellR)==1
 fillers=rou.source_atoms(m,source)[:p['bounds']['maximum_fillers']];vars_=list(source[2]);cap=p['bounds']['maximum_interactions_per_term'];maxt=p['bounds']['maximum_term_size'];cache={}
 def interactions(term,origin):
  ck=(origin,canon(m,term))
  if ck in cache:return cache[ck]
  opp=shellR[0] if origin=='L' else shellL[0];out=[];seen=set()
  for side_name,pat in [('lhs',source[0]),('rhs',source[1])]:
   for path,sub in rou.paths(term):
    mp={}
    if not m.match_term(pat,sub,mp):continue
    missing=[v for v in vars_ if v not in mp]
    if len(missing)>2:continue
    for vals in itertools.product(fillers,repeat=len(missing)):
     full=dict(mp);full.update(zip(missing,vals));it=rou.lifted_item(m,selfm,source,target,term,path,side_name,full,'cf-probe')
     if not it:continue
     endpoint=it['schema'][1]
     if m.term_size(endpoint)>maxt:continue
     k=canon(m,endpoint)
     if k in seen:continue
     seen.add(k);desc=(side_name,pathshape(path),subst_pattern(m,full,vars_),bucket(md(m,endpoint,L)),bucket(md(m,endpoint,R)),shared_nontrivial(m,endpoint,opp));out.append({'endpoint':endpoint,'desc':desc,'side':side_name,'path':tuple(path),'subst':full})
     if len(out)>=cap:return out
  return out
 def iface(t,o):return tuple(sorted({x['desc'] for x in interactions(t,o)}))
 fronts={}
 for o,shell in [('L',shellL[0]),('R',shellR[0])]:
  vals=[];seen=set()
  for x in interactions(shell,o):
   k=canon(m,x['endpoint'])
   if k not in seen:seen.add(k);vals.append(x['endpoint'])
  fronts[o]=vals
 classes={}
 for o in ('L','R'):
  by=defaultdict(list);edges=0
  for t in fronts[o]:
   ints=interactions(t,o);edges+=len(ints)
   if edges>4000:break
   by[iface(t,o)].append(t)
  classes[o]=list(by.items())
 assert len(classes['L'])==5 and len(classes['R'])==5
 stages=defaultdict(int);per=defaultdict(lambda:defaultdict(int));examples={};maxchecks=p['bounds']['maximum_pair_checks_per_cell']
 def bump(cell,k):stages[k]+=1;per[cell][k]+=1
 for i,(_,A) in enumerate(classes['L']):
  for j,(_,B) in enumerate(classes['R']):
   cell=f'{i},{j}';checks=0
   stop=False
   for ta in A[:p['bounds']['maximum_terms_per_class']]:
    if stop:break
    for tb in B[:p['bounds']['maximum_terms_per_class']]:
     if stop:break
     for a in interactions(ta,'L'):
      if stop:break
      for b in interactions(tb,'R'):
       checks+=1;bump(cell,'P0_pair_examined')
       if checks>maxchecks:stop=True;break
       if a['side']!=b['side'] or pathshape(a['path'])!=pathshape(b['path']):continue
       bump(cell,'P1_orientation_and_path_match')
       shared=sorted(set(a['subst'])&set(b['subst']));conf=[v for v in shared if a['subst'][v]!=b['subst'][v]]
       if not conf:continue
       bump(cell,'P2_literal_conflict_present')
       theta=qr.unify_all([(a['subst'][v],b['subst'][v]) for v in conf])
       if theta is None:continue
       bump(cell,'P3_common_specialization_exists')
       sa={v:apply_theta(t,theta) for v,t in a['subst'].items()};sb={v:apply_theta(t,theta) for v,t in b['subst'].items()}
       if any(sa[v]!=sb[v] for v in set(sa)&set(sb)):continue
       bump(cell,'P4_specialized_shared_assignments_agree')
       la=rou.lifted_item(m,selfm,source,target,ta,a['path'],a['side'],sa,f'cf-{i}-{j}-L')
       if not la:
        examples.setdefault('left_construct_fail',{'cell':[i,j],'theta':{k:m.render_term(v) for k,v in theta.items()}});continue
       bump(cell,'P5_left_contextual_item_constructible')
       lb=rou.lifted_item(m,selfm,source,target,tb,b['path'],b['side'],sb,f'cf-{i}-{j}-R')
       if not lb:
        examples.setdefault('right_construct_fail',{'cell':[i,j],'theta':{k:m.render_term(v) for k,v in theta.items()}});continue
       bump(cell,'P6_right_contextual_item_constructible')
       lrv=m.replay_dag(source,la['proof'][0],la['proof'][1],maximum_term_size=p['bounds']['replay_maximum_term_size'],maximum_nodes=p['bounds']['replay_maximum_nodes'])
       if lrv:bump(cell,'P7_left_replay_valid')
       else:examples.setdefault('left_replay_fail',{'cell':[i,j]})
       rrv=m.replay_dag(source,lb['proof'][0],lb['proof'][1],maximum_term_size=p['bounds']['replay_maximum_term_size'],maximum_nodes=p['bounds']['replay_maximum_nodes'])
       if rrv:bump(cell,'P8_right_replay_valid')
       else:examples.setdefault('right_replay_fail',{'cell':[i,j]})
       if lrv and rrv:bump(cell,'P9_pair_replay_valid')
 cells_p3=sum(1 for x in per.values() if x['P3_common_specialization_exists']>0);cells_p4=sum(1 for x in per.values() if x['P4_specialized_shared_assignments_agree']>0);cells_p5=sum(1 for x in per.values() if x['P5_left_contextual_item_constructible']>0);cells_p6=sum(1 for x in per.values() if x['P6_right_contextual_item_constructible']>0);cells_p9=sum(1 for x in per.values() if x['P9_pair_replay_valid']>0)
 if stages['P9_pair_replay_valid']>0:decision='REPLAYABLE_PAIR_EXISTS'
 elif stages['P4_specialized_shared_assignments_agree']==0:decision='FAILS_BEFORE_SPECIALIZATION'
 elif stages['P5_left_contextual_item_constructible']==0 or stages['P6_right_contextual_item_constructible']==0:
  decision='ASYMMETRIC_COMPILATION_FAILURE' if bool(stages['P5_left_contextual_item_constructible'])!=bool(stages['P6_right_contextual_item_constructible']) else 'SPECIALIZATION_AGREES_BUT_ITEM_CONSTRUCTION_FAILS'
 elif stages['P7_left_replay_valid']==0 or stages['P8_right_replay_valid']==0:decision='ASYMMETRIC_COMPILATION_FAILURE' if bool(stages['P7_left_replay_valid'])!=bool(stages['P8_right_replay_valid']) else 'ITEMS_CONSTRUCT_BUT_REPLAY_FAILS'
 else:decision='MIXED_FAILURE_VERSION_SPACE'
 out={'schema':'mathgraph.normal0040-specialization-compilation-factorization.v1','id':RID,'protocol':p,'frozen':{'distance':d,'classes':{'L':5,'R':5},'front_terms':{'L':len(fronts['L']),'R':len(fronts['R'])}},'stage_counts':dict(stages),'cells_reaching':{'P3':cells_p3,'P4':cells_p4,'P5':cells_p5,'P6':cells_p6,'P9':cells_p9},'per_cell':{k:dict(v) for k,v in per.items()},'examples':examples,'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
