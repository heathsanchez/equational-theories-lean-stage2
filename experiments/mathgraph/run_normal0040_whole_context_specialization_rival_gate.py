#!/usr/bin/env python3
import importlib.util,itertools,json,sys
from collections import defaultdict
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py';EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py';CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py';ROU=ROOT/'experiments/mathgraph/run_normal0040_router_overlap_unification_gate.py';QR=ROOT/'experiments/mathgraph/run_normal0040_substitution_quotient_rival_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-whole-context-specialization-rival-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-whole-context-specialization-rival-gate.json';RID='evaluation_normal_0040'
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
 p=json.loads(PROTO.read_text());m=load(SOLVER,'mgwc');sym=load(SYM,'symwc');selfm=load(SELF,'selfwc');op=load(OPC,'opwc');op.selfmod=selfm;rhs=load(RHS,'rhswc');rhs.selfm=selfm;ep=load(EP,'epwc');cut=load(CUT,'cutwc');rou=load(ROU,'rouwc');rou.epmod=ep;qr=load(QR,'qrwc')
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
     full=dict(mp);full.update(zip(missing,vals));it=rou.lifted_item(m,selfm,source,target,term,path,side_name,full,'wc-probe')
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
 stages=defaultdict(int);per=defaultdict(lambda:defaultdict(int));examples=[];maxchecks=p['bounds']['maximum_pair_checks_per_cell'];maxex=p['bounds']['maximum_success_examples_per_cell']
 def bump(cell,k):stages[k]+=1;per[cell][k]+=1
 for i,(_,A) in enumerate(classes['L']):
  for j,(_,B) in enumerate(classes['R']):
   cell=f'{i},{j}';checks=0;cell_examples=0;stop=False
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
       shared=sorted(set(a['subst'])&set(b['subst']));conf=[v for v in shared if a['subst'][v]!=b['subst'][v]]
       if not conf:continue
       theta=qr.unify_all([(a['subst'][v],b['subst'][v]) for v in conf])
       if theta is None:continue
       bump(cell,'P1_common_specialization_exists')
       sa={v:apply_theta(t,theta) for v,t in a['subst'].items()};sb={v:apply_theta(t,theta) for v,t in b['subst'].items()}
       if any(sa[v]!=sb[v] for v in set(sa)&set(sb)):continue
       bump(cell,'P2_specialized_assignments_agree')
       olda=rou.lifted_item(m,selfm,source,target,ta,a['path'],a['side'],sa,f'wc-{i}-{j}-A-L')
       oldb=rou.lifted_item(m,selfm,source,target,tb,b['path'],b['side'],sb,f'wc-{i}-{j}-A-R')
       if olda:bump(cell,'P3_payload_left_constructible')
       if oldb:bump(cell,'P4_payload_right_constructible')
       hta=apply_theta(ta,theta);htb=apply_theta(tb,theta)
       newa=rou.lifted_item(m,selfm,source,target,hta,a['path'],a['side'],sa,f'wc-{i}-{j}-B-L')
       newb=rou.lifted_item(m,selfm,source,target,htb,b['path'],b['side'],sb,f'wc-{i}-{j}-B-R')
       if newa:bump(cell,'P5_whole_left_constructible')
       if newb:bump(cell,'P6_whole_right_constructible')
       lrv=bool(newa and m.replay_dag(source,newa['proof'][0],newa['proof'][1],maximum_term_size=p['bounds']['replay_maximum_term_size'],maximum_nodes=p['bounds']['replay_maximum_nodes']))
       rrv=bool(newb and m.replay_dag(source,newb['proof'][0],newb['proof'][1],maximum_term_size=p['bounds']['replay_maximum_term_size'],maximum_nodes=p['bounds']['replay_maximum_nodes']))
       if lrv:bump(cell,'P7_whole_left_replay_valid')
       if rrv:bump(cell,'P8_whole_right_replay_valid')
       if lrv and rrv:
        bump(cell,'P9_whole_pair_replay_valid')
        if cell_examples<maxex:
         examples.append({'cell':[i,j],'theta':{k:m.render_term(v) for k,v in theta.items()},'host_L_before':m.render_term(ta),'host_L_after':m.render_term(hta),'host_R_before':m.render_term(tb),'host_R_after':m.render_term(htb),'path':list(a['path']),'side':a['side']});cell_examples+=1
 if stages['P3_payload_left_constructible'] or stages['P4_payload_right_constructible']:decision='PAYLOAD_ONLY_RESCUE_UNEXPECTED'
 elif stages['P9_whole_pair_replay_valid']>0:decision='WHOLE_CONTEXT_RESCUES_CONSTRUCTION_AND_REPLAY'
 elif stages['P5_whole_left_constructible'] or stages['P6_whole_right_constructible']:decision='WHOLE_CONTEXT_CONSTRUCTS_BUT_REPLAY_FAILS'
 else:decision='WHOLE_CONTEXT_NO_RESCUE'
 out={'schema':'mathgraph.normal0040-whole-context-specialization-rival.v1','id':RID,'protocol':p,'frozen':{'distance':d,'classes':{'L':5,'R':5},'front_terms':{'L':len(fronts['L']),'R':len(fronts['R'])}},'stage_counts':dict(stages),'per_cell':{k:dict(v) for k,v in per.items()},'examples':examples,'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
