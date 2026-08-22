#!/usr/bin/env python3
import importlib.util,itertools,json,sys,time
from collections import defaultdict
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py';EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py';CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py';ROU=ROOT/'experiments/mathgraph/run_normal0040_router_overlap_unification_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-common-specialization-matrix-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-common-specialization-matrix-gate.json';RID='evaluation_normal_0040'
def load(p,n):s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def md(m,t,S):return min((m.structural_distance(t,u) for u in S),default=999)
def bucket(d):return 0 if d<=0 else 1 if d==1 else 2 if d==2 else 3 if d<=4 else 5
def canon(m,t):return repr(m.alpha_canonical_term(t,{}))
def pathshape(path):return ''.join(path) if path else 'ROOT'
def subst_pattern(m,mp,vars_):
 vals=[canon(m,mp[v]) for v in vars_ if v in mp];ids={};out=[]
 for x in vals:
  if x not in ids:ids[x]=len(ids)
  out.append(ids[x])
 return tuple(out)
def shared_nontrivial(m,t,shell):
 a={canon(m,x) for x in m.walk_subterms(t) if m.term_size(x)>=2};b={canon(m,x) for x in m.walk_subterms(shell) if m.term_size(x)>=2};return bool(a&b)
def deref(t,s):
 while t[0]=='var' and t[1] in s and s[t[1]]!=t:t=s[t[1]]
 return t
def occurs(v,t,s):
 t=deref(t,s)
 if t[0]=='var':return t[1]==v
 return (occurs(v,t[1],s) or occurs(v,t[2],s)) if t[0]=='op' else False
def unify_all(eqs):
 s={};stack=list(eqs)
 while stack:
  a,b=stack.pop();a=deref(a,s);b=deref(b,s)
  if a==b:continue
  if a[0]=='var':
   if occurs(a[1],b,s):return None
   s[a[1]]=b;continue
  if b[0]=='var':
   if occurs(b[1],a,s):return None
   s[b[1]]=a;continue
  if a[0]!=b[0]:return None
  if a[0]=='op':stack.extend([(a[1],b[1]),(a[2],b[2])]);continue
  return None
 return s
def main():
 p=json.loads(PROTO.read_text());deadline=time.monotonic()+p['bounds']['seconds_soft']
 m=load(SOLVER,'mgcsm');sym=load(SYM,'symcsm');selfm=load(SELF,'selfcsm');op=load(OPC,'opcsm');op.selfmod=selfm;rhs=load(RHS,'rhscsm');rhs.selfm=selfm;ep=load(EP,'epcsm');cut=load(CUT,'cutcsm');rou=load(ROU,'roucsm');rou.epmod=ep
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
     if time.monotonic()>deadline:break
     full=dict(mp);full.update(zip(missing,vals));it=rou.lifted_item(m,selfm,source,target,term,path,side_name,full,'csm')
     if not it:continue
     endpoint=it['schema'][1]
     if m.term_size(endpoint)>maxt:continue
     k=canon(m,endpoint)
     if k in seen:continue
     seen.add(k);desc=(side_name,pathshape(path),subst_pattern(m,full,vars_),bucket(md(m,endpoint,L)),bucket(md(m,endpoint,R)),shared_nontrivial(m,endpoint,opp));out.append({'endpoint':endpoint,'desc':desc,'side':side_name,'path':tuple(path),'subst':full})
     if len(out)>=cap:break
    if len(out)>=cap or time.monotonic()>deadline:break
   if len(out)>=cap or time.monotonic()>deadline:break
  cache[ck]=out;return out
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
 assert len(classes['L'])==5 and len(classes['R'])==5,(len(classes['L']),len(classes['R']))
 def spec_compat(a,b):
  if a['side']!=b['side'] or pathshape(a['path'])!=pathshape(b['path']):return False
  shared=sorted(set(a['subst'])&set(b['subst']));eqs=[(a['subst'][v],b['subst'][v]) for v in shared if a['subst'][v]!=b['subst'][v]]
  return not eqs or unify_all(eqs) is not None
 def class_compat(A,B):
  checks=0
  for ta in A[:p['bounds']['maximum_terms_per_class']]:
   for tb in B[:p['bounds']['maximum_terms_per_class']]:
    for a in interactions(ta,'L'):
     for b in interactions(tb,'R'):
      checks+=1
      if spec_compat(a,b):return {'lhs_term':m.render_term(ta),'rhs_term':m.render_term(tb),'source_side':a['side'],'path_shape':pathshape(a['path']),'shared_vars':sorted(set(a['subst'])&set(b['subst'])),'checks':checks}
      if checks>=p['bounds']['maximum_pair_checks_per_cell'] or time.monotonic()>deadline:return None
  return None
 matrix=[];hits=[]
 for i,(_,A) in enumerate(classes['L']):
  row=[]
  for j,(_,B) in enumerate(classes['R']):
   w=class_compat(A,B);row.append(bool(w))
   if w:hits.append({'L':i,'R':j,'witness':w})
  matrix.append(row)
 decision='COMMON_SPECIALIZATION_MATRIX_RESCUE' if hits else 'NO_MATRIX_RESCUE'
 out={'schema':'mathgraph.normal0040-common-specialization-matrix.v1','id':RID,'protocol':p,'frozen_distance':d,'generation1':{'lhs_terms':len(fronts['L']),'rhs_terms':len(fronts['R']),'lhs_classes':len(classes['L']),'rhs_classes':len(classes['R'])},'compatibility_matrix':matrix,'compatible_cells':len(hits),'hits':hits,'decision':decision,'timed_out':time.monotonic()>deadline}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
