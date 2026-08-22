#!/usr/bin/env python3
import importlib.util,itertools,json,sys,time
from collections import defaultdict
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py';EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py';CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py';ROU=ROOT/'experiments/mathgraph/run_normal0040_router_overlap_unification_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-substitution-quotient-rival-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-substitution-quotient-rival-gate.json';RID='evaluation_normal_0040'
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
 return occurs(v,t[1],s) or occurs(v,t[2],s) if t[0]=='op' else False
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
 m=load(SOLVER,'mgq');sym=load(SYM,'symq');selfm=load(SELF,'selfq');op=load(OPC,'opq');op.selfmod=selfm;rhs=load(RHS,'rhsq');rhs.selfm=selfm;ep=load(EP,'epq');cut=load(CUT,'cutq');rou=load(ROU,'rouq');rou.epmod=ep
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target);s3,_=ep.frontier(m,sym,source,target,frozen,20.0);_,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes);c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3);good=[x for x in c3 if x['cross_distance']<3];best=min(x['cross_distance'] for x in good);step=[x for x in good if x['cross_distance']==best];assert d3==3 and best==2 and len(step)==1
 prior=frozen+[step[0]];s2,_=ep.frontier(m,sym,source,target,prior,25.0);_,_,L,R,_,_,d=cut.components(m,target,s2.nodes);assert d==2
 shellL=[t for t in L if md(m,t,R)==2];shellR=[t for t in R if md(m,t,L)==2];assert len(shellL)==len(shellR)==1
 parent={}
 def key(t):return repr(t)
 def find(x):
  parent.setdefault(x,x)
  if parent[x]!=x:parent[x]=find(parent[x])
  return parent[x]
 def union(a,b):
  a=find(a);b=find(b)
  if a!=b:parent[b]=a
 for n in s2.nodes:union(key(n.lhs),key(n.rhs))
 def veq(a,b):return a==b or (key(a) in parent and key(b) in parent and find(key(a))==find(key(b)))
 fillers=rou.source_atoms(m,source)[:p['bounds']['maximum_fillers']];vars_=list(source[2]);maxt=p['bounds']['maximum_term_size'];cap=p['bounds']['maximum_interactions_per_term'];cache={}
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
     full=dict(mp);full.update(zip(missing,vals));it=rou.lifted_item(m,selfm,source,target,term,path,side_name,full,'qr')
     if not it:continue
     endpoint=it['schema'][1]
     if m.term_size(endpoint)>maxt:continue
     k=canon(m,endpoint)
     if k in seen:continue
     seen.add(k);desc=(side_name,pathshape(path),subst_pattern(m,full,vars_),bucket(md(m,endpoint,L)),bucket(md(m,endpoint,R)),shared_nontrivial(m,endpoint,opp))
     out.append({'endpoint':endpoint,'desc':desc,'side':side_name,'path':tuple(path),'subst':full})
     if len(out)>=cap:break
    if len(out)>=cap or time.monotonic()>deadline:break
   if len(out)>=cap or time.monotonic()>deadline:break
  cache[ck]=out;return out
 def iface(term,origin):return tuple(sorted({x['desc'] for x in interactions(term,origin)}))
 fronts={}
 for o,shell in [('L',shellL[0]),('R',shellR[0])]:
  vals=[];seen=set()
  for x in interactions(shell,o):
   k=canon(m,x['endpoint'])
   if k not in seen:seen.add(k);vals.append(x['endpoint'])
  fronts[o]=vals
 classes={}
 for o in ('L','R'):
  by=defaultdict(list)
  for t in fronts[o]:by[iface(t,o)].append(t)
  classes[o]=list(by.items())
 assert len(classes['L'])==p['parent_evidence']['generation1_lhs_classes'] and len(classes['R'])==p['parent_evidence']['generation1_rhs_classes']
 lterms=classes['L'][0][1][:p['bounds']['maximum_terms_per_class']];rterms=classes['R'][0][1][:p['bounds']['maximum_terms_per_class']]
 lr=[];rr=[]
 for t in lterms:lr.extend(interactions(t,'L'))
 for t in rterms:rr.extend(interactions(t,'R'))
 counts={'frontier_pairs':0,'literal_conflicts':0,'alpha_rescues':0,'verified_equality_rescues':0,'common_specialization_rescues':0};examples={}
 for a in lr:
  for b in rr:
   if counts['frontier_pairs']>=p['bounds']['maximum_pair_checks'] or time.monotonic()>deadline:break
   if a['side']!=b['side'] or pathshape(a['path'])!=pathshape(b['path']):continue
   shared=sorted(set(a['subst'])&set(b['subst']));conflicts=[v for v in shared if a['subst'][v]!=b['subst'][v]]
   if not conflicts:continue
   counts['frontier_pairs']+=1;counts['literal_conflicts']+=1
   alpha=all(canon(m,a['subst'][v])==canon(m,b['subst'][v]) for v in conflicts);eq=all(veq(a['subst'][v],b['subst'][v]) for v in conflicts);spec=unify_all([(a['subst'][v],b['subst'][v]) for v in conflicts]) is not None
   if alpha:counts['alpha_rescues']+=1;examples.setdefault('alpha',{'shared':shared,'conflicts':conflicts})
   if eq:counts['verified_equality_rescues']+=1;examples.setdefault('verified_equality',{'shared':shared,'conflicts':conflicts})
   if spec:counts['common_specialization_rescues']+=1;examples.setdefault('common_specialization',{'shared':shared,'conflicts':conflicts})
  if counts['frontier_pairs']>=p['bounds']['maximum_pair_checks'] or time.monotonic()>deadline:break
 positive=[k for k in ('alpha_rescues','verified_equality_rescues','common_specialization_rescues') if counts[k]>0]
 if not positive:decision='LITERAL_CONFLICT_ONLY'
 elif len(positive)>1:decision='MIXED_QUOTIENT_RESCUE'
 elif positive[0]=='alpha_rescues':decision='ALPHA_QUOTIENT_RESCUE'
 elif positive[0]=='verified_equality_rescues':decision='VERIFIED_EQUALITY_QUOTIENT_RESCUE'
 else:decision='COMMON_SPECIALIZATION_RESCUE'
 out={'schema':'mathgraph.normal0040-substitution-quotient-rival.v1','id':RID,'protocol':p,'frozen':{'distance':d,'generation1_classes':{'L':len(classes['L']),'R':len(classes['R'])},'tested_class_pair':[0,0]},'counts':counts,'examples':examples,'decision':decision,'timed_out':time.monotonic()>deadline}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
