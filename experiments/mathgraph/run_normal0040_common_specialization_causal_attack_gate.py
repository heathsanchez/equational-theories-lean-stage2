#!/usr/bin/env python3
import importlib.util,itertools,json,sys,time
from collections import defaultdict
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py';EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py';CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py';ROU=ROOT/'experiments/mathgraph/run_normal0040_router_overlap_unification_gate.py';QR=ROOT/'experiments/mathgraph/run_normal0040_substitution_quotient_rival_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-common-specialization-causal-attack-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-common-specialization-causal-attack-gate.json';RID='evaluation_normal_0040'
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
def apply_theta(m,t,theta):
 if not theta:return t
 if t[0]=='var':
  if t[1] not in theta:return t
  u=theta[t[1]]
  if u==t:return t
  return apply_theta(m,u,theta)
 if t[0]=='op':return ('op',apply_theta(m,t[1],theta),apply_theta(m,t[2],theta))
 return t
def main():
 p=json.loads(PROTO.read_text());m=load(SOLVER,'mgca');sym=load(SYM,'symca');selfm=load(SELF,'selfca');op=load(OPC,'opca');op.selfmod=selfm;rhs=load(RHS,'rhsca');rhs.selfm=selfm;ep=load(EP,'epca');cut=load(CUT,'cutca');rou=load(ROU,'rouca');rou.epmod=ep;qr=load(QR,'qrca')
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
     full=dict(mp);full.update(zip(missing,vals));it=rou.lifted_item(m,selfm,source,target,term,path,side_name,full,'ca-probe')
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
 assert len(classes['L'])==5 and len(classes['R'])==5,(len(classes['L']),len(classes['R']))
 candidates=[];cell_counts=defaultdict(int);pair_checks=defaultdict(int)
 for i,(_,A) in enumerate(classes['L']):
  for j,(_,B) in enumerate(classes['R']):
   for ta in A[:p['bounds']['maximum_terms_per_class']]:
    for tb in B[:p['bounds']['maximum_terms_per_class']]:
     for a in interactions(ta,'L'):
      for b in interactions(tb,'R'):
       if cell_counts[(i,j)]>=p['bounds']['maximum_candidates_per_cell']:break
       pair_checks[(i,j)]+=1
       if pair_checks[(i,j)]>p['bounds']['maximum_pair_checks_per_cell']:break
       if a['side']!=b['side'] or pathshape(a['path'])!=pathshape(b['path']):continue
       shared=sorted(set(a['subst'])&set(b['subst']));conf=[v for v in shared if a['subst'][v]!=b['subst'][v]]
       if not conf:continue
       theta=qr.unify_all([(a['subst'][v],b['subst'][v]) for v in conf])
       if theta is None:continue
       sa={v:apply_theta(m,t,theta) for v,t in a['subst'].items()};sb={v:apply_theta(m,t,theta) for v,t in b['subst'].items()}
       if any(sa[v]!=sb[v] for v in set(sa)&set(sb)):continue
       la=rou.lifted_item(m,selfm,source,target,ta,a['path'],a['side'],sa,f'ca-{i}-{j}-L')
       lb=rou.lifted_item(m,selfm,source,target,tb,b['path'],b['side'],sb,f'ca-{i}-{j}-R')
       if not la or not lb:continue
       rv=all(m.replay_dag(source,it['proof'][0],it['proof'][1],maximum_term_size=190,maximum_nodes=30000) for it in (la,lb))
       if not rv:continue
       candidates.append({'cell':[i,j],'theta':theta,'a':a,'b':b,'items':[la,lb],'ta':ta,'tb':tb});cell_counts[(i,j)]+=1
      if cell_counts[(i,j)]>=p['bounds']['maximum_candidates_per_cell'] or pair_checks[(i,j)]>p['bounds']['maximum_pair_checks_per_cell']:break
     if cell_counts[(i,j)]>=p['bounds']['maximum_candidates_per_cell'] or pair_checks[(i,j)]>p['bounds']['maximum_pair_checks_per_cell']:break
    if cell_counts[(i,j)]>=p['bounds']['maximum_candidates_per_cell'] or pair_checks[(i,j)]>p['bounds']['maximum_pair_checks_per_cell']:break
 baseline=ep.run_arm(m,sym,source,target,prior,20.0,'ca-baseline');tested=[];admitted=None;ablation=None
 for idx,c in enumerate(candidates[:p['bounds']['maximum_isolation_tests']]):
  arm=ep.run_arm(m,sym,source,target,prior+c['items'],p['bounds']['seconds_isolation'],f'ca-{idx}')
  contract=bool(arm.get('closure') or (arm.get('cross_distance') is not None and arm['cross_distance']<=1))
  row={'index':idx,'cell':c['cell'],'cross_distance':arm.get('cross_distance'),'closure':bool(arm.get('closure')),'contract':contract}
  tested.append(row)
  if contract:
   abl=ep.run_arm(m,sym,source,target,prior,p['bounds']['seconds_ablation'],'ca-ablation')
   restored=bool((arm.get('closure') and not abl.get('closure')) or ((not arm.get('closure')) and abl.get('cross_distance')==2))
   row['ablation_restores']=restored
   if restored:admitted=(c,arm);ablation=abl;break
 if admitted and admitted[1].get('closure'):decision='PASS_CLOSURE'
 elif admitted:decision='PASS_2_TO_1_CAUSAL'
 elif candidates:decision='REPRESENTATION_RESCUE_NO_CAUSAL_ATTACHMENT'
 else:decision='NO_REPLAYABLE_SPECIALIZATION'
 def rtheta(th):return {k:m.render_term(v) for k,v in th.items()}
 out={'schema':'mathgraph.normal0040-common-specialization-causal-attack.v1','id':RID,'protocol':p,'frozen':{'distance':d,'classes':{'L':len(classes['L']),'R':len(classes['R'])},'front_terms':{'L':len(fronts['L']),'R':len(fronts['R'])}},'counts':{'replayable_candidates':len(candidates),'cells_with_replayable_candidates':len(cell_counts),'tested':len(tested)},'baseline':baseline,'tested':tested,'admitted':None if not admitted else {'cell':admitted[0]['cell'],'theta':rtheta(admitted[0]['theta']),'arm':admitted[1]},'ablation':ablation,'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
