#!/usr/bin/env python3
import importlib.util,itertools,json,sys,time
from collections import defaultdict,deque,Counter
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py';EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py';CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py';ROU=ROOT/'experiments/mathgraph/run_normal0040_router_overlap_unification_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-interface-obstruction-factorization-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-interface-obstruction-factorization-gate.json';RID='evaluation_normal_0040'
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
def inclusion_minimal(sets_):
 u=[]
 for s in sorted(set(map(tuple,sets_)),key=lambda z:(len(z),z)):
  ss=set(s)
  if not any(set(t)<ss for t in u):u.append(s)
 return u
def main():
 p=json.loads(PROTO.read_text());start=time.monotonic();deadline=start+p['bounds']['seconds_soft'];expand_deadline=start+min(205,p['bounds']['seconds_soft']-35)
 m=load(SOLVER,'mgfac');sym=load(SYM,'symfac');selfm=load(SELF,'selffac');op=load(OPC,'opfac');op.selfmod=selfm;rhs=load(RHS,'rhsfac');rhs.selfm=selfm;ep=load(EP,'epfac');cut=load(CUT,'cutfac');rou=load(ROU,'roufac');rou.epmod=ep
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target);s3,_=ep.frontier(m,sym,source,target,frozen,20.0);_,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes);c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3);good=[x for x in c3 if x['cross_distance']<3];best=min(x['cross_distance'] for x in good);step=[x for x in good if x['cross_distance']==best];assert d3==3 and best==2 and len(step)==1
 prior=frozen+[step[0]];s2,_=ep.frontier(m,sym,source,target,prior,25.0);_,_,L,R,_,_,d=cut.components(m,target,s2.nodes);assert d==2
 shellL=[t for t in L if md(m,t,R)==2];shellR=[t for t in R if md(m,t,L)==2];assert len(shellL)==len(shellR)==1
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
     full=dict(mp);full.update(zip(missing,vals));it=rou.lifted_item(m,selfm,source,target,term,path,side_name,full,'fac')
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
 exp=p['parent_evidence'];assert len(classes['L'])==exp['generation1_lhs_interface_classes'] and len(classes['R'])==exp['generation1_rhs_interface_classes']
 sig_ids={};id_sigs=[]
 def sid(sig):
  if sig not in sig_ids:sig_ids[sig]=len(id_sigs);id_sigs.append(sig)
  return sig_ids[sig]
 lhs_ids=[];members={};rhs_classes=[]
 for sig,terms in classes['L']:
  i=sid(sig);lhs_ids.append(i);members[i]=terms[:p['bounds']['maximum_terms_per_class']]
 for j,(sig,terms) in enumerate(classes['R']):rhs_classes.append((j,sig,terms[:p['bounds']['maximum_terms_per_class']]))
 edges=set();queue=deque((i,0) for i in lhs_ids);visited={i:0 for i in lhs_ids};examined=0
 while queue and examined<p['bounds']['maximum_transition_edges'] and time.monotonic()<expand_deadline:
  i,depth=queue.popleft()
  if depth>=p['bounds']['search_depth_from_generation1']:continue
  dest=defaultdict(list)
  for t in members.get(i,[]):
   for x in interactions(t,'L'):
    examined+=1;j=sid(iface(x['endpoint'],'L'));edges.add((i,j));dest[j].append(x['endpoint'])
    if examined>=p['bounds']['maximum_transition_edges'] or time.monotonic()>expand_deadline:break
   if examined>=p['bounds']['maximum_transition_edges'] or time.monotonic()>expand_deadline:break
  for j,ts in dest.items():
   members.setdefault(j,ts[:p['bounds']['maximum_terms_per_class']]);nd=depth+1
   if nd<p['bounds']['search_depth_from_generation1'] and (j not in visited or nd<visited[j]):visited[j]=nd;queue.append((j,nd))
 def records(terms,origin):
  out=[]
  for t in terms[:p['bounds']['maximum_terms_per_class']]:
   out.extend(interactions(t,origin))
  return out
 rhs_records=[(j,records(ts,'R')) for j,_,ts in rhs_classes]
 pair_rows=[];global_sets=[];freq=Counter();pair_budget=0
 for li,lterms in sorted(members.items()):
  if time.monotonic()>deadline:break
  lr=records(lterms,'L')
  for rj,rr in rhs_records:
   fails=[]
   for a in lr:
    for b in rr:
     f=[]
     if a['side']!=b['side']:f.append('same_source_side_orientation')
     if pathshape(a['path'])!=pathshape(b['path']):f.append('same_context_path_shape')
     if not rou.compatible(a['subst'],b['subst']):f.append('jointly_compatible_substitution')
     if not f:raise SystemExit('unexpected compatible pair contradicts parent matrix/transition result')
     fails.append(tuple(sorted(f)));pair_budget+=1
     if pair_budget>=250000 or time.monotonic()>deadline:break
    if pair_budget>=250000 or time.monotonic()>deadline:break
   mins=inclusion_minimal(fails) if fails else []
   for s in mins:global_sets.append(s);freq[s]+=1
   pair_rows.append({'lhs_class':li,'rhs_class':rj,'minimal_failing_sets':[list(s) for s in mins],'interaction_pairs_examined':len(fails)})
   if pair_budget>=250000 or time.monotonic()>deadline:break
  if pair_budget>=250000 or time.monotonic()>deadline:break
 gmins=inclusion_minimal(global_sets);sizes=sorted({len(s) for s in gmins})
 if not gmins:decision='NO_FACTORABLE_FRONTIER'
 elif len(gmins)==1 and len(gmins[0])==1:decision='SINGLE_OBLIGATION_FRONTIER'
 elif len(gmins)==1:decision='MULTI_OBLIGATION_FRONTIER'
 else:decision='MIXED_MINIMAL_FRONTIER'
 dominant=sorted(({'failing_set':list(s),'class_pair_frequency':freq[s]} for s in gmins),key=lambda x:(-x['class_pair_frequency'],x['failing_set']))
 out={'schema':'mathgraph.normal0040-interface-obstruction-factorization.v1','id':RID,'protocol':p,'frozen':{'distance':d,'generation1_classes':{'L':len(classes['L']),'R':len(classes['R'])}},'observed_transition_graph':{'class_count':len(id_sigs),'edge_count':len(edges),'transition_edges_examined':examined,'timed_out_expansion':time.monotonic()>expand_deadline},'factorization':{'reachable_lhs_classes_factorized':len({r['lhs_class'] for r in pair_rows}),'class_pairs_factorized':len(pair_rows),'interaction_pairs_examined':pair_budget,'global_inclusion_minimal_failing_sets':dominant,'minimum_failure_sizes':sizes,'pair_rows':pair_rows[:150]},'K_next_version_space':[x['failing_set'] for x in dominant],'decision':decision,'timed_out':time.monotonic()>deadline}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
