#!/usr/bin/env python3
import importlib.util,itertools,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py';EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py';CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py';ROU=ROOT/'experiments/mathgraph/run_normal0040_router_overlap_unification_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-continuation-interface-depth3-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-continuation-interface-depth3-gate.json';RID='evaluation_normal_0040'
def load(p,n):s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def md(m,t,S):return min((m.structural_distance(t,u) for u in S),default=999)
def bucket(d):return 0 if d<=0 else 1 if d==1 else 2 if d==2 else 3 if d<=4 else 5
def canon(m,t):return repr(m.alpha_canonical_term(t,{}))
def subst_pattern(m,mp,vars_):
 vals=[canon(m,mp[v]) for v in vars_ if v in mp]; ids={};out=[]
 for x in vals:
  if x not in ids:ids[x]=len(ids)
  out.append(ids[x])
 return tuple(out)
def shared_nontrivial(m,t,shell):
 a={canon(m,x) for x in m.walk_subterms(t) if m.term_size(x)>=2};b={canon(m,x) for x in m.walk_subterms(shell) if m.term_size(x)>=2};return bool(a&b)
def main():
 p=json.loads(PROTO.read_text());m=load(SOLVER,'mgci');sym=load(SYM,'symci');selfm=load(SELF,'selfci');op=load(OPC,'opci');op.selfmod=selfm;rhs=load(RHS,'rhsci');rhs.selfm=selfm;ep=load(EP,'epci');cut=load(CUT,'cutci');rou=load(ROU,'rouci');rou.epmod=ep
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target);s3,_=ep.frontier(m,sym,source,target,frozen,20.0);_,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes);c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3);good=[x for x in c3 if x['cross_distance']<3];best=min(x['cross_distance'] for x in good);step=[x for x in good if x['cross_distance']==best];assert d3==3 and best==2 and len(step)==1
 prior=frozen+[step[0]];s2,_=ep.frontier(m,sym,source,target,prior,25.0);_,_,L,R,_,_,d=cut.components(m,target,s2.nodes);assert d==2
 shellL=[t for t in L if md(m,t,R)==2];shellR=[t for t in R if md(m,t,L)==2];assert len(shellL)==len(shellR)==1
 fillers=rou.source_atoms(m,source)[:6];vars_=list(source[2]);maxterms=p['bounds']['maximum_terms_per_side_per_generation'];maxedges=p['bounds']['maximum_replay_valid_edges_per_generation'];maxt=p['bounds']['maximum_term_size']
 def interactions(term,origin):
  opp=R if origin=='L' else L;oppshell=shellR[0] if origin=='L' else shellL[0];out=[];seen=set()
  for side_name,pat in [('lhs',source[0]),('rhs',source[1])]:
   for path,sub in rou.paths(term):
    mp={}
    if not m.match_term(pat,sub,mp):continue
    missing=[v for v in vars_ if v not in mp]
    if len(missing)>2:continue
    for vals in itertools.product(fillers,repeat=len(missing)):
     full=dict(mp);full.update(zip(missing,vals));it=rou.lifted_item(m,selfm,source,target,term,path,side_name,full,'ci')
     if not it:continue
     endpoint=it['schema'][1]
     if m.term_size(endpoint)>maxt:continue
     k=canon(m,endpoint)
     if k in seen:continue
     seen.add(k)
     desc=(side_name,''.join(path) if path else 'ROOT',subst_pattern(m,full,vars_),bucket(md(m,endpoint,L)),bucket(md(m,endpoint,R)),shared_nontrivial(m,endpoint,oppshell))
     out.append((endpoint,desc,it))
     if len(out)>=96:return out
  return out
 def iface(term,origin):
  return tuple(sorted({x[1] for x in interactions(term,origin)}))
 fronts={'L':[shellL[0]],'R':[shellR[0]]};seen={'L':{canon(m,shellL[0])},'R':{canon(m,shellR[0])}};iface_seen={'L':set(),'R':set()};gens=[];direct=None
 for g in range(4):
  rec={'generation':g,'sides':{},'minimum_structural_distance':None,'new_interface_classes':0,'new_terms':0,'replay_valid_edges':0}
  allterms=fronts['L']+fronts['R'];rec['minimum_structural_distance']=min((m.structural_distance(a,b) for a in fronts['L'] for b in fronts['R']),default=999)
  nextf={'L':[],'R':[]}
  if g==3:
   for o in ('L','R'):
    sigs=[iface(t,o) for t in fronts[o]];new=sum(s not in iface_seen[o] for s in sigs);rec['sides'][o]={'terms':len(fronts[o]),'interface_classes':len(set(sigs)),'new_interface_classes':new}
    iface_seen[o].update(sigs);rec['new_interface_classes']+=new
   gens.append(rec);break
  edges=0
  for o in ('L','R'):
   sigs=[];nov=0
   for t in fronts[o]:
    ints=interactions(t,o);sig=tuple(sorted({z[1] for z in ints}));sigs.append(sig)
    if sig not in iface_seen[o]:iface_seen[o].add(sig);nov+=1
    for endpoint,desc,it in ints:
     edges+=1
     if edges>maxedges:break
     if (o=='L' and md(m,endpoint,R)<=1) or (o=='R' and md(m,endpoint,L)<=1):
      if direct is None:direct={'generation':g+1,'side':o,'from':m.render_term(t),'to':m.render_term(endpoint),'descriptor':repr(desc)}
     k=canon(m,endpoint)
     if k not in seen[o] and len(nextf[o])<maxterms:seen[o].add(k);nextf[o].append(endpoint)
    if edges>maxedges:break
   rec['sides'][o]={'terms':len(fronts[o]),'interface_classes':len(set(sigs)),'new_interface_classes':nov};rec['new_interface_classes']+=nov
  rec['replay_valid_edges']=edges;rec['new_terms']=len(nextf['L'])+len(nextf['R']);gens.append(rec);fronts=nextf
  if not fronts['L'] or not fronts['R']:break
 syntax=sum(x['new_terms'] for x in gens);novel=sum(x['new_interface_classes'] for x in gens);mind=min(x['minimum_structural_distance'] for x in gens)
 if direct:decision='DIRECT_CONTRACTION'
 elif novel>2 and mind>=2:decision='INTERFACE_GROWTH_WITHOUT_GEOMETRY'
 elif syntax>=20 and novel<=2:decision='LATE_QUOTIENT_REDISCOVERY'
 elif syntax<20 and novel<=2:decision='TRUE_CONTINUATION_GRAMMAR_OBSTRUCTION'
 else:decision='INTERFACE_PRECEDES_GEOMETRY' if mind<2 else 'INTERFACE_GROWTH_WITHOUT_GEOMETRY'
 out={'schema':'mathgraph.normal0040-continuation-interface-depth3.v1','id':RID,'protocol':p,'frozen':{'distance':d,'lhs_component':len(L),'rhs_component':len(R),'lhs_shell':m.render_term(shellL[0]),'rhs_shell':m.render_term(shellR[0])},'generations':gens,'totals':{'syntactic_new_terms':syntax,'novel_interface_classes':novel,'interface_to_syntax_ratio':(novel/syntax if syntax else None),'minimum_structural_distance_seen':mind},'direct_contraction_witness':direct,'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
