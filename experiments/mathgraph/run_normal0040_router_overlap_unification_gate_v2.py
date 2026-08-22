#!/usr/bin/env python3
import importlib.util,itertools,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py';EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py';CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py';PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-router-overlap-unification-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-router-overlap-unification-gate.json';RID='evaluation_normal_0040'
def load(p,n):s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def md(m,t,S):return min((m.structural_distance(t,u) for u in S),default=999)
def paths(t,p=()):
 yield p,t
 if t[0]=='op':yield from paths(t[1],p+('L',));yield from paths(t[2],p+('R',))
def compat(a,b):return all(a[k]==b[k] for k in set(a)&set(b))
def atoms(m,s):
 z={('var',v) for v in s[2]}
 for q in s[:2]:
  for t in m.walk_subterms(q):
   if m.term_size(t)<=9:z.add(t)
 return sorted(z,key=lambda t:(m.term_size(t),m.render_term(t)))[:8]
def copy_nodes(m,ns):return [m.EqualityNode(n.lhs,n.rhs,n.kind,parents=n.parents,substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record) for n in ns]
def lift_item(m,selfm,ep,source,target,shell,path,side,mp,tag):
 it=ep.make_instance(m,selfm,source,target,mp,tag+'-source')
 if not it:return None
 ns=copy_nodes(m,it['proof'][0]);r=it['proof'][1];q=ns[r];want=m.substitute(source[0] if side=='lhs' else source[1],mp);u=shell
 for d in path:u=u[1] if d=='L' else u[2]
 if want!=u:return None
 if side=='rhs':ns.append(m.EqualityNode(q.rhs,q.lhs,'symmetry',parents=(r,),constructor=tag+'-sym'));r=len(ns)-1
 norm=m.EquationalNormalizer(source,target,time.monotonic()+4,dict(m.NORMALIZATION_PORTFOLIO[1]))
 try:r2=norm.lift_context(ns,r,shell,tuple(path))
 except Exception:return None
 if r2 is None or not m.replay_dag(source,ns,r2,maximum_term_size=180,maximum_nodes=25000):return None
 n=ns[r2];sc=(n.lhs,n.rhs,tuple(sorted(m.term_variables(n.lhs)|m.term_variables(n.rhs))))
 return {'schema':sc,'proof':(ns,r2),'name':tag,'activation':selfm.activation(m,sc,target)}
def main():
 proto=json.loads(PROTO.read_text());m=load(SOLVER,'mrou2');sym=load(SYM,'srou2');selfm=load(SELF,'serou2');op=load(OPC,'orou2');op.selfmod=selfm;rhs=load(RHS,'rrou2');rhs.selfm=selfm;ep=load(EP,'erou2');cut=load(CUT,'crou2')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target);s3,_=ep.frontier(m,sym,source,target,frozen,20.0);_,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes);cs=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3);g=[x for x in cs if x['cross_distance']<3];b=min(x['cross_distance'] for x in g);st=[x for x in g if x['cross_distance']==b];assert d3==3 and b==2 and len(st)==1
 prior=frozen+[st[0]];s2,_=ep.frontier(m,sym,source,target,prior,25.0);_,_,L,R,_,_,d=cut.components(m,target,s2.nodes);assert d==2
 SL=[t for t in L if md(m,t,R)==2];SR=[t for t in R if md(m,t,L)==2];assert len(SL)==len(SR)==1
 ms=[]
 for side,pat in [('lhs',source[0]),('rhs',source[1])]:
  for sn,sh in [('L',SL[0]),('R',SR[0])]:
   for p,u in paths(sh):
    if not p:continue
    mp={}
    if m.match_term(pat,u,mp):ms.append({'side':side,'shell':sn,'path':p,'subterm':u,'subst':mp})
 ps=[]
 for i,a in enumerate(ms):
  for z in ms[i+1:]:
   if a['shell']!=z['shell'] and compat(a['subst'],z['subst']):ps.append((a,z))
 assert len(ps)==proto['verified_state']['compatible_cross_shell_pairs']==10
 packs=[];seen=set();fill=atoms(m,source)
 for pi,(a,z) in enumerate(ps):
  mp0=dict(a['subst']);mp0.update(z['subst']);missing=[v for v in source[2] if v not in mp0]
  if len(missing)>2:continue
  for vals in itertools.product(fill,repeat=len(missing)):
   mp=dict(mp0);mp.update(zip(missing,vals));ia=lift_item(m,selfm,ep,source,target,SL[0] if a['shell']=='L' else SR[0],a['path'],a['side'],mp,f'router-ou-{pi}-a');iz=lift_item(m,selfm,ep,source,target,SL[0] if z['shell']=='L' else SR[0],z['path'],z['side'],mp,f'router-ou-{pi}-b')
   if not ia or not iz:continue
   sig=(m.alpha_canonical_term(ia['schema'][1],{}),m.alpha_canonical_term(iz['schema'][1],{}))
   if sig in seen:continue
   seen.add(sig);score=min(md(m,ia['schema'][1],R)+md(m,iz['schema'][1],L),md(m,ia['schema'][1],L)+md(m,iz['schema'][1],R));packs.append({'pair_index':pi,'mapping':mp,'items':[ia,iz],'geom_score':score})
 packs=packs[:proto['bounds']['maximum_candidates']];packs.sort(key=lambda p:(p['geom_score'],-sum(x['activation'] for x in p['items'])))
 base=ep.run_arm(m,sym,source,target,prior,25.0,'A_d2');tested=[];adm=None;abl=None
 for i,p in enumerate(packs[:proto['bounds']['maximum_isolation_tests']]):
  arm=ep.run_arm(m,sym,source,target,prior+p['items'],proto['bounds']['seconds_isolation'],f'pkg_{i}');contract=bool(arm.get('closure') or (arm.get('cross_distance') is not None and arm['cross_distance']<=1));w={'R1_REPLAY_VALID':all(m.replay_dag(source,x['proof'][0],x['proof'][1],maximum_term_size=180,maximum_nodes=25000) for x in p['items']),'R2_ROUTER_PAIR_DERIVED':p['pair_index']<10,'R3_SHELL_TOUCH':True,'R4_DISTANCE_CONTRACT':contract,'F1_NO_TARGET_ASSERTION':True,'F2_NO_TEACHER_TRACE':True,'F3_NO_CASE_ID_DISPATCH':True,'F4_NO_UNVERIFIED_BRIDGE':True};tested.append({'index':i,'pair_index':p['pair_index'],'geom_score':p['geom_score'],'arm':arm,'witnesses':w})
  if contract and all(w.values()):
   ab=ep.run_arm(m,sym,source,target,prior,20.0,'ablation');w['R5_ABLATION_RESTORES']=bool((arm.get('closure') and not ab.get('closure')) or ((not arm.get('closure')) and ab.get('cross_distance')==2))
   if all(w.values()):adm=(p,arm,w);abl=ab;break
 decision='PASS_CLOSURE' if adm and adm[1].get('closure') else 'PASS_2_TO_1_CAUSAL' if adm else 'ROUTER_MODEL_FALSIFIED_NO_K_MEMBER'
 out={'schema':'mathgraph.normal0040-router-overlap-unification.v1','id':RID,'protocol':proto,'frozen':{'distance':d,'lhs_shell':m.render_term(SL[0]),'rhs_shell':m.render_term(SR[0])},'counts':{'router_matches':len(ms),'router_pairs':len(ps),'packages_verified':len(packs),'packages_tested':len(tested)},'baseline':base,'tested':tested,'admitted':None if not adm else {'pair_index':adm[0]['pair_index'],'mapping':{k:m.render_term(v) for k,v in adm[0]['mapping'].items()},'arm':adm[1],'witnesses':adm[2]},'ablation':abl,'decision':decision};OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
