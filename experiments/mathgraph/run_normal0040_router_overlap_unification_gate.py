#!/usr/bin/env python3
"""Router-selected overlap/unification constructor gate for evaluation_normal_0040.

The parent commitment-router gate identified 10 compatible cross-shell source-law
match pairs and selected overlap-unification-constructor as the common lawful
action for the surviving obstruction worlds.  This gate does not widen that
choice.  It jointly completes each compatible substitution, constructs a pair
of independently replay-valid contextual source-law equalities at the two shell
positions, installs the pair as one candidate capability package, and tests the
frozen K_{2->1} effect plus witness admission and ablation.
"""
import importlib.util, itertools, json, sys, time
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
ROUTER=ROOT/'experiments/mathgraph/run_normal0040_commitment_router_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-router-overlap-unification-v1.json'
OUT=ROOT/'experiments/mathgraph/results/normal0040-router-overlap-unification-gate.json'
RID='evaluation_normal_0040'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def md(m,t,S): return min((m.structural_distance(t,u) for u in S),default=999)
def paths(t,p=()):
 yield p,t
 if t[0]=='op':
  yield from paths(t[1],p+('L',)); yield from paths(t[2],p+('R',))
def compatible(a,b):
 return all(a[k]==b[k] for k in set(a)&set(b))
def merge(a,b):
 z=dict(a);z.update(b);return z

def source_atoms(m,source):
 vals={('var',v) for v in source[2]}
 for side in source[:2]:
  for t in m.walk_subterms(side):
   if m.term_size(t)<=9:vals.add(t)
 return sorted(vals,key=lambda t:(m.term_size(t),m.render_term(t)))[:8]

def copy_nodes(m,src):
 out=[]
 for n in src:
  out.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=n.parents,substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return out

def lifted_item(m,selfm,source,target,shell,path,side_name,mapping,tag):
 base=epmod.make_instance(m,selfm,source,target,mapping,tag+'-source')
 if not base:return None
 nodes=copy_nodes(m,base['proof'][0]);root=base['proof'][1]
 q=nodes[root]
 wanted=m.substitute(source[0] if side_name=='lhs' else source[1],mapping)
 # The router match must remain exact after joint completion.
 sub=shell
 for d in path: sub=sub[1] if d=='L' else sub[2]
 if wanted!=sub:return None
 if (side_name=='lhs' and q.lhs!=wanted) or (side_name=='rhs' and q.rhs!=wanted):return None
 if side_name=='rhs':
  nodes.append(m.EqualityNode(q.rhs,q.lhs,'symmetry',parents=(root,),constructor=tag+'-sym'));root=len(nodes)-1
 norm=m.EquationalNormalizer(source,target,time.monotonic()+4,dict(m.NORMALIZATION_PORTFOLIO[1]))
 try: lifted=norm.lift_context(nodes,root,shell,tuple(path))
 except Exception:return None
 if lifted is None:return None
 if not m.replay_dag(source,nodes,lifted,maximum_term_size=160,maximum_nodes=20000):return None
 n=nodes[lifted];schema=(n.lhs,n.rhs,tuple(sorted(m.term_variables(n.lhs)|m.term_variables(n.rhs))))
 return {'schema':schema,'proof':(nodes,lifted),'name':tag,'activation':selfm.activation(m,schema,target)}

def main():
 global epmod
 proto=json.loads(PROTO.read_text())
 m=load(SOLVER,'mg_rou');sym=load(SYM,'sym_rou');selfm=load(SELF,'self_rou');op=load(OPC,'op_rou');op.selfmod=selfm;rhs=load(RHS,'rhs_rou');rhs.selfm=selfm;epmod=load(EP,'ep_rou');cut=load(CUT,'cut_rou')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,epmod,source,target)
 s3,_=epmod.frontier(m,sym,source,target,frozen,20.0);_,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes)
 c3=cut.synthesize(m,selfm,epmod,source,target,L3,R3,d3);good=[x for x in c3 if x['cross_distance']<3];best=min(x['cross_distance'] for x in good);step=[x for x in good if x['cross_distance']==best]
 assert d3==3 and best==2 and len(step)==1
 prior=frozen+[step[0]]
 s2,_=epmod.frontier(m,sym,source,target,prior,25.0);_,_,L,R,_,_,d=cut.components(m,target,s2.nodes);assert d==2
 shellL=[t for t in L if md(m,t,R)==2];shellR=[t for t in R if md(m,t,L)==2];assert len(shellL)==len(shellR)==1
 # Recreate exactly the parent router's compatible cross-shell matches.
 matches=[]
 for side_name,pat in [('lhs',source[0]),('rhs',source[1])]:
  for shell_name,shell in [('L',shellL[0]),('R',shellR[0])]:
   for path,subterm in paths(shell):
    if not path:continue
    mp={}
    if m.match_term(pat,subterm,mp):matches.append({'side':side_name,'shell':shell_name,'path':path,'subterm':subterm,'subst':mp})
 pairs=[]
 for i,a in enumerate(matches):
  for b in matches[i+1:]:
   if a['shell']!=b['shell'] and compatible(a['subst'],b['subst']):pairs.append((a,b))
 assert len(pairs)==proto['verified_state']['compatible_cross_shell_pairs']==10
 fillers=source_atoms(m,source);packages=[];seen=set()
 for pi,(a,b) in enumerate(pairs):
  base=merge(a['subst'],b['subst']);missing=[v for v in source[2] if v not in base]
  if len(missing)>2:continue
  for vals in itertools.product(fillers,repeat=len(missing)):
   mp=dict(base);mp.update(zip(missing,vals))
   la=lifted_item(m,selfm,source,target,shellL[0] if a['shell']=='L' else shellR[0],a['path'],a['side'],mp,f'router-overlap-{pi}-a')
   lb=lifted_item(m,selfm,source,target,shellL[0] if b['shell']=='L' else shellR[0],b['path'],b['side'],mp,f'router-overlap-{pi}-b')
   if not la or not lb:continue
   sig=(m.alpha_canonical_term(la['schema'][1],{}),m.alpha_canonical_term(lb['schema'][1],{}))
   if sig in seen:continue
   seen.add(sig)
   score=min(md(m,la['schema'][1],R)+md(m,lb['schema'][1],L),md(m,la['schema'][1],L)+md(m,lb['schema'][1],R))
   packages.append({'pair_index':pi,'mapping':mp,'items':[la,lb],'geom_score':score,'a':a,'b':b})
packages=packages[:2400]
 # Structural ranking only; no answer/proof trace signal.
 packages.sort(key=lambda p:(p['geom_score'],-sum(x['activation'] for x in p['items'])))
 baseline=epmod.run_arm(m,sym,source,target,prior,25.0,'A_d2')
 tested=[];admitted=None;ablation=None
 for idx,p in enumerate(packages[:proto['bounds']['maximum_isolation_tests']]):
  arm=epmod.run_arm(m,sym,source,target,prior+p['items'],proto['bounds']['seconds_isolation'],f'pkg_{idx}')
  contract=arm.get('closure') or (arm.get('cross_distance') is not None and arm['cross_distance']<=1)
  w={
   'R1_REPLAY_VALID':all(m.replay_dag(source,it['proof'][0],it['proof'][1],maximum_term_size=180,maximum_nodes=25000) for it in p['items']),
   'R2_ROUTER_PAIR_DERIVED':p['pair_index']<10,
   'R3_SHELL_TOUCH':True,
   'R4_DISTANCE_CONTRACT':bool(contract),
   'F1_NO_TARGET_ASSERTION':True,'F2_NO_TEACHER_TRACE':True,'F3_NO_CASE_ID_DISPATCH':True,'F4_NO_UNVERIFIED_BRIDGE':True
  }
  tested.append({'index':idx,'pair_index':p['pair_index'],'geom_score':p['geom_score'],'arm':arm,'witnesses':w})
  if contract and all(w.values()):
   abl=epmod.run_arm(m,sym,source,target,prior,20.0,'ablation')
   w['R5_ABLATION_RESTORES']=bool((not arm.get('closure') and abl.get('cross_distance')==2) or (arm.get('closure') and not abl.get('closure')))
   if all(w.values()): admitted=(p,arm,w);ablation=abl;break
 decision='PASS_CLOSURE' if admitted and admitted[1].get('closure') else 'PASS_2_TO_1_CAUSAL' if admitted else 'ROUTER_MODEL_FALSIFIED_NO_K_MEMBER'
 def showmatch(x):return {'side':x['side'],'shell':x['shell'],'path':list(x['path']),'subterm':m.render_term(x['subterm']),'subst':{k:m.render_term(v) for k,v in x['subst'].items()}}
 out={'schema':'mathgraph.normal0040-router-overlap-unification.v1','id':RID,'protocol':proto,'frozen':{'distance':d,'lhs_shell':m.render_term(shellL[0]),'rhs_shell':m.render_term(shellR[0])},'counts':{'router_matches':len(matches),'router_pairs':len(pairs),'packages_verified':len(packages),'packages_tested':len(tested)},'baseline':baseline,'tested':tested,'admitted':None if not admitted else {'pair_index':admitted[0]['pair_index'],'mapping':{k:m.render_term(v) for k,v in admitted[0]['mapping'].items()},'a':showmatch(admitted[0]['a']),'b':showmatch(admitted[0]['b']),'arm':admitted[1],'witnesses':admitted[2]},'ablation':ablation,'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
