#!/usr/bin/env python3
"""Semantic JOIN gate for O5-0014: combine two independently exposed residual constraints.

Constraint A (multisub): residual missing motifs require simultaneous substitution
of multiple non-endpoint source variables.  This creates the right structure but
leaves activation zero.
Constraint B (endpoint promotion): a useful consequence must become addressable
from the live target cut by promoting the distinguished bare source endpoint.

D JOIN = retain each replay-verified residual multisub mapping, but additionally
map the bare source endpoint variable to one target side.  Every candidate remains
a direct source-law instance.  Controls isolate each constituent constraint.
"""
import importlib.util,itertools,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py';MS=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
OUT=ROOT/'experiments/mathgraph/results/0014-semantic-join-endpoint-multisub-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def canon(m,t):return m.alpha_canonical_term(t,{})
def eqkey(m,a,b):return min((canon(m,a),canon(m,b)),(canon(m,b),canon(m,a)))
def endpoint_vars(source):
 return [s[1] for s in source[:2] if s[0]=='var']
def make(m,source,target,mp,tag):
 if any(v not in mp for v in source[2]):return None
 a=m.substitute(source[0],mp);b=m.substitute(source[1],mp)
 if max(m.term_size(a),m.term_size(b))>180:return None
 node=m.EqualityNode(a,b,'source instance',substitution=tuple((v,mp[v]) for v in source[2]),orientation=False,constructor=tag)
 if not m.replay_dag(source,[node],0,maximum_term_size=220,maximum_nodes=8):return None
 s=(a,b,tuple(sorted(m.term_variables(a)|m.term_variables(b))))
 return {'schema':s,'proof':([node],0),'name':tag,'activation':selfm.activation(m,s,target),'mapping':mp}
def source_atoms(m,source):
 vals={('var',v) for v in source[2]}
 for side in source[:2]:
  for t in m.walk_subterms(side):
   if m.term_size(t)<=9:vals.add(t)
 return sorted(vals,key=lambda t:(m.term_size(t),m.render_term(t)))[:8]
def endpoint_only(m,source,target,ep,special,limit=96):
 others=[v for v in source[2] if v!=ep];atoms=source_atoms(m,source);out=[];seen=set()
 for vals in itertools.product(atoms[:6],repeat=len(others)):
  mp={ep:special};mp.update(zip(others,vals));x=make(m,source,target,mp,'endpoint-only-control')
  if not x:continue
  k=eqkey(m,*x['schema'][:2])
  if k in seen:continue
  seen.add(k);out.append(x)
  if len(out)>=limit:break
 return out
def metrics(m,target,s):
 keys={canon(m,target[0]):'L',canon(m,target[1]):'R'};parent={};terms={}
 def find(x):
  parent.setdefault(x,x)
  if parent[x]!=x:parent[x]=find(parent[x])
  return parent[x]
 def union(a,b):
  a=find(a);b=find(b)
  if a!=b:parent[b]=a
 for n in s.nodes:
  a=canon(m,n.lhs);b=canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;union(a,b)
 lp=canon(m,target[0]) in terms;rp=canon(m,target[1]) in terms;joined=lp and rp and find(canon(m,target[0]))==find(canon(m,target[1]));cross=None;ls=rs=0
 if lp:
  lr=find(canon(m,target[0]));L=[t for k,t in terms.items() if find(k)==lr];ls=len(L)
 else:L=[]
 if rp:
  rr=find(canon(m,target[1]));R=[t for k,t in terms.items() if find(k)==rr];rs=len(R)
 else:R=[]
 if L and R and not joined:
  L=sorted(L,key=m.term_size)[:180];R=sorted(R,key=m.term_size)[:180];cross=min(m.structural_distance(a,b) for a in L for b in R)
 return {'lhs_endpoint':lp,'rhs_endpoint':rp,'lhs_component_size':ls,'rhs_component_size':rs,'joined':bool(joined),'cross_distance':cross}
def run(m,sym,source,target,items,seconds,tag):
 started=time.monotonic();Norm=sym.make_normalizer(m);cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=seconds,candidate_equalities=9000,overlap_candidates=8500,selected_rules=1200,replayed_rules=5000,maximum_term_size=130,maximum_proof_nodes=150000);s=Norm(source,target,started+seconds,cfg)
 for it in items:
  ns,r=it['proof'];off=len(s.nodes)
  for n in ns:s.nodes.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 found=s.solve();ok=False;cert=None
 if found:
  ns,r=found;ok=bool(m.replay_dag(source,ns,r,maximum_term_size=180,maximum_nodes=180000));
  if ok:cert=len(m.make_dag_certificate(target,ns,r)[0].encode())
 d={'closure':ok,'installed':len(items),'rules':len(s.rules),'nodes':len(s.nodes),'overlaps':s.overlap_candidates,'certificate_bytes':cert,'tag':tag};d.update(metrics(m,target,s));return d
def main():
 global selfm
 m=load(SOLVER,'mg_join0014');sym=load(SYM,'sym_join0014');selfm=load(SELF,'self_join0014');op=load(OPC,'op_join0014');op.selfmod=selfm;miss=load(MISS,'miss_join0014');ms=load(MS,'ms_join0014');ms.selfmod=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 eps=endpoint_vars(source)
 if not eps:raise SystemExit('no bare endpoint variable in source')
 ep=eps[0]
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfm.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));base=g1[:32]+g2[:128]
 _,_,fterms=miss.frontier(m,sym,source,target,base,10.0);missing=miss.target_missing(m,target,fterms);multi=ms.synthesize(m,source,target,missing)
 # Recover the exact verified substitutions underlying each multisub source instance.
 mappings=[]
 for it in multi:
  node=it['proof'][0][it['proof'][1]];mp=dict(node.substitution or ())
  if mp and all(v in mp for v in source[2]):mappings.append(mp)
 join=[];near=[];seen=set();jseen=set()
 # A structural near-miss endpoint is the closest reachable endpoint-sized term, excluding target sides.
 reachable=[];tkeys={canon(m,target[0]),canon(m,target[1])}
 for t in fterms.values():
  if canon(m,t) not in tkeys:reachable.append(t)
 for base_mp in mappings:
  for side in target[:2]:
   mp=dict(base_mp);mp[ep]=side;x=make(m,source,target,mp,'semantic-join-endpoint-multisub')
   if x:
    k=eqkey(m,*x['schema'][:2]);
    if k not in jseen:jseen.add(k);join.append(x)
  if reachable:
   q=min(reachable,key=lambda t:min(m.structural_distance(t,target[0]),m.structural_distance(t,target[1])))
   mp=dict(base_mp);mp[ep]=q;x=make(m,source,target,mp,'joined-nearmiss-endpoint-control')
   if x:
    k=eqkey(m,*x['schema'][:2]);
    if k not in seen:seen.add(k);near.append(x)
 # Endpoint-only control gets same endpoint intervention without residual y/z mapping.
 eonly=[]
 for side in target[:2]:eonly.extend(endpoint_only(m,source,target,ep,side,48))
 join.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));near.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));eonly.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 common=g1[:24]+g2[:56]
 A=run(m,sym,source,target,base,25,'A_frozen')
 B=run(m,sym,source,target,common+multi[:32],25,'B_multisub_structure_only')
 C=run(m,sym,source,target,common+eonly[:max(8,len(join))],25,'C_endpoint_only') if eonly else {'closure':False,'tag':'C_endpoint_only','error':'no_candidates'}
 D=run(m,sym,source,target,common+join[:64],35,'D_semantic_join') if join else {'closure':False,'tag':'D_semantic_join','error':'no_candidates'}
 N=run(m,sym,source,target,common+near[:64],35,'N_joined_nearmiss_control') if near else {'closure':False,'tag':'N_joined_nearmiss_control','error':'no_candidates'}
 Abl=run(m,sym,source,target,common+multi[:32],35,'D_join_ablation') if D.get('closure') else None
 strong=D.get('closure') and not A.get('closure') and not B.get('closure') and not C.get('closure') and not N.get('closure') and Abl and not Abl.get('closure')
 endpoint_gain=(D.get('lhs_endpoint') or D.get('rhs_endpoint')) and ((D.get('lhs_component_size',0)+D.get('rhs_component_size',0))>(B.get('lhs_component_size',0)+B.get('rhs_component_size',0)))
 decision='PASS_STRONG' if strong else 'JOIN_ENDPOINT_GAIN_NO_CLOSURE' if endpoint_gain and not D.get('closure') else 'JOIN_CLOSURE_NOT_UNIQUE' if D.get('closure') else 'NO_JOIN_ADVANTAGE'
 out={'schema':'mathgraph.0014-semantic-join-endpoint-multisub.v1','id':RID,'J':'combine independently derived missing-structure multisubstitution with independently validated endpoint-promotion/addressability constraint','K_rho':{'required':['simultaneous residual-derived non-endpoint substitutions','target-side equality endpoint addressability','direct replay-valid source-law instance'],'forbidden':['external proof trace','asserted target equality','unverified synthetic edge']},'endpoint_variable':ep,'counts':{'multisub':len(multi),'base_mappings':len(mappings),'join_candidates':len(join),'near_join_controls':len(near),'endpoint_only_controls':len(eonly),'join_nonzero_activation':sum(x['activation']>0 for x in join)},'arms':{'A':A,'B':B,'C':C,'N':N,'D':D,'D_ablation':Abl},'top_join':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'activation':x['activation'],'mapping':{v:m.render_term(t) for v,t in x['mapping'].items()}} for x in join[:12]],'protocol':{'two_constraints_independently_exposed_before_join':True,'same_source_law_all_arms':True,'all_join_candidates_direct_source_instances_and_replay_verified':True,'no_external_proof_trace':True},'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
