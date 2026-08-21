#!/usr/bin/env python3
"""Prospective semantic JOIN gate for evaluation_normal_0040.

The hypothesis/prediction is frozen separately in
protocols/normal0040-semantic-join-v1.json before this executable gate.
No teacher trace is used here.

A: base developmental state
B: full history through RHS reification, no JOIN
C: matched wrong-JOIN using a reachable near-miss motif
D: semantic JOIN: direct source-law instances anchored in the established
   target-LHS equality region while carrying the newly reified RHS motif.
"""
import importlib.util, itertools, json, sys, time
from collections import defaultdict
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-semantic-join-v1.json'
OUT=ROOT/'experiments/mathgraph/results/normal0040-semantic-join-gate.json'
RID='evaluation_normal_0040'


def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def copy_nodes(m,src,dst,tag):
 off=len(dst)
 for n in src:
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off

def append_proof(m,dst,proof,tag='semantic-join-installed'):
 ns,r=proof;off=copy_nodes(m,ns,dst,tag);return off+r

def canon(m,t):return m.alpha_canonical_term(t,{})

def eqkey(m,a,b):
 names={};x=(m.alpha_canonical_term(a,names),m.alpha_canonical_term(b,names))
 names={};y=(m.alpha_canonical_term(b,names),m.alpha_canonical_term(a,names))
 return min(x,y)

def all_subterms(m,t):return list(m.walk_subterms(t))

class UF:
 def __init__(self):self.p={}
 def find(self,x):
  self.p.setdefault(x,x)
  if self.p[x]!=x:self.p[x]=self.find(self.p[x])
  return self.p[x]
 def union(self,a,b):
  a=self.find(a);b=self.find(b)
  if a!=b:self.p[b]=a

def graph_state(m,nodes):
 uf=UF();terms={}
 for n in nodes:
  a=canon(m,n.lhs);b=canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 return uf,terms

def frontier(m,sym,source,target,items,seconds=12.0):
 started=time.monotonic();Norm=sym.make_normalizer(m)
 cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=seconds,candidate_equalities=8000,overlap_candidates=7500,selected_rules=1100,replayed_rules=4500,maximum_term_size=110,maximum_proof_nodes=120000)
 s=Norm(source,target,started+seconds,cfg)
 for x in items:append_proof(m,s.nodes,x['proof'])
 found=s.solve();terms={}
 for n in s.nodes:
  for side in (n.lhs,n.rhs):
   terms[canon(m,side)]=side
   for u in all_subterms(m,side):terms.setdefault(canon(m,u),u)
 return s,found,terms

def source_atoms(m,source):
 vals={('var',v) for v in source[2]}
 for side in source[:2]:
  for t in all_subterms(m,side):
   if m.term_size(t)<=9:vals.add(t)
 return sorted(vals,key=lambda t:(m.term_size(t),m.render_term(t)))[:10]

def make_instance(m,source,target,mapping,tag):
 lhs=m.substitute(source[0],mapping);rhs=m.substitute(source[1],mapping)
 if max(m.term_size(lhs),m.term_size(rhs))>110:return None
 node=m.EqualityNode(lhs,rhs,'source instance',substitution=tuple((v,mapping[v]) for v in source[2]),orientation=False,constructor=tag)
 if not m.replay_dag(source,[node],0,maximum_term_size=130,maximum_nodes=8):return None
 schema=(lhs,rhs,tuple(sorted(m.term_variables(lhs)|m.term_variables(rhs))))
 return {'schema':schema,'proof':([node],0),'name':tag,'activation':selfm.activation(m,schema,target)}

def generate_reification(m,source,target,specials,tag,limit=520):
 fillers=source_atoms(m,source);raw={};out=[];vars_=source[2]
 for special in specials:
  for focus in vars_:
   others=[v for v in vars_ if v!=focus]
   for vals in itertools.product(fillers[:6],repeat=len(others)):
    mp={focus:special};mp.update(zip(others,vals));item=make_instance(m,source,target,mp,tag)
    if not item:continue
    k=eqkey(m,item['schema'][0],item['schema'][1])
    if k in raw:continue
    raw[k]=item;out.append(item)
    if len(out)>=limit:return out
 return out

def hit_count(m,item,keys):
 hits=set()
 for side in item['schema'][:2]:
  for u in all_subterms(m,side):
   k=canon(m,u)
   if k in keys:hits.add(k)
 return len(hits)

def generate_cross_region(m,source,target,anchors,motif,tag,limit=360):
 """Direct source instances combining proven-LHS anchors with a motif."""
 vars_=source[2];xvar=vars_[0];others=list(vars_[1:]);fill=source_atoms(m,source)
 raw={};out=[];mkey=canon(m,motif)
 # Put motif in each non-x slot, with remaining slots fed by small source atoms
 # and small LHS-component anchors. Source-x remains a proven LHS-region term.
 extra=[]
 for a in anchors[:10]:extra.append(a)
 pool=[];seen=set()
 for t in fill[:7]+extra:
  k=canon(m,t)
  if k not in seen:seen.add(k);pool.append(t)
 for anchor in anchors[:28]:
  for focus in others:
   rem=[v for v in others if v!=focus]
   products=itertools.product(pool[:10],repeat=len(rem)) if rem else [()]
   for vals in products:
    mp={xvar:anchor,focus:motif};mp.update(zip(rem,vals))
    item=make_instance(m,source,target,mp,tag)
    if not item:continue
    k=eqkey(m,item['schema'][0],item['schema'][1])
    if k in raw:continue
    raw[k]=item
    item['motif_hits']=hit_count(m,item,{mkey})
    item['target_distance']=min(m.structural_distance(item['schema'][0],target[1]),m.structural_distance(item['schema'][1],target[1]))
    out.append(item)
    if len(out)>=limit:return out
 return out

def rhs_missing(m,target,terms):
 out=[];seen=set();whole=canon(m,target[1])
 for u in all_subterms(m,target[1]):
  if u[0]!='op':continue
  k=canon(m,u)
  if k not in terms and k not in seen:seen.add(k);out.append(u)
 out.sort(key=lambda t:(-m.term_size(t),m.render_term(t)))
 return out,[t for t in out if canon(m,t)!=whole]

def connection_metrics(m,target,s):
 uf,terms=graph_state(m,s.nodes);lk=canon(m,target[0]);rk=canon(m,target[1])
 lp=lk in terms;rp=rk in terms
 joined=bool(lp and rp and uf.find(lk)==uf.find(rk))
 lsize=rsize=0;cross=None
 if lp:
  lr=uf.find(lk);L=[t for k,t in terms.items() if uf.find(k)==lr];lsize=len(L)
 else:L=[]
 if rp:
  rr=uf.find(rk);R=[t for k,t in terms.items() if uf.find(k)==rr];rsize=len(R)
 else:R=[]
 if L and R and not joined:
  # bounded deterministic sample: smaller terms are most informative for cut distance
  L=sorted(L,key=lambda t:(m.term_size(t),m.render_term(t)))[:160]
  R=sorted(R,key=lambda t:(m.term_size(t),m.render_term(t)))[:160]
  cross=min(m.structural_distance(a,b) for a in L for b in R)
 rhs_keys={canon(m,u) for u in all_subterms(m,target[1]) if u[0]=='op'}
 return {'lhs_present':lp,'rhs_present':rp,'joined':joined,'lhs_component_size':lsize,'rhs_component_size':rsize,'cross_distance':cross,'rhs_structured_present':sum(k in terms for k in rhs_keys),'rhs_structured_total':len(rhs_keys)}

def run_arm(m,sym,source,target,items,seconds,tag):
 s,found,_=frontier(m,sym,source,target,items,seconds);ok=False;cert=None;pn=None
 if found:
  nodes,root=found;ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=140,maximum_nodes=140000))
  if ok:code,pn=m.make_dag_certificate(target,nodes,root);cert=len(code.encode())
 out={'closure':ok,'installed':len(items),'rules':len(s.rules),'overlaps':s.overlap_candidates,'nodes':len(s.nodes),'seconds':seconds,'certificate_bytes':cert,'proof_nodes':pn,'tag':tag}
 out.update(connection_metrics(m,target,s));return out,s

def main():
 global selfm
 protocol=json.loads(PROTO.read_text())
 if not protocol.get('frozen_before_execution') or protocol.get('teacher_trace_used'):
  raise SystemExit('protocol freeze/teacher-trace invariant failed')
 m=load(SOLVER,'mg_join0040');sym=load(SYM,'sym_join0040');selfm=load(SELF,'self_join0040');op=load(OPC,'op_join0040');op.selfmod=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 # Shared G1/G2 history.
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:
   sc=p['schema'];g1.append({'schema':sc,'proof':pr,'name':'g1','activation':selfm.activation(m,sc,target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base=g1[:32]+g2[:128]
 diag,_,fterms=frontier(m,sym,source,target,base,10.0)
 missing,proper=rhs_missing(m,target,fterms);focus=proper or missing
 if not focus:raise SystemExit('expected absent RHS motif not found')
 miss_keys={canon(m,t) for t in missing}
 reachable=[t for t in fterms.values() if t[0]=='op' and canon(m,t) not in miss_keys]
 reachable.sort(key=lambda t:(min(m.structural_distance(t,q) for q in focus),abs(m.term_size(t)-m.term_size(focus[0])),m.term_size(t),m.render_term(t)))
 near=reachable[0]
 cR=generate_reification(m,source,target,focus,'join-prior-rhs-reification',520)
 cR.sort(key=lambda x:(-hit_count(m,x,miss_keys),-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 reified=g1[:24]+g2[:56]+cR[:72]
 # Freeze a developed reified world and identify established LHS-component anchors.
 _,stateB,_=frontier(m,sym,source,target,reified,12.0)
 uf,terms=graph_state(m,stateB.nodes);lk=canon(m,target[0]);lr=uf.find(lk)
 anchors=[]
 for k,t in terms.items():
  if uf.find(k)==lr and m.term_size(t)<=17:anchors.append(t)
 anchors=sorted(anchors,key=lambda t:(m.term_size(t),m.render_term(t)))
 # D uses the residual-derived motif; C substitutes the closest reachable near-miss.
 Dall=generate_cross_region(m,source,target,anchors,focus[0],'semantic-join-cross-region',360)
 Call=generate_cross_region(m,source,target,anchors,near,'wrong-join-nearmiss',360)
 Dall.sort(key=lambda x:(-x['motif_hits'],x['target_distance'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 Call.sort(key=lambda x:(-x['motif_hits'],x['target_distance'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 n=min(96,len(Dall),len(Call))
 A,_=run_arm(m,sym,source,target,base,20.0,'A_latest_base')
 B,_=run_arm(m,sym,source,target,reified,20.0,'B_full_history_no_join')
 C,_=run_arm(m,sym,source,target,reified+Call[:n],20.0,'C_wrong_join') if n else ({'closure':False,'error':'no_matched_candidates'},None)
 D,_=run_arm(m,sym,source,target,reified+Dall[:n],20.0,'D_semantic_join') if n else ({'closure':False,'error':'no_matched_candidates'},None)
 # Prospective decision exactly follows the frozen prediction.
 strong=bool(D.get('closure') and not B.get('closure') and not C.get('closure'))
 partial=False
 if not strong and not D.get('closure'):
  if D.get('joined') and not B.get('joined') and not C.get('joined'):partial=True
  else:
   dd=D.get('cross_distance');bd=B.get('cross_distance');cd=C.get('cross_distance')
   partial=dd is not None and (bd is None or dd<bd) and (cd is None or dd<cd)
 decision='PASS_STRONG' if strong else 'PASS_PARTIAL' if partial else 'FALSIFIED_NO_JOIN_ADVANTAGE'
 def show(xs,k=12):return [{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'activation':x['activation'],'motif_hits':x['motif_hits'],'target_distance':x['target_distance']} for x in xs[:k]]
 out={'schema':'mathgraph.normal0040-semantic-join-gate.v1','id':RID,'protocol_commit_claim':'JOIN frozen before execution in protocols/normal0040-semantic-join-v1.json','J':protocol['J'],'K_rho':protocol['K_rho'],'prediction':protocol['prediction'],'evidence_channels':protocol['evidence_channels'],'residual_objects':{'rhs_motif':m.render_term(focus[0]),'wrong_join_motif':m.render_term(near),'lhs_anchor_count':len(anchors)},'counts':{'D_candidates':len(Dall),'C_candidates':len(Call),'installed_per_join_arm':n},'arms':{'A':A,'B':B,'C':C,'D':D},'top_D':show(Dall),'top_C':show(Call),'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)

if __name__=='__main__':main()
