#!/usr/bin/env python3
"""Residual-cut congruence completion after developmental reification.

The post-development graph for evaluation_order5_0014 contains the target lhs
and rhs in distinct equality components even after the residual has induced
previously missing target structure.  A direct source-instance bridge does not
exist.  This gate asks a stricter residual-derived question: is the cut caused
by missing *congruence closure* between two already-established child
equalities?

We search pairs A=op(a,c) in the lhs component and B=op(b,d) in the rhs
component such that a~b and c~d are already proven in the current equality
graph.  If found, we synthesize the missing A=B edge using only existing trusted
congruence + transitivity, then compose existing graph paths from target lhs to
A and B to target rhs.  The complete proof must replay to the original source
law. No external proof trace, answer label, or new trusted inference rule is
used.
"""
import importlib.util, json, sys
from collections import deque
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-cut-congruence-completion-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

class UF:
 def __init__(self): self.p={}
 def find(self,x):
  self.p.setdefault(x,x)
  if self.p[x]!=x:self.p[x]=self.find(self.p[x])
  return self.p[x]
 def union(self,a,b):
  a=self.find(a);b=self.find(b)
  if a!=b:self.p[b]=a

def build_state(m,sym,selfm,op,r,source,target):
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:
   s=p['schema'];g1.append({'schema':s,'proof':pr,'name':'g1','activation':selfm.activation(m,s,target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base=g1[:32]+g2[:128]
 _,_,t0=r.frontier(m,sym,source,target,base,10.0)
 miss0=r.target_missing(m,target,t0); proper=r.proper_missing(m,target,miss0)
 c1=r.generate_instances(m,source,target,proper,'retained-reification',520); k0={r.canon(m,t) for t in miss0}
 for x in c1:x['missing_hits']=r.hit_count(m,x,k0)
 c1.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 state1=g1[:24]+g2[:56]+c1[:72]
 _,_,t1=r.frontier(m,sym,source,target,state1,15.0)
 miss1=r.target_missing(m,target,t1); keys=set(t1)
 fill=[q for q in miss1 if q[0]=='op' and r.canon(m,q[1]) in keys and r.canon(m,q[2]) in keys]
 c2=r.generate_instances(m,source,target,fill,'retained-tree-completion',520); k1={r.canon(m,t) for t in miss1}
 for x in c2:x['missing_hits']=r.hit_count(m,x,k1)
 c2.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 return g1[:20]+g2[:40]+c1[:48]+c2[:72]

def graph(m,r,nodes):
 uf=UF();adj={};terms={}
 for i,n in enumerate(nodes):
  a=r.canon(m,n.lhs);b=r.canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
  adj.setdefault(a,[]).append((b,i,False));adj.setdefault(b,[]).append((a,i,True))
 return uf,adj,terms

def path_edges(adj,start,goal):
 if start==goal:return []
 q=deque([start]);prev={start:None}
 while q:
  u=q.popleft()
  for v,e,rev in adj.get(u,[]):
   if v in prev:continue
   prev[v]=(u,e,rev)
   if v==goal:
    out=[];cur=v
    while prev[cur] is not None:
     pu,pe,pr=prev[cur];out.append((pe,pr));cur=pu
    return list(reversed(out))
   q.append(v)
 return None

def oriented_edge(m,nodes,e,rev,tag):
 if not rev:return e
 p=nodes[e]
 nodes.append(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(e,),constructor=tag))
 return len(nodes)-1

def prove_path(m,nodes,adj,r,start,goal,tag):
 es=path_edges(adj,r.canon(m,start),r.canon(m,goal))
 if es is None:return None
 if not es:
  nodes.append(m.EqualityNode(start,start,'reflexivity',constructor=tag));return len(nodes)-1
 root=None
 for e,rev in es:
  pe=oriented_edge(m,nodes,e,rev,tag)
  if root is None:root=pe
  else:
   L=nodes[root];R=nodes[pe]
   if L.rhs!=R.lhs:return None
   nodes.append(m.EqualityNode(L.lhs,R.rhs,'transitivity',parents=(root,pe),constructor=tag));root=len(nodes)-1
 return root

def main():
 m=load(SOLVER,'mg_cc');sym=load(SYM,'sym_cc');selfm=load(SELF,'self_cc');op=load(OPC,'op_cc');r=load(REIFY,'reify_cc');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 state=build_state(m,sym,selfm,op,r,source,target)
 s,found,_=r.frontier(m,sym,source,target,state,20.0)
 uf,adj,terms=graph(m,r,s.nodes)
 lk=r.canon(m,target[0]);rk=r.canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 left=[t for k,t in terms.items() if uf.find(k)==lr and t[0]=='op']
 right=[t for k,t in terms.items() if uf.find(k)==rr and t[0]=='op']
 candidates=[]
 for A in sorted(left,key=lambda t:(m.term_size(t),m.render_term(t))):
  for B in sorted(right,key=lambda t:(m.term_size(t),m.render_term(t))):
   if uf.find(r.canon(m,A[1]))==uf.find(r.canon(m,B[1])) and uf.find(r.canon(m,A[2]))==uf.find(r.canon(m,B[2])):
    candidates.append((A,B));break
  if candidates:break
 proof_ok=False;cert_bytes=None;proof_nodes=None;witness=None
 if candidates:
  A,B=candidates[0];nodes=list(s.nodes)
  p0=prove_path(m,nodes,adj,r,target[0],A,'residual-cut-congruence-completion')
  pL=prove_path(m,nodes,adj,r,A[1],B[1],'residual-cut-congruence-completion')
  if pL is not None:
   nodes.append(m.EqualityNode(('op',A[1],A[2]),('op',B[1],A[2]),'congruence on left child',parents=(pL,),context=('left',A[2]),constructor='residual-cut-congruence-completion'));cL=len(nodes)-1
   pR=prove_path(m,nodes,adj,r,A[2],B[2],'residual-cut-congruence-completion')
   if pR is not None:
    nodes.append(m.EqualityNode(('op',B[1],A[2]),('op',B[1],B[2]),'congruence on right child',parents=(pR,),context=('right',B[1]),constructor='residual-cut-congruence-completion'));cR=len(nodes)-1
    nodes.append(m.EqualityNode(A,B,'transitivity',parents=(cL,cR),constructor='residual-cut-congruence-completion'));bridge=len(nodes)-1
    p1=prove_path(m,nodes,adj,r,B,target[1],'residual-cut-congruence-completion')
    root=bridge
    if p0 is not None:
     nodes.append(m.EqualityNode(target[0],B,'transitivity',parents=(p0,bridge),constructor='residual-cut-congruence-completion'));root=len(nodes)-1
    if p1 is not None:
     nodes.append(m.EqualityNode(target[0] if p0 is not None else A,target[1],'transitivity',parents=(root,p1),constructor='residual-cut-congruence-completion'));root=len(nodes)-1
    proof_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=200,maximum_nodes=120000))
    if proof_ok:
     code,proof_nodes=m.make_dag_certificate(target,nodes,root);cert_bytes=len(code.encode())
     witness={'A':m.render_term(A),'B':m.render_term(B),'left_child_A':m.render_term(A[1]),'left_child_B':m.render_term(B[1]),'right_child_A':m.render_term(A[2]),'right_child_B':m.render_term(B[2])}
 out={'schema':'mathgraph.residual-cut-congruence-completion.v1','id':RID,'protocol':{'post_development_cut_recomputed':True,'only_existing_trusted_congruence_symmetry_transitivity':True,'no_external_proof_trace':True,'no_answer_label':True},'component_state':{'lhs_component_size':sum(1 for k in terms if uf.find(k)==lr),'rhs_component_size':sum(1 for k in terms if uf.find(k)==rr),'already_joined':lr==rr,'nodes':len(s.nodes),'rules':len(s.rules),'overlaps':s.overlap_candidates},'candidate_pairs':len(candidates),'witness':witness,'proof_replay':proof_ok,'certificate_bytes':cert_bytes,'proof_nodes':proof_nodes,'decision':'PASS' if proof_ok else ('CANDIDATE_REPLAY_FAILED' if candidates else 'NO_CONGRUENCE_CUT_PAIR')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
