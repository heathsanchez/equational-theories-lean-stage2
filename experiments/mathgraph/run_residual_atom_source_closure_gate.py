#!/usr/bin/env python3
"""Residual-induced exact source-instance closure over target structural atoms.

The post-development boundary audit shows the closest lhs/rhs component pairs
differ by exactly the unresolved x <-> target-RHS relation, even when nested in
shared contexts. Direct source instances, congruence closure, and one contextual
source rewrite cannot cross the cut.

V2 fixes an over-aggressive alpha-canonical quotient in the first atom-closure
probe. Target variables and target subterms are now kept as exact syntactic
objects: x, y, and z are distinct atoms, and connectivity is computed over exact
term identity. We enumerate simultaneous source-law substitutions over the
finite exact target/residual atom basis, add those verified source instances as
possible intermediate equality edges, and ask whether their finite closure
connects the exact target lhs and rhs.

Every added edge is an ordinary instance of the original source equation and
the final path must replay. No external proof body or new trusted inference rule
is used.
"""
import importlib.util,itertools,json,sys
from collections import deque
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py';CC=ROOT/'experiments/mathgraph/run_residual_cut_congruence_completion_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-atom-source-closure-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

class ExactUF:
 def __init__(self):self.p={}
 def find(self,x):
  self.p.setdefault(x,x)
  if self.p[x]!=x:self.p[x]=self.find(self.p[x])
  return self.p[x]
 def union(self,a,b):
  a=self.find(a);b=self.find(b)
  if a!=b:self.p[b]=a

def atoms(m,target,limit_size=11):
 raw=[];seen=set()
 for side in target[:2]:
  for u in m.walk_subterms(side):
   if m.term_size(u)>limit_size:continue
   if u not in seen:seen.add(u);raw.append(u)
 raw.sort(key=lambda t:(m.term_size(t),m.render_term(t)))
 return raw

def exact_graph(nodes):
 uf=ExactUF();adj={}
 for i,n in enumerate(nodes):
  a,b=n.lhs,n.rhs;uf.union(a,b)
  adj.setdefault(a,[]).append((b,i,False));adj.setdefault(b,[]).append((a,i,True))
 return uf,adj

def exact_path(adj,start,goal):
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

def exact_prove_path(m,nodes,adj,start,goal,tag):
 es=exact_path(adj,start,goal)
 if es is None:return None
 if not es:
  nodes.append(m.EqualityNode(start,start,'reflexivity',constructor=tag));return len(nodes)-1
 root=None
 for eid,rev in es:
  if rev:
   p=nodes[eid];nodes.append(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(eid,),constructor=tag));pe=len(nodes)-1
  else:pe=eid
  if root is None:root=pe
  else:
   L,R=nodes[root],nodes[pe]
   if L.rhs!=R.lhs:return None
   nodes.append(m.EqualityNode(L.lhs,R.rhs,'transitivity',parents=(root,pe),constructor=tag));root=len(nodes)-1
 return root

def main():
 m=load(SOLVER,'mg_atom_v2');sym=load(SYM,'sym_atom_v2');selfm=load(SELF,'self_atom_v2');op=load(OPC,'op_atom_v2');r=load(REIFY,'reify_atom_v2');cc=load(CC,'cc_atom_v2');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 state=cc.build_state(m,sym,selfm,op,r,source,target);s,_,_=r.frontier(m,sym,source,target,state,20.0)
 nodes=list(s.nodes);uf,adj=exact_graph(nodes)
 basis=atoms(m,target);vars_=source[2];existing={(n.lhs,n.rhs) for n in nodes};added=0;substitutions=0
 for vals in itertools.product(basis,repeat=len(vars_)):
  substitutions+=1;env=dict(zip(vars_,vals));il=m.substitute(source[0],env);ir=m.substitute(source[1],env)
  if max(m.term_size(il),m.term_size(ir))>100:continue
  for rev,a,b in ((False,il,ir),(True,ir,il)):
   key=(a,b)
   if key in existing:continue
   existing.add(key)
   nodes.append(m.EqualityNode(a,b,'source instance',substitution=tuple((v,env[v]) for v in vars_),orientation=rev,constructor='residual-atom-source-closure-v2'));eid=len(nodes)-1;added+=1
   adj.setdefault(a,[]).append((b,eid,False));adj.setdefault(b,[]).append((a,eid,True));uf.union(a,b)
 connected=uf.find(target[0])==uf.find(target[1]);proof_ok=False;cert_bytes=None;proof_nodes=None
 if connected:
  root=exact_prove_path(m,nodes,adj,target[0],target[1],'residual-atom-source-closure-v2')
  if root is not None:
   proof_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=220,maximum_nodes=200000))
   if proof_ok:
    code,proof_nodes=m.make_dag_certificate(target,nodes,root);cert_bytes=len(code.encode())
 out={'schema':'mathgraph.residual-atom-source-closure.v2','id':RID,'protocol':{'atom_basis_only_from_exact_target_residual_structure':True,'exact_target_variable_identity':True,'exact_term_connectivity':True,'all_new_edges_are_original_source_instances':True,'no_external_proof_trace':True,'no_answer_body':True,'final_path_replay_required':True},'basis':[m.render_term(x) for x in basis],'counts':{'basis':len(basis),'substitutions_considered':substitutions,'source_instance_edges_added':added,'initial_nodes':len(s.nodes),'augmented_nodes':len(nodes)},'connected':connected,'proof_replay':proof_ok,'certificate_bytes':cert_bytes,'proof_nodes':proof_nodes,'decision':'PASS' if proof_ok else ('CONNECTED_REPLAY_FAILED' if connected else 'NO_CLOSURE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
