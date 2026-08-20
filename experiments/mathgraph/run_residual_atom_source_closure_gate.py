#!/usr/bin/env python3
"""Residual-induced source-instance closure over target-derived structural atoms.

The post-development boundary audit shows the closest lhs/rhs component pairs
differ by exactly the unresolved x <-> target-RHS relation, even when nested in
shared contexts. Direct source instances, congruence closure, and one contextual
source rewrite cannot cross the cut. This gate therefore changes the *proposal
language*: instead of requiring a new source instance endpoint to already lie
in either component, enumerate simultaneous source-law substitutions over the
finite atom basis exposed by the residual/target structure, add those verified
source instances as possible intermediate edges, and ask whether their closure
connects the two target components.

Every added edge is an ordinary instance of the original source equation and
the final path must replay. No external proof body or new trusted inference rule
is used.
"""
import importlib.util,itertools,json,sys
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py';CC=ROOT/'experiments/mathgraph/run_residual_cut_congruence_completion_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-atom-source-closure-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def atoms(m,r,target,limit_size=11):
 raw=[];seen=set()
 for side in target[:2]:
  for u in m.walk_subterms(side):
   if m.term_size(u)>limit_size:continue
   k=r.canon(m,u)
   if k not in seen:seen.add(k);raw.append(u)
 raw.sort(key=lambda t:(m.term_size(t),m.render_term(t)))
 return raw

def main():
 m=load(SOLVER,'mg_atom');sym=load(SYM,'sym_atom');selfm=load(SELF,'self_atom');op=load(OPC,'op_atom');r=load(REIFY,'reify_atom');cc=load(CC,'cc_atom');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 state=cc.build_state(m,sym,selfm,op,r,source,target);s,_,_=r.frontier(m,sym,source,target,state,20.0)
 nodes=list(s.nodes);uf,adj,terms=cc.graph(m,r,nodes);lr=uf.find(r.canon(m,target[0]));rr=uf.find(r.canon(m,target[1]))
 basis=atoms(m,r,target);vars_=source[2];existing={(r.canon(m,n.lhs),r.canon(m,n.rhs)) for n in nodes};added=0
 for vals in itertools.product(basis,repeat=len(vars_)):
  env=dict(zip(vars_,vals));il=m.substitute(source[0],env);ir=m.substitute(source[1],env)
  if max(m.term_size(il),m.term_size(ir))>100:continue
  for rev,a,b in ((False,il,ir),(True,ir,il)):
   key=(r.canon(m,a),r.canon(m,b))
   if key in existing:continue
   existing.add(key)
   nodes.append(m.EqualityNode(a,b,'source instance',substitution=tuple((v,env[v]) for v in vars_),orientation=rev,constructor='residual-atom-source-closure'));eid=len(nodes)-1;added+=1
   ka,kb=key;terms.setdefault(ka,a);terms.setdefault(kb,b);adj.setdefault(ka,[]).append((kb,eid,False));adj.setdefault(kb,[]).append((ka,eid,True));uf.union(ka,kb)
 connected=uf.find(r.canon(m,target[0]))==uf.find(r.canon(m,target[1]));proof_ok=False;cert_bytes=None;proof_nodes=None
 if connected:
  root=cc.prove_path(m,nodes,adj,r,target[0],target[1],'residual-atom-source-closure')
  if root is not None:
   proof_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=220,maximum_nodes=200000))
   if proof_ok:
    code,proof_nodes=m.make_dag_certificate(target,nodes,root);cert_bytes=len(code.encode())
 out={'schema':'mathgraph.residual-atom-source-closure.v1','id':RID,'protocol':{'atom_basis_only_from_target_residual_structure':True,'all_new_edges_are_original_source_instances':True,'no_external_proof_trace':True,'no_answer_body':True,'final_path_replay_required':True},'basis':[m.render_term(x) for x in basis],'counts':{'basis':len(basis),'source_instance_edges_added':added,'initial_nodes':len(s.nodes),'augmented_nodes':len(nodes)},'connected':connected,'proof_replay':proof_ok,'certificate_bytes':cert_bytes,'proof_nodes':proof_nodes,'decision':'PASS' if proof_ok else ('CONNECTED_REPLAY_FAILED' if connected else 'NO_CLOSURE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
