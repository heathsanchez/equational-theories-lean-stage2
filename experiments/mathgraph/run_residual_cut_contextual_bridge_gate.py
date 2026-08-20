#!/usr/bin/env python3
"""Residual-cut contextual source-instance bridge.

After direct source-instance and congruence-completion cuts both fail, test the
next strictly stronger trusted constructor: an ORIGINAL source-law instance
applied at a non-root context position.  Candidate generation is conditioned
only on the recomputed lhs/rhs equality-component cut.  A candidate is admitted
iff replacing a matched source RHS occurrence inside a term from one target
component lands exactly in the opposite target component.  The proof is built
from a replay-verified source instance plus ordinary congruence along the
context path, symmetry/transitivity for component paths, and must replay fully.
"""
import importlib.util,json,sys
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py';CC=ROOT/'experiments/mathgraph/run_residual_cut_congruence_completion_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-cut-contextual-bridge-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def positions(t,path=()):
 yield path,t
 if t[0]=='op':
  yield from positions(t[1],path+('L',));yield from positions(t[2],path+('R',))

def ancestors(term,path):
 cur=term;out=[]
 for d in path:
  if cur[0]!='op':return None
  if d=='L':out.append(('L',cur[2]));cur=cur[1]
  else:out.append(('R',cur[1]));cur=cur[2]
 return out

def lift(m,nodes,whole,path,proof,tag):
 anc=ancestors(whole,path)
 if anc is None:return None
 root=proof
 for d,sib in reversed(anc):
  p=nodes[root]
  if d=='L':
   lhs=('op',p.lhs,sib);rhs=('op',p.rhs,sib);kind='congruence on left child';ctx=('left',sib)
  else:
   lhs=('op',sib,p.lhs);rhs=('op',sib,p.rhs);kind='congruence on right child';ctx=('right',sib)
  nodes.append(m.EqualityNode(lhs,rhs,kind,parents=(root,),context=ctx,constructor=tag));root=len(nodes)-1
 return root

def main():
 m=load(SOLVER,'mg_ctxcut');sym=load(SYM,'sym_ctxcut');selfm=load(SELF,'self_ctxcut');op=load(OPC,'op_ctxcut');r=load(REIFY,'reify_ctxcut');cc=load(CC,'cc_ctxcut');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 state=cc.build_state(m,sym,selfm,op,r,source,target);s,_,_=r.frontier(m,sym,source,target,state,20.0);uf,adj,terms=cc.graph(m,r,s.nodes)
 lk=r.canon(m,target[0]);rk=r.canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 comps=[('L2R',lr,rr),('R2L',rr,lr)];hits=[]
 # Match the structured source side, which binds all source variables.
 pattern=source[1];vars_=source[2]
 for direction,srcroot,dstroot in comps:
  for k,A in list(terms.items()):
   if uf.find(k)!=srcroot:continue
   for path,u in positions(A):
    env={}
    if not m.match_term(pattern,u,env) or any(v not in env for v in vars_):continue
    replacement=m.substitute(source[0],env)
    B=m.replace_subterm(A,path,replacement)
    kb=r.canon(m,B)
    if kb not in terms or uf.find(kb)!=dstroot:continue
    hits.append((direction,A,B,path,env));break
   if hits:break
  if hits:break
 proof_ok=False;cert_bytes=None;proof_nodes=None;witness=None
 if hits:
  direction,A,B,path,env=hits[0];nodes=list(s.nodes);tag='residual-cut-contextual-bridge'
  # source instance is lhs -> rhs; contextual replacement needs rhs -> lhs.
  il=m.substitute(source[0],env);ir=m.substitute(source[1],env)
  nodes.append(m.EqualityNode(il,ir,'source instance',substitution=tuple((v,env[v]) for v in vars_),orientation=False,constructor=tag));si=len(nodes)-1
  nodes.append(m.EqualityNode(ir,il,'symmetry',parents=(si,),constructor=tag));rev=len(nodes)-1
  br=lift(m,nodes,A,path,rev,tag)
  if br is not None:
   start=target[0] if direction=='L2R' else target[1];goal=target[1] if direction=='L2R' else target[0]
   p0=cc.prove_path(m,nodes,adj,r,start,A,tag);p1=cc.prove_path(m,nodes,adj,r,B,goal,tag)
   root=br
   if p0 is not None:
    nodes.append(m.EqualityNode(start,B,'transitivity',parents=(p0,br),constructor=tag));root=len(nodes)-1
   if p1 is not None:
    nodes.append(m.EqualityNode(start,goal,'transitivity',parents=(root,p1),constructor=tag));root=len(nodes)-1
   if direction=='R2L':
    nodes.append(m.EqualityNode(target[0],target[1],'symmetry',parents=(root,),constructor=tag));root=len(nodes)-1
   proof_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=220,maximum_nodes=120000))
   if proof_ok:
    code,proof_nodes=m.make_dag_certificate(target,nodes,root);cert_bytes=len(code.encode())
    witness={'direction':direction,'from_term':m.render_term(A),'to_term':m.render_term(B),'path':list(path),'matched_subterm':m.render_term(ir),'replacement':m.render_term(il),'mapping':{v:m.render_term(env[v]) for v in vars_}}
 out={'schema':'mathgraph.residual-cut-contextual-bridge.v1','id':RID,'protocol':{'post_development_cut_recomputed':True,'source_side_match_binds_all_variables':True,'only_source_instance_congruence_symmetry_transitivity':True,'no_external_proof_trace':True,'no_answer_label':True},'component_state':{'lhs_component_size':sum(1 for k in terms if uf.find(k)==lr),'rhs_component_size':sum(1 for k in terms if uf.find(k)==rr),'nodes':len(s.nodes),'rules':len(s.rules),'overlaps':s.overlap_candidates},'bridge_candidates':len(hits),'witness':witness,'proof_replay':proof_ok,'certificate_bytes':cert_bytes,'proof_nodes':proof_nodes,'decision':'PASS' if proof_ok else ('CANDIDATE_REPLAY_FAILED' if hits else 'NO_CONTEXTUAL_CUT_BRIDGE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
