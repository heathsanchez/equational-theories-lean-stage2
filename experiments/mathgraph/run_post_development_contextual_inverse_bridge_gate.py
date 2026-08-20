#!/usr/bin/env python3
"""Fifth developmental iteration: contextual inverse transport across the post-development cut.

The previous inverse-depth gate found 36 root RHS matches but zero new
predecessors: root inversion is closed inside the target component.  This gate
changes exactly one thing.  It permits a replay-verified source instance to be
applied at a matched *subterm*, then lifts that equality to the whole term using
only trusted congruence.  Breadth, source law, target, and post-development
state stay fixed.

A positive is a contextual predecessor chain from the target component into the
x component whose every edge replays to the original source law.  Installing
that chain must close while the post-development baseline remains open and
removing the chain must restore failure.
"""
import importlib.util, json, sys
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
CUT=ROOT/'experiments/mathgraph/run_post_development_component_bridge_gate.py'
CC=ROOT/'experiments/mathgraph/run_residual_cut_congruence_completion_gate.py'
OUT=ROOT/'experiments/mathgraph/results/post-development-contextual-inverse-bridge-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def paths(t,p=()):
 yield p,t
 if t[0]=='op':
  yield from paths(t[1],p+('L',))
  yield from paths(t[2],p+('R',))

def at(t,p):
 for d in p:t=t[1] if d=='L' else t[2]
 return t

def replace(t,p,u):
 if not p:return u
 d=p[0]
 if d=='L':return ('op',replace(t[1],p[1:],u),t[2])
 return ('op',t[1],replace(t[2],p[1:],u))

def contextual_instance(m,r,cut,source,target,whole,path,depth):
 old=at(whole,path);env={}
 if not cut.match(source[1],old,env) or any(v not in env for v in source[2]):return None
 new=m.substitute(source[0],env)
 pred=replace(whole,path,new)
 if max(m.term_size(pred),m.term_size(whole))>120:return None
 # Source instance new = old.
 n0=m.EqualityNode(new,old,'source instance',substitution=tuple((v,env[v]) for v in source[2]),orientation=False,constructor=f'contextual-inverse-depth-{depth}')
 nodes=[n0];root=0;lhs=new;rhs=old
 # Lift from the matched site to the root by trusted congruence.
 for i in range(len(path)-1,-1,-1):
  anc_path=path[:i];anc=at(whole,anc_path);d=path[i]
  if d=='L':
   fixed=anc[2];L=('op',lhs,fixed);R=('op',rhs,fixed)
   nodes.append(m.EqualityNode(L,R,'congruence on left child',parents=(root,),context=('left',fixed),constructor=f'contextual-inverse-depth-{depth}'))
  else:
   fixed=anc[1];L=('op',fixed,lhs);R=('op',fixed,rhs)
   nodes.append(m.EqualityNode(L,R,'congruence on right child',parents=(root,),context=('right',fixed),constructor=f'contextual-inverse-depth-{depth}'))
  root=len(nodes)-1;lhs=L;rhs=R
 if nodes[root].lhs!=pred or nodes[root].rhs!=whole:return None
 if not m.replay_dag(source,nodes,root,maximum_term_size=140,maximum_nodes=256):return None
 schema=(pred,whole,tuple(sorted(m.term_variables(pred)|m.term_variables(whole))))
 return {'schema':schema,'proof':(nodes,root),'name':f'contextual-inverse-depth-{depth}','activation':0,'path':''.join(path) or 'ROOT'}

def main():
 m=load(SOLVER,'mg_ctxinv');sym=load(SYM,'sym_ctxinv');selfm=load(SELF,'self_ctxinv');op=load(OPC,'op_ctxinv');r=load(REIFY,'reify_ctxinv');cut=load(CUT,'cut_ctxinv');cc=load(CC,'cc_ctxinv');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 state=cc.build_state(m,sym,selfm,op,r,source,target)
 s,_,_=r.frontier(m,sym,source,target,state,20.0)
 uf=cut.UF();terms={}
 for n in s.nodes:
  a=r.canon(m,n.lhs);b=r.canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 lk=r.canon(m,target[0]);rk=r.canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 lhskeys={k for k in terms if uf.find(k)==lr};rhskeys={k for k in terms if uf.find(k)==rr}
 front=[terms[k] for k in rhskeys];seen={r.canon(m,t) for t in front}
 parents={};edge_by_key={};layers=[];hit=None
 for depth in range(1,4):
  nxt=[];matches=0;ctxmatches=0
  for whole in front:
   for p,_ in paths(whole):
    item=contextual_instance(m,r,cut,source,target,whole,p,depth)
    if not item:continue
    matches+=1
    if p:ctxmatches+=1
    pred=item['schema'][0];k=r.canon(m,pred)
    # Keep first shortest proof of each predecessor.
    if k not in edge_by_key:
     edge_by_key[k]=item;parents[k]=r.canon(m,whole)
    if k in lhskeys:
     hit=(depth,k);break
    if k not in seen:
     seen.add(k);nxt.append(pred)
   if hit:break
  # Deterministic bounded next frontier: simplest predecessors first.
  uniq={r.canon(m,t):t for t in nxt};nxt=sorted(uniq.values(),key=lambda t:(m.term_size(t),m.render_term(t)))[:600]
  layers.append({'depth':depth,'frontier':len(front),'replay_verified_matches':matches,'nonroot_context_matches':ctxmatches,'new_predecessors':len(nxt),'hit_lhs_component':bool(hit)})
  if hit:break
  front=nxt
  if not front:break
 chain=[]
 if hit:
  k=hit[1]
  while k not in rhskeys and k in parents:
   chain.append(edge_by_key[k]);k=parents[k]
  chain=list(reversed(chain))
 A=r.run_arm(m,sym,source,target,state,30.0,'A_post_development')
 C=r.run_arm(m,sym,source,target,state+chain,35.0,'C_contextual_inverse_chain') if chain else {'closure':False,'installed':0,'tag':'C_contextual_inverse_chain','error':'no_contextual_bridge_depth_le_3'}
 abl=r.run_arm(m,sym,source,target,state,35.0,'C_ablation') if C.get('closure') else None
 out={'schema':'mathgraph.post-development-contextual-inverse-bridge.v1','id':RID,
      'protocol':{'post_development_components_recomputed':True,'root_only_inverse_previously_exhausted':True,'every_context_edge_replays_to_source_via_congruence':True,'no_external_proof_trace':True,'no_answer_label':True},
      'components':{'lhs_size':len(lhskeys),'rhs_size':len(rhskeys)},'layers':layers,
      'first_bridge_depth':hit[0] if hit else None,'chain_length':len(chain),
      'chain':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'path':x['path']} for x in chain],
      'arms':{'A':A,'C':C,'C_ablation':abl}}
 out['decision']='PASS' if C.get('closure') and not A.get('closure') and abl and not abl.get('closure') else 'CHAIN_FOUND_NO_CLOSURE' if chain else 'NO_CONTEXTUAL_BRIDGE_DEPTH_LE_3'
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
