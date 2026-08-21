#!/usr/bin/env python3
"""Residual-induced bidirectional contextual rewrite closure for O5-0014.

The post-development residual is a disconnected equality cut. Direct source
instances, one contextual rewrite, ten source-instance proposal families and a
12k two-source pool all fail. This gate changes the continuation representation:
intermediate terms are no longer required to pre-exist in a finite atom pool.
Starting from BOTH verified target components, it applies either orientation of
the ORIGINAL source law at any matched subterm, lifts each step by ordinary
congruence, and grows a bounded replay-verified rewrite graph until the two
frontiers meet.

No external proof trace, answer identity or new trusted inference rule is used.
A positive must replay from the original source, close only with the discovered
bridge installed, and fail again under ablation.
"""
import importlib.util,json,sys
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py';CUT=ROOT/'experiments/mathgraph/run_post_development_component_bridge_gate.py';CC=ROOT/'experiments/mathgraph/run_residual_cut_congruence_completion_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-cut-bidirectional-context-bfs-gate.json';RID='evaluation_order5_0014'
MAX_DEPTH=4;FRONTIER_CAP=900;MAX_TERM_SIZE=130

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def paths(t,p=()):
 yield p,t
 if t[0]=='op':
  yield from paths(t[1],p+('L',));yield from paths(t[2],p+('R',))

def at(t,p):
 for d in p:t=t[1] if d=='L' else t[2]
 return t

def replace(t,p,u):
 if not p:return u
 d=p[0]
 return ('op',replace(t[1],p[1:],u),t[2]) if d=='L' else ('op',t[1],replace(t[2],p[1:],u))

def rewrite_item(m,r,cut,source,target,whole,path,rev,depth):
 # rev=False: lhs -> rhs. rev=True: rhs -> lhs.
 pat=source[1] if rev else source[0];rep=source[0] if rev else source[1]
 old=at(whole,path);env={}
 if not cut.match(pat,old,env) or any(v not in env for v in source[2]):return None
 new=m.substitute(rep,env);whole2=replace(whole,path,new)
 if max(m.term_size(whole),m.term_size(whole2))>MAX_TERM_SIZE:return None
 # Primitive source node is always source lhs = source rhs; orient with symmetry if needed.
 il=m.substitute(source[0],env);ir=m.substitute(source[1],env);tag=f'bidir-context-d{depth}'
 nodes=[m.EqualityNode(il,ir,'source instance',substitution=tuple((v,env[v]) for v in source[2]),orientation=False,constructor=tag)];root=0
 if rev:
  # desired old(rhs) -> new(lhs)
  nodes.append(m.EqualityNode(ir,il,'symmetry',parents=(root,),constructor=tag));root=1
 lhs=nodes[root].lhs;rhs=nodes[root].rhs
 for i in range(len(path)-1,-1,-1):
  anc_path=path[:i];anc=at(whole,anc_path);d=path[i]
  if d=='L':
   fixed=anc[2];L=('op',lhs,fixed);R=('op',rhs,fixed);kind='congruence on left child';ctx=('left',fixed)
  else:
   fixed=anc[1];L=('op',fixed,lhs);R=('op',fixed,rhs);kind='congruence on right child';ctx=('right',fixed)
  nodes.append(m.EqualityNode(L,R,kind,parents=(root,),context=ctx,constructor=tag));root=len(nodes)-1;lhs=L;rhs=R
 if nodes[root].lhs!=whole or nodes[root].rhs!=whole2:return None
 if not m.replay_dag(source,nodes,root,maximum_term_size=MAX_TERM_SIZE+30,maximum_nodes=256):return None
 schema=(whole,whole2,tuple(sorted(m.term_variables(whole)|m.term_variables(whole2))))
 return {'schema':schema,'proof':(nodes,root),'name':tag,'activation':0,'path':''.join(path) or 'ROOT','orientation':'rhs_to_lhs' if rev else 'lhs_to_rhs'}

def expand(m,r,cut,source,target,front,seen,depth):
 out=[];items={};matches=nonroot=0
 for whole in front:
  for p,_ in paths(whole):
   for rev in (False,True):
    it=rewrite_item(m,r,cut,source,target,whole,p,rev,depth)
    if not it:continue
    matches+=1;nonroot+=bool(p);t=it['schema'][1];k=r.canon(m,t)
    if k in seen:continue
    seen.add(k);items[k]=it;out.append(t)
 out=sorted({r.canon(m,t):t for t in out}.values(),key=lambda t:(m.term_size(t),m.render_term(t)))[:FRONTIER_CAP]
 keep={r.canon(m,t) for t in out};items={k:v for k,v in items.items() if k in keep}
 return out,items,matches,nonroot

def main():
 m=load(SOLVER,'mg_bctx');sym=load(SYM,'sym_bctx');selfm=load(SELF,'self_bctx');op=load(OPC,'op_bctx');r=load(REIFY,'reify_bctx');cut=load(CUT,'cut_bctx');cc=load(CC,'cc_bctx');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 state=cc.build_state(m,sym,selfm,op,r,source,target);s,_,_=r.frontier(m,sym,source,target,state,20.0)
 uf=cut.UF();terms={}
 for n in s.nodes:
  a=r.canon(m,n.lhs);b=r.canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 lk=r.canon(m,target[0]);rk=r.canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 L0=[terms[k] for k in terms if uf.find(k)==lr];R0=[terms[k] for k in terms if uf.find(k)==rr]
 seenL={r.canon(m,t) for t in L0};seenR={r.canon(m,t) for t in R0};frontL=L0;frontR=R0
 parentL={};parentR={};edgeL={};edgeR={};layers=[];meet=None
 for depth in range(1,MAX_DEPTH+1):
  nextL,itL,ml,nl=expand(m,r,cut,source,target,frontL,seenL,depth);nextR,itR,mr,nr=expand(m,r,cut,source,target,frontR,seenR,depth)
  for k,it in itL.items(): parentL[k]=r.canon(m,it['schema'][0]);edgeL[k]=it
  for k,it in itR.items(): parentR[k]=r.canon(m,it['schema'][0]);edgeR[k]=it
  common=(seenL & seenR)
  # Ignore terms that were already common before expansion (components are disjoint, so normally none).
  if common: meet=min(common,key=str)
  layers.append({'depth':depth,'left_frontier':len(frontL),'right_frontier':len(frontR),'left_matches':ml,'right_matches':mr,'left_nonroot':nl,'right_nonroot':nr,'left_new':len(nextL),'right_new':len(nextR),'seen_left':len(seenL),'seen_right':len(seenR),'met':bool(meet)})
  if meet:break
  frontL,nextL0=nextL,nextL;frontR,nextR0=nextR,nextR
  if not frontL and not frontR:break
 chain=[]
 if meet:
  # Walk discovered L-side path back to original component.
  k=meet;left=[]
  while k not in {r.canon(m,t) for t in L0} and k in edgeL:
   left.append(edgeL[k]);k=parentL[k]
  left=list(reversed(left))
  # Walk discovered R-side path from meet back to original R component; equalities are symmetric so installation suffices.
  k=meet;right=[]
  while k not in {r.canon(m,t) for t in R0} and k in edgeR:
   right.append(edgeR[k]);k=parentR[k]
  chain=left+right
 A=r.run_arm(m,sym,source,target,state,30.0,'A_post_development')
 C=r.run_arm(m,sym,source,target,state+chain,40.0,'C_bidirectional_context_bfs') if chain else {'closure':False,'installed':0,'error':'no_frontier_meet'}
 abl=r.run_arm(m,sym,source,target,state,40.0,'C_ablation') if C.get('closure') else None
 decision='PASS' if C.get('closure') and not A.get('closure') and abl and not abl.get('closure') else 'FRONTIERS_MET_NO_CLOSURE' if meet else 'NO_MEET_DEPTH_LE_4'
 out={'schema':'mathgraph.residual-cut-bidirectional-context-bfs.v1','id':RID,'protocol':{'post_development_cut_recomputed':True,'both_source_orientations':True,'all_subterm_positions':True,'intermediates_not_limited_to_atom_pool':True,'every_edge_replay_verified':True,'no_external_proof_trace':True,'no_answer_label':True},'components':{'lhs':len(L0),'rhs':len(R0)},'limits':{'depth':MAX_DEPTH,'frontier_cap':FRONTIER_CAP,'max_term_size':MAX_TERM_SIZE},'layers':layers,'meet':str(meet) if meet else None,'chain_length':len(chain),'arms':{'A':A,'C':C,'C_ablation':abl},'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
