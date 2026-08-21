#!/usr/bin/env python3
"""Fourth developmental iteration: infer bridge depth from the post-development cut.

Starting from the target equality component after reification + tree completion,
repeatedly invert direct instances of the ORIGINAL source law.  Depth is not
preselected as an operator family: the residual determines that depth-1 has no
bridge, so we test the minimum next depths 2..4.  Every edge is a direct source
instance and replays independently.
"""
import importlib.util,json,sys
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py';CUT=ROOT/'experiments/mathgraph/run_post_development_component_bridge_gate.py'
OUT=ROOT/'experiments/mathgraph/results/post-development-inverse-bridge-depth-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def main():
 m=load(SOLVER,'mg_inv');sym=load(SYM,'sym_inv');selfm=load(SELF,'self_inv');op=load(OPC,'op_inv');r=load(REIFY,'reify_inv');cut=load(CUT,'cut_inv');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:
   s=p['schema'];g1.append({'schema':s,'proof':pr,'name':'g1','activation':selfm.activation(m,s,target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base=g1[:32]+g2[:128];_,_,t0=r.frontier(m,sym,source,target,base,10.0);miss0=r.target_missing(m,target,t0);proper=r.proper_missing(m,target,miss0)
 c1=r.generate_instances(m,source,target,proper,'retained-reification',520);k0={r.canon(m,t) for t in miss0}
 for x in c1:x['missing_hits']=r.hit_count(m,x,k0)
 c1.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 state1=g1[:24]+g2[:56]+c1[:72];_,_,t1=r.frontier(m,sym,source,target,state1,15.0);miss1=r.target_missing(m,target,t1);postkeys=set(t1)
 fill=[q for q in miss1 if q[0]=='op' and r.canon(m,q[1]) in postkeys and r.canon(m,q[2]) in postkeys]
 c2=r.generate_instances(m,source,target,fill,'retained-tree-completion',520);k1={r.canon(m,t) for t in miss1}
 for x in c2:x['missing_hits']=r.hit_count(m,x,k1)
 c2.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 state=g1[:20]+g2[:40]+c1[:48]+c2[:72]
 s,_,_=r.frontier(m,sym,source,target,state,20.0);uf=cut.UF();terms={}
 for n in s.nodes:
  a=r.canon(m,n.lhs);b=r.canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 lk=r.canon(m,target[0]);rk=r.canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 lhskeys={k for k in terms if uf.find(k)==lr};front=[terms[k] for k in terms if uf.find(k)==rr]
 seen={r.canon(m,t) for t in front};parents={};edges=[];layers=[];hit=None
 for depth in range(1,5):
  nxt=[];matches=0
  for t in front:
   env={}
   if not cut.match(source[1],t,env) or any(v not in env for v in source[2]):continue
   pred=m.substitute(source[0],env);item=r.make_instance(m,source,target,env,f'inverse-bridge-depth-{depth}')
   if not item:continue
   matches+=1;k=r.canon(m,pred);edges.append(item);parents[k]=(r.canon(m,t),len(edges)-1)
   if k in lhskeys:
    hit=(depth,k);break
   if k not in seen:seen.add(k);nxt.append(pred)
  layers.append({'depth':depth,'frontier':len(front),'direct_inverse_matches':matches,'new_predecessors':len(nxt),'hit_lhs_component':bool(hit)})
  if hit:break
  front=nxt
  if not front:break
 chain=[]
 if hit:
  k=hit[1]
  while k not in {r.canon(m,t) for t in [target[1]]} and k in parents:
   pk,ei=parents[k];chain.append(edges[ei]);k=pk
  chain=list(reversed(chain))
 A=r.run_arm(m,sym,source,target,state,30.0,'A_post_development')
 C=r.run_arm(m,sym,source,target,state+chain,30.0,'C_inverse_bridge_chain') if chain else {'closure':False,'installed':0,'tag':'C_inverse_bridge_chain','error':'no_depth_le_4_bridge'}
 abl=r.run_arm(m,sym,source,target,state,30.0,'C_ablation') if C.get('closure') else None
 out={'schema':'mathgraph.post-development-inverse-bridge-depth.v1','id':RID,'protocol':{'depth_increased_only_after_verified_depth1_absence':True,'every_edge_direct_source_instance':True,'no_external_proof_trace':True},'components':{'lhs_size':len(lhskeys),'rhs_size':sum(uf.find(k)==rr for k in terms)},'layers':layers,'first_bridge_depth':hit[0] if hit else None,'chain_length':len(chain),'chain':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1])} for x in chain],'arms':{'A':A,'C':C,'C_ablation':abl}}
 out['decision']='PASS' if C.get('closure') and not A.get('closure') and abl and not abl.get('closure') else 'CHAIN_FOUND_NO_CLOSURE' if chain else 'NO_BRIDGE_DEPTH_LE_4'
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
