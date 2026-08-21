#!/usr/bin/env python3
"""Test the post-reification residual: structure exists, but can it be used coherently?

Freeze the replay-verified residual multisubstitution operators. Compare:
 A frozen G1/G2;
 B exact single-hole target-context lifts of those operators;
 C coordinated multi-hole lifts of the SAME operator into 2-3 disjoint target positions.
Every transported equality is compiled from the original source proof by congruence +
transitivity and must replay. No external proof trace is used.
"""
import importlib.util,itertools,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py';MS=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-coordinated-context-transport-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def copy_nodes(m,src,dst,tag):
 off=len(dst)
 for n in src:dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off
def paths(t,p=()):
 yield p,t
 if t[0]=='op':yield from paths(t[1],p+('L',));yield from paths(t[2],p+('R',))
def incomparable(ps):
 for a,b in itertools.combinations(ps,2):
  if a==b or a==b[:len(a)] or b==a[:len(b)]:return False
 return True
def orient_proof(m,item,rev):
 nodes=[];off=copy_nodes(m,item['proof'][0],nodes,'coord-parent');r=off+item['proof'][1]
 if rev:
  n=nodes[r];nodes.append(m.EqualityNode(n.rhs,n.lhs,'symmetry',parents=(r,),constructor='coord-parent-sym'));r=len(nodes)-1
 return nodes,r,nodes[r].lhs,nodes[r].rhs
def transport(m,source,target,item,side_i,chosen,rev=False):
 nodes,r,a,b=orient_proof(m,item,rev);root0=target[side_i];current=root0;chain=None
 norm=m.EquationalNormalizer(source,target,time.monotonic()+3,dict(m.NORMALIZATION_PORTFOLIO[1]))
 for p in chosen:
  try:lr=norm.lift_context(nodes,r,current,p)
  except Exception:return None
  if lr is None:return None
  if chain is None:chain=lr
  else:
   if nodes[chain].rhs!=nodes[lr].lhs:return None
   nodes.append(m.EqualityNode(nodes[chain].lhs,nodes[lr].rhs,'transitivity',parents=(chain,lr),constructor='coordinated-context-transport'));chain=len(nodes)-1
  current=nodes[lr].rhs
 if chain is None:return None
 if not m.replay_dag(source,nodes,chain,maximum_term_size=220,maximum_nodes=20000):return None
 sch=(nodes[chain].lhs,nodes[chain].rhs,tuple(sorted(m.term_variables(nodes[chain].lhs)|m.term_variables(nodes[chain].rhs))))
 return {'schema':sch,'proof':(nodes,chain),'name':f'context_transport_{len(chosen)}','holes':len(chosen),'activation':selfm.activation(m,sch,target)}
def build(m,source,target,multi,hmin,hmax,limit=500):
 out=[];seen=set()
 for item in multi:
  for rev in (False,True):
   _,_,a,_=orient_proof(m,item,rev)
   for si in (0,1):
    ps=[p for p,t in paths(target[si]) if t==a]
    for h in range(hmin,min(hmax,len(ps))+1):
     for ch in itertools.combinations(ps,h):
      if not incomparable(ch):continue
      x=transport(m,source,target,item,si,ch,rev)
      if not x:continue
      k=(m.alpha_canonical_term(x['schema'][0],{}),m.alpha_canonical_term(x['schema'][1],{}))
      if k in seen:continue
      seen.add(k);out.append(x)
      if len(out)>=limit:return sorted(out,key=lambda z:(-z['activation'],-z['holes'],m.term_size(z['schema'][1])))
 return sorted(out,key=lambda z:(-z['activation'],-z['holes'],m.term_size(z['schema'][1])))
def main():
 global selfm
 m=load(SOLVER,'mg_coord');sym=load(SYM,'sym_coord');selfm=load(SELF,'self_coord');op=load(OPC,'op_coord');op.selfmod=selfm;miss=load(MISS,'miss_coord');ms=load(MS,'ms_coord');ms.selfmod=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfm.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));base=g1[:32]+g2[:128]
 _,_,fterms=miss.frontier(m,sym,source,target,base,10.0);missing=miss.target_missing(m,target,fterms);multi=ms.synthesize(m,source,target,missing)
 one=build(m,source,target,multi,1,1,500);many=build(m,source,target,multi,2,3,500)
 A=miss.run_arm(m,sym,source,target,g1[:24]+g2[:56],30.0,'A_frozen')
 B=miss.run_arm(m,sym,source,target,g1[:24]+g2[:56]+multi[:16]+one[:120],30.0,'B_single_hole_transport')
 C=miss.run_arm(m,sym,source,target,g1[:24]+g2[:56]+multi[:16]+many[:160],45.0,'C_coordinated_multihole_transport')
 Abl=miss.run_arm(m,sym,source,target,g1[:24]+g2[:56]+multi[:16]+one[:120],45.0,'C_coordination_ablation') if C['closure'] else None
 out={'schema':'mathgraph.residual-coordinated-context-transport.v1','id':RID,'hypothesis':'after residual-derived construction succeeds, the remaining obstruction is exact coordinated attachment/transport of one verified equality across multiple target contexts','counts':{'multisub':len(multi),'single_hole_verified':len(one),'multi_hole_verified':len(many)},'arms':{'A':A,'B':B,'C':C,'C_ablation':Abl},'protocol':{'multisub_basis_frozen':True,'same_parent_equalities_B_C':True,'exact_target_context_match_required':True,'all_transports_source_replay_verified':True,'no_external_proof_trace':True,'no_answer_label_in_generator':True},'decision':'PASS' if C['closure'] and not A['closure'] and not B['closure'] and Abl and not Abl['closure'] else ('SINGLE_HOLE_SUFFICIENT' if B['closure'] and not A['closure'] else 'PARTIAL' if C['closure'] else 'NO_CLOSURE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
