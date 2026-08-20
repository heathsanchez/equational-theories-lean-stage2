#!/usr/bin/env python3
"""Residual-derived critical-pair escalation for evaluation_order5_0014.

Prior gates established that the post-development target components cannot be
joined by a single replay-verified source instance, direct contextual bridge,
congruence completion, ten residual-conditioned source-instance families, or a
two-source chain over 12k source instances.  This gate therefore changes the
operator family itself: it permits one generation of replay-checkable
*contextual critical-pair* consequences between already verified equalities.

The residual supplies only the disconnected component cut.  Candidate overlaps
are ranked by the existing generic overlap score, then preferentially selected
when their predicted consequence touches opposite target components.  No
external proof trace, answer label, target-specific equality, or new trusted
inference rule is used: every new edge is compiled from context lifting,
symmetry and transitivity already accepted by replay_dag.
"""
import importlib.util, json, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-cut-critical-pair-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def copy_proof_into(m, search, proof, tag):
 ns,root=proof;off=len(search.nodes)
 ids=[]
 for i,n in enumerate(ns):
  nn=m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record)
  # Only the proof root is a semantic edge; ancestors are replay support.
  nid=search.add_node(nn,graph_edge=(i==root))
  if nid is None and i==root:
   # Root may duplicate an existing edge; recover an oriented existing edge.
   nid=search.oriented_edge_node(nn.lhs,nn.rhs)
  ids.append(nid)
 return ids[root] if root < len(ids) else None

def build_state(m,sym,selfm,op,r,source,target):
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
 _,_,t0=r.frontier(m,sym,source,target,base,10.0);miss0=r.target_missing(m,target,t0);proper=r.proper_missing(m,target,miss0)
 c1=r.generate_instances(m,source,target,proper,'retained-reification',520);k0={r.canon(m,t) for t in miss0}
 for x in c1:x['missing_hits']=r.hit_count(m,x,k0)
 c1.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 state1=g1[:24]+g2[:56]+c1[:72]
 _,_,t1=r.frontier(m,sym,source,target,state1,15.0);miss1=r.target_missing(m,target,t1);keys=set(t1)
 fill=[q for q in miss1 if q[0]=='op' and r.canon(m,q[1]) in keys and r.canon(m,q[2]) in keys]
 c2=r.generate_instances(m,source,target,fill,'retained-tree-completion',520);k1={r.canon(m,t) for t in miss1}
 for x in c2:x['missing_hits']=r.hit_count(m,x,k1)
 c2.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 return g1[:20]+g2[:40]+c1[:48]+c2[:72]

def main():
 m=load(SOLVER,'mg_cp');sym=load(SYM,'sym_cp');selfm=load(SELF,'self_cp');op=load(OPC,'op_cp');r=load(REIFY,'reify_cp');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 state=build_state(m,sym,selfm,op,r,source,target)
 deadline=time.monotonic()+75.0
 limits={'max_term_size':120,'max_pool_terms':120,'max_core_terms':18,'max_source_attempts':200000,'max_source_edges':5000,'max_derivation_nodes':50000,'max_graph_edges':30000,'max_congruence_rounds':1}
 s=m.ContextualSearch(source,target,deadline,limits)
 roots=[]
 for item in state:
  root=copy_proof_into(m,s,item['proof'],'post-development-installed')
  if root is not None: roots.append(root)
 # Add a residual-conditioned but generic source pool, not a target equality.
 pool=s.make_pool();s.instantiate_sources(pool)
 source_nodes=[i for i,n in enumerate(s.nodes) if n.kind in ('source instance','source reentry')]
 root0=s.shortest_path()
 comps0=s.components();tl,tr=target[:2]
 lhs_comp=comps0.get(tl);rhs_comp=comps0.get(tr)
 # Outer equalities include retained developmental laws plus source instances;
 # inner equalities use the same verified pool. This is a genuine critical-pair
 # family rather than another source substitution family.
 outer=list(dict.fromkeys(roots+source_nodes))[:5000]
 inner=list(dict.fromkeys(source_nodes+roots))[:5000]
 candidates=s.collect_overlap_candidates(outer,inner,4,18000)
 def cut_priority(c):
  score,oid,iid,oside,iside,path,before,after,changed=c
  outer_node=s.nodes[oid];other=outer_node.rhs if oside==0 else outer_node.lhs
  co=comps0.get(other);cc=comps0.get(changed)
  exact_cross=(co==lhs_comp and cc==rhs_comp) or (co==rhs_comp and cc==lhs_comp)
  touches=int(co in (lhs_comp,rhs_comp))+int(cc in (lhs_comp,rhs_comp))
  return (0 if exact_cross else 1, -touches, score)
 candidates.sort(key=cut_priority)
 applied=0;join_events=0;found=None;first_witness=None
 for idx,c in enumerate(candidates[:12000]):
  if time.monotonic()>=deadline: break
  before=s.components_joined
  nid=s.apply_overlap(c,1)
  if nid is None: continue
  applied+=1
  if s.components_joined>before:
   join_events+=1
   if first_witness is None:
    n=s.nodes[nid];first_witness={'lhs':m.render_term(n.lhs),'rhs':m.render_term(n.rhs),'candidate_rank':idx,'node':nid}
  if applied%16==0 or s.components_joined>before:
   root=s.shortest_path()
   if root is not None:
    found=root;break
 proof_ok=False;cert_bytes=None;proof_nodes=None
 if found is not None:
  proof_ok=bool(m.replay_dag(source,s.nodes,found,maximum_term_size=140,maximum_nodes=60000))
  if proof_ok:
   code,proof_nodes=m.make_dag_certificate(target,s.nodes,found);cert_bytes=len(code.encode())
 out={'schema':'mathgraph.residual-cut-critical-pair.v1','id':RID,'protocol':{'post_development_cut_only':True,'new_family_contextual_critical_pairs':True,'only_existing_trusted_context_symmetry_transitivity':True,'no_external_proof_trace':True,'no_answer_label':True},'baseline':{'closure':root0 is not None,'lhs_component':lhs_comp,'rhs_component':rhs_comp,'already_joined':lhs_comp==rhs_comp,'installed_roots':len(roots),'source_nodes':len(source_nodes)},'critical_pair':{'candidates':len(candidates),'applied':applied,'component_join_events':join_events,'overlaps_added':s.overlaps_added,'missing_target_introduced':s.missing_target_introduced,'first_join_witness':first_witness},'proof_replay':proof_ok,'certificate_bytes':cert_bytes,'proof_nodes':proof_nodes,'nodes':len(s.nodes),'graph_edges':s.graph_edges,'decision':'PASS' if proof_ok else ('CUT_TOUCHED_NO_CLOSURE' if join_events else 'NO_CRITICAL_PAIR_CUT_BRIDGE')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
