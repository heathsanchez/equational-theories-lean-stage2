#!/usr/bin/env python3
"""K2 intervention for evaluation_order5_0014: anchored cut contraction.

Prior audit established that 320/320 cross-cone binary fusions mixed lhs/rhs
provenance only at the subterm level while both equality endpoints remained
outside either residual component.  K2 therefore requires a useful extension to
*keep one endpoint attached to a frozen residual component while introducing
opposite-side structure*.

This gate constructs exactly that previously absent family.  Starting from a
verified equality p=q and an anchor term A already in the lhs or rhs component,
if p occurs inside A, lift p=q through the exact context of A to obtain
    A = A[p:=q].
The first endpoint is therefore attached by construction.  Candidates are
ranked by whether the rewritten endpoint contains a subterm from the opposite
component.  Every derived equality is produced by the existing context-lift
constructor and replayed to the original source law.

Matched arms:
 A frozen post-development state
 B anchored rewrites that do NOT introduce opposite-component structure
 C K2 anchored rewrites that DO introduce opposite-component structure
If C closes while A/B fail, C is rerun without the K2 extensions for ablation.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py';CP=ROOT/'experiments/mathgraph/run_residual_cut_critical_pair_gate.py'
OUT=ROOT/'experiments/mathgraph/results/anchored-cut-contraction-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def copy_nodes(m,src):
 out=[]
 for n in src:out.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=n.parents,substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return out
def paths(t,needle,path=()):
 out=[]
 if t==needle:out.append(path)
 if t[0]=='op':
  out+=paths(t[1],needle,path+('L',));out+=paths(t[2],needle,path+('R',))
 return out
def subs(m,t):return list(m.walk_subterms(t))
def make_search(m,sym,selfm,op,r,cp,source,target,secs=28):
 state=cp.build_state(m,sym,selfm,op,r,source,target); lim={'max_term_size':140,'max_pool_terms':120,'max_core_terms':20,'max_source_attempts':190000,'max_source_edges':4800,'max_derivation_nodes':50000,'max_graph_edges':32000,'max_congruence_rounds':1}; s=m.ContextualSearch(source,target,time.monotonic()+secs,lim); roots=[]
 for item in state:
  q=cp.copy_proof_into(m,s,item['proof'],'post-development-installed');
  if q is not None:roots.append((item,q))
 pool=s.make_pool();s.instantiate_sources(pool)
 return state,s,roots
def proof_item_from_root(m,s,idx,name):
 # Prefix contains all parents because nodes are appended in topological order.
 ns=copy_nodes(m,s.nodes[:idx+1]); n=ns[idx]
 return {'schema':(n.lhs,n.rhs,tuple(sorted(m.term_variables(n.lhs)|m.term_variables(n.rhs)))),'proof':(ns,idx),'name':name}
def derive(m,source,target,item,anchor,rev=False,max_size=140):
 ns,root=item['proof'];nodes=copy_nodes(m,ns);r0=root;n=nodes[r0]
 if rev:
  rr=len(nodes);nodes.append(m.EqualityNode(n.rhs,n.lhs,'symmetry',parents=(r0,),constructor='anchored-parent-symmetry'));r0=rr;n=nodes[r0]
 for path in paths(anchor,n.lhs):
  norm=m.EquationalNormalizer(source,target,time.monotonic()+2,dict(m.NORMALIZATION_PORTFOLIO[1]))
  try: rr=norm.lift_context(nodes,r0,anchor,path)
  except Exception: rr=None
  if rr is None:continue
  u,v=nodes[rr].lhs,nodes[rr].rhs
  if u!=anchor or max(m.term_size(u),m.term_size(v))>max_size:continue
  if not m.replay_dag(source,nodes,rr,maximum_term_size=180,maximum_nodes=30000):continue
  return {'schema':(u,v,tuple(sorted(m.term_variables(u)|m.term_variables(v)))),'proof':(nodes,rr),'name':'anchored_cut_contraction','anchor':anchor,'path':path}
 return None
def install(m,s,item,tag):
 ns,root=item['proof'];off=len(s.nodes)
 for n in ns:s.nodes.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off+root
def arm(m,sym,selfm,op,r,cp,source,target,mode):
 state,s,roots=make_search(m,sym,selfm,op,r,cp,source,target,28);tl,tr=target[:2];comps=s.components();lc,rc=comps.get(tl),comps.get(tr)
 if lc==rc:return {'closure':True,'base_joined':True,'nodes':len(s.nodes)}
 # Small anchor pools from exact component membership.
 terms={}
 for n in s.nodes:
  for t in (n.lhs,n.rhs):
   c=comps.get(t)
   if c in (lc,rc):terms.setdefault(c,[]).append(t)
 def uniq_short(xs):
  seen=set();out=[]
  for t in sorted(xs,key=lambda z:(m.term_size(z),m.render_term(z))):
   k=m.alpha_canonical_term(t,{})
   if k in seen:continue
   seen.add(k);out.append(t)
   if len(out)>=36:break
  return out
 LA,RA=uniq_short(terms.get(lc,[])),uniq_short(terms.get(rc,[]))
 # Candidate verified equalities: installed roots + short source/reentry nodes.
 items=[item for item,q in roots]
 extra=[]
 for i,n in enumerate(s.nodes):
  if n.kind in ('source instance','source reentry') and m.term_size(n.lhs)+m.term_size(n.rhs)<=28:
   extra.append(proof_item_from_root(m,s,i,'source'))
   if len(extra)>=80:break
 items+=extra
 cand=[];seen=set()
 for side,anchors,opp in (('L',LA,rc),('R',RA,lc)):
  for A in anchors:
   for it in items:
    for rev in (False,True):
     x=derive(m,source,target,it,A,rev)
     if not x:continue
     u,v,_=x['schema'];k=(m.alpha_canonical_term(u,{}),m.alpha_canonical_term(v,{}))
     if k in seen:continue
     seen.add(k)
     opp_hits=sum(1 for z in subs(m,v) if comps.get(z)==opp)
     x.update(anchor_side=side,opposite_subterm_hits=opp_hits,size=m.term_size(v));cand.append(x)
     if len(cand)>=1600:break
    if len(cand)>=1600:break
   if len(cand)>=1600:break
  if len(cand)>=1600:break
 pos=[x for x in cand if x['opposite_subterm_hits']>0];neg=[x for x in cand if x['opposite_subterm_hits']==0]
 key=lambda x:(-x['opposite_subterm_hits'],x['size'])
 pos.sort(key=key);neg.sort(key=lambda x:x['size'])
 chosen=[]
 if mode=='control':chosen=neg[:96]
 elif mode=='k2':chosen=pos[:96]
 for x in chosen:install(m,s,x,'anchored-cut-installed')
 if chosen:
  # Let the ordinary trusted search propagate the installed anchored equalities.
  pool=s.make_pool();s.instantiate_sources(pool); outer=list(range(max(0,len(s.nodes)-min(len(s.nodes),5000)),len(s.nodes)));c=s.collect_overlap_candidates(outer,outer,4,12000)
  for q in c[:7000]:
   if time.monotonic()>=s.deadline:break
   s.apply_overlap(q,1)
 fin=s.components();closed=fin.get(tl)==fin.get(tr)
 return {'closure':closed,'base_joined':False,'nodes':len(s.nodes),'graph_edges':s.graph_edges,'candidate_count':len(cand),'k2_candidates':len(pos),'control_candidates':len(neg),'installed':len(chosen),'lhs_anchors':len(LA),'rhs_anchors':len(RA),'top_k2':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'opposite_subterm_hits':x['opposite_subterm_hits'],'anchor_side':x['anchor_side']} for x in pos[:12]]}
def main():
 m=load(SOLVER,'mg_acc');sym=load(SYM,'sym_acc');selfm=load(SELF,'self_acc');op=load(OPC,'op_acc');r=load(REIFY,'reify_acc');cp=load(CP,'cp_acc');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 A=arm(m,sym,selfm,op,r,cp,source,target,'base');B=arm(m,sym,selfm,op,r,cp,source,target,'control');C=arm(m,sym,selfm,op,r,cp,source,target,'k2');ab=None
 if C.get('closure'):ab=arm(m,sym,selfm,op,r,cp,source,target,'base')
 decision='K2_CLOSES_WITH_ABLATION' if C.get('closure') and not A.get('closure') and not B.get('closure') and ab and not ab.get('closure') else ('K2_CLOSES' if C.get('closure') else ('K2_INSTANTIABLE_NO_CLOSURE' if C.get('k2_candidates',0)>0 else 'K2_NOT_INSTANTIABLE'))
 out={'schema':'mathgraph.anchored-cut-contraction.v1','id':RID,'K2':'keep one equality endpoint in a frozen residual component while introducing substructure from the opposite component','protocol':{'derived_from_prior_cut_attachment_audit':True,'no_external_proof_trace':True,'target_only_defines_residual_cut':True,'all_extensions_replay_to_source':True,'matched_control':True},'arms':{'A_frozen':A,'B_anchored_same_side_control':B,'C_anchored_opposite_structure':C,'C_ablation':ab},'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
