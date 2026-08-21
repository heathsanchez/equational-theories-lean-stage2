#!/usr/bin/env python3
"""Real-residual JOIN intervention for evaluation_order5_0014.

The semantic specification was frozen in REAL_RESIDUAL_FIELD_JOIN_FREEZE_20260821.json
before this file was implemented.  Its central prediction is that the exhausted
operator language is missing coordinated multi-site transport: two linked
verified rewrites must be composed inside one anchored context, rather than
applied as independent local edits.

Matched arms:
 A frozen post-development state
 B factorized control: install the two independent single-site anchor rewrites
 C synchronized intervention: install the replay-verified joint two-site anchored equality

The strongest K(rho) candidates are those for which neither single-site rewrite
introduces an opposite-component subterm, but their synchronized composition does.
If C closes while A/B fail, rerun A as ablation.  No external proof trace or
answer label is used; target sides define only the frozen residual components.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py';CP=ROOT/'experiments/mathgraph/run_residual_cut_critical_pair_gate.py';ACC=ROOT/'experiments/mathgraph/run_anchored_cut_contraction_gate.py'
OUT=ROOT/'experiments/mathgraph/results/real-residual-join-multisite-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def clone_node(m,n,off=0):
 return m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record)

def merge_transitive(m,source,x1,x2,max_nodes=30000):
 ns1,r1=x1['proof'];ns2,r2=x2['proof'];nodes=[clone_node(m,n) for n in ns1];off=len(nodes);nodes += [clone_node(m,n,off) for n in ns2]
 a,b=nodes[r1].lhs,nodes[r1].rhs;c,d=nodes[off+r2].lhs,nodes[off+r2].rhs
 if b!=c:return None
 rr=len(nodes);nodes.append(m.EqualityNode(a,d,'transitivity',parents=(r1,off+r2),constructor='residual-join-synchronized-multisite'))
 if len(nodes)>max_nodes or not m.replay_dag(source,nodes,rr,maximum_term_size=200,maximum_nodes=max_nodes):return None
 return {'schema':(a,d,tuple(sorted(m.term_variables(a)|m.term_variables(d)))),'proof':(nodes,rr),'name':'residual_join_multisite'}

def uniq_short(m,xs,limit=24):
 seen=set();out=[]
 for t in sorted(xs,key=lambda z:(m.term_size(z),m.render_term(z))):
  k=m.alpha_canonical_term(t,{})
  if k in seen:continue
  seen.add(k);out.append(t)
  if len(out)>=limit:break
 return out

def opp_hits(m,comps,opp,t):return sum(1 for z in m.walk_subterms(t) if comps.get(z)==opp)

def build(m,sym,selfm,op,r,cp,acc,source,target):
 state,s,roots=acc.make_search(m,sym,selfm,op,r,cp,source,target,32);tl,tr=target[:2];comps=s.components();lc,rc=comps.get(tl),comps.get(tr)
 terms={}
 for n in s.nodes:
  for t in (n.lhs,n.rhs):
   c=comps.get(t)
   if c in (lc,rc):terms.setdefault(c,[]).append(t)
 LA,RA=uniq_short(m,terms.get(lc,[])),uniq_short(m,terms.get(rc,[]))
 items=[item for item,q in roots]
 for i,n in enumerate(s.nodes):
  if n.kind in ('source instance','source reentry') and m.term_size(n.lhs)+m.term_size(n.rhs)<=26:
   items.append(acc.proof_item_from_root(m,s,i,'source'))
   if len(items)>=72:break
 cand=[];seen=set()
 for side,anchors,opp in (('L',LA,rc),('R',RA,lc)):
  for A in anchors:
   singles=[]
   for ii,it in enumerate(items):
    for rev in (False,True):
     x=acc.derive(m,source,target,it,A,rev,max_size=150)
     if not x:continue
     v=x['schema'][1];k=m.alpha_canonical_term(v,{})
     if any(q['key']==k for q in singles):continue
     singles.append({'key':k,'item':it,'rev':rev,'x':x,'hits':opp_hits(m,comps,opp,v)})
     if len(singles)>=18:break
    if len(singles)>=18:break
   for i,a in enumerate(singles):
    v1=a['x']['schema'][1]
    for j,b in enumerate(singles):
     if i==j:continue
     # Require the second rewrite to act after the first, not merely beside it.
     x2=acc.derive(m,source,target,b['item'],v1,b['rev'],max_size=170)
     if not x2:continue
     joint=merge_transitive(m,source,a['x'],x2)
     if not joint:continue
     v2=b['x']['schema'][1];vj=joint['schema'][1];key=(m.alpha_canonical_term(A,{}),m.alpha_canonical_term(vj,{}))
     if key in seen:continue
     seen.add(key)
     h1=a['hits'];h2=b['hits'];hj=opp_hits(m,comps,opp,vj);synergy=(h1==0 and h2==0 and hj>0)
     cand.append({'joint':joint,'single1':a['x'],'single2':b['x'],'side':side,'h1':h1,'h2':h2,'hj':hj,'synergy':synergy,'size':m.term_size(vj)})
     if len(cand)>=1400:break
    if len(cand)>=1400:break
   if len(cand)>=1400:break
  if len(cand)>=1400:break
 return s,lc,rc,cand,LA,RA

def propagate(s):
 pool=s.make_pool();s.instantiate_sources(pool);outer=list(range(max(0,len(s.nodes)-min(len(s.nodes),5200)),len(s.nodes)));cs=s.collect_overlap_candidates(outer,outer,4,14000)
 for q in cs[:8000]:
  if time.monotonic()>=s.deadline:break
  s.apply_overlap(q,1)

def run_arm(m,sym,selfm,op,r,cp,acc,source,target,mode):
 s,lc,rc,cand,LA,RA=build(m,sym,selfm,op,r,cp,acc,source,target);tl,tr=target[:2]
 if lc==rc:return {'closure':True,'base_joined':True,'nodes':len(s.nodes)}
 syn=[x for x in cand if x['synergy']];ordinary=[x for x in cand if not x['synergy']]
 syn.sort(key=lambda x:(-x['hj'],x['size']));ordinary.sort(key=lambda x:(x['size'],-x['hj']))
 chosen=(syn[:64] if syn else sorted(cand,key=lambda x:(-x['hj'],x['size']))[:64])
 installed=0
 if mode=='factorized':
  for x in chosen:
   acc.install(m,s,x['single1'],'residual-join-factorized-single');acc.install(m,s,x['single2'],'residual-join-factorized-single');installed+=2
 elif mode=='synchronized':
  for x in chosen:acc.install(m,s,x['joint'],'residual-join-synchronized');installed+=1
 if mode!='base' and chosen:propagate(s)
 fin=s.components();closed=fin.get(tl)==fin.get(tr)
 return {'closure':closed,'nodes':len(s.nodes),'graph_edges':s.graph_edges,'candidate_count':len(cand),'synergy_candidates':len(syn),'ordinary_candidates':len(ordinary),'selected':len(chosen),'installed':installed,'lhs_anchors':len(LA),'rhs_anchors':len(RA),'best_joint_opposite_hits':max([x['hj'] for x in cand],default=0),'top_synergy':[{'side':x['side'],'anchor':m.render_term(x['joint']['schema'][0]),'joint_rhs':m.render_term(x['joint']['schema'][1]),'single_hits':[x['h1'],x['h2']],'joint_hits':x['hj'],'size':x['size']} for x in syn[:12]]}

def main():
 m=load(SOLVER,'mg_rj');sym=load(SYM,'sym_rj');selfm=load(SELF,'self_rj');op=load(OPC,'op_rj');r=load(REIFY,'reify_rj');cp=load(CP,'cp_rj');acc=load(ACC,'acc_rj');r.selfm=selfm;op.selfmod=selfm
 row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 A=run_arm(m,sym,selfm,op,r,cp,acc,source,target,'base');B=run_arm(m,sym,selfm,op,r,cp,acc,source,target,'factorized');C=run_arm(m,sym,selfm,op,r,cp,acc,source,target,'synchronized');ab=None
 if C.get('closure'):ab=run_arm(m,sym,selfm,op,r,cp,acc,source,target,'base')
 if C.get('closure') and not A.get('closure') and not B.get('closure') and ab and not ab.get('closure'):decision='REAL_JOIN_MULTISITE_CLOSES_WITH_ABLATION'
 elif C.get('closure'):decision='REAL_JOIN_MULTISITE_CLOSES'
 elif C.get('synergy_candidates',0)>0:decision='REAL_JOIN_K_INSTANTIABLE_NO_CLOSURE'
 else:decision='REAL_JOIN_K_NOT_INSTANTIABLE'
 out={'schema':'mathgraph.real-residual-join-multisite.v1','id':RID,'freeze_commit':'302cde1df02e71baa251deea6ab69d1a28fd2940','K':'coordinated multi-site transport under a shared residual anchor','protocol':{'K_frozen_before_operator_implementation':True,'no_external_proof_trace':True,'target_only_defines_residual_cut':True,'all_joint_extensions_replay_to_source':True,'matched_factorized_control':True},'arms':{'A_frozen':A,'B_factorized_single_site':B,'C_synchronized_multisite':C,'C_ablation':ab},'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
