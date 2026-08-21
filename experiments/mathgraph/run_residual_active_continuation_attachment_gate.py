#!/usr/bin/env python3
"""Frozen semantic-JOIN refinement for evaluation_order5_0014.

Evidence available before this gate:
- residual reification changes the generator: 517/520 descendants contain the
  missing structure while matched controls contain 0/520;
- top residual descendants have activation=1 while controls have activation=0;
- nevertheless the theorem remains open.

Frozen refinement: the missing step is target-context handoff of the *newly active
continuation*, not construction of another raw lemma.  Generate the same matched
B/C reification descendants, then lift each replay-valid active C descendant whose
endpoint occurs in the target through the exact target context. Compare against
identically processed near-miss B descendants.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'; SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'; SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'; OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'; REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'; OUT=ROOT/'experiments/mathgraph/results/residual-active-continuation-attachment-gate.json'; RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def canon(m,t):return m.alpha_canonical_term(t,{})
def paths(t,p=()):
 yield p,t
 if t[0]=='op':yield from paths(t[1],p+('L',));yield from paths(t[2],p+('R',))
def eqkey(m,a,b):return min((canon(m,a),canon(m,b)),(canon(m,b),canon(m,a)))
def copy(m,item):
 out=[]
 for n in item['proof'][0]:out.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=n.parents,substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or 'active-attachment-parent',derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return out,item['proof'][1]
def attach(m,source,target,item,endpoint,side,path):
 nodes,root=copy(m,item); n=nodes[root]
 if endpoint==1:
  rr=len(nodes);nodes.append(m.EqualityNode(n.rhs,n.lhs,'symmetry',parents=(root,),constructor='active-attachment-symmetry'));root=rr
 norm=m.EquationalNormalizer(source,target,time.monotonic()+2,dict(m.NORMALIZATION_PORTFOLIO[1]))
 try:r=norm.lift_context(nodes,root,side,path)
 except Exception:return None
 if r is None or not m.replay_dag(source,nodes,r,maximum_term_size=260,maximum_nodes=50000):return None
 q=nodes[r];schema=(q.lhs,q.rhs,tuple(sorted(m.term_variables(q.lhs)|m.term_variables(q.rhs))))
 return {'schema':schema,'proof':(nodes,r),'name':'active_target_context_attachment','activation':selfm.activation(m,schema,target),'path':path}
def attachments(m,source,target,items,limit=256):
 out=[];seen=set();tkeys={canon(m,target[0]),canon(m,target[1])}
 for it in items:
  for endpoint,e in enumerate(it['schema'][:2]):
   for si,side in enumerate(target[:2]):
    for p,u in paths(side):
     if canon(m,u)!=canon(m,e):continue
     x=attach(m,source,target,it,endpoint,side,p)
     if not x:continue
     k=eqkey(m,x['schema'][0],x['schema'][1])
     if k in seen:continue
     seen.add(k);x['target_side']=si;x['direct_target_contact']=int(canon(m,x['schema'][0]) in tkeys or canon(m,x['schema'][1]) in tkeys);out.append(x)
     if len(out)>=limit:return out
 out.sort(key=lambda x:(-x['direct_target_contact'],-x['activation'],len(x['path']),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 return out
def main():
 global selfm
 m=load(SOLVER,'mg_actatt');sym=load(SYM,'sym_actatt');selfm=load(SELF,'self_actatt');op=load(OPC,'op_actatt');reify=load(REIFY,'reify_actatt');op.selfmod=selfm;reify.selfm=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfm.proposals(m,source):
  pr=selfm.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfm.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));base=g1[:32]+g2[:128]
 _,_,fterms=reify.frontier(m,sym,source,target,base,10);missing=reify.target_missing(m,target,fterms);proper=reify.proper_missing(m,target,missing);mkeys={canon(m,t) for t in missing}
 vals=[t for t in fterms.values() if t[0]=='op' and canon(m,t) not in mkeys];vals.sort(key=lambda t:(min((m.structural_distance(t,q) for q in (proper or missing)),default=999),m.term_size(t),m.render_term(t)));near=vals[:max(1,len(proper))]
 cs=reify.generate_instances(m,source,target,proper,'C_reify_seed',520)[:72];bs=reify.generate_instances(m,source,target,near,'B_near_seed',520)[:72]
 cc=op.build_gen2(m,source,target,cs,limit=520);bc=op.build_gen2(m,source,target,bs,limit=520)
 for xs in (cc,bc):
  for x in xs:x['activation']=selfm.activation(m,x['schema'],target)
 cc=[x for x in cc if m.replay_dag(source,x['proof'][0],x['proof'][1],maximum_term_size=180,maximum_nodes=50000)];bc=[x for x in bc if m.replay_dag(source,x['proof'][0],x['proof'][1],maximum_term_size=180,maximum_nodes=50000)]
 cc.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])));bc.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 CA=attachments(m,source,target,cc);BA=attachments(m,source,target,bc);common=g1[:24]+g2[:56]
 A=reify.run_arm(m,sym,source,target,base,20,'A_frozen');B=reify.run_arm(m,sym,source,target,common+bc[:72]+BA[:72],25,'B_near_continuation_attachment') if BA else {'closure':False,'error':'no_B_attachments'};C=reify.run_arm(m,sym,source,target,common+cc[:72]+CA[:72],25,'C_active_continuation_attachment') if CA else {'closure':False,'error':'no_C_attachments'};ab=reify.run_arm(m,sym,source,target,common+cc[:72],25,'C_attachment_ablation') if C.get('closure') else None
 out={'schema':'mathgraph.residual-active-continuation-attachment.v1','id':RID,'frozen_prediction':'reification has already created active local continuations; the missing developmental operation is target-context handoff of those active continuations','counts':{'C_continuations':len(cc),'B_continuations':len(bc),'C_nonzero_activation':sum(x['activation']>0 for x in cc),'B_nonzero_activation':sum(x['activation']>0 for x in bc),'C_attachments':len(CA),'B_attachments':len(BA),'C_direct_target_contact':sum(x['direct_target_contact'] for x in CA),'B_direct_target_contact':sum(x['direct_target_contact'] for x in BA),'C_attachment_nonzero_activation':sum(x['activation']>0 for x in CA),'B_attachment_nonzero_activation':sum(x['activation']>0 for x in BA)},'arms':{'A':A,'B':B,'C':C,'C_ablation':ab},'protocol':{'prediction_frozen_before_gate':True,'same_seed_and_continuation_constructors_B_C':True,'same_attachment_operator_B_C':True,'target_contexts_only':True,'all_installed_objects_replay_to_source':True,'no_external_proof_trace':True,'no_answer_label':True},'decision':('PASS' if C.get('closure') and not A.get('closure') and not B.get('closure') and ab and not ab.get('closure') else 'ACTIVE_ATTACHMENT_SIGNAL_NO_CLOSURE' if len(CA)>len(BA) or sum(x['direct_target_contact'] for x in CA)>sum(x['direct_target_contact'] for x in BA) else 'NO_DIFFERENTIAL_ATTACHMENT_SIGNAL')}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
