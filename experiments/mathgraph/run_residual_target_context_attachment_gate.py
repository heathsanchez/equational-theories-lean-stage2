#!/usr/bin/env python3
"""Prospective semantic-JOIN test: verified pieces exist but do not attach to target continuation.

Frozen prediction (from heterogeneous 0014 residuals before this gate): the missing
means is not another term constructor but an attachment/handoff operation.  Residual-
derived replay-verified equalities can contain the missing structure while having zero
ordinary activation.  Explicitly lift such equalities through *actual target contexts*
and test whether this creates target-side continuation and/or closure.

A: frozen G1+G2.
B: same residual multisubstitution lemmas installed globally.
C: same lemmas, but replay-verified target-context attachments are installed.
A positive closure requires C only; a weaker predicted intermediate is that C creates
nonzero target-context attachments/activation where B has zero activation.
"""
import importlib.util, json, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
MISS=ROOT/'experiments/mathgraph/run_missing_subterm_constraint_induction_gate.py'
MS=ROOT/'experiments/mathgraph/run_residual_unified_multisubstitution_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-target-context-attachment-gate.json'
RID='evaluation_order5_0014'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def canon(m,t): return m.alpha_canonical_term(t,{})

def paths(t,p=()):
 yield p,t
 if t[0]=='op':
  yield from paths(t[1],p+('L',)); yield from paths(t[2],p+('R',))

def eqkey(m,a,b):
 x=(canon(m,a),canon(m,b)); y=(canon(m,b),canon(m,a)); return min(x,y)

def attach(m,source,target,item,target_side,path):
 nodes=[]
 # copy the replay-verified proof exactly
 for n in item['proof'][0]:
  nodes.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=n.parents,substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or 'attachment-parent',derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 root=item['proof'][1]
 norm=m.EquationalNormalizer(source,target,time.monotonic()+2.0,dict(m.NORMALIZATION_PORTFOLIO[1]))
 try: r=norm.lift_context(nodes,root,target_side,path)
 except Exception: return None
 if r is None:return None
 if not m.replay_dag(source,nodes,r,maximum_term_size=260,maximum_nodes=16000):return None
 n=nodes[r]; schema=(n.lhs,n.rhs,tuple(sorted(m.term_variables(n.lhs)|m.term_variables(n.rhs))))
 return {'schema':schema,'proof':(nodes,r),'name':'residual_target_context_attachment','activation':selfmod.activation(m,schema,target),'path':path}

def build_attachments(m,source,target,multi,limit=256):
 raw={}; out=[]
 for item in multi:
  lhs=item['schema'][0]
  for side_i,side in enumerate(target[:2]):
   for path,sub in paths(side):
    if sub!=lhs:continue
    x=attach(m,source,target,item,side,path)
    if not x:continue
    k=eqkey(m,x['schema'][0],x['schema'][1])
    if k in raw:continue
    raw[k]=x; x['target_side']=side_i; out.append(x)
    if len(out)>=limit:return out
 out.sort(key=lambda z:(-z['activation'],len(z['path']),m.term_size(z['schema'][0])+m.term_size(z['schema'][1])))
 return out

def main():
 global selfmod
 m=load(SOLVER,'mg_att');sym=load(SYM,'sym_att');selfmod=load(SELF,'self_att');op=load(OPC,'op_att');op.selfmod=selfmod;miss=load(MISS,'miss_att');ms=load(MS,'ms_att');ms.selfmod=selfmod
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 g1=[]
 for p in selfmod.proposals(m,source):
  pr=selfmod.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'name':'g1','activation':selfmod.activation(m,p['schema'],target)})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g2=op.build_gen2(m,source,target,g1,limit=520)
 for x in g2:x['name']='g2'
 g2.sort(key=lambda x:(-x.get('activation',0),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 base=g1[:32]+g2[:128]
 diag,_,fterms=miss.frontier(m,sym,source,target,base,10.0); missing=miss.target_missing(m,target,fterms)
 multi=ms.synthesize(m,source,target,missing)
 attachments=build_attachments(m,source,target,multi)
 A=miss.run_arm(m,sym,source,target,base,20.0,'A_frozen')
 B=miss.run_arm(m,sym,source,target,g1[:24]+g2[:56]+multi[:96],20.0,'B_global_multisub')
 C=miss.run_arm(m,sym,source,target,g1[:24]+g2[:56]+attachments[:96],30.0,'C_target_context_attachment') if attachments else {'closure':False,'installed':0,'tag':'C_target_context_attachment','error':'no_attachments'}
 Abl=miss.run_arm(m,sym,source,target,g1[:24]+g2[:56],30.0,'C_ablation') if C.get('closure') else None
 top=[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'activation':x['activation'],'path':list(x['path']),'target_side':x['target_side']} for x in attachments[:20]]
 structural_positive=bool(attachments) and (max((x['activation'] for x in attachments),default=0)>0 or any(canon(m,x['schema'][0]) in {canon(m,target[0]),canon(m,target[1])} or canon(m,x['schema'][1]) in {canon(m,target[0]),canon(m,target[1])} for x in attachments))
 decision='PASS' if C.get('closure') and not A.get('closure') and not B.get('closure') and Abl and not Abl.get('closure') else ('ATTACHMENT_SIGNAL_NO_CLOSURE' if structural_positive else 'NO_ATTACHMENT_SIGNAL')
 out={'schema':'mathgraph.residual-target-context-attachment.v1','id':RID,'frozen_prediction':'heterogeneous residual JOIN predicts a missing attachment/handoff capability: verified residual-derived pieces must be transported through target contexts to become active continuations','missing_target_subterms':[m.render_term(t) for t in missing],'counts':{'g1':len(g1),'g2':len(g2),'multisub_verified':len(multi),'multisub_nonzero_activation':sum(x.get('activation',0)>0 for x in multi),'attachments_verified':len(attachments),'attachments_nonzero_activation':sum(x.get('activation',0)>0 for x in attachments),'attachments_direct_target_contact':sum(canon(m,x['schema'][0]) in {canon(m,target[0]),canon(m,target[1])} or canon(m,x['schema'][1]) in {canon(m,target[0]),canon(m,target[1])} for x in attachments)},'arms':{'A':A,'B':B,'C':C,'C_ablation':Abl},'top_attachments':top,'protocol':{'prediction_frozen_before_gate':True,'no_external_proof_trace':True,'no_answer_label_in_generator':True,'all_parent_lemmas_replay_verified':True,'all_attachments_replay_verified':True,'contexts_derived_only_from_target_syntax':True},'decision':decision}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
