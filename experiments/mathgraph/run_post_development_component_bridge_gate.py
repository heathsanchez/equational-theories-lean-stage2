#!/usr/bin/env python3
"""Third developmental iteration: exact residual-cut source-instance synthesis.

After reification and tree completion, the target term is generatable but the
proof remains open. Recompute the equality graph, identify the component of the
target lhs and target rhs, then synthesize ONLY source-law instances whose two
endpoints cross that verified residual cut. Candidate bridges are obtained by
matching the original source RHS against actual endpoints in one component and
checking whether the induced source LHS lies in the opposite component.
"""
import importlib.util,json,sys
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py';SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py';SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py';OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py';REIFY=ROOT/'experiments/mathgraph/run_missing_subterm_reification_gate.py'
OUT=ROOT/'experiments/mathgraph/results/post-development-component-bridge-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def match(p,t,env):
 if p[0]=='var':
  v=p[1]
  if v in env:return env[v]==t
  env[v]=t;return True
 if t[0]!='op' or p[0]!='op':return False
 return match(p[1],t[1],env) and match(p[2],t[2],env)
class UF:
 def __init__(self):self.p={}
 def find(self,x):
  self.p.setdefault(x,x)
  if self.p[x]!=x:self.p[x]=self.find(self.p[x])
  return self.p[x]
 def union(self,a,b):
  a=self.find(a);b=self.find(b)
  if a!=b:self.p[b]=a
def main():
 m=load(SOLVER,'mg_cut3');sym=load(SYM,'sym_cut3');selfm=load(SELF,'self_cut3');op=load(OPC,'op_cut3');r=load(REIFY,'reify_cut3');r.selfm=selfm;op.selfmod=selfm
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
 fill=[]
 for q in miss1:
  if q[0]=='op' and r.canon(m,q[1]) in postkeys and r.canon(m,q[2]) in postkeys:fill.append(q)
 c2=r.generate_instances(m,source,target,fill,'retained-tree-completion',520);k1={r.canon(m,t) for t in miss1}
 for x in c2:x['missing_hits']=r.hit_count(m,x,k1)
 c2.sort(key=lambda x:(-x['missing_hits'],-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 state=g1[:20]+g2[:40]+c1[:48]+c2[:72]
 s,found,_=r.frontier(m,sym,source,target,state,20.0)
 uf=UF();terms={}
 for n in s.nodes:
  a=r.canon(m,n.lhs);b=r.canon(m,n.rhs);terms[a]=n.lhs;terms[b]=n.rhs;uf.union(a,b)
 lk=r.canon(m,target[0]);rk=r.canon(m,target[1]);lr=uf.find(lk);rr=uf.find(rk)
 cx=[(k,t) for k,t in terms.items() if uf.find(k)==lr];ct=[(k,t) for k,t in terms.items() if uf.find(k)==rr]
 bridges=[];controls=[];seen=set()
 def scan(side,otherroot,want_cross):
  for k,t in side:
   env={}
   if not match(source[1],t,env) or any(v not in env for v in source[2]):continue
   lhs=m.substitute(source[0],env);kl=r.canon(m,lhs);root=uf.find(kl)
   cross=(root==otherroot)
   if cross!=want_cross:continue
   item=r.make_instance(m,source,target,env,'residual-cut-source-instance' if cross else 'same-component-control')
   if not item:continue
   ek=r.eqkey(m,item['schema'][0],item['schema'][1])
   if ek in seen:continue
   seen.add(ek);(bridges if cross else controls).append(item)
 scan(ct,lr,True);scan(cx,rr,True)
 # matched non-crossing source instances from the two endpoint components
 for side,root in ((cx,lr),(ct,rr)):
  for k,t in side:
   env={}
   if not match(source[1],t,env) or any(v not in env for v in source[2]):continue
   lhs=m.substitute(source[0],env)
   if uf.find(r.canon(m,lhs))!=root:continue
   item=r.make_instance(m,source,target,env,'same-component-control')
   if item:controls.append(item)
 bridges.sort(key=lambda x:(m.term_size(x['schema'][0])+m.term_size(x['schema'][1]),-x.get('activation',0)));controls.sort(key=lambda x:(m.term_size(x['schema'][0])+m.term_size(x['schema'][1]),-x.get('activation',0)))
 n=min(max(1,len(bridges)),32,len(controls)) if bridges and controls else min(len(bridges),32)
 A=r.run_arm(m,sym,source,target,state,25.0,'A_post_development')
 B=r.run_arm(m,sym,source,target,state+controls[:n],25.0,'B_same_component_control') if n and controls else {'closure':False,'installed':0,'tag':'B_same_component_control'}
 C=r.run_arm(m,sym,source,target,state+bridges[:n],25.0,'C_exact_residual_cut_bridge') if n else {'closure':False,'installed':0,'tag':'C_exact_residual_cut_bridge','error':'no_exact_bridge_candidates'}
 abl=r.run_arm(m,sym,source,target,state,25.0,'C_ablation') if C.get('closure') else None
 out={'schema':'mathgraph.post-development-component-bridge.v1','id':RID,'protocol':{'post_development_components_recomputed':True,'bridges_are_direct_replay_verified_source_instances':True,'no_external_proof_trace':True},'component_state':{'lhs_component_size':len(cx),'rhs_component_size':len(ct),'already_joined':lr==rr,'nodes':len(s.nodes),'rules':len(s.rules),'overlaps':s.overlap_candidates},'counts':{'bridge_candidates':len(bridges),'control_candidates':len(controls),'installed_per_arm':n},'top_bridges':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1])} for x in bridges[:10]],'arms':{'A':A,'B':B,'C':C,'C_ablation':abl}}
 out['decision']='PASS' if C.get('closure') and not A.get('closure') and not B.get('closure') and abl and not abl.get('closure') else 'PARTIAL' if C.get('closure') else 'NO_EXACT_BRIDGE' if not bridges else 'BRIDGE_FOUND_NO_CLOSURE'
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
