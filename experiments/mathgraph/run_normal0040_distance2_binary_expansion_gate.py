#!/usr/bin/env python3
import importlib.util,itertools,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'; SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'; SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'; OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'; RHS=ROOT/'experiments/mathgraph/run_normal0040_rhs_reification_gate.py'; EP=ROOT/'experiments/mathgraph/run_normal0040_endpoint_promotion_gate.py'; CUT=ROOT/'experiments/mathgraph/run_normal0040_cut_contraction_gate.py'; D2=ROOT/'experiments/mathgraph/run_normal0040_distance2_frontier_gate.py'; PROTO=ROOT/'experiments/mathgraph/protocols/normal0040-distance2-binary-expansion-v1.json'; OUT=ROOT/'experiments/mathgraph/results/normal0040-distance2-binary-expansion-gate.json'; RID='evaluation_normal_0040'
def load(p,n): s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
def cp(m,src,dst,tag):
 o=len(dst)
 for n in src: dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(o+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return o
def orient(m,item,nodes,rev,tag):
 ns,r=item['proof'];o=cp(m,ns,nodes,tag);q=o+r
 if rev:
  n=nodes[q];nodes.append(m.EqualityNode(n.rhs,n.lhs,'symmetry',parents=(q,),constructor=tag+'-sym'));q=len(nodes)-1
 return q
def canonpair(m,a,b):
 n={};x=(m.alpha_canonical_term(a,n),m.alpha_canonical_term(b,n));n={};y=(m.alpha_canonical_term(b,n),m.alpha_canonical_term(a,n));return min(x,y)
def md(m,t,S): return min((m.structural_distance(t,u) for u in S),default=999)
def binary(m,selfm,source,target,leftpool,rightpool,L,R,limit=1200):
 norm=m.EquationalNormalizer(source,target,time.monotonic()+25,dict(m.NORMALIZATION_PORTFOLIO[1]));raw={}
 for i,x in enumerate(leftpool[:72]):
  for j,y in enumerate(rightpool[:48]):
   for rx,ry in itertools.product((False,True),repeat=2):
    nodes=[];r1=orient(m,x,nodes,rx,'bin-a');r2=orient(m,y,nodes,ry,'bin-b');a,b=nodes[r1].lhs,nodes[r1].rhs;c,d=nodes[r2].lhs,nodes[r2].rhs
    s=('op',a,c);mid=('op',b,c);e=('op',b,d)
    if max(m.term_size(s),m.term_size(e))>120: continue
    try:l1=norm.lift_context(nodes,r1,s,('L',));l2=norm.lift_context(nodes,r2,mid,('R',))
    except Exception: continue
    if l1 is None or l2 is None: continue
    nodes.append(m.EqualityNode(s,e,'transitivity',parents=(l1,l2),constructor='normal0040-binary-expansion'));root=len(nodes)-1
    if not m.replay_dag(source,nodes,root,maximum_term_size=200,maximum_nodes=20000): continue
    k=canonpair(m,s,e)
    if k in raw: continue
    score=min(md(m,s,L)+md(m,e,R),md(m,s,R)+md(m,e,L))
    raw[k]={'schema':(s,e,tuple(sorted(m.term_variables(s)|m.term_variables(e)))),'proof':(nodes,root),'activation':selfm.activation(m,(s,e,()),target),'geom_score':score,'parents':(i,j)}
    if len(raw)>=limit: break
   if len(raw)>=limit: break
  if len(raw)>=limit: break
 out=list(raw.values());out.sort(key=lambda z:(z['geom_score'],-z['activation'],m.term_size(z['schema'][0])+m.term_size(z['schema'][1])));return out
def main():
 p=json.loads(PROTO.read_text());m=load(SOLVER,'mgbin');sym=load(SYM,'symbin');selfm=load(SELF,'selfbin');op=load(OPC,'opbin');op.selfmod=selfm;rhs=load(RHS,'rhsbin');rhs.selfm=selfm;ep=load(EP,'epbin');cut=load(CUT,'cutbin');d2m=load(D2,'d2bin')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID);source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 frozen=cut.build_frozen(m,sym,selfm,op,rhs,ep,source,target);s3,_=ep.frontier(m,sym,source,target,frozen,20.0);_,_,L3,R3,_,_,d3=cut.components(m,target,s3.nodes);c3=cut.synthesize(m,selfm,ep,source,target,L3,R3,d3);g3=[x for x in c3 if x['cross_distance']<3];best=min(x['cross_distance'] for x in g3);step=[x for x in g3 if x['cross_distance']==best]
 if d3!=3 or best!=2 or len(step)!=1: raise SystemExit('prior geometry changed')
 prior=frozen+[step[0]];s2,_=ep.frontier(m,sym,source,target,prior,25.0);_,_,L,R,_,_,d=cut.components(m,target,s2.nodes)
 if d!=2: raise SystemExit('expected d2')
 shellL=[t for t in L if md(m,t,R)==2];shellR=[t for t in R if md(m,t,L)==2];unary,basis=d2m.enumerate_shell(m,selfm,ep,source,target,L,R,shellL,shellR,2)
 # independent replay-valid parents: shell-touching unary continuations x existing retained history
 libs=[x for x in prior if isinstance(x,dict) and x.get('proof')]
 bins=binary(m,selfm,source,target,unary,libs,L,R)
 n=min(48,len(bins),len(unary));A=ep.run_arm(m,sym,source,target,prior,30.0,'A_d2');B=ep.run_arm(m,sym,source,target,prior+unary[:n],30.0,'B_unary_control') if n else None;C=ep.run_arm(m,sym,source,target,prior+bins[:n],35.0,'C_binary_expansion') if n else None
 causal=[];abl=None
 if C and C.get('cross_distance') is not None and C['cross_distance']<2:
  for idx,x in enumerate(bins[:min(24,len(bins))]):
   r=ep.run_arm(m,sym,source,target,prior+[x],15.0,f'isolate_{idx}')
   if r.get('cross_distance') is not None and r['cross_distance']<2: causal.append((x,r));break
  if causal: abl=ep.run_arm(m,sym,source,target,prior,20.0,'ablation')
 strong=bool(causal and causal[0][1].get('closure') and abl and not abl.get('closure'))
 partial=bool(causal and causal[0][1].get('cross_distance',2)<2 and abl and abl.get('cross_distance')==2)
 dec='PASS_STRONG_CLOSURE' if strong else 'PASS_2_TO_1_CAUSAL' if partial else 'BINARY_BATCH_CONTRACTED_NOT_ISOLATED' if C and C.get('cross_distance',2)<2 else 'BINARY_GRAMMAR_OBSTRUCTION_K_EMPTY'
 def sh(x):return {'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'geom_score':x.get('geom_score'),'activation':x.get('activation')}
 out={'schema':'mathgraph.normal0040-distance2-binary-expansion.v1','id':RID,'protocol':p,'frozen':{'distance':d,'lhs':len(L),'rhs':len(R),'shellL':[m.render_term(t) for t in shellL],'shellR':[m.render_term(t) for t in shellR]},'counts':{'unary':len(unary),'binary_verified':len(bins),'installed':n},'arms':{'A':A,'B':B,'C':C,'ablation':abl},'isolated':[{'candidate':sh(x),'arm':r} for x,r in causal],'top_binary':[sh(x) for x in bins[:20]],'decision':dec}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
