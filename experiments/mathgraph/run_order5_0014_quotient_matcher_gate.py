#!/usr/bin/env python3
"""Focused port of the previously promoted proof-producing quotient matcher.

Tests evaluation_order5_0014 using e-matching modulo verified equality classes.
Every representative change is compiled to existing equality paths; every rewrite
uses an original source-law instance; the final proof must replay from the source.
"""
import importlib.util,json,sys,time
from collections import defaultdict,deque
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]; SOLVER=ROOT/'submissions/mathgraph/solver.py'
OUT=ROOT/'experiments/mathgraph/results/order5-0014-quotient-matcher-gate.json';RID='evaluation_order5_0014'
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
class QM:
 def __init__(self,m,source,target,deadline,edge_cap=256):
  self.m=m;self.source=source;self.target=target;self.deadline=deadline
  cfg=dict(m.NORMALIZATION_PORTFOLIO[1]);self.n=m.EquationalNormalizer(source,target,deadline,cfg);self.n.generate_consequences();self.n.orient();self.n.select_rulebook();self.nodes=self.n.nodes;self.maxsize=cfg['maximum_term_size'];self.parent={};self.members=defaultdict(set);self.adj=defaultdict(list);self.matches=0;self.qonly=0;self.instances=0;self.replay_failures=0;self.front={'left':{target[0]},'right':{target[1]}}
  tv=set(target[2])
  for i,node in enumerate(self.nodes[:min(edge_cap,len(self.nodes))]):
   if set(m.term_variables(node.lhs))<=tv and set(m.term_variables(node.rhs))<=tv:self.edge(node.lhs,node.rhs,i)
  for side in target[:2]:
   for t in m.walk_subterms(side):self.find(t)
  self.rebuild()
 def find(self,t):
  self.parent.setdefault(t,t)
  if self.parent[t]!=t:self.parent[t]=self.find(self.parent[t])
  return self.parent[t]
 def union(self,a,b):
  a=self.find(a);b=self.find(b)
  if a!=b:
   if self.m.render_term(a)>self.m.render_term(b):a,b=b,a
   self.parent[b]=a
 def edge(self,a,b,i):self.adj[a].append((b,i,False));self.adj[b].append((a,i,True));self.union(a,b)
 def rebuild(self):
  self.members=defaultdict(set)
  for t in list(self.parent):self.members[self.find(t)].add(t)
 def path(self,a,b):
  if a==b:self.nodes.append(self.m.EqualityNode(a,b,'reflexivity'));return len(self.nodes)-1
  q=deque([a]);prev={a:None}
  while q:
   x=q.popleft()
   for y,i,rev in self.adj.get(x,()):
    if y in prev:continue
    prev[y]=(x,i,rev)
    if y==b:q.clear();break
    q.append(y)
  if b not in prev:return None
  es=[];x=b
  while x!=a:p,i,rev=prev[x];es.append((i,rev));x=p
  es.reverse();ids=[]
  for i,rev in es:
   if rev:
    n=self.nodes[i];self.nodes.append(self.m.EqualityNode(n.rhs,n.lhs,'symmetry',parents=(i,),constructor='qm-rep'));ids.append(len(self.nodes)-1)
   else:ids.append(i)
  root=ids[0]
  for i in ids[1:]:
   if self.nodes[root].rhs!=self.nodes[i].lhs:return None
   self.nodes.append(self.m.EqualityNode(self.nodes[root].lhs,self.nodes[i].rhs,'transitivity',parents=(root,i),constructor='qm-rep'));root=len(self.nodes)-1
  return root
 def ematch(self,p,c,mp):
  if p[0]=='var':
   v=p[1];val=self.find(c)
   if v in mp and mp[v]!=val:return []
   z=dict(mp);z[v]=val;return [(z,('var',c))]
  out=[]
  for cand in self.members.get(self.find(c),{c}):
   if cand[0]!='op':continue
   for lm,lw in self.ematch(p[1],cand[1],mp):
    for rm,rw in self.ematch(p[2],cand[2],lm):out.append((rm,('op',c,cand,lw,rw)))
  return out
 def reps(self,mp):return {v:min(self.members.get(cls,{cls}),key=lambda t:(self.m.term_size(t),self.m.render_term(t))) for v,cls in mp.items()}
 def witness(self,p,w,reps):
  if p[0]=='var':return self.path(w[1],reps[p[1]])
  _,con,cand,lw,rw=w;pre=self.path(con,cand);L=self.witness(p[1],lw,reps);R=self.witness(p[2],rw,reps)
  if pre is None or L is None or R is None:return None
  ln=self.nodes[L];self.nodes.append(self.m.EqualityNode(('op',ln.lhs,cand[2]),('op',ln.rhs,cand[2]),'congruence on left child',parents=(L,),context=('left',cand[2]),constructor='qm'));ll=len(self.nodes)-1
  rn=self.nodes[R];self.nodes.append(self.m.EqualityNode(('op',ln.rhs,rn.lhs),('op',ln.rhs,rn.rhs),'congruence on right child',parents=(R,),context=('right',ln.rhs),constructor='qm'));rr=len(self.nodes)-1
  self.nodes.append(self.m.EqualityNode(self.nodes[ll].lhs,self.nodes[rr].rhs,'transitivity',parents=(ll,rr),constructor='qm'));mid=len(self.nodes)-1
  if self.nodes[pre].lhs==self.nodes[pre].rhs:return mid
  self.nodes.append(self.m.EqualityNode(self.nodes[pre].lhs,self.nodes[mid].rhs,'transitivity',parents=(pre,mid),constructor='qm'));return len(self.nodes)-1
 def paths(self):
  for side in ('left','right'):
   for root in sorted(self.front[side],key=lambda t:(self.m.term_size(t),self.m.render_term(t)))[:32]:
    st=[(root,())]
    while st:
     t,p=st.pop();yield side,root,t,p
     if t[0]=='op':st.append((t[2],p+('R',)));st.append((t[1],p+('L',)))
 def gen(self,cap=128):
  cands=[];seen=set()
  for orient,pat,repl,rev in [('f',self.source[0],self.source[1],False),('r',self.source[1],self.source[0],True)]:
   for side,root,con,path in self.paths():
    if time.monotonic()>=self.deadline:return []
    exactmp={};exact=self.m.match_term(pat,con,exactmp)
    for mp,w in self.ematch(pat,con,{}):
     if set(mp)!=set(self.source[2]):continue
     self.matches+=1
     if exact and set(exactmp)==set(self.source[2]):continue
     self.qonly+=1;reps=self.reps(mp)
     if any(not set(self.m.term_variables(t))<=set(self.target[2]) for t in reps.values()):continue
     after=self.m.replace_subterm(root,path,self.m.substitute(repl,reps));opp=self.target[1] if side=='left' else self.target[0]
     key=(side,path,tuple(sorted(reps.items())))
     if key in seen:continue
     seen.add(key);connect=int(self.find(after)==self.find(opp));score=(-connect,self.m.structural_distance(after,opp),self.m.term_size(after),len(path));cands.append((score,side,pat,repl,rev,root,con,path,reps,w))
  cands.sort(key=lambda x:x[0]);added=[]
  for _,side,pat,repl,rev,root,con,path,reps,w in cands:
   if time.monotonic()>=self.deadline:break
   start=len(self.nodes);pp=self.witness(pat,w,reps)
   if pp is None:del self.nodes[start:];continue
   ip=self.m.substitute(pat,reps);ir=self.m.substitute(repl,reps)
   if self.nodes[pp].rhs!=ip:del self.nodes[start:];continue
   self.nodes.append(self.m.EqualityNode(ip,ir,'source instance',substitution=tuple((v,reps[v]) for v in self.source[2]),orientation=rev,constructor='qm'));sid=len(self.nodes)-1
   self.nodes.append(self.m.EqualityNode(con,ir,'transitivity',parents=(pp,sid),constructor='qm'));seg=len(self.nodes)-1
   lift=self.n.lift_context(self.nodes,seg,root,path);node=self.nodes[lift]
   if max(self.m.term_size(node.lhs),self.m.term_size(node.rhs))>self.maxsize or not self.m.replay_dag(self.source,self.nodes,lift,maximum_term_size=self.maxsize):self.replay_failures+=1;del self.nodes[start:];continue
   self.edge(node.lhs,node.rhs,lift);self.front[side].add(node.rhs);added.append(lift);self.instances+=1
   if len(added)>=cap:break
  self.rebuild();return added
 def solve(self,gens=2,cap=128):
  for g in range(gens):
   self.gen(cap)
   if self.find(self.target[0])==self.find(self.target[1]):
    r=self.path(self.target[0],self.target[1])
    if r is not None and self.m.replay_dag(self.source,self.nodes,r,maximum_term_size=self.maxsize):return self.nodes,r,g+1
   if time.monotonic()>=self.deadline:break
  return None

def run(m,row,seconds,edge,gens):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);st=time.monotonic();q=QM(m,src,tgt,st+seconds,edge);f=q.solve(gens,128);rec={'seconds':round(time.monotonic()-st,6),'edge_cap':edge,'generations':gens,'found':bool(f),'matches':q.matches,'quotient_only':q.qonly,'instances':q.instances,'replay_failures':q.replay_failures,'final_classes':len({q.find(x) for x in q.parent})}
 if f:
  nodes,root,g=f;code,pn=m.make_dag_certificate(tgt,nodes,root);rec.update(proof_nodes=pn,certificate_bytes=len(code.encode()),found_generation=g)
 return rec

def main():
 m=load(SOLVER,'mg_qm0014');row=next(dict(x) for x in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if x['id']==RID)
 arms=[]
 for sec,edge,gens in [(5.0,256,2),(10.0,512,3),(20.0,1024,4)]:
  r=run(m,row,sec,edge,gens);arms.append(r);print(json.dumps(r,sort_keys=True),flush=True)
  if r['found']:break
 out={'schema':'mathgraph.order5-0014-quotient-matcher.v1','id':RID,'protocol':{'constructor_previously_promoted_on_external_audit':True,'all_class_edges_verified':True,'representative_changes_compile_to_proof_paths':True,'all_rewrites_original_source_instances':True,'final_replay_required':True,'progressive_caps_only_after_negative':True},'arms':arms,'decision':'PASS' if any(x['found'] for x in arms) else 'NO_CLOSURE'};OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__':main()
