#!/usr/bin/env python3
"""Bidirectional search over replay-verified proof-carrying operators v2.

A verified proof operator may need free parameters not fixed by the matched
subterm. v2 makes that completion policy explicit: missing variables are filled
from a small residual vocabulary built only from target/current terms. Every
completed rewrite is compiled to the original source proof DAG, lifted through
its exact context, replayed, and only then added as a search edge.

No theorem-specific identities, external proof traces, or answer labels enter
the operator language or completion vocabulary.
"""
import importlib.util,json,sys,time
from itertools import product
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
OUT=ROOT/'experiments/mathgraph/results/bidirectional-proof-operator-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def all_proof_vars(m,nodes):
 out=set()
 for n in nodes:
  out|=m.term_variables(n.lhs)|m.term_variables(n.rhs)
  for _,v in n.substitution:out|=m.term_variables(v)
  if n.context and isinstance(n.context,tuple) and len(n.context)>1 and isinstance(n.context[1],tuple):out|=m.term_variables(n.context[1])
 return out

def subst_context(m,c,mp):
 if not c:return c
 if isinstance(c,tuple) and len(c)>1 and isinstance(c[1],tuple) and c[1] and c[1][0] in ('var','op'):
  return (c[0],m.substitute(c[1],mp))
 return c

def instantiate_proof(m,source,proof,mapping,target_vars):
 nodes,root=proof;allv=all_proof_vars(m,nodes);expanded=dict(mapping)
 fallback=next(iter(mapping.values()),('var',target_vars[0]))
 for v in allv:expanded.setdefault(v,fallback)
 out=[]
 try:
  for n in nodes:
   out.append(m.EqualityNode(m.substitute(n.lhs,expanded),m.substitute(n.rhs,expanded),n.kind,parents=n.parents,substitution=tuple((v,m.substitute(val,expanded)) for v,val in n.substitution),context=subst_context(m,n.context,expanded),orientation=n.orientation,generation=n.generation,term_origins=(),constructor=n.constructor or 'bidirectional-proof-operator',derivation_depth=n.derivation_depth,context_record=None,overlap_record=None))
 except Exception:return None
 if not m.replay_dag(source,out,root,maximum_term_size=260,maximum_nodes=16000):return None
 return out,root

def make_source_proof(m,source):
 lhs,rhs,vars_=source
 node=m.EqualityNode(lhs,rhs,'source instance',substitution=tuple((v,('var',v)) for v in vars_),orientation=False,constructor='source-law')
 return (lhs,rhs,vars_),([node],0)

def library(m,selfmod,opmod,source,target):
 g1=[]
 for p in selfmod.proposals(m,source):
  pr=selfmod.compile_proposal(m,source,target,p)
  if pr:g1.append({'schema':p['schema'],'proof':pr,'generation':1})
 g1.sort(key=lambda x:(-selfmod.activation(m,x['schema'],target),m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 g2=opmod.build_gen2(m,source,target,[{'schema':x['schema'],'proof':x['proof'],'name':'g1','activation':0,'meta':None} for x in g1[:20]],limit=420)
 g2=[{'schema':x['schema'],'proof':x['proof'],'generation':2} for x in g2]
 ss,sp=make_source_proof(m,source);items=[{'schema':ss,'proof':sp,'generation':0}]+g1[:48]+g2[:140]
 out=[];seen=set()
 for x in items:
  l,r,_=x['schema'];names={};k=(m.alpha_canonical_term(l,names),m.alpha_canonical_term(r,names))
  if k in seen:continue
  seen.add(k);out.append(x)
 return out,len(g1),len(g2)

def paths(m,term,depth=8):
 if term[0]!='op':return [()]
 return [()]+[p for p in m.nonvariable_positions(term,depth,include_root=False)]

def vocabulary(m,target,current,cap=8):
 vals=[];seen=set()
 for v in target[2]:
  t=('var',v)
  if t not in seen:seen.add(t);vals.append(t)
 for side in target[:2]:
  for t in m.walk_subterms(side):
   if m.term_size(t)<=11 and t not in seen:seen.add(t);vals.append(t)
 for t in m.walk_subterms(current):
  if m.term_size(t)<=9 and t not in seen:seen.add(t);vals.append(t)
 vals.sort(key=lambda t:(m.term_size(t),m.render_term(t)))
 return vals[:cap]

def completions(m,pattern,repl,concrete,target,current,cap=32):
 base={}
 if not m.match_term(pattern,concrete,base):return []
 missing=sorted(m.term_variables(repl)-set(base))
 if len(missing)>3:return []
 if not missing:return [(base,0)]
 pool=vocabulary(m,target,current,8)
 out=[]
 for fill in product(pool,repeat=len(missing)):
  mp=dict(base);mp.update(zip(missing,fill));out.append((mp,len(missing)))
  if len(out)>=cap:break
 return out

def compile_rewrite(m,source,target,whole,path,rule,reverse,mp):
 lhs,rhs,_=rule['schema'];pattern,repl=(rhs,lhs) if reverse else (lhs,rhs)
 concrete=m.get_subterm(whole,path);inst=m.substitute(repl,mp);new=m.replace_subterm(whole,path,inst)
 if new==whole or m.term_size(new)>120:return None
 pr=instantiate_proof(m,source,rule['proof'],mp,target[2])
 if pr is None:return None
 nodes,root=pr;rn=nodes[root]
 if reverse:
  sid=len(nodes);nodes.append(m.EqualityNode(rn.rhs,rn.lhs,'symmetry',parents=(root,),constructor='bidirectional-proof-operator'));root=sid;rn=nodes[root]
 if rn.lhs!=concrete or rn.rhs!=inst:return None
 normalizer=m.EquationalNormalizer(source,(whole,new,target[2]),time.monotonic()+2,dict(m.NORMALIZATION_PORTFOLIO[1]))
 try:lift=normalizer.lift_context(nodes,root,whole,path)
 except Exception:return None
 if nodes[lift].lhs!=whole or nodes[lift].rhs!=new:return None
 if not m.replay_dag(source,nodes,lift,maximum_term_size=260,maximum_nodes=16000):return None
 return new,(nodes,lift)

def append_edge(m,graph,proof):
 nodes,root=proof;off=len(graph.nodes);rid=None
 for i,n in enumerate(nodes):
  nn=m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record)
  if i==root:rid=graph.add_node(nn,graph_edge=True)
  else:graph.nodes.append(nn)
 return rid

def run(m,selfmod,opmod,row,seconds=24.0):
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);started=time.monotonic();rules,g1n,g2n=library(m,selfmod,opmod,source,target);limits={'max_term_size':140,'max_derivation_nodes':120000,'max_graph_edges':12000};graph=m.EqualitySearch(source,target,started+seconds,limits)
 frontier=[target[0],target[1]];seen={target[0],target[1]};generated=0;replay_edges=0;rounds=0;bygen={0:0,1:0,2:0};completed_edges=0;best_distance=m.structural_distance(target[0],target[1])
 for rnd in range(8):
  rounds=rnd+1;cands=[]
  for term in frontier:
   if time.monotonic()>=started+seconds:break
   for rule in rules:
    for rev in (False,True):
     pat,rep=(rule['schema'][1],rule['schema'][0]) if rev else (rule['schema'][0],rule['schema'][1])
     for path in paths(m,term):
      try:concrete=m.get_subterm(term,path)
      except Exception:continue
      for mp,missing_n in completions(m,pat,rep,concrete,target,term,32):
       try:new=m.replace_subterm(term,path,m.substitute(rep,mp))
       except Exception:continue
       if new==term or m.term_size(new)>120:continue
       d=min(m.structural_distance(new,target[0]),m.structural_distance(new,target[1]));best_distance=min(best_distance,d)
       score=(d,m.term_size(new),missing_n,rule['generation'],len(path),m.render_term(new))
       cands.append((score,term,path,rule,rev,new,mp,missing_n));generated+=1
       if len(cands)>=12000:break
      if len(cands)>=12000:break
     if len(cands)>=12000:break
    if len(cands)>=12000:break
   if len(cands)>=12000:break
  cands.sort(key=lambda x:x[0]);newfront=[];used=set()
  for _,term,path,rule,rev,new,mp,missing_n in cands[:1200]:
   key=(term,new)
   if key in used:continue
   used.add(key);compiled=compile_rewrite(m,source,target,term,path,rule,rev,mp)
   if compiled is None:continue
   new2,proof=compiled
   if append_edge(m,graph,proof) is not None:
    replay_edges+=1;bygen[rule['generation']]+=1;completed_edges+=int(missing_n>0)
   if new2 not in seen:seen.add(new2);newfront.append(new2)
   if replay_edges and replay_edges%50==0:
    root=graph.shortest_path()
    if root is not None and m.replay_dag(source,graph.nodes,root,maximum_term_size=260,maximum_nodes=120000):
     code,pn=m.make_dag_certificate(target,graph.nodes,root);return {'closure':True,'seconds':round(time.monotonic()-started,6),'g1_verified':g1n,'g2_verified':g2n,'rules':len(rules),'rounds':rounds,'states':len(seen),'candidates':generated,'replay_edges':replay_edges,'completion_edges':completed_edges,'edge_generation':bygen,'best_distance':best_distance,'proof_nodes':pn,'certificate_bytes':len(code.encode())}
  frontier=newfront[:900]
  root=graph.shortest_path()
  if root is not None and m.replay_dag(source,graph.nodes,root,maximum_term_size=260,maximum_nodes=120000):
   code,pn=m.make_dag_certificate(target,graph.nodes,root);return {'closure':True,'seconds':round(time.monotonic()-started,6),'g1_verified':g1n,'g2_verified':g2n,'rules':len(rules),'rounds':rounds,'states':len(seen),'candidates':generated,'replay_edges':replay_edges,'completion_edges':completed_edges,'edge_generation':bygen,'best_distance':best_distance,'proof_nodes':pn,'certificate_bytes':len(code.encode())}
  if not frontier or time.monotonic()>=started+seconds:break
 return {'closure':False,'seconds':round(time.monotonic()-started,6),'g1_verified':g1n,'g2_verified':g2n,'rules':len(rules),'rounds':rounds,'states':len(seen),'candidates':generated,'replay_edges':replay_edges,'completion_edges':completed_edges,'edge_generation':bygen,'best_distance':best_distance,'exhaustion':graph.exhaustion}

def main():
 m=load(SOLVER,'mg_bidir2');selfmod=load(SELF,'self_bidir2');opmod=load(OPC,'op_bidir2');opmod.selfmod=selfmod;rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.bidirectional-proof-operator.v2','records':[]}
 for rid in IDS:
  try:rec={'id':rid,**run(m,selfmod,opmod,rows[rid])}
  except Exception as e:rec={'id':rid,'closure':False,'error':repr(e)}
  out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['gains']=[r['id'] for r in out['records'] if r.get('closure')];OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains']},indent=2))
if __name__=='__main__':main()
