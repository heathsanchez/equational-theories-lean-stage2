#!/usr/bin/env python3
"""Verifier-gated self-embedding/context-contraction invention gate v2.

The invented object retains the derivation conditions that created it:
source substitution, source orientation, exact embedded endpoint, context path,
and contraction orientation. It is compiled directly to existing trusted proof
primitives (source instances, congruence, transitivity) and replayed before use.
No new trusted inference rule, Vampire proof body, theorem-specific identity, or
answer label is used.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
OUT=ROOT/'experiments/mathgraph/results/verified-self-embedding-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def occurrences(term,needle,path=()):
 out=[]
 if term==needle:out.append(path)
 if term[0]=='op':
  out.extend(occurrences(term[1],needle,path+('L',)));out.extend(occurrences(term[2],needle,path+('R',)))
 return out

def structured_subterms(m,source):
 seen=set();out=[]
 for side in source[:2]:
  for t in m.walk_subterms(side):
   if t[0]=='op' and 2<=m.term_size(t)<=18 and t not in seen:seen.add(t);out.append(t)
 return sorted(out,key=lambda t:(m.term_size(t),m.render_term(t)))

def canonical(m,s):
 names={};return (m.alpha_canonical_term(s[0],names),m.alpha_canonical_term(s[1],names))

def proposals(m,source):
 lhs,rhs,vars_=source;out={}
 for v in vars_:
  for sub in structured_subterms(m,source):
   if v not in m.term_variables(sub):continue
   mp={x:('var',x) for x in vars_};mp[v]=sub
   il=m.substitute(lhs,mp);ir=m.substitute(rhs,mp)
   for base_reverse,start,end in ((False,il,ir),(True,ir,il)):
    for contract_reverse,needle,repl in ((False,lhs,rhs),(True,rhs,lhs)):
     for path in occurrences(end,needle):
      if not path:continue
      changed=m.replace_subterm(end,path,repl)
      if changed==end or changed==start:continue
      vs=tuple(sorted(m.term_variables(start)|m.term_variables(changed)))
      if not vs or len(vs)>7 or max(m.term_size(start),m.term_size(changed))>55:continue
      schema=(start,changed,vs);key=canonical(m,schema)
      out.setdefault(key,{'schema':schema,'mapping':mp,'base_reverse':base_reverse,'contract_reverse':contract_reverse,'needle':needle,'replacement':repl,'end':end,'path':path,'variable':v,'embedded':sub})
 return list(out.values())

def compile_proposal(m,source,target,p):
 cfg=dict(m.NORMALIZATION_PORTFOLIO[1]);normalizer=m.EquationalNormalizer(source,target,time.monotonic()+2,cfg);nodes=[]
 start,changed,_=p['schema'];end=p['end'];vars_=source[2]
 nodes.append(m.EqualityNode(start,end,'source instance',substitution=tuple((x,p['mapping'][x]) for x in vars_),orientation=p['base_reverse'],constructor='self-embedding-base'))
 nodes.append(m.EqualityNode(p['needle'],p['replacement'],'source instance',substitution=tuple((x,('var',x)) for x in vars_),orientation=p['contract_reverse'],constructor='self-embedding-contract'))
 try:lift=normalizer.lift_context(nodes,1,end,p['path'])
 except Exception:return None
 if lift is None or nodes[lift].lhs!=end or nodes[lift].rhs!=changed:return None
 root=len(nodes);nodes.append(m.EqualityNode(start,changed,'transitivity',parents=(0,lift),constructor='verified-self-embedding'))
 if not m.replay_dag(source,nodes,root,maximum_term_size=120,maximum_nodes=1000):return None
 return nodes,root

def activation(m,schema,target):
 score=0
 for pat in schema[:2]:
  if pat[0]=='var':continue
  for side in target[:2]:
   for t in m.walk_subterms(side):
    mp={}
    if m.match_term(pat,t,mp):score+=1
 return score

def append(m,dst,proof):
 nodes,root=proof;off=len(dst)
 for n in nodes:dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or 'verified-self-embedding',derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off+root

def run(m,sym,row,seconds=18.0):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);start=time.monotonic();raw=proposals(m,src);verified=[];rejected=0
 for p in raw:
  pr=compile_proposal(m,src,tgt,p)
  if pr:verified.append((p,pr))
  else:rejected+=1
 verified.sort(key=lambda x:(-activation(m,x[0]['schema'],tgt),m.term_size(x[0]['schema'][0])+m.term_size(x[0]['schema'][1])))
 Norm=sym.make_normalizer(m);cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=max(.5,seconds-(time.monotonic()-start)),candidate_equalities=3600,overlap_candidates=3200,selected_rules=512,replayed_rules=1800,maximum_term_size=70,maximum_proof_nodes=50000)
 search=Norm(src,tgt,start+seconds,cfg);roots=[append(m,search.nodes,pr) for _,pr in verified[:32]];found=search.solve();ok=False;cert=None;pn=None
 if found:
  nodes,root=found;ok=bool(m.replay_dag(src,nodes,root,maximum_term_size=70,maximum_nodes=50000))
  if ok:code,pn=m.make_dag_certificate(tgt,nodes,root);cert=len(code.encode())
 def show(p):
  s=p['schema'];return {'lhs':m.render_term(s[0]),'rhs':m.render_term(s[1]),'activation':activation(m,s,tgt),'variable':p['variable'],'embedded':m.render_term(p['embedded']),'path':''.join(p['path']),'base_reverse':p['base_reverse'],'contract_reverse':p['contract_reverse']}
 return {'closure':ok,'seconds':round(time.monotonic()-start,6),'proposals':len(raw),'verified':len(verified),'rejected_by_replay':rejected,'verified_schemas':[show(p) for p,_ in verified[:32]],'installed':len(roots),'symbolic_rules':len(search.rules),'symbolic_overlaps':search.overlap_candidates,'left_steps':search.left_steps,'right_steps':search.right_steps,'certificate_bytes':cert,'proof_nodes':pn}

def main():
 m=load(SOLVER,'mg_selfembed2');sym=load(SYM,'sym_selfembed2');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.verified-self-embedding.v2','records':[]}
 for rid in IDS:
  try:rec={'id':rid,**run(m,sym,rows[rid])}
  except Exception as e:rec={'id':rid,'closure':False,'error':repr(e)}
  out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['gains']=[r['id'] for r in out['records'] if r.get('closure')];OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains'],'verified_counts':{r['id']:r.get('verified',0) for r in out['records']}},indent=2))
if __name__=='__main__':main()
