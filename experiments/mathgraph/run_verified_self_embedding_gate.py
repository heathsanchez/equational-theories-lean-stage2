#!/usr/bin/env python3
"""Verifier-gated self-embedding/context-contraction invention gate.

Generic construction only:
1. Take structured subterms already present in the source law.
2. Substitute one such subterm for one source variable in a source instance.
3. If the instantiated endpoint contains an EXACT original source endpoint,
   contract that embedded occurrence using the source law in either direction.
4. Treat the resulting equality only as a proposal.
5. Independently re-prove every proposal from the ORIGINAL source law.
6. Install only replay-verified proposals into the symbolic normalizer and retry.

This mechanically includes the previously independently reconstructed normal_0036
prefix, while invalid skeleton-similar candidates have no authority. No Vampire
proof body, theorem-specific identity, or answer label is used.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
GIVEN=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/verified-self-embedding-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def occurrences(term,needle,path=()):
 out=[]
 if term==needle:out.append(path)
 if term[0]=='op':
  out.extend(occurrences(term[1],needle,path+('L',)))
  out.extend(occurrences(term[2],needle,path+('R',)))
 return out

def structured_subterms(m,source):
 seen=set();out=[]
 for side in source[:2]:
  for t in m.walk_subterms(side):
   if t[0]=='op' and 2<=m.term_size(t)<=18 and t not in seen:
    seen.add(t);out.append(t)
 return sorted(out,key=lambda t:(m.term_size(t),m.render_term(t)))

def canonical(m,s):
 names={};return (m.alpha_canonical_term(s[0],names),m.alpha_canonical_term(s[1],names))

def proposals(m,source):
 lhs,rhs,vars_=source; subs=structured_subterms(m,source); out={}
 for v in vars_:
  for s in subs:
   if v not in m.term_variables(s):continue
   mp={x:('var',x) for x in vars_};mp[v]=s
   il=m.substitute(lhs,mp);ir=m.substitute(rhs,mp)
   for start,end in ((il,ir),(ir,il)):
    # Embedded source endpoint can be contracted in either source direction.
    for needle,repl,orientation in ((lhs,rhs,'forward'),(rhs,lhs,'reverse')):
     for p in occurrences(end,needle):
      if not p:continue
      changed=m.replace_subterm(end,p,repl)
      if changed==end or start==changed:continue
      vs=tuple(sorted(m.term_variables(start)|m.term_variables(changed)))
      if not vs or len(vs)>7:continue
      if max(m.term_size(start),m.term_size(changed))>55:continue
      schema=(start,changed,vs);k=canonical(m,schema)
      out.setdefault(k,(schema,{'variable':v,'embedded':m.render_term(s),'path':''.join(p),'orientation':orientation}))
 return list(out.values())

def activation(m,schema,target):
 score=0
 for pat in schema[:2]:
  if pat[0]=='var':continue
  for side in target[:2]:
   for t in m.walk_subterms(side):
    mp={}
    if m.match_term(pat,t,mp):score+=1
 return score

def prove(m,gate,src,schema,seconds=.8):
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':seconds,'maximum_term_size':70,'maximum_replay_term_size':280,'maximum_depth':13,'maximum_rules':900,'maximum_rounds':80,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':320,'maximum_proof_nodes':50000})
 e=m.TargetGroundedRefutation(src,schema,time.monotonic()+seconds,limits);recipe,st=gate.solve_given(m,e.search)
 if recipe is None:return None,st
 try:
  rr=e.inline_recipe(recipe);cc=m.CompactSuperposition(m,src,schema,time.monotonic()+2,e.search.limits);nodes,root=cc.compile(rr)
  ok=nodes[root].lhs==schema[0] and nodes[root].rhs==schema[1] and m.replay_dag(src,nodes,root,maximum_term_size=280,maximum_nodes=50000)
  return ((nodes,root) if ok else None),st
 except Exception:return None,st

def append(m,dst,proof):
 nodes,root=proof;off=len(dst)
 for n in nodes:
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor='verified-self-embedding',derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off+root

def run(m,sym,gate,row,seconds=20.0):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);start=time.monotonic();ps=proposals(m,src)
 ranked=sorted(ps,key=lambda x:(-activation(m,x[0],tgt),m.term_size(x[0][0])+m.term_size(x[0][1]),m.render_term(x[0][0]),m.render_term(x[0][1])))[:64]
 proved=[];screen=[]
 for schema,meta in ranked:
  if time.monotonic()-start>seconds*.65:break
  pr,st=prove(m,gate,src,schema,.8);screen.append({'lhs':m.render_term(schema[0]),'rhs':m.render_term(schema[1]),'activation':activation(m,schema,tgt),'proved':pr is not None,'meta':meta,'given':st.get('given',0),'generated':st.get('generated',0)})
  if pr:proved.append((schema,pr,meta))
  if len(proved)>=16:break
 Norm=sym.make_normalizer(m);cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=max(.5,seconds-(time.monotonic()-start)),candidate_equalities=2600,overlap_candidates=2400,selected_rules=384,replayed_rules=1200,maximum_term_size=55,maximum_proof_nodes=40000)
 s=Norm(src,tgt,start+seconds,cfg);roots=[append(m,s.nodes,p) for _,p,_ in proved];found=s.solve();ok=False;cert=None;pn=None
 if found:
  nodes,root=found;ok=bool(m.replay_dag(src,nodes,root,maximum_term_size=55,maximum_nodes=40000))
  if ok:code,pn=m.make_dag_certificate(tgt,nodes,root);cert=len(code.encode())
 return {'closure':ok,'seconds':round(time.monotonic()-start,6),'proposals':len(ps),'screened':len(screen),'proved':len(proved),'proved_schemas':[{'lhs':m.render_term(x[0]),'rhs':m.render_term(x[1]),'variables':list(x[2]),'activation':activation(m,x,tgt),'meta':meta} for x,_,meta in proved],'screen':screen,'installed':len(roots),'symbolic_rules':len(s.rules),'symbolic_overlaps':s.overlap_candidates,'left_steps':s.left_steps,'right_steps':s.right_steps,'certificate_bytes':cert,'proof_nodes':pn}

def main():
 m=load(SOLVER,'mg_selfembed');sym=load(SYM,'sym_selfembed');gate=load(GIVEN,'given_selfembed');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.verified-self-embedding.v1','records':[]}
 for rid in IDS:
  try:rec={'id':rid,**run(m,sym,gate,rows[rid])}
  except Exception as e:rec={'id':rid,'closure':False,'error':repr(e)}
  out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['gains']=[r['id'] for r in out['records'] if r.get('closure')];OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains'],'proved_counts':{r['id']:r.get('proved',0) for r in out['records']}},indent=2))
if __name__=='__main__':main()
