#!/usr/bin/env python3
"""Two-generation proof-carrying operator closure on the four frozen residuals.

Generation 1 is the replay-verified self-embedding/context-contraction language.
Generation 2 is generated WITHOUT new theorem-specific identities: source
instances may embed endpoints of verified generation-1 operators, and exact
occurrences of a verified operator endpoint may be contracted through a context.
Every generation-2 macro is compiled back to the original source proof DAG and
must replay before installation. Thus the search language grows while the trust
boundary stays fixed.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OUT=ROOT/'experiments/mathgraph/results/verified-operator-closure-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def copy_nodes(m,src_nodes,dst,tag):
 off=len(dst)
 for n in src_nodes:
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(off+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=n.constructor or tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return off

def canonical(m,lhs,rhs):
 names={};return (m.alpha_canonical_term(lhs,names),m.alpha_canonical_term(rhs,names))

def endpoint_pool(m,source,library):
 seen=set();out=[]
 for t in selfmod.structured_subterms(m,source):
  if t not in seen:seen.add(t);out.append(t)
 for item in library:
  for side in item['schema'][:2]:
   if side[0]=='op' and m.term_size(side)<=28 and side not in seen:
    seen.add(side);out.append(side)
 return sorted(out,key=lambda t:(m.term_size(t),m.render_term(t)))[:48]

def activation(m,lhs,rhs,target):
 return selfmod.activation(m,(lhs,rhs,tuple(sorted(m.term_variables(lhs)|m.term_variables(rhs)))),target)

def build_gen2(m,source,target,library,limit=320):
 lhs,rhs,vars_=source;subs=endpoint_pool(m,source,library);raw={};normalizer=m.EquationalNormalizer(source,target,time.monotonic()+5,dict(m.NORMALIZATION_PORTFOLIO[1]))
 # Source law plus verified g1 laws are admissible contraction operators.
 laws=[{'schema':source,'proof':None,'name':'source'}]+library[:16]
 for v in vars_:
  for sub in subs:
   if v not in m.term_variables(sub):continue
   mp={x:('var',x) for x in vars_};mp[v]=sub
   il=m.substitute(lhs,mp);ir=m.substitute(rhs,mp)
   for base_reverse,start,end in ((False,il,ir),(True,ir,il)):
    for law in laws:
     ll,lr,_=law['schema']
     for rev,needle,repl in ((False,ll,lr),(True,lr,ll)):
      for path in selfmod.occurrences(end,needle):
       if not path:continue
       changed=m.replace_subterm(end,path,repl)
       if changed==end or changed==start:continue
       if max(m.term_size(start),m.term_size(changed))>90:continue
       key=min(canonical(m,start,changed),canonical(m,changed,start))
       if key in raw:continue
       nodes=[]
       nodes.append(m.EqualityNode(start,end,'source instance',substitution=tuple((x,mp[x]) for x in vars_),orientation=base_reverse,constructor='operator-closure-base'))
       if law['proof'] is None:
        nodes.append(m.EqualityNode(needle,repl,'source instance',substitution=tuple((x,('var',x)) for x in vars_),orientation=rev,constructor='operator-closure-source'))
        croot=1
       else:
        pnodes,proot=law['proof'];off=copy_nodes(m,pnodes,nodes,'operator-closure-parent');croot=off+proot
        cn=nodes[croot]
        if rev:
         sid=len(nodes);nodes.append(m.EqualityNode(cn.rhs,cn.lhs,'symmetry',parents=(croot,),constructor='operator-closure-symmetry'));croot=sid
        cn=nodes[croot]
        if cn.lhs!=needle or cn.rhs!=repl:continue
       try:lift=normalizer.lift_context(nodes,croot,end,path)
       except Exception:continue
       if lift is None or nodes[lift].lhs!=end or nodes[lift].rhs!=changed:continue
       root=len(nodes);nodes.append(m.EqualityNode(start,changed,'transitivity',parents=(0,lift),constructor='verified-operator-closure'))
       if not m.replay_dag(source,nodes,root,maximum_term_size=180,maximum_nodes=8000):continue
       raw[key]={'schema':(start,changed,tuple(sorted(m.term_variables(start)|m.term_variables(changed)))),'proof':(nodes,root),'parent':law['name'],'variable':v,'embedded':sub,'path':path,'activation':activation(m,start,changed,target)}
       if len(raw)>=limit:return list(raw.values())
 return list(raw.values())

def append_proof(m,dst,proof):
 nodes,root=proof;off=copy_nodes(m,nodes,dst,'operator-closure-installed');return off+root

def run(m,sym,row,seconds=24.0):
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);started=time.monotonic()
 # G1: compile all valid provenance-carrying source self-embeddings.
 g1=[]
 for p in selfmod.proposals(m,source):
  pr=selfmod.compile_proposal(m,source,target,p)
  if pr:
   s=p['schema'];g1.append({'schema':s,'proof':pr,'name':'g1','activation':selfmod.activation(m,s,target),'meta':p})
 g1.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 # G2: let verified G1 operators participate as exact context contractions.
 g2=build_gen2(m,source,target,g1)
 g2.sort(key=lambda x:(-x['activation'],m.term_size(x['schema'][0])+m.term_size(x['schema'][1])))
 Norm=sym.make_normalizer(m);cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=max(.5,seconds-(time.monotonic()-started)),candidate_equalities=5000,overlap_candidates=4500,selected_rules=700,replayed_rules=2600,maximum_term_size=90,maximum_proof_nodes=70000)
 search=Norm(source,target,started+seconds,cfg)
 roots=[]
 for item in g1[:24]+g2[:56]:roots.append(append_proof(m,search.nodes,item['proof']))
 found=search.solve();ok=False;cert=None;pn=None
 if found:
  nodes,root=found;ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=90,maximum_nodes=70000))
  if ok:code,pn=m.make_dag_certificate(target,nodes,root);cert=len(code.encode())
 return {'closure':ok,'seconds':round(time.monotonic()-started,6),'g1_verified':len(g1),'g2_verified':len(g2),'g2_target_active':sum(x['activation']>0 for x in g2),'g2_parent_counts':{k:sum(x['parent']==k for x in g2) for k in sorted(set(x['parent'] for x in g2))},'installed':len(roots),'symbolic_rules':len(search.rules),'symbolic_overlaps':search.overlap_candidates,'left_steps':search.left_steps,'right_steps':search.right_steps,'certificate_bytes':cert,'proof_nodes':pn,'top_g2':[{'lhs':m.render_term(x['schema'][0]),'rhs':m.render_term(x['schema'][1]),'activation':x['activation'],'parent':x['parent'],'path':''.join(x['path'])} for x in g2[:12]]}

def main():
 global selfmod
 m=load(SOLVER,'mg_opclosure');sym=load(SYM,'sym_opclosure');selfmod=load(SELF,'self_opclosure');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.verified-operator-closure.v1','records':[]}
 for rid in IDS:
  try:rec={'id':rid,**run(m,sym,rows[rid])}
  except Exception as e:rec={'id':rid,'closure':False,'error':repr(e)}
  out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['gains']=[r['id'] for r in out['records'] if r.get('closure')];OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains'],'g2_counts':{r['id']:r.get('g2_verified',0) for r in out['records']}},indent=2))
if __name__=='__main__':main()
