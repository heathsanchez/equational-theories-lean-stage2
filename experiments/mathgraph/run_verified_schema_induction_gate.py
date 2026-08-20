#!/usr/bin/env python3
"""Residual-driven abstraction invention with verifier-gated schema promotion.

1. Generate replay-verified quotient-derived instances.
2. Anti-unify pairs of derived equalities to propose schematic equations.
3. Independently prove each proposed schema from the ORIGINAL source law.
4. Install only proved schemas into a symbolic normalizer and retry the target.

No Vampire proof bodies, theorem-specific identities, or answer labels are used.
A proposed abstraction has no authority until its proof DAG replays.
"""
import importlib.util,json,sys,time,itertools
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
QM=ROOT/'experiments/mathgraph/run_quotient_matcher_research.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
GIVEN=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/verified-schema-induction-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def lgg(a,b,memo,counter):
 if a==b:return a
 key=(a,b)
 if key in memo:return memo[key]
 if a[0]=='op' and b[0]=='op':
  out=('op',lgg(a[1],b[1],memo,counter),lgg(a[2],b[2],memo,counter));memo[key]=out;return out
 name=f'z{counter[0]}';counter[0]+=1;out=('var',name);memo[key]=out;return out

def anti_equation(m,a,b,reverse_b=False):
 bl,br=(b.rhs,b.lhs) if reverse_b else (b.lhs,b.rhs);memo={};counter=[0];lhs=lgg(a.lhs,bl,memo,counter);rhs=lgg(a.rhs,br,memo,counter)
 if lhs==rhs:return None
 vars_=tuple(sorted(m.term_variables(lhs)|m.term_variables(rhs)))
 if not vars_ or len(vars_)>6:return None
 # Reject maximally unconstrained x=y and huge patterns.
 if m.term_size(lhs)+m.term_size(rhs)<5:return None
 if max(m.term_size(lhs),m.term_size(rhs))>31:return None
 return (lhs,rhs,vars_)

def activation_score(m,schema,target):
 score=0
 for pat in schema[:2]:
  for side in target[:2]:
   for t in m.walk_subterms(side):
    mp={}
    if m.match_term(pat,t,mp):score+=1
 return score

def prove_schema(m,gate,source,schema,seconds=0.45):
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':seconds,'maximum_term_size':45,'maximum_replay_term_size':180,'maximum_depth':10,'maximum_rules':512,'maximum_rounds':48,'new_clauses_per_round':192,'maximum_clauses':3500,'normalization_steps':192,'maximum_proof_nodes':12000})
 e=m.TargetGroundedRefutation(source,schema,time.monotonic()+seconds,limits);recipe,stats=gate.solve_given(m,e.search)
 if recipe is None:return None,stats
 try:
  rr=e.inline_recipe(recipe);cc=m.CompactSuperposition(m,source,schema,time.monotonic()+1.0,e.search.limits);nodes,root=cc.compile(rr)
  ok=nodes[root].lhs==schema[0] and nodes[root].rhs==schema[1] and m.replay_dag(source,nodes,root,maximum_term_size=limits['maximum_replay_term_size'],maximum_nodes=limits['maximum_proof_nodes'])
  return ((nodes,root) if ok else None),stats
 except Exception:return None,stats

def append_proof(m,dst,proof,tag):
 nodes,root=proof;offset=len(dst)
 for n in nodes:
  dst.append(m.EqualityNode(n.lhs,n.rhs,n.kind,parents=tuple(offset+p for p in n.parents),substitution=n.substitution,context=n.context,orientation=n.orientation,generation=n.generation,term_origins=n.term_origins,constructor=tag,derivation_depth=n.derivation_depth,context_record=n.context_record,overlap_record=n.overlap_record))
 return offset+root

def run(m,qm,sym,gate,row,seconds=18.0):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2']);started=time.monotonic()
 q=qm.QuotientMatcher(m,src,tgt,started+min(5.0,seconds*.3),edge_cap=384);added=[]
 for g in range(2):
  q.generations=g+1;added.extend(q.one_generation(160))
  if time.monotonic()>=q.deadline:break
 # Prefer concise derived equalities for generalization.
 ids=sorted(set(added),key=lambda i:(m.term_size(q.nodes[i].lhs)+m.term_size(q.nodes[i].rhs),m.render_term(q.nodes[i].lhs),m.render_term(q.nodes[i].rhs)))[:28]
 candidates={}
 for ia,ib in itertools.combinations(ids,2):
  for rev in (False,True):
   s=anti_equation(m,q.nodes[ia],q.nodes[ib],rev)
   if s is None:continue
   names={};key=(m.alpha_canonical_term(s[0],names),m.alpha_canonical_term(s[1],names))
   if key in candidates:continue
   candidates[key]=s
 ranked=sorted(candidates.values(),key=lambda s:(-activation_score(m,s,tgt),len(s[2]),m.term_size(s[0])+m.term_size(s[1]),m.render_term(s[0]),m.render_term(s[1])))[:32]
 proved=[];proof_stats=[]
 for schema in ranked:
  if time.monotonic()-started>seconds*.72:break
  proof,st=prove_schema(m,gate,src,schema,0.45);proof_stats.append({'activation':activation_score(m,schema,tgt),'proved':proof is not None,'given':st.get('given',0),'generated':st.get('generated',0)})
  if proof is not None:
   proved.append((schema,proof))
   if len(proved)>=8:break
 Norm=sym.make_normalizer(m);cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=max(.5,seconds-(time.monotonic()-started)),candidate_equalities=1800,overlap_candidates=1600,selected_rules=256,replayed_rules=800,maximum_term_size=35,maximum_proof_nodes=20000)
 s=Norm(src,tgt,started+seconds,cfg)
 schema_roots=[]
 for schema,proof in proved:schema_roots.append(append_proof(m,s.nodes,proof,'verified-induced-schema'))
 found=s.solve();ok=False;cert=None;pn=None
 if found is not None:
  nodes,root=found;ok=bool(m.replay_dag(src,nodes,root,maximum_term_size=35,maximum_nodes=20000))
  if ok:code,pn=m.make_dag_certificate(tgt,nodes,root);cert=len(code.encode())
 return {'closure':ok,'seconds':round(time.monotonic()-started,6),'quotient_instances':q.instances,'quotient_only':q.quotient_only,'derived_instances_considered':len(ids),'schemas_proposed':len(candidates),'schemas_screened':len(proof_stats),'schemas_proved':len(proved),'proved_schemas':[{'lhs':m.render_term(x[0]),'rhs':m.render_term(x[1]),'variables':list(x[2]),'activation':activation_score(m,x,tgt)} for x,_ in proved],'proof_stats':proof_stats,'installed_schema_roots':len(schema_roots),'symbolic_overlaps':s.overlap_candidates,'symbolic_rules':len(s.rules),'selected_rules':len(s.selected_rules),'left_steps':s.left_steps,'right_steps':s.right_steps,'symbolic_replay_failures':s.replay_failures,'certificate_bytes':cert,'proof_nodes':pn}

def main():
 m=load(SOLVER,'mg_schema');qm=load(QM,'qm_schema');sym=load(SYM,'sym_schema');gate=load(GIVEN,'given_schema');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.verified-schema-induction.v1','records':[]}
 for rid in IDS:
  try:rec={'id':rid,**run(m,qm,sym,gate,rows[rid])}
  except Exception as e:rec={'id':rid,'closure':False,'error':repr(e)}
  out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['gains']=[r['id'] for r in out['records'] if r.get('closure')];out['invented']={r['id']:r.get('proved_schemas',[]) for r in out['records'] if r.get('schemas_proved',0)}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains'],'invented_counts':{k:len(v) for k,v in out['invented'].items()}},indent=2))
if __name__=='__main__':main()
