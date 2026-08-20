#!/usr/bin/env python3
"""Residual-induced cut invention gate.

The operator family is not selected up front. We first build two replay-gated
reachable components from the two target sides using the already frozen verified
operator library.  The residual is their failure to meet.  For the closest
cross-component pairs we factor their largest shared one-hole context; the two
subterms in the hole become a *derived bridge obligation*.  Only bridge
obligations independently proved from the original source law are promoted as
lemmas.  Those proved cuts are then installed into a fresh symbolic search.

Thus the experimental map is:
  residual component gap -> necessary local bridge obligation -> verified cut
  -> retry target.
No Vampire proof body, theorem-specific identity, or answer label is used.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
BIDIR=ROOT/'experiments/mathgraph/run_bidirectional_proof_operator_gate.py'
SELF=ROOT/'experiments/mathgraph/run_verified_self_embedding_gate.py'
OPC=ROOT/'experiments/mathgraph/run_verified_operator_closure_gate.py'
SCHEMA=ROOT/'experiments/mathgraph/run_verified_schema_induction_gate.py'
SYM=ROOT/'experiments/mathgraph/run_symbolic_superposition_research.py'
GIVEN=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-cut-induction-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def diff_path(a,b,path=()):
 if a==b:return None
 if a[0]=='op' and b[0]=='op':
  ld=a[1]!=b[1];rd=a[2]!=b[2]
  if ld and not rd:return diff_path(a[1],b[1],path+('L',)) or path+('L',)
  if rd and not ld:return diff_path(a[2],b[2],path+('R',)) or path+('R',)
 return path

def expand_component(m,bidir,rules,source,target,start,deadline,rounds=3,cap=380):
 seen={start};front=[start];replayed=0
 for _ in range(rounds):
  if time.monotonic()>=deadline:break
  cand=[]
  for term in front[:220]:
   if time.monotonic()>=deadline:break
   for rule in rules:
    for rev in (False,True):
     pat,rep=(rule['schema'][1],rule['schema'][0]) if rev else (rule['schema'][0],rule['schema'][1])
     for path in bidir.paths(m,term,7):
      try:concrete=m.get_subterm(term,path)
      except Exception:continue
      for mp,missing in bidir.completions(m,pat,rep,concrete,target,term,12):
       try:new=m.replace_subterm(term,path,m.substitute(rep,mp))
       except Exception:continue
       if new==term or new in seen or m.term_size(new)>105:continue
       d=min(m.structural_distance(new,target[0]),m.structural_distance(new,target[1]))
       cand.append(((d,m.term_size(new),missing,rule['generation'],len(path)),term,path,rule,rev,mp))
       if len(cand)>=3200:break
      if len(cand)>=3200:break
     if len(cand)>=3200:break
    if len(cand)>=3200:break
   if len(cand)>=3200:break
  cand.sort(key=lambda x:x[0]);nf=[]
  for _,term,path,rule,rev,mp in cand:
   if len(nf)>=cap or time.monotonic()>=deadline:break
   compiled=bidir.compile_rewrite(m,source,target,term,path,rule,rev,mp)
   if compiled is None:continue
   new,_=compiled
   if new in seen:continue
   seen.add(new);nf.append(new);replayed+=1
  front=nf
  if not front:break
 return list(seen),replayed

def closest_obligations(m,left,right,target,limit=16):
 # Compare compact representatives; prefer a small local hole inside a deep
 # common context over simply restating the full target.
 L=sorted(left,key=lambda t:(min(m.structural_distance(t,target[0]),m.structural_distance(t,target[1])),m.term_size(t)))[:240]
 R=sorted(right,key=lambda t:(min(m.structural_distance(t,target[0]),m.structural_distance(t,target[1])),m.term_size(t)))[:240]
 best=[];seen=set()
 for a in L:
  for b in R:
   if a==b:continue
   d=m.structural_distance(a,b)
   p=diff_path(a,b)
   if p is None:continue
   try:u=m.get_subterm(a,p);v=m.get_subterm(b,p)
   except Exception:continue
   if u==v:continue
   vars_=tuple(sorted(m.term_variables(u)|m.term_variables(v)))
   if not vars_ or max(m.term_size(u),m.term_size(v))>48:continue
   # Exclude the original theorem itself; the residual must induce a smaller cut.
   if (u==target[0] and v==target[1]) or (u==target[1] and v==target[0]):continue
   names={};k=(m.alpha_canonical_term(u,names),m.alpha_canonical_term(v,names))
   if k in seen:continue
   seen.add(k)
   score=(d,m.term_size(u)+m.term_size(v),-len(p),m.term_size(a)+m.term_size(b))
   best.append((score,a,b,p,(u,v,vars_)))
 best.sort(key=lambda x:x[0])
 return best[:limit]

def run(m,bidir,selfmod,opmod,schema,sym,given,row,seconds=42.0):
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);started=time.monotonic()
 rules,g1n,g2n=bidir.library(m,selfmod,opmod,source,target)
 dl=started+seconds*.50
 left,le=expand_component(m,bidir,rules,source,target,target[0],dl,3,360)
 right,re=expand_component(m,bidir,rules,source,target,target[1],dl,3,360)
 exact=len(set(left)&set(right))
 obs=closest_obligations(m,left,right,target,18)
 proved=[];screen=[]
 for score,a,b,path,cut in obs:
  if time.monotonic()-started>seconds*.72:break
  proof,st=schema.prove_schema(m,given,source,cut,1.35)
  rec={'lhs':m.render_term(cut[0]),'rhs':m.render_term(cut[1]),'context_depth':len(path),'cross_distance':score[0],'proved':proof is not None,'given':st.get('given',0),'generated':st.get('generated',0)}
  screen.append(rec)
  if proof is not None:
   proved.append((cut,proof,rec))
   if len(proved)>=8:break
 # The new meta-language is "verified residual cuts": only obligations selected
 # by the component gap and proved independently receive authority.
 Norm=sym.make_normalizer(m);cfg=dict(m.NORMALIZATION_PORTFOLIO[3]);cfg.update(source_substitutions=0,seconds=max(.6,seconds-(time.monotonic()-started)),candidate_equalities=3000,overlap_candidates=2600,selected_rules=420,replayed_rules=1400,maximum_term_size=48,maximum_proof_nodes=60000)
 s=Norm(source,target,started+seconds,cfg);roots=[]
 for cut,proof,_ in proved:roots.append(schema.append_proof(m,s.nodes,proof,'residual-induced-cut'))
 found=s.solve();ok=False;cert=None;pn=None
 if found is not None:
  nodes,root=found;ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=60000))
  if ok:
   code,pn=m.make_dag_certificate(target,nodes,root);cert=len(code.encode())
 return {'closure':ok,'seconds':round(time.monotonic()-started,6),'g1_verified':g1n,'g2_verified':g2n,'left_states':len(left),'right_states':len(right),'left_replayed':le,'right_replayed':re,'exact_component_intersection':exact,'bridge_obligations':len(obs),'cuts_screened':len(screen),'cuts_proved':len(proved),'proved_cuts':[x[2] for x in proved],'screen':screen,'installed_cut_roots':len(roots),'symbolic_rules':len(s.rules),'selected_rules':len(s.selected_rules),'left_steps':s.left_steps,'right_steps':s.right_steps,'replay_failures':s.replay_failures,'certificate_bytes':cert,'proof_nodes':pn}

def main():
 m=load(SOLVER,'mg_cut');b=load(BIDIR,'bidir_cut');se=load(SELF,'self_cut');op=load(OPC,'op_cut');op.selfmod=se;sc=load(SCHEMA,'schema_cut');sy=load(SYM,'sym_cut');gv=load(GIVEN,'given_cut');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.residual-cut-induction.v1','records':[]}
 for rid in IDS:
  try:rec={'id':rid,**run(m,b,se,op,sc,sy,gv,rows[rid])}
  except Exception as e:rec={'id':rid,'closure':False,'error':repr(e)}
  out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['gains']=[r['id'] for r in out['records'] if r.get('closure')]
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains'],'proved_cuts':{r['id']:r.get('cuts_proved',0) for r in out['records']}},indent=2))
if __name__=='__main__':main()
