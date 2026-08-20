#!/usr/bin/env python3
import importlib.util, json, re, sys, time, urllib.request
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
OUT=ROOT/'experiments/mathgraph/results/five-residual-operator-attribution.json'
IDS={'evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196','evaluation_order5_0014','evaluation_order5_0042'}
CONFIGS=['evaluation_normal','evaluation_hard','evaluation_order5']

def load_solver():
 spec=importlib.util.spec_from_file_location('mg_attr',SOLVER); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m
class P:
 def __init__(self,s): self.s,self.i=s,0
 def ws(self):
  while self.i<len(self.s) and self.s[self.i].isspace(): self.i+=1
 def name(self):
  self.ws(); j=self.i
  while self.i<len(self.s) and (self.s[self.i].isalnum() or self.s[self.i] in '_$@'): self.i+=1
  if self.i==j: raise ValueError('name')
  return self.s[j:self.i]
 def term(self):
  n=self.name(); self.ws()
  if self.i<len(self.s) and self.s[self.i]=='(':
   self.i+=1; a=self.term(); self.ws();
   if self.s[self.i]!=',': raise ValueError('comma')
   self.i+=1; b=self.term(); self.ws();
   if self.s[self.i]!=')': raise ValueError('close')
   self.i+=1
   if n!='f': raise ValueError('non-f')
   return ('op',a,b)
  return ('var',n)
def parse_term(s):
 p=P(s.strip()); t=p.term(); p.ws();
 if p.i!=len(p.s): raise ValueError('trailing')
 return t
def strip_outer(s):
 s=s.strip(); changed=True
 while changed and len(s)>=2 and s[0]=='(' and s[-1]==')':
  depth=0; changed=False
  for i,c in enumerate(s):
   if c=='(': depth+=1
   elif c==')':
    depth-=1
    if depth==0:
     if i==len(s)-1: s=s[1:-1].strip(); changed=True
     break
 return s
def split_top(s,sep=','):
 out=[]; start=0; d=b=0
 for i,c in enumerate(s):
  if c=='(': d+=1
  elif c==')': d-=1
  elif c=='[': b+=1
  elif c==']': b-=1
  elif c==sep and d==0 and b==0: out.append(s[start:i].strip()); start=i+1
 out.append(s[start:].strip()); return out
def fof_blocks(proof):
 out=[]; start=0
 while True:
  i=proof.find('fof(',start)
  if i<0: break
  d=0; j=i+3
  while j<len(proof):
   if proof[j]=='(': d+=1
   elif proof[j]==')':
    d-=1
    if d==0: out.append(proof[i:j+1]); start=j+1; break
   j+=1
  else: break
 return out
def formula_eq(f):
 s=strip_outer(f); q=re.match(r'^[!?]\s*\[[^\]]*\]\s*:\s*(.*)$',s,re.S)
 if q:s=strip_outer(q.group(1))
 d=0
 for i,c in enumerate(s):
  if c=='(': d+=1
  elif c==')': d-=1
  elif c=='=' and d==0 and not(i and s[i-1]=='!'): return parse_term(s[:i]),parse_term(s[i+1:])
 return None
def inline_defs(t,defs,seen=None):
 seen=set() if seen is None else seen
 if t[0]=='var' and t[1] in defs and t[1] not in seen:return inline_defs(defs[t[1]],defs,seen|{t[1]})
 if t[0]=='op':return ('op',inline_defs(t[1],defs,seen),inline_defs(t[2],defs,seen))
 return t
def map_rigids(t,tvars):
 if t[0]=='var':
  q=re.fullmatch(r'sK(\d+)',t[1])
  if q:
   i=int(q.group(1)); return ('var','@'+(tvars[i] if i<len(tvars) else 'sk'+str(i)))
  return t
 return ('op',map_rigids(t[1],tvars),map_rigids(t[2],tvars))
def inline_names(t,rev,seen=None):
 seen=set() if seen is None else seen
 if t[0]=='var' and t[1] in rev and t[1] not in seen:return inline_names(rev[t[1]],rev,seen|{t[1]})
 if t[0]=='op':return ('op',inline_names(t[1],rev,seen),inline_names(t[2],rev,seen))
 return t
def sig(m,a,b):
 names={}; x=m.alpha_canonical_term(a,names); y=m.alpha_canonical_term(b,names); return min((x,y),(y,x))
def covers(m,sa,sb,ta,tb):
 for x,y in ((sa,sb),(sb,sa)):
  mp={}
  if m.match_term(x,ta,mp) and m.match_term(y,tb,mp): return True
 return False
def first_missing(m,proof,target,student):
 defs={}
 for block in fof_blocks(proof):
  parts=split_top(block[4:-1]);
  if len(parts)<3: continue
  fid,kind,formula=parts[:3]; tail=parts[3:]
  try:eq=formula_eq(formula)
  except: eq=None
  if eq is None: continue
  a,b=eq
  if kind=='definition':
   if a[0]=='var' and a[1].startswith('sF'): defs[a[1]]=b
   elif b[0]=='var' and b[1].startswith('sF'): defs[b[1]]=a
   continue
  mi=re.search(r'inference\(([^,\]]+)',','.join(tail)); inf=mi.group(1) if mi else ''
  if inf not in ('superposition','forward_demodulation'):continue
  a=map_rigids(inline_defs(a,defs),target[2]); b=map_rigids(inline_defs(b,defs),target[2])
  exact=any(sig(m,a,b)==sig(m,sa,sb) for sa,sb in student)
  present=exact or any(covers(m,sa,sb,a,b) for sa,sb in student)
  if not present:return {'id':fid,'inference':inf,'lhs':a,'rhs':b}
 return None

def main():
 m=load_solver(); rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r.get('id') in IDS:rows[r['id']]=r
 trace=json.load(urllib.request.urlopen(TRACE_URL)); proofs={r['id']:r['proof'] for r in trace['rows']}
 results=[]
 for rid in sorted(IDS):
  r=rows[rid]; src=m.parse_equation(r['equation1']); tgt=m.parse_equation(r['equation2'])
  limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':12.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
  eng=m.TargetGroundedRefutation(src,tgt,time.monotonic()+12.0,limits); eng.solve()
  student=[(inline_names(c.lhs,eng.reverse_constants),inline_names(c.rhs,eng.reverse_constants)) for c in eng.search.clauses]
  fm=first_missing(m,proofs[rid],tgt,student)
  if fm is None: raise RuntimeError(rid+' has no missing step')
  ta,tb=fm['lhs'],fm['rhs']; target_sig=sig(m,ta,tb)
  rules=list(eng.search.rules())
  demod_hit=None; demod_examined=0
  t0=time.monotonic()
  for ci,c in enumerate(list(eng.search.clauses)):
   if time.monotonic()-t0>8: break
   try:q=eng.search.interreduce(c,rules)
   except Exception:continue
   demod_examined+=1
   if q is None:continue
   qa=inline_names(q.lhs,eng.reverse_constants); qb=inline_names(q.rhs,eng.reverse_constants)
   if sig(m,qa,qb)==target_sig or covers(m,qa,qb,ta,tb):
    demod_hit={'clause_index':ci,'lhs':m.render_term(qa),'rhs':m.render_term(qb),'kind':getattr(q,'kind',None)}; break
  cp_hit=None; cp_calls=cp_nonnull=0; deadline=time.monotonic()+12.0
  for oi,outer in enumerate(rules):
   if cp_hit or time.monotonic()>=deadline:break
   for ii,inner in enumerate(rules):
    if cp_hit or time.monotonic()>=deadline:break
    for path in m.nonvariable_positions(outer.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
     if time.monotonic()>=deadline:break
     cp_calls+=1
     try:q=eng.search.critical_pair(outer,inner,oi,ii,path)
     except Exception:continue
     if q is None:continue
     cp_nonnull+=1
     qa=inline_names(q.lhs,eng.reverse_constants); qb=inline_names(q.rhs,eng.reverse_constants)
     if sig(m,qa,qb)==target_sig or covers(m,qa,qb,ta,tb):
      cp_hit={'outer_index':oi,'inner_index':ii,'path':list(path),'lhs':m.render_term(qa),'rhs':m.render_term(qb),'kind':getattr(q,'kind',None)}; break
  rec={'id':rid,'first_missing':{'id':fm['id'],'inference':fm['inference'],'lhs':m.render_term(ta),'rhs':m.render_term(tb)},'rules':len(rules),'clauses':len(eng.search.clauses),'demod_examined':demod_examined,'demod_hit':demod_hit,'critical_pair_calls':cp_calls,'critical_pair_nonnull':cp_nonnull,'critical_pair_hit':cp_hit}
  results.append(rec); print(json.dumps(rec,sort_keys=True),flush=True)
 out={'schema':'mathgraph.five-residual-operator-attribution.v1','rows':results,'summary':{'demod_hits':[x['id'] for x in results if x['demod_hit']],'critical_pair_hits':[x['id'] for x in results if x['critical_pair_hit']]}}
 OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out['summary'],indent=2,sort_keys=True))
if __name__=='__main__':main()
