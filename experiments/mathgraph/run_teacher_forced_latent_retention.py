#!/usr/bin/env python3
# Diagnostic only: Vampire identifies the first missing transition; MathGraph must generate it itself.
import importlib.util,json,re,sys,time,urllib.request
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]; SOLVER=ROOT/'submissions/mathgraph/solver.py'; OUT=ROOT/'experiments/mathgraph/results/teacher-forced-latent-retention.json'
TRACE='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
IDS={'evaluation_hard_0196','evaluation_normal_0040','evaluation_order5_0014'}
CFGS=['evaluation_hard','evaluation_normal','evaluation_order5']
def loadm():
 s=importlib.util.spec_from_file_location('mg_force',SOLVER);m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m);return m
class P:
 def __init__(self,s):self.s,self.i=s,0
 def ws(self):
  while self.i<len(self.s) and self.s[self.i].isspace():self.i+=1
 def name(self):
  self.ws();j=self.i
  while self.i<len(self.s) and (self.s[self.i].isalnum() or self.s[self.i] in '_$@'):self.i+=1
  if j==self.i:raise ValueError
  return self.s[j:self.i]
 def term(self):
  n=self.name();self.ws()
  if self.i<len(self.s) and self.s[self.i]=='(':
   self.i+=1;a=self.term();self.ws();assert self.s[self.i]==',';self.i+=1;b=self.term();self.ws();assert self.s[self.i]==')';self.i+=1;assert n=='f';return ('op',a,b)
  return ('var',n)
def pt(s):p=P(s.strip());t=p.term();p.ws();return t
def strip(s):
 s=s.strip()
 while len(s)>1 and s[0]=='(' and s[-1]==')':
  d=0;ok=True
  for i,c in enumerate(s):
   d+=c=='(';d-=c==')'
   if d==0 and i<len(s)-1:ok=False;break
  if not ok:break
  s=s[1:-1].strip()
 return s
def split(s):
 out=[];st=d=b=0
 for i,c in enumerate(s):
  if c=='(':d+=1
  elif c==')':d-=1
  elif c=='[':b+=1
  elif c==']':b-=1
  elif c==',' and d==0 and b==0:out.append(s[st:i].strip());st=i+1
 out.append(s[st:].strip());return out
def blocks(p):
 out=[];st=0
 while True:
  i=p.find('fof(',st)
  if i<0:return out
  d=0
  for j in range(i+3,len(p)):
   if p[j]=='(':d+=1
   elif p[j]==')':
    d-=1
    if d==0:out.append(p[i:j+1]);st=j+1;break
  else:return out
def eq(f):
 s=strip(f);q=re.match(r'^[!?]\s*\[[^\]]*\]\s*:\s*(.*)$',s,re.S)
 if q:s=strip(q.group(1))
 d=0
 for i,c in enumerate(s):
  if c=='(':d+=1
  elif c==')':d-=1
  elif c=='=' and d==0:return pt(s[:i]),pt(s[i+1:])
def inline(t,defs,seen=None):
 seen=set() if seen is None else seen
 if t[0]=='var' and t[1] in defs and t[1] not in seen:return inline(defs[t[1]],defs,seen|{t[1]})
 return ('op',inline(t[1],defs,seen),inline(t[2],defs,seen)) if t[0]=='op' else t
def rigid(t,tv):
 if t[0]=='var':
  q=re.fullmatch(r'sK(\d+)',t[1]);return ('var','@'+tv[int(q.group(1))]) if q and int(q.group(1))<len(tv) else t
 return ('op',rigid(t[1],tv),rigid(t[2],tv))
def inames(t,rev,seen=None):
 seen=set() if seen is None else seen
 if t[0]=='var' and t[1] in rev and t[1] not in seen:return inames(rev[t[1]],rev,seen|{t[1]})
 return ('op',inames(t[1],rev,seen),inames(t[2],rev,seen)) if t[0]=='op' else t
def cover(m,a,b,x,y):
 for p,q in ((a,b),(b,a)):
  z={}
  if m.match_term(p,x,z) and m.match_term(q,y,z):return True
 return False
def first_missing(m,proof,tgt,clauses,rev):
 defs={}
 for bl in blocks(proof):
  p=split(bl[4:-1]);
  if len(p)<3:continue
  fid,k,f=p[:3];tail=p[3:]
  try:e=eq(f)
  except Exception:continue
  if not e:continue
  a,b=e
  if k=='definition':
   if a[0]=='var' and a[1].startswith('sF'):defs[a[1]]=b
   elif b[0]=='var' and b[1].startswith('sF'):defs[b[1]]=a
   continue
  mm=re.search(r'inference\(([^,\]]+)',','.join(tail));inf=mm.group(1) if mm else ''
  if inf not in ('superposition','forward_demodulation'):continue
  a,b=rigid(inline(a,defs),tgt[2]),rigid(inline(b,defs),tgt[2])
  if not any(cover(m,inames(c.lhs,rev),inames(c.rhs,rev),a,b) for c in clauses):return fid,inf,a,b

def finish(m,e,r):
 if r is None:return False
 try:
  r=e.inline_recipe(r);c=m.CompactSuperposition(m,e.source,e.target,time.monotonic()+3,e.search.limits);nodes,root=c.compile(r)
  return (nodes[root].lhs,nodes[root].rhs)==e.target[:2] and m.replay_dag(e.source,nodes,root,maximum_term_size=e.search.limits['maximum_replay_term_size'],maximum_nodes=e.search.limits['maximum_proof_nodes'])
 except:return False
def main():
 m=loadm();rows={}
 for cfg in CFGS:
  for rr in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(rr)
   if r['id'] in IDS:rows[r['id']]=r
 traces={x['id']:x['proof'] for x in json.load(urllib.request.urlopen(TRACE))['rows']};out=[]
 lim=dict(m.COMPACT_SUPERPOSITION_PROBE);lim.update({'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 for rid in sorted(IDS):
  src=m.parse_equation(rows[rid]['equation1']);tgt=m.parse_equation(rows[rid]['equation2'])
  ce=m.TargetGroundedRefutation(src,tgt,time.monotonic()+6,dict(lim));cr=ce.search.solve();
  if cr is None:ce.search.deadline=time.monotonic()+6;cr=ce.search.solve()
  control=finish(m,ce,cr)
  e=m.TargetGroundedRefutation(src,tgt,time.monotonic()+6,dict(lim));r=e.search.solve();injected=False;meta=None
  if r is None:
   fm=first_missing(m,traces[rid],tgt,e.search.clauses,e.reverse_constants);rules=list(e.search.rules());deadline=time.monotonic()+6
   if fm:
    fid,inf,ta,tb=fm
    for oi,o in enumerate(rules):
     if injected or time.monotonic()>=deadline:break
     for ii,inn in enumerate(rules):
      if injected or time.monotonic()>=deadline:break
      for path in m.nonvariable_positions(o.lhs,maximum_depth=lim['maximum_depth'],include_root=True):
       if time.monotonic()>=deadline:break
       q=e.search.critical_pair(o,inn,oi,ii,path)
       if q is not None:
        qa,qb=inames(q.lhs,e.reverse_constants),inames(q.rhs,e.reverse_constants)
        if cover(m,qa,qb,ta,tb):
         accepted=e.search.add_clause(q);injected=bool(accepted);meta={'teacher_id':fid,'teacher_inference':inf,'accepted':bool(accepted),'outer':oi,'inner':ii,'path':list(path),'lhs':m.render_term(qa),'rhs':m.render_term(qb),'score':repr(e.search.target_score(q))};break
    e.search.deadline=time.monotonic()+6;r=e.search.solve()
  candidate=finish(m,e,r)
  rec={'id':rid,'control_replay':bool(control),'injected':injected,'injection':meta,'candidate_replay':bool(candidate),'marginal':bool(candidate and not control),'clauses':len(e.search.clauses),'superpositions':e.search.superpositions};out.append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 result={'schema':'mathgraph.teacher-forced-latent-retention.v1','diagnostic_only':True,'rows':out,'summary':{'marginal_hits':[x['id'] for x in out if x['marginal']],'injected':[x['id'] for x in out if x['injected']]}}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result['summary'],indent=2))
if __name__=='__main__':main()
