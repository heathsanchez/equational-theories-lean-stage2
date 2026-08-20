#!/usr/bin/env python3
import importlib.util, json, re, sys, time, urllib.request
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
OUT=ROOT/'experiments/mathgraph/results/demodulation-boundary-audit.json'
IDS=['evaluation_normal_0036','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']


def loadm():
 s=importlib.util.spec_from_file_location('mg_demod_audit',SOLVER);m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m);return m

class P:
 def __init__(self,s):self.s,self.i=s,0
 def ws(self):
  while self.i<len(self.s) and self.s[self.i].isspace():self.i+=1
 def name(self):
  self.ws();j=self.i
  while self.i<len(self.s) and (self.s[self.i].isalnum() or self.s[self.i] in '_$@'):self.i+=1
  if self.i==j:raise ValueError('name')
  return self.s[j:self.i]
 def term(self):
  n=self.name();self.ws()
  if self.i<len(self.s) and self.s[self.i]=='(':
   self.i+=1;a=self.term();self.ws()
   if self.s[self.i]!=',':raise ValueError('comma')
   self.i+=1;b=self.term();self.ws()
   if self.s[self.i]!=')':raise ValueError('close')
   self.i+=1
   if n!='f':raise ValueError('non-f function')
   return ('op',a,b)
  return ('var',n)

def parse_term(s):
 p=P(s.strip());t=p.term();p.ws()
 if p.i!=len(p.s):raise ValueError('trailing')
 return t

def strip_outer(s):
 s=s.strip();changed=True
 while changed and len(s)>=2 and s[0]=='(' and s[-1]==')':
  depth=0;changed=False
  for i,c in enumerate(s):
   if c=='(':depth+=1
   elif c==')':
    depth-=1
    if depth==0:
     if i==len(s)-1:s=s[1:-1].strip();changed=True
     break
 return s

def split_top_level(s,sep=','):
 out=[];start=0;depth=0;br=0
 for i,c in enumerate(s):
  if c=='(':depth+=1
  elif c==')':depth-=1
  elif c=='[':br+=1
  elif c==']':br-=1
  elif c==sep and depth==0 and br==0:out.append(s[start:i].strip());start=i+1
 out.append(s[start:].strip());return out

def fof_blocks(proof):
 out=[];start=0
 while True:
  i=proof.find('fof(',start)
  if i<0:break
  depth=0;j=i+3
  while j<len(proof):
   if proof[j]=='(':depth+=1
   elif proof[j]==')':
    depth-=1
    if depth==0:out.append(proof[i:j+1]);start=j+1;break
   j+=1
  else:break
 return out

def parse_fof(block):
 parts=split_top_level(block[4:-1]);return None if len(parts)<3 else (parts[0],parts[1],parts[2],parts[3:])

def formula_equality(formula):
 s=strip_outer(formula);q=re.match(r'^[!?]\s*\[[^\]]*\]\s*:\s*(.*)$',s,re.S)
 if q:s=strip_outer(q.group(1))
 depth=0
 for i,c in enumerate(s):
  if c=='(':depth+=1
  elif c==')':depth-=1
  elif c=='=' and depth==0 and not(i and s[i-1]=='!'):return parse_term(s[:i]),parse_term(s[i+1:])
 return None

def inline_defs(term,defs,seen=None):
 seen=set() if seen is None else seen
 if term[0]=='var' and term[1] in defs and term[1] not in seen:return inline_defs(defs[term[1]],defs,seen|{term[1]})
 if term[0]=='op':return ('op',inline_defs(term[1],defs,seen),inline_defs(term[2],defs,seen))
 return term

def map_rigids(term,target_vars):
 if term[0]=='var':
  q=re.fullmatch(r'sK(\d+)',term[1])
  if q:
   i=int(q.group(1));return ('var','@'+(target_vars[i] if i<len(target_vars) else 'sk'+str(i)))
  return term
 return ('op',map_rigids(term[1],target_vars),map_rigids(term[2],target_vars))

def inline_engine(term,rev,seen=None):
 seen=set() if seen is None else seen
 if term[0]=='var' and term[1] in rev and term[1] not in seen:return inline_engine(rev[term[1]],rev,seen|{term[1]})
 if term[0]=='op':return ('op',inline_engine(term[1],rev,seen),inline_engine(term[2],rev,seen))
 return term

def clause_covers(m,sa,sb,ta,tb):
 for x,y in ((sa,sb),(sb,sa)):
  mp={}
  if m.match_term(x,ta,mp) and m.match_term(y,tb,mp):return True
 return False

def eq_same(m,a,b,c,d):
 rigid=m.RigidSuperpositionModule();n={};x=(rigid.alpha_canonical_term(a,n),rigid.alpha_canonical_term(b,n));n={};y=(rigid.alpha_canonical_term(c,n),rigid.alpha_canonical_term(d,n));return x==y or x==y[::-1]

def positions_all(term,path=()):
 yield path
 if term[0]=='op':
  yield from positions_all(term[1],path+('L',));yield from positions_all(term[2],path+('R',))

def rewrite_matches(m, victim, rule, result):
 out=[]
 for side_name,root in [('lhs',victim[0]),('rhs',victim[1])]:
  for path in positions_all(root):
   sel=m.get_subterm(root,path) if path else root;mp={}
   if not m.match_term(rule.lhs,sel,mp):continue
   if not m.term_variables(rule.lhs)<=set(mp):continue
   try:rep=m.substitute_partial(rule.rhs,mp);after=m.replace_subterm(root,path,rep)
   except Exception:continue
   eq=(after,victim[1]) if side_name=='lhs' else (victim[0],after)
   if eq_same(m,eq[0],eq[1],result[0],result[1]):out.append({'side':side_name,'path':list(path),'whole_decreases':m.normalization_order_key(after,'size')<m.normalization_order_key(root,'size')})
 return out

def parse_trace(m,proof,target_vars):
 defs={};records={};order=[]
 for block in fof_blocks(proof):
  p=parse_fof(block)
  if not p:continue
  fid,kind,formula,tail=p
  try:eq=formula_equality(formula)
  except Exception:eq=None
  if eq is None:continue
  a,b=eq
  if kind=='definition':
   if a[0]=='var' and a[1].startswith('sF'):defs[a[1]]=b
   elif b[0]=='var' and b[1].startswith('sF'):defs[b[1]]=a
   continue
  a=map_rigids(inline_defs(a,defs),target_vars);b=map_rigids(inline_defs(b,defs),target_vars)
  text=','.join(tail);mi=re.search(r'inference\(([^,\]]+)',text);inf=mi.group(1) if mi else ''
  rec={'id':fid,'kind':kind,'inference':inf,'eq':(a,b),'tail':text,'parents':[]};records[fid]=rec;order.append(fid)
 # resolve parent references conservatively from already-known ids in inference text
 ids=set(records)
 for fid in order:
  text=records[fid]['tail'];records[fid]['parents']=[x for x in order if x!=fid and x in ids and re.search(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',text)]
 return records,order

def student_closure(m,source,target):
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 eng=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits);eng.solve()
 clauses=[(inline_engine(c.lhs,eng.reverse_constants),inline_engine(c.rhs,eng.reverse_constants),c) for c in eng.search.clauses]
 return eng,clauses

def main():
 m=loadm();rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 trace=json.load(urllib.request.urlopen(TRACE_URL));proofs={r['id']:r['proof'] for r in trace['rows']}
 results={}
 for rid in IDS:
  row=rows[rid];source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2']);eng,student=student_closure(m,source,target);records,order=parse_trace(m,proofs[rid],target[2])
  first=None
  for fid in order:
   rec=records[fid]
   if rec['inference']!='forward_demodulation':continue
   a,b=rec['eq'];present=any(clause_covers(m,sa,sb,a,b) for sa,sb,_ in student)
   if not present:first=rec;break
  if first is None:results[rid]={'classification':'no-missing-forward-demodulation-found'};continue
  parent_records=[records[p] for p in first['parents'] if p in records]
  candidates=[]
  for i,dem in enumerate(parent_records):
   for j,vic in enumerate(parent_records):
    if i==j:continue
    for reverse in (False,True):
     dl,dr=dem['eq'] if not reverse else dem['eq'][::-1]
     recipe=m.Recipe(dl,dr,'diagnostic')
     oriented=eng.search.orient(recipe)
     matches=rewrite_matches(m,vic['eq'],recipe,first['eq'])
     if not matches:continue
     dem_present=[(sa,sb,c) for sa,sb,c in student if clause_covers(m,sa,sb,dl,dr)]
     current_rule_cover=False
     for rule in eng.search.rules():
      rr=(inline_engine(rule.lhs,eng.reverse_constants),inline_engine(rule.rhs,eng.reverse_constants))
      if clause_covers(m,rr[0],rr[1],dl,dr):current_rule_cover=True;break
     candidates.append({'demod_parent':dem['id'],'victim_parent':vic['id'],'reverse':reverse,'demod_lhs':m.render_term(dl),'demod_rhs':m.render_term(dr),'lhs_key':m.normalization_order_key(dl,'size'),'rhs_key':m.normalization_order_key(dr,'size'),'variable_condition':sorted(m.term_variables(dr))<=sorted(m.term_variables(dl)),'mathgraph_orientable':oriented is not None,'demodulator_present_in_closure':bool(dem_present),'demodulator_present_in_active_rules':current_rule_cover,'teacher_rewrite_matches':matches})
  if not candidates:
   classification='teacher-parent-reconstruction-failed'
  elif any(c['demodulator_present_in_closure'] and not c['mathgraph_orientable'] for c in candidates):classification='orientation-boundary'
  elif any(c['demodulator_present_in_closure'] and c['mathgraph_orientable'] and not c['demodulator_present_in_active_rules'] for c in candidates):classification='rule-selection-boundary'
  elif any(c['demodulator_present_in_active_rules'] and c['mathgraph_orientable'] for c in candidates):classification='reapplication-or-rewrite-admissibility-boundary'
  elif any(not c['demodulator_present_in_closure'] for c in candidates):classification='derivability-timing-boundary'
  else:classification='unclassified'
  results[rid]={'classification':classification,'first_missing_step':{'id':first['id'],'lhs':m.render_term(first['eq'][0]),'rhs':m.render_term(first['eq'][1]),'parents':first['parents']},'clauses':len(eng.search.clauses),'rules':len(eng.search.rules()),'candidates':candidates}
  print(rid,json.dumps(results[rid],sort_keys=True),flush=True)
 out={'schema':'mathgraph.demodulation-boundary-audit.v1','cases':results};OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:v['classification'] for k,v in results.items()},indent=2,sort_keys=True))
if __name__=='__main__':main()
