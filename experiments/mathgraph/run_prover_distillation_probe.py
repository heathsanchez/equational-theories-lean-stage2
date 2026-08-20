#!/usr/bin/env python3
"""Teacher→student transition probe for MathGraph TRUE-side prover distillation.

For a deterministic sample of TRUE evaluation problems, run Vampire and the
current target-grounded MathGraph engine, then record the earliest teacher
superposition/demodulation equality not covered by the student's reachable
clause surface. Coverage is semantic at the equation-instance level: a more
general student equality counts as covering a specific teacher instance.
"""
import argparse, importlib.util, json, re, subprocess, sys, tempfile, time
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'

def load_solver():
    spec=importlib.util.spec_from_file_location('mg_distill_solver',SOLVER)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def tptp_term(m,t):
    if t[0]=='var': return t[1].upper()
    return 'f('+tptp_term(m,t[1])+','+tptp_term(m,t[2])+')'
def vampire_problem(m,source,target):
    sv=source[2]; tv=target[2]
    s='! ['+','.join(v.upper() for v in sv)+'] : ('+tptp_term(m,source[0])+' = '+tptp_term(m,source[1])+')'
    t='! ['+','.join(v.upper() for v in tv)+'] : ('+tptp_term(m,target[0])+' = '+tptp_term(m,target[1])+')'
    return "fof(source,axiom,(%s)).\nfof(target,conjecture,(%s)).\n"%(s,t)
def run_vampire(text,seconds):
    with tempfile.NamedTemporaryFile('w',suffix='.p',delete=False) as f: f.write(text); path=f.name
    try:
        p=subprocess.run(['vampire','--mode','casc','--proof','tptp','--time_limit',str(seconds),path],text=True,capture_output=True,timeout=seconds+3)
        out=(p.stdout or '')+'\n'+(p.stderr or '')
        return 'SZS status Theorem' in out,out
    except Exception as e: return False,'ERROR '+type(e).__name__+': '+str(e)
    finally: Path(path).unlink(missing_ok=True)
def fof_blocks(proof):
    out=[]; start=0
    while True:
        i=proof.find('fof(',start)
        if i<0: break
        depth=0; j=i+3
        while j<len(proof):
            if proof[j]=='(': depth+=1
            elif proof[j]==')':
                depth-=1
                if depth==0: out.append(proof[i:j+1]); start=j+1; break
            j+=1
        else: break
    return out
def split_top(s):
    out=[]; st=0; d=0; b=0
    for i,c in enumerate(s):
        if c=='(': d+=1
        elif c==')': d-=1
        elif c=='[': b+=1
        elif c==']': b-=1
        elif c==',' and d==0 and b==0: out.append(s[st:i].strip()); st=i+1
    out.append(s[st:].strip()); return out
def strip_outer(s):
    s=s.strip()
    while len(s)>1 and s[0]=='(' and s[-1]==')':
        d=0; ok=True
        for i,c in enumerate(s):
            d+=(c=='(')-(c==')')
            if d==0 and i!=len(s)-1: ok=False; break
        if not ok: break
        s=s[1:-1].strip()
    return s
class P:
    def __init__(self,s): self.s=s; self.i=0
    def ws(self):
        while self.i<len(self.s) and self.s[self.i].isspace(): self.i+=1
    def name(self):
        self.ws(); j=self.i
        while self.i<len(self.s) and (self.s[self.i].isalnum() or self.s[self.i] in '_$@'): self.i+=1
        if j==self.i: raise ValueError
        return self.s[j:self.i]
    def term(self):
        n=self.name(); self.ws()
        if self.i<len(self.s) and self.s[self.i]=='(':
            self.i+=1; a=self.term(); self.ws(); assert self.s[self.i]==','; self.i+=1; b=self.term(); self.ws(); assert self.s[self.i]==')'; self.i+=1
            if n!='f': raise ValueError
            return ('op',a,b)
        return ('var',n)
def parse_term(s): return P(s.strip()).term()
def formula_eq(formula):
    s=strip_outer(formula); q=re.match(r'^[!?]\s*\[[^\]]*\]\s*:\s*(.*)$',s,re.S)
    if q: s=strip_outer(q.group(1))
    d=0
    for i,c in enumerate(s):
        if c=='(': d+=1
        elif c==')': d-=1
        elif c=='=' and d==0 and not(i and s[i-1]=='!'): return parse_term(s[:i]),parse_term(s[i+1:])
    return None
def inline_defs(t,defs,seen=None):
    seen=set() if seen is None else seen
    if t[0]=='var' and t[1] in defs and t[1] not in seen: return inline_defs(defs[t[1]],defs,seen|{t[1]})
    if t[0]=='op': return ('op',inline_defs(t[1],defs,seen),inline_defs(t[2],defs,seen))
    return t
def map_rigid(t,target_vars):
    if t[0]=='var':
        q=re.fullmatch(r'sK(\d+)',t[1])
        if q:
            i=int(q.group(1)); return ('var','@'+(target_vars[i] if i<len(target_vars) else 'sk'+str(i)))
        return t
    return ('op',map_rigid(t[1],target_vars),map_rigid(t[2],target_vars))
def inline_engine(t,rev,seen=None):
    seen=set() if seen is None else seen
    if t[0]=='var' and t[1] in rev and t[1] not in seen: return inline_engine(rev[t[1]],rev,seen|{t[1]})
    if t[0]=='op': return ('op',inline_engine(t[1],rev,seen),inline_engine(t[2],rev,seen))
    return t
def sig(rigid,a,b):
    names={}; x=rigid.alpha_canonical_term(a,names); y=rigid.alpha_canonical_term(b,names); return min((x,y),(y,x))
def covers(rigid,sa,sb,ta,tb):
    for x,y in ((sa,sb),(sb,sa)):
        mp={}
        if rigid.match_term(x,ta,mp) and rigid.match_term(y,tb,mp): return True
    return False
def teacher_steps(m,proof,target_vars):
    defs={}; out=[]
    for block in fof_blocks(proof):
        parts=split_top(block[4:-1])
        if len(parts)<3: continue
        fid,kind,formula=parts[:3]; tail=','.join(parts[3:])
        try: eq=formula_eq(formula)
        except Exception: continue
        if not eq: continue
        a,b=eq
        if kind=='definition':
            if a[0]=='var' and a[1].startswith('sF'): defs[a[1]]=b
            elif b[0]=='var' and b[1].startswith('sF'): defs[b[1]]=a
            continue
        mi=re.search(r'inference\(([^,\]]+)',tail); inf=mi.group(1) if mi else ''
        if inf not in ('superposition','forward_demodulation'): continue
        out.append((fid,inf,map_rigid(inline_defs(a,defs),target_vars),map_rigid(inline_defs(b,defs),target_vars)))
    return out
def feature(m,a,b,inf):
    va=len(m.RigidSuperpositionModule.term_variables(a)|m.RigidSuperpositionModule.term_variables(b)); sa,sb=m.term_size(a),m.term_size(b)
    bare=int(a[0]=='var' or b[0]=='var'); collapse=int(bare and va<=1)
    return {'inference':inf,'variables':va,'max_size':max(sa,sb),'size_gap':abs(sa-sb),'bare_side':bare,'collapse_like':collapse}
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); ap.add_argument('--limit',type=int,default=40); ap.add_argument('--seconds',type=float,default=.25); args=ap.parse_args()
    m=load_solver(); rows=sorted(json.load(open(args.input)),key=lambda r:r['id'])[:args.limit]; rigid=m.RigidSuperpositionModule(); recs=[]; buckets=Counter()
    for row in rows:
        source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); theorem,proof=run_vampire(vampire_problem(m,source,target),2)
        if not theorem: recs.append({'id':row['id'],'teacher':False}); continue
        limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'maximum_term_size':55,'maximum_replay_term_size':220,'maximum_depth':10,'maximum_rules':384,'maximum_rounds':32,'new_clauses_per_round':256,'maximum_clauses':5000,'normalization_steps':160,'maximum_proof_nodes':30000})
        engine=m.TargetGroundedRefutation(source,target,time.monotonic()+args.seconds,limits); found=engine.solve()
        student=[(inline_engine(c.lhs,engine.reverse_constants),inline_engine(c.rhs,engine.reverse_constants)) for c in engine.search.clauses]
        steps=teacher_steps(m,proof,target[2]); first=None; present=0; exact=0
        for fid,inf,a,b in steps:
            ex=any(sig(rigid,a,b)==sig(rigid,sa,sb) for sa,sb in student)
            ok=ex or any(covers(rigid,sa,sb,a,b) for sa,sb in student)
            exact+=int(ex); present+=int(ok)
            if not ok and first is None: first={'fid':fid,'lhs':m.render_term(a),'rhs':m.render_term(b),**feature(m,a,b,inf)}
        if first: buckets[(first['inference'],first['bare_side'],first['collapse_like'],first['variables'])]+=1
        recs.append({'id':row['id'],'teacher':True,'student_found':bool(found),'teacher_steps':len(steps),'present_teacher_steps':present,'exact_teacher_steps':exact,'first_missing':first,'student_clauses':len(engine.search.clauses)})
        print(row['id'],'student',bool(found),'teacher_steps',len(steps),'covered',present,'first',first,flush=True)
    out={'rows':recs,'summary':{'teacher_solved':sum(r.get('teacher',False) for r in recs),'student_solved':sum(r.get('student_found',False) for r in recs),'first_missing_buckets':[{'bucket':list(k),'count':v} for k,v in buckets.most_common()]}}
    Path(args.output).parent.mkdir(parents=True,exist_ok=True); Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)); print(json.dumps(out['summary'],indent=2))
if __name__=='__main__': main()
