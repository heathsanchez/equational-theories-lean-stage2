#!/usr/bin/env python3
import argparse, importlib.util, json, re, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'


def load_solver():
    spec=importlib.util.spec_from_file_location('mg_divergence_solver',SOLVER)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

class P:
    def __init__(self,s): self.s=s; self.i=0
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
            self.i+=1; b=self.term(); self.ws()
            if self.s[self.i]!=')': raise ValueError('close')
            self.i+=1
            if n!='f': raise ValueError('non-f function')
            return ('op',a,b)
        return ('var',n)

def parse_term(s): return P(s).term()

def extract_eq_formula(block):
    # Return the first top-level equality body inside a Vampire fof block.
    body=block.split(':',1)[-1] if ':' in block else block
    # strip quantifier prefix if present
    body=re.sub(r'^.*?\:\s*\(?','',body, count=1) if '! [' in body else body
    # remove inference tail by operating only before 'inference('
    body=body.split('inference(',1)[0]
    # collect candidate equality text from innermost outer parentheses
    m=re.search(r'\(([^\n]+?)\)\s*[,)]?\s*$',body.strip())
    text=m.group(1) if m else body.strip()
    # find equality sign not part of !=
    depth=0; pos=None
    for i,c in enumerate(text):
        if c=='(': depth+=1
        elif c==')': depth-=1
        elif c=='=' and (i==0 or text[i-1]!='!'):
            pos=i; break
    if pos is None: return None
    l=text[:pos].strip().strip('() '); r=text[pos+1:].strip().strip('() ,')
    try: return parse_term(l),parse_term(r)
    except Exception: return None

def fof_blocks(proof):
    out=[]; start=0
    while True:
        i=proof.find('fof(',start)
        if i<0: break
        depth=0; j=i
        while j<len(proof):
            if proof[j]=='(': depth+=1
            elif proof[j]==')':
                depth-=1
                if depth==0:
                    out.append(proof[i:j+1]); start=j+1; break
            j+=1
        else: break
    return out

def inline_defs(term,defs,seen=None):
    seen=set() if seen is None else seen
    if term[0]=='var' and term[1] in defs and term[1] not in seen:
        return inline_defs(defs[term[1]],defs,seen|{term[1]})
    if term[0]=='op': return ('op',inline_defs(term[1],defs,seen),inline_defs(term[2],defs,seen))
    return term

def normalize_names(term):
    # Vampire skolems are rigid ground constants. Preserve them distinctly.
    if term[0]=='var':
        n=term[1]
        return ('var','@'+n if n.startswith(('sK','sF')) else n)
    return ('op',normalize_names(term[1]),normalize_names(term[2]))

def sig(m,a,b):
    names={}
    x=m.alpha_canonical_term(a,names); y=m.alpha_canonical_term(b,names)
    return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); args=ap.parse_args()
    m=load_solver(); rows=json.load(open(args.input)); row=next(r for r in rows if r['id']=='evaluation_order5_0014')
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    engine=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits)
    found=engine.solve()
    clause_sigs={sig(m,c.lhs,c.rhs) for c in engine.search.clauses}
    trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==row['id'])
    defs={}; audited=[]; first=None
    for block in fof_blocks(proof):
        nm=re.match(r'fof\(([^,]+),([^,]+),',block)
        if not nm: continue
        fid,kind=nm.group(1),nm.group(2)
        eq=extract_eq_formula(block)
        if eq is None: continue
        a,b=eq
        # Capture introduced definition sF = f(...), in either orientation.
        if kind=='definition':
            if a[0]=='var' and a[1].startswith('sF'): defs[a[1]]=b
            elif b[0]=='var' and b[1].startswith('sF'): defs[b[1]]=a
            continue
        inf=''
        mi=re.search(r'inference\(([^,\]]+)',block)
        if mi: inf=mi.group(1)
        if inf not in ('superposition','forward_demodulation'): continue
        ia=normalize_names(inline_defs(a,defs)); ib=normalize_names(inline_defs(b,defs))
        present=sig(m,ia,ib) in clause_sigs
        rec={'id':fid,'inference':inf,'present':present,'lhs':m.render_term(ia),'rhs':m.render_term(ib),'lhs_size':m.term_size(ia),'rhs_size':m.term_size(ib)}
        audited.append(rec)
        if first is None and not present: first=rec
    out={'solver_found':bool(found),'clauses':len(engine.search.clauses),'rounds':engine.search.rounds,'superpositions':engine.search.superpositions,'reductions':engine.search.reductions,'audited_steps':len(audited),'present_steps':sum(x['present'] for x in audited),'first_missing':first,'steps':audited}
    Path(args.output).parent.mkdir(parents=True,exist_ok=True); Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)); print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__': main()
