#!/usr/bin/env python3
import json,re
from pathlib import Path
RID='evaluation_normal_0040'
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
            self.i+=1; a=self.term(); self.ws()
            if self.s[self.i]!=',': raise ValueError('comma')
            self.i+=1; b=self.term(); self.ws()
            if self.s[self.i]!=')': raise ValueError('close')
            self.i+=1
            if n!='f': raise ValueError('non-f function')
            return ('op',a,b)
        return ('var',n)
def parse_term(s):
    p=P(s.strip()); t=p.term(); p.ws()
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
def split_top_level(s,sep=','):
    out=[]; start=0; depth=0; brackets=0
    for i,c in enumerate(s):
        if c=='(': depth+=1
        elif c==')': depth-=1
        elif c=='[': brackets+=1
        elif c==']': brackets-=1
        elif c==sep and depth==0 and brackets==0: out.append(s[start:i].strip()); start=i+1
    out.append(s[start:].strip()); return out
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
def parse_fof(block):
    p=split_top_level(block[4:-1]); return None if len(p)<3 else (p[0],p[1],p[2],p[3:])
def formula_equality(formula):
    s=strip_outer(formula); q=re.match(r'^[!?]\s*\[[^\]]*\]\s*:\s*(.*)$',s,re.S)
    if q: s=strip_outer(q.group(1))
    depth=0
    for i,c in enumerate(s):
        if c=='(': depth+=1
        elif c==')': depth-=1
        elif c=='=' and depth==0 and not(i and s[i-1]=='!'): return parse_term(s[:i]),parse_term(s[i+1:])
    return None
def inline_defs(term,defs,seen=None):
    seen=set() if seen is None else seen
    if term[0]=='var' and term[1] in defs and term[1] not in seen: return inline_defs(defs[term[1]],defs,seen|{term[1]})
    if term[0]=='op': return ('op',inline_defs(term[1],defs,seen),inline_defs(term[2],defs,seen))
    return term
def map_rigids(term,target_vars):
    if term[0]=='var':
        q=re.fullmatch(r'sK(\d+)',term[1])
        if q:
            i=int(q.group(1)); return ('var','@'+(target_vars[i] if i<len(target_vars) else 'sk'+str(i)))
        return term
    return ('op',map_rigids(term[1],target_vars),map_rigids(term[2],target_vars))
def inline_engine_names(term,reverse_constants,seen=None):
    seen=set() if seen is None else seen
    if term[0]=='var' and term[1] in reverse_constants and term[1] not in seen: return inline_engine_names(reverse_constants[term[1]],reverse_constants,seen|{term[1]})
    if term[0]=='op': return ('op',inline_engine_names(term[1],reverse_constants,seen),inline_engine_names(term[2],reverse_constants,seen))
    return term
def load_row(path):
    rows=[json.loads(x) for x in Path(path).read_text().splitlines() if x.strip()]
    for i,r in enumerate(rows):
        rid=r.get('id') or f'evaluation_normal_{i:04d}'
        if rid==RID:
            r=dict(r); r['id']=rid; return r
    raise RuntimeError('row missing')
