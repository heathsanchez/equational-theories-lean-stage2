#!/usr/bin/env python3
import argparse, importlib.util, json, re, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'


def load_solver():
    spec=importlib.util.spec_from_file_location('mg_0040_selfoverlap',SOLVER)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

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
        elif c==sep and depth==0 and brackets==0:
            out.append(s[start:i].strip()); start=i+1
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

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
    m=load_solver(); row=load_row(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    engine=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits); baseline=engine.solve(); rigid=m.RigidSuperpositionModule()
    trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
    defs={}; wanted={}
    for block in fof_blocks(proof):
        q=parse_fof(block)
        if not q: continue
        fid,kind,formula,tail=q
        try: eq=formula_equality(formula)
        except Exception: eq=None
        if eq is None: continue
        x,y=eq
        if kind=='definition':
            if x[0]=='var' and x[1].startswith('sF'): defs[x[1]]=y
            elif y[0]=='var' and y[1].startswith('sF'): defs[y[1]]=x
            continue
        if fid in ('f81','f95'):
            wanted[fid]=(map_rigids(inline_defs(x,defs),target[2]),map_rigids(inline_defs(y,defs),target[2]))
    f81=wanted['f81']; f95=wanted['f95']
    clauses=[]
    for c in engine.search.clauses:
        clauses.append((c,inline_engine_names(c.lhs,engine.reverse_constants),inline_engine_names(c.rhs,engine.reverse_constants)))
    cover=None; cover_map=None; cover_rev=False
    for c,x,y in clauses:
        for rev,(u,v) in enumerate(((x,y),(y,x))):
            subst={}
            if rigid.match_term(u,f81[0],subst) and rigid.match_term(v,f81[1],subst):
                cover=(c,x,y); cover_map=subst; cover_rev=bool(rev); break
        if cover: break
    out={'id':RID,'baseline_found':bool(baseline),'cover_found':cover is not None,'cover_substitution':None,'materialized_matches_f81':False,'self_overlap_matches_f95':False,'replay_ok':False}
    if cover:
        out['cover_substitution']={k:m.render_term(v) for k,v in sorted(cover_map.items())}
        c,x,y=cover
        mx=rigid.substitute(x,cover_map); my=rigid.substitute(y,cover_map)
        if cover_rev: mx,my=my,mx
        out['materialized_matches_f81']=(mx,my)==f81
        # Reconstruct the materialized covering recipe inside the engine's symbolic vocabulary,
        # then ask the same critical-pair constructor used by CompactSuperposition to self-overlap it.
        base_recipe=c
        if cover_rev: base_recipe=m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
        mat=engine.search.instantiate(base_recipe,cover_map)
        proposals=[]
        for side,root in ((0,mat.lhs),(1,mat.rhs)):
            for path in rigid.nonvariable_positions(root,maximum_depth=limits['maximum_depth'],include_root=True):
                p=engine.search.critical_pair(mat,mat,0,0,path) if side==0 else None
                if p is None: continue
                ix=inline_engine_names(p.lhs,engine.reverse_constants); iy=inline_engine_names(p.rhs,engine.reverse_constants)
                proposals.append((ix,iy,p))
                if (ix,iy)==f95 or (iy,ix)==f95:
                    out['self_overlap_matches_f95']=True
                    nodes,root_id=m.recipe_to_dag(p)
                    out['replay_ok']=bool(m.replay_dag(source,nodes,root_id,maximum_term_size=260,maximum_nodes=50000))
                    break
            if out['self_overlap_matches_f95']: break
        out['proposal_count']=len(proposals)
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('NORMAL0040_MATERIALIZED_SELF_OVERLAP',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()
