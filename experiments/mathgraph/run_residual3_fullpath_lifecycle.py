#!/usr/bin/env python3
import importlib.util, json, re, subprocess, sys, tempfile, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
IDS={'hard1_0067','hard2_0107','hard3_0208'}
DERIVED={'superposition','forward_demodulation','backward_demodulation','forward_subsumption_resolution','subsumption_resolution','equality_resolution','resolution'}

def load_solver():
    text=subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)
    td=tempfile.TemporaryDirectory(); p=Path(td.name)/'solver796.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg796fullpath',p); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)
    return td,m

def rows():
    out=[]
    for split in ('hard1','hard2','hard3'):
        for line in (ROOT/f'examples/problems/{split}.jsonl').read_text().splitlines():
            if not line.strip(): continue
            r=json.loads(line)
            if r.get('id') in IDS: out.append(r)
    return sorted(out,key=lambda x:x['id'])

def render(t):
    if t[0]=='var': return 'V_'+t[1].upper()
    return f'f({render(t[1])},{render(t[2])})'

def quantified(eq):
    lhs,rhs,vs=eq; return f"! [{','.join('V_'+v.upper() for v in vs)}] : {render(lhs)} = {render(rhs)}"

def split_top(s,sep=','):
    out=[]; start=0; dp=db=0
    for i,ch in enumerate(s):
        if ch=='(': dp+=1
        elif ch==')': dp-=1
        elif ch=='[': db+=1
        elif ch==']': db-=1
        elif ch==sep and dp==0 and db==0: out.append(s[start:i].strip()); start=i+1
    out.append(s[start:].strip()); return out

def strip_outer(s):
    s=s.strip()
    while s.startswith('(') and s.endswith(')'):
        d=0; ok=True
        for i,ch in enumerate(s):
            if ch=='(': d+=1
            elif ch==')': d-=1
            if d==0 and i!=len(s)-1: ok=False; break
        if not ok: break
        s=s[1:-1].strip()
    return s

def statements(text):
    out=[]; cur=[]; depth=0; active=False
    for line in text.splitlines():
        z=line.strip()
        if not active and (z.startswith('fof(') or z.startswith('cnf(')): active=True; cur=[]; depth=0
        if active:
            cur.append(z); depth += z.count('(')-z.count(')')
            if depth==0 and z.endswith('.'): out.append(' '.join(cur)); active=False
    return out

def parse_stmt(line):
    kind='fof' if line.startswith('fof(') else ('cnf' if line.startswith('cnf(') else None)
    if not kind: return None
    body=line[len(kind)+1:]
    if body.endswith(').'): body=body[:-2]
    parts=split_top(body,',')
    if len(parts)<3: return None
    formula=strip_outer(parts[2]); tail=','.join(parts[3:])
    mm=re.search(r'inference\(([^,\]]+)',tail)
    return formula,(mm.group(1) if mm else None)

def remove_quantifier(s):
    s=strip_outer(s)
    if s.startswith('!') or s.startswith('?'):
        k=s.find(':')
        if k>=0: s=s[k+1:].strip()
    return strip_outer(s)

def find_eq(s):
    s=remove_quantifier(s); dp=db=0
    for i,ch in enumerate(s):
        if ch=='(': dp+=1
        elif ch==')': dp-=1
        elif ch=='[': db+=1
        elif ch==']': db-=1
        elif ch in '|&' and dp==0 and db==0: return None
        elif ch=='=' and dp==0 and db==0:
            if i>0 and s[i-1]=='!': return None
            return s[:i].strip(),s[i+1:].strip()
    return None

def parse_term(s):
    s=strip_outer(s.strip())
    if s.startswith('f(') and s.endswith(')'):
        ps=split_top(s[2:-1],',')
        if len(ps)!=2: raise ValueError(s)
        return ('op',parse_term(ps[0]),parse_term(ps[1]))
    return ('var',s)

def key_term(t,names):
    if t[0]=='var':
        if t[1] not in names: names[t[1]]=len(names)
        return ('v',names[t[1]])
    return ('f',key_term(t[1],names),key_term(t[2],names))

def pair_key(lhs,rhs):
    n={}; a=(key_term(lhs,n),key_term(rhs,n)); n={}; b=(key_term(rhs,n),key_term(lhs,n)); return min(a,b)

def clause_key(c): return pair_key(c.lhs,c.rhs)

def formula_key(f):
    e=find_eq(f)
    if not e: return None
    try: return pair_key(parse_term(e[0]),parse_term(e[1]))
    except Exception: return None

def vampire_path(m,r):
    source=m.parse_equation(r['equation1']); target=m.parse_equation(r['equation2'])
    problem=f"fof(source,axiom,({quantified(source)})).\nfof(target,conjecture,({quantified(target)})).\n"
    with tempfile.NamedTemporaryFile(mode='w',suffix='.p',dir='/tmp',delete=True) as h:
        h.write(problem); h.flush(); run=subprocess.run(['vampire','--mode','casc','--time_limit','20','--proof','tptp',h.name],capture_output=True,text=True,timeout=22)
    path=[]
    for idx,st in enumerate(statements(run.stdout+run.stderr)):
        got=parse_stmt(st)
        if not got: continue
        formula,inf=got; k=formula_key(formula)
        if k is not None and inf in DERIVED: path.append({'index':idx,'formula':formula,'inference':inf,'key':k})
    if not path: raise RuntimeError('no derived Vampire equalities parsed')
    return source,target,path

def oriented_variants(m,c):
    if c.lhs==c.rhs: return (c,)
    return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))

def trace_all(m,source,target,wanted,seconds=20.0):
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,'maximum_clauses':16000,'normalization_steps':384,'maximum_proof_nodes':60000})
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits); search=eng.search
    passive=list(search.clauses); active=[]; age={id(c):i for i,c in enumerate(passive)}; next_age=len(passive); given=0
    hits={k:{'raw':False,'post_interreduce':False,'best_rank':None,'topk':False,'add_clause':False,'passive':False,'selected':False,'first_seen_given':None,'selected_given':None} for k in wanted}
    while passive and given<1024 and not search.expired():
        rules=[]
        for c in active:
            q=search.orient(c)
            if q is not None: rules.append(q)
        idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
        selected=passive.pop(idx); sk=clause_key(selected)
        if sk in hits:
            hits[sk]['selected']=True
            if hits[sk]['selected_given'] is None: hits[sk]['selected_given']=given
        selected=search.interreduce(selected,rules); active.append(selected); given+=1
        rules=[]
        for c in active:
            q=search.orient(c)
            if q is not None: rules.append(q)
        proposals=[]
        for oi,other in enumerate(active):
            for bo,bi,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
                for oside,outer in enumerate(oriented_variants(m,bo)):
                    for iside,inner in enumerate(oriented_variants(m,bi)):
                        for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                            if search.expired(): break
                            q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                            if q is None: continue
                            k0=clause_key(q)
                            if k0 in hits:
                                hits[k0]['raw']=True
                                if hits[k0]['first_seen_given'] is None: hits[k0]['first_seen_given']=given
                            qr=search.interreduce(q,rules); k1=clause_key(qr)
                            if k1 in hits: hits[k1]['post_interreduce']=True
                            proposals.append((search.target_score(qr),qr))
        proposals.sort(key=lambda x:x[0])
        rankmap={}
        for i,(_,q) in enumerate(proposals):
            k=clause_key(q)
            if k in hits and k not in rankmap: rankmap[k]=i
        for k,mr in rankmap.items():
            h=hits[k]; h['best_rank']=mr if h['best_rank'] is None else min(h['best_rank'],mr)
            if mr<search.limits['new_clauses_per_round']: h['topk']=True
        for _,q in proposals[:search.limits['new_clauses_per_round']]:
            k=clause_key(q); ok=search.add_clause(q)
            if ok:
                if k in hits: hits[k]['add_clause']=True
                passive.append(q); age[id(q)]=next_age; next_age+=1
        pkeys={clause_key(c) for c in passive}
        for k in hits:
            if k in pkeys: hits[k]['passive']=True
        new=[]; seen=set()
        for c in passive:
            if search.expired(): break
            c=search.interreduce(c,rules)
            names={}; a=(m.alpha_canonical_term(c.lhs,names),m.alpha_canonical_term(c.rhs,names)); names={}; b=(m.alpha_canonical_term(c.rhs,names),m.alpha_canonical_term(c.lhs,names)); kk=min(a,b)
            if kk in seen: continue
            seen.add(kk); new.append(c)
        passive=new
    return hits,given

def status(h):
    if h['selected']: return 'selected'
    if h['passive']: return 'passive-unselected'
    if h['add_clause']: return 'added-then-lost'
    if h['topk']: return 'topk-not-added'
    if h['post_interreduce']: return 'post-interreduce-only'
    if h['raw']: return 'raw-only'
    return 'absent'

def main():
    td,m=load_solver(); results=[]
    try:
        for r in rows():
            source,target,path=vampire_path(m,r); wanted={x['key'] for x in path}; hits,given=trace_all(m,source,target,wanted)
            outpath=[]; first_bad=None
            for x in path:
                h=hits[x['key']]; rec={k:v for k,v in x.items() if k!='key'}; rec['status']=status(h); rec['pipeline']=h; outpath.append(rec)
                if first_bad is None and rec['status']!='selected': first_bad=rec
            summary={'id':r['id'],'vampire_derived':len(path),'selected_count':sum(1 for x in outpath if x['status']=='selected'),'first_unavailable':first_bad,'given':given}
            print('FULLPATH',json.dumps(summary,sort_keys=True),flush=True); results.append({'summary':summary,'path':outpath})
    finally: td.cleanup()
    p=ROOT/'experiments/mathgraph/results/residual3-fullpath-lifecycle.json'; p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps({'rows':results},indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()
