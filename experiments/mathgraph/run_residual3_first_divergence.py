#!/usr/bin/env python3
import importlib.util, json, re, subprocess, sys, tempfile, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
IDS={'hard1_0067','hard2_0107','hard3_0208'}
SKIP_INF={'cnf_transformation','ennf_transformation','skolemize','negated_conjecture','reorient_equations','definition_folding'}

def load_solver():
    text=subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)
    td=tempfile.TemporaryDirectory(); p=Path(td.name)/'solver796.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg796div2',p); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)
    return td,m

def rows():
    out=[]
    for split in ('hard1','hard2','hard3'):
        for line in (ROOT/f'examples/problems/{split}.jsonl').read_text().splitlines():
            if not line.strip(): continue
            r=json.loads(line)
            if r.get('id') in IDS: out.append(r)
    return sorted(out,key=lambda x:x['id'])

def render(term):
    if term[0]=='var': return 'V_'+term[1].upper()
    return f'f({render(term[1])},{render(term[2])})'

def quantified(eq):
    lhs,rhs,variables=eq; binders=','.join('V_'+v.upper() for v in variables)
    return f'! [{binders}] : {render(lhs)} = {render(rhs)}'

def vampire_trace(m,r):
    source=m.parse_equation(r['equation1']); target=m.parse_equation(r['equation2'])
    problem=f"fof(source,axiom,({quantified(source)})).\nfof(target,conjecture,({quantified(target)})).\n"
    with tempfile.NamedTemporaryFile(mode='w',suffix='.p',dir='/tmp',delete=True) as h:
        h.write(problem); h.flush(); run=subprocess.run(['vampire','--mode','casc','--time_limit','20','--proof','tptp',h.name],capture_output=True,text=True,timeout=22)
    out=run.stdout+run.stderr
    proof=[x for x in out.splitlines() if x.startswith('fof(')]
    return source,target,proof,out

def strip_outer(s):
    s=s.strip()
    while s.startswith('(') and s.endswith(')'):
        depth=0; ok=True
        for i,ch in enumerate(s):
            if ch=='(': depth+=1
            elif ch==')': depth-=1
            if depth==0 and i!=len(s)-1: ok=False; break
        if not ok: break
        s=s[1:-1].strip()
    return s

def split_top(s,sep=','):
    out=[]; start=0; dp=db=0
    for i,ch in enumerate(s):
        if ch=='(': dp+=1
        elif ch==')': dp-=1
        elif ch=='[': db+=1
        elif ch==']': db-=1
        elif ch==sep and dp==0 and db==0:
            out.append(s[start:i].strip()); start=i+1
    out.append(s[start:].strip())
    return out

def parse_fof(line):
    if not line.startswith('fof('): return None
    body=line[4:]
    if body.endswith(').'): body=body[:-2]
    parts=split_top(body,',')
    if len(parts)<3: return None
    formula=strip_outer(parts[2]); tail=','.join(parts[3:])
    mm=re.search(r'inference\(([^,\]]+)',tail)
    inf=mm.group(1) if mm else None
    return formula,inf

def remove_quantifier(s):
    s=strip_outer(s)
    if s.startswith('!') or s.startswith('?'):
        # ! [X,Y] : body
        k=s.find(':')
        if k>=0: s=s[k+1:].strip()
    return strip_outer(s)

def find_top_equality(s):
    s=remove_quantifier(s)
    # Only single positive equality literals are useful for exact lifecycle matching.
    dp=db=0
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

def parse_tptp_term(s):
    s=strip_outer(s.strip())
    if s.startswith('f(') and s.endswith(')'):
        inner=s[2:-1]; ps=split_top(inner,',')
        if len(ps)!=2: raise ValueError(s)
        return ('f',parse_tptp_term(ps[0]),parse_tptp_term(ps[1]))
    # Vampire may rename variables to X0, X1, V_X, etc.
    return ('v',s)

def term_key(t,names):
    if t[0] in ('v','var'):
        name=t[1]
        if name not in names: names[name]=len(names)
        return ('v',names[name])
    return ('f',term_key(t[1],names),term_key(t[2],names))

def pair_key(lhs,rhs):
    names={}; a=(term_key(lhs,names),term_key(rhs,names))
    names={}; b=(term_key(rhs,names),term_key(lhs,names))
    return min(a,b)

def clause_key(cl):
    try: return pair_key(cl.lhs,cl.rhs)
    except Exception: return None

def formula_key(formula):
    eq=find_top_equality(formula)
    if not eq: return None
    try: return pair_key(parse_tptp_term(eq[0]),parse_tptp_term(eq[1]))
    except Exception: return None

def engine_snapshots(m,source,target,seconds=5.0):
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':seconds,'maximum_term_size':90,'maximum_replay_term_size':300,'maximum_depth':18,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':768,'maximum_clauses':24000,'normalization_steps':384,'maximum_proof_nodes':60000})
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits); search=eng.search
    initial={clause_key(c) for c in search.clauses}; generated=set(initial); selected=set(); discarded=set(); simplified=set()
    passive=list(search.clauses); active=[]; age={id(c):i for i,c in enumerate(passive)}; given=0
    while passive and given<1024 and not search.expired():
        rules=[]
        for clause in active:
            rule=search.orient(clause)
            if rule is not None: rules.append(rule)
        idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
        c=passive.pop(idx); selected.add(clause_key(c)); red=search.interreduce(c,rules)
        if clause_key(red)!=clause_key(c): simplified.add(clause_key(red))
        c=red; active.append(c); given+=1
        rules=[]
        for clause in active:
            rule=search.orient(clause)
            if rule is not None: rules.append(rule)
        proposals=[]
        for oi,o in enumerate(active):
            for outer,inner,a,b in ((c,o,given,oi),(o,c,oi,given)):
                for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                    q=search.critical_pair(outer,inner,a,b,path)
                    if q is None: continue
                    q=search.interreduce(q,rules); k=clause_key(q); generated.add(k); proposals.append((search.target_score(q),q,k))
        proposals.sort(key=lambda x:x[0])
        for _,q,k in proposals[:search.limits['new_clauses_per_round']]:
            if search.add_clause(q): passive.append(q); age[id(q)]=len(age)
            else: discarded.add(k)
    for d in (initial,generated,selected,discarded,simplified): d.discard(None)
    return {'initial':initial,'generated':generated,'selected':selected,'discarded':discarded,'simplified':simplified}

def classify(k,snap):
    if k in snap['initial']: return 'initial'
    if k in snap['selected']: return 'selected'
    if k in snap['simplified']: return 'simplified'
    if k in snap['discarded']: return 'generated-discarded'
    if k in snap['generated']: return 'generated-unselected'
    return 'absent'

def main():
    td,m=load_solver(); results=[]
    try:
        for r in rows():
            source,target,proof,raw=vampire_trace(m,r); snap=engine_snapshots(m,source,target)
            eqs=[]
            for i,line in enumerate(proof):
                got=parse_fof(line)
                if not got: continue
                formula,inf=got; k=formula_key(formula)
                if k is None: continue
                status=classify(k,snap)
                eqs.append({'index':i,'formula':formula,'inference':inf,'status':status,'key':repr(k)})
            rec={'id':r['id'],'vampire_equalities':len(eqs),'first_divergence':None,'class_counts':{}}
            for e in eqs:
                rec['class_counts'][e['status']]=rec['class_counts'].get(e['status'],0)+1
                if rec['first_divergence'] is None and e['status'] in ('absent','generated-discarded','generated-unselected') and e['inference'] not in SKIP_INF:
                    rec['first_divergence']=e
            rec['engine_counts']={k:len(v) for k,v in snap.items()}; rec['vampire_path']=eqs
            results.append(rec)
            print('DIVERGENCE',json.dumps({k:v for k,v in rec.items() if k!='vampire_path'},sort_keys=True),flush=True)
    finally: td.cleanup()
    out=ROOT/'experiments/mathgraph/results/residual3-first-divergence.json'; out.parent.mkdir(parents=True,exist_ok=True); out.write_text(json.dumps({'rows':results},indent=2,sort_keys=True)+'\n')
    if any(r['vampire_equalities']==0 for r in results): raise SystemExit('parser produced zero equalities')
if __name__=='__main__': main()
