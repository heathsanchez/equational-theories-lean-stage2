#!/usr/bin/env python3
import importlib.util, json, re, subprocess, sys, tempfile, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
IDS={'hard1_0067','hard2_0107','hard3_0208'}

def load_solver():
    text=subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)
    td=tempfile.TemporaryDirectory(); p=Path(td.name)/'solver796.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg796div',p); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)
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

def clause_canon(m,cl):
    try:
        names={}; a=(m.alpha_canonical_term(cl.lhs,names),m.alpha_canonical_term(cl.rhs,names))
        names={}; b=(m.alpha_canonical_term(cl.rhs,names),m.alpha_canonical_term(cl.lhs,names))
        return min(a,b)
    except Exception: return None

def engine_snapshots(m,source,target,seconds=5.0):
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':seconds,'maximum_term_size':90,'maximum_replay_term_size':300,'maximum_depth':18,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':768,'maximum_clauses':24000,'normalization_steps':384,'maximum_proof_nodes':60000})
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits)
    search=eng.search
    seen_initial={clause_canon(m,c) for c in search.clauses}
    generated=set(seen_initial); selected=set(); discarded=set(); simplified=set()
    passive=list(search.clauses); active=[]; age={id(c):i for i,c in enumerate(passive)}; given=0
    while passive and given<1024 and not search.expired():
        rules=[]
        for clause in active:
            rule=search.orient(clause)
            if rule is not None: rules.append(rule)
        idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
        c=passive.pop(idx); selected.add(clause_canon(m,c)); red=search.interreduce(c,rules)
        if clause_canon(m,red)!=clause_canon(m,c): simplified.add(clause_canon(m,red))
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
                    q=search.interreduce(q,rules); k=clause_canon(m,q); generated.add(k); proposals.append((search.target_score(q),q,k))
        proposals.sort(key=lambda x:x[0])
        for _,q,k in proposals[:search.limits['new_clauses_per_round']]:
            if search.add_clause(q): passive.append(q); age[id(q)]=len(age)
            else: discarded.add(k)
    return {'initial':seen_initial,'generated':generated,'selected':selected,'discarded':discarded,'simplified':simplified}

def extract_equalities(lines):
    out=[]
    for i,line in enumerate(lines):
        if 'inference(' not in line: continue
        m=re.search(r'fof\([^,]+,[^,]+,\((.*?)\),inference\(([^,\]]+)',line)
        if not m: continue
        formula=m.group(1); inf=m.group(2)
        if '=' not in formula: continue
        out.append({'index':i,'formula':formula,'inference':inf,'line':line})
    return out

def rough_norm_formula(s):
    s=re.sub(r'\s+','',s)
    s=s.replace('~','')
    return s

def main():
    td,m=load_solver(); results=[]
    try:
        for r in rows():
            source,target,proof,raw=vampire_trace(m,r)
            snap=engine_snapshots(m,source,target)
            eqs=extract_equalities(proof)
            rec={'id':r['id'],'vampire_equalities':len(eqs),'first_divergence':None,'class_counts':{}}
            # TPTP syntactic matching is approximate; classify derived equalities by whether exact rendered sides occur among our clause renderings.
            pools={k:set() for k in snap}
            for k,vals in snap.items():
                for v in vals:
                    if v is None: continue
                    pools[k].add(str(v))
            for e in eqs:
                f=rough_norm_formula(e['formula'])
                status='absent'
                # record first Vampire derived equality after source whose text has no obvious analogue in generated canonical strings.
                if any(frag in ''.join(pools['generated']) for frag in re.findall(r'V_[A-Z]|f',f)[:1]):
                    status='generated-unknown-match'
                e['status']=status
                rec['class_counts'][status]=rec['class_counts'].get(status,0)+1
                if rec['first_divergence'] is None and status=='absent' and e['inference'] not in ('cnf_transformation','ennf_transformation','skolemize','negated_conjecture','reorient_equations','definition_folding'):
                    rec['first_divergence']=e
            rec['engine_counts']={k:len(v) for k,v in snap.items()}
            results.append(rec); print('DIVERGENCE',json.dumps(rec,sort_keys=True),flush=True)
    finally: td.cleanup()
    out=ROOT/'experiments/mathgraph/results/residual3-first-divergence.json'; out.parent.mkdir(parents=True,exist_ok=True); out.write_text(json.dumps({'rows':results},indent=2,sort_keys=True)+'\n')
if __name__=='__main__': main()
