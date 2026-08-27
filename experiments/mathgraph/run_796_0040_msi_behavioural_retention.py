#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from collections import defaultdict
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
SOLVER=ROOT/'submissions/mathgraph/solver.py'; RID='evaluation_normal_0040'

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def row_for(path):
    with open(path) as f:
        for line in f:
            r=json.loads(line)
            if r.get('id')==RID:return r
    raise RuntimeError('0040 not found')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',required=True); ap.add_argument('--output',required=True)
    ap.add_argument('--seconds',type=float,default=45.0)
    ap.add_argument('--partners',type=int,default=12)
    ap.add_argument('--max-reps',type=int,default=2)
    ap.add_argument('--max-behavioural-retains',type=int,default=64)
    a=ap.parse_args()
    m=load(SOLVER,'mg_msi_retention')
    row=row_for(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':a.seconds,'maximum_term_size':65,'maximum_replay_term_size':300,
                   'maximum_depth':12,'maximum_rules':768,'maximum_rounds':100000,
                   'new_clauses_per_round':64,'maximum_clauses':12000,
                   'normalization_steps':256,'maximum_proof_nodes':60000})
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+a.seconds,limits); s=eng.search
    orig_cp=s.critical_pair
    def expand_term(t):
        if t[0]=='var' and t[1] in eng.reverse_constants:return expand_term(eng.reverse_constants[t[1]])
        if t[0]=='op':return ('op',expand_term(t[1]),expand_term(t[2]))
        return t
    def expand_recipe(r,cache=None):
        cache={} if cache is None else cache
        if id(r) in cache:return cache[id(r)]
        ps=tuple(expand_recipe(p,cache) for p in r.parents); data=r.data
        if r.kind=='source':
            sub,rev=data; data=(tuple((k,expand_term(v)) for k,v in sub),rev)
        elif r.kind=='instantiate':data=tuple((k,expand_term(v)) for k,v in data)
        elif r.kind=='congruence':data=(data[0],expand_term(data[1]))
        q=m.Recipe(expand_term(r.lhs),expand_term(r.rhs),r.kind,ps,data); cache[id(r)]=q; return q
    def cp(o,i,oi,ii,path):return orig_cp(expand_recipe(o),expand_recipe(i),oi,ii,path)
    s.critical_pair=cp

    def variants(c):
        o=s.orient(c)
        if o is not None:return [o]
        z=[]
        if c.lhs[0]!='var':z.append(c)
        if c.rhs[0]!='var':z.append(m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
        return z
    def akey(r):return s.alpha_signature(r.lhs,r.rhs)
    def classkey(r):
        k=akey(r); rev=s.alpha_signature(r.rhs,r.lhs)
        return min(str(k),str(rev))
    def exactkey(r):return (akey(r),r.lhs,r.rhs)
    def fingerprint(rule,partners):
        out=set(); total=0
        rules=s.rules()
        for pi,p in enumerate(partners):
            for outer,inner in ((rule,p),(p,rule)):
                for path in m.nonvariable_positions(outer.lhs,maximum_depth=4,include_root=True):
                    if s.expired():return frozenset(out),total
                    q=s.critical_pair(outer,inner,0,pi+1,path)
                    if q is None:continue
                    q=s.interreduce(q,rules); total+=1
                    out.add(str(s.alpha_signature(q.lhs,q.rhs)))
        return frozenset(out),total

    reps=defaultdict(list)
    for c in s.clauses: reps[classkey(c)].append(c)
    pending=[]; queued=set(); processed=set(); active=[]
    collisions=0; fp_calls=0; fp_outputs=0; behavioural_retains=0; matched_discards=0
    useful={'f217':False,'f258':False,'f259':False,'target':False}
    # Known corridor signatures are used only as diagnostics, never as search guidance.
    def enqueue(r):
        k=exactkey(r)
        if k in queued or k in processed:return
        queued.add(k); pending.append(r)
    for r in s.rules():enqueue(r)
    given=0; enumerated=0
    found=None
    while pending and not s.expired():
        rules=s.rules(); goal=s.target_proof(rules)
        if goal is not None:
            found=goal; useful['target']=True; break
        pending.sort(key=s.target_score); g=pending.pop(0); gk=exactkey(g); queued.discard(gk)
        if gk in processed:continue
        processed.add(gk); given+=1
        partners=active[-64:]; props=[]; pairings=[]
        for p in partners: pairings.extend(((g,p),(p,g)))
        pairings.append((g,g))
        for oi,(o,i) in enumerate(pairings):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired():break
                q=s.critical_pair(o,i,oi,oi+1,path)
                if q is None:continue
                q=s.interreduce(q,rules); props.append((s.target_score(q),q)); enumerated+=1
            if s.expired():break
        props.sort(key=lambda x:x[0]); added=0
        for _,q in props:
            before=len(s.clauses); ok=s.add_clause(q)
            retained=False
            if ok:
                retained=True
                reps[classkey(q)].append(s.clauses[-1])
            else:
                ck=classkey(q); same=reps.get(ck,[])
                if same and len(same)<a.max_reps and behavioural_retains<a.max_behavioural_retains:
                    collisions+=1; frozen=(active+[g])[-a.partners:]
                    fq,nq=fingerprint(q,frozen); fp_calls+=1; fp_outputs+=nq
                    differs=True
                    for rep in same:
                        fr,nr=fingerprint(rep,frozen); fp_calls+=1; fp_outputs+=nr
                        if fq==fr:
                            differs=False; matched_discards+=1; break
                    if differs:
                        candidate=s.orient(q) or q
                        if candidate.lhs!=candidate.rhs and max(m.term_size(candidate.lhs),m.term_size(candidate.rhs))<=limits['maximum_term_size']:
                            s.clauses.append(candidate)
                            s.maximum_recipe_cost=max(s.maximum_recipe_cost,candidate.cost)
                            s.generated+=1
                            reps[ck].append(candidate)
                            behavioural_retains+=1; retained=True
            if retained:
                s.superpositions+=1; added+=1
                for c in s.clauses[before:]:
                    for r in variants(c):enqueue(r)
                if added>=64:break
        active.append(g)
        if len(s.clauses)>=limits['maximum_clauses']:break
    if found is None: found=s.target_proof(s.rules())
    replay=False; nodes=0
    if found is not None:
        try:
            ns,root=s.compile(found); nodes=len(ns); replay=m.replay_dag(source,ns,root,maximum_term_size=300,maximum_nodes=60000)
        except Exception: replay=False
    out={'id':RID,'given_steps':given,'enumerated':enumerated,'clauses':len(s.clauses),
         'behavioural_collisions_tested':collisions,'fingerprint_calls':fp_calls,
         'fingerprint_outputs':fp_outputs,'behavioural_retains':behavioural_retains,
         'matched_discards':matched_discards,'found_recipe':found is not None,
         'replay':replay,'proof_nodes':nodes,'expired':s.expired()}
    Path(a.output).parent.mkdir(parents=True,exist_ok=True)
    Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('MSI_BEHAVIOURAL_RETENTION',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__':main()
