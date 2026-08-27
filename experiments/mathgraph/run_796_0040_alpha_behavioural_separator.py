#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
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
    ap.add_argument('--seconds',type=float,default=30.0)
    ap.add_argument('--partners',type=int,default=12)
    ap.add_argument('--max-collisions',type=int,default=200)
    a=ap.parse_args()
    m=load(SOLVER,'mg_alpha_behaviour')
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
    def exactkey(r):return (akey(r),r.lhs,r.rhs)
    def fingerprint(rule,partners):
        out=set(); total=0
        for pi,p in enumerate(partners):
            for outer,inner in ((rule,p),(p,rule)):
                for path in m.nonvariable_positions(outer.lhs,maximum_depth=4,include_root=True):
                    if s.expired():return sorted(map(str,out)),total
                    q=s.critical_pair(outer,inner,0,pi+1,path)
                    if q is None:continue
                    q=s.interreduce(q,s.rules()); total+=1
                    out.add(str(s.alpha_signature(q.lhs,q.rhs)))
        return sorted(out),total

    pending=[]; queued=set(); processed=set(); active=[]; collisions=[]; separated=[]
    def enqueue(r):
        k=exactkey(r)
        if k in queued or k in processed:return
        queued.add(k); pending.append(r)
    for r in s.rules():enqueue(r)
    given=0; enumerated=0
    while pending and not s.expired() and len(collisions)<a.max_collisions:
        pending.sort(key=s.target_score); g=pending.pop(0); gk=exactkey(g); queued.discard(gk)
        if gk in processed:continue
        processed.add(gk); given+=1; rules=s.rules(); partners=active[-64:]; props=[]
        pairings=[]
        for p in partners:
            pairings.append((g,p)); pairings.append((p,g))
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
            before_rules=s.rules(); same=[r for r in before_rules if akey(r)==akey(q)]
            before=len(s.clauses); ok=s.add_clause(q)
            if ok:
                s.superpositions+=1; added+=1
                for c in s.clauses[before:]:
                    for r in variants(c):enqueue(r)
                if added>=64:break
            elif same and len(collisions)<a.max_collisions:
                rep=min(same,key=s.target_score)
                frozen=(active+[g])[-a.partners:]
                fq,nq=fingerprint(q,frozen); fr,nr=fingerprint(rep,frozen)
                rec={'alpha':str(akey(q)),'candidate':[str(q.lhs),str(q.rhs)],
                     'representative':[str(rep.lhs),str(rep.rhs)],
                     'candidate_future':fq,'representative_future':fr,
                     'candidate_outputs':nq,'representative_outputs':nr,
                     'separated':fq!=fr}
                collisions.append(rec)
                if rec['separated']:
                    separated.append(rec)
                    break
        active.append(g)
        if separated:break
    out={'id':RID,'given_steps':given,'enumerated':enumerated,'clauses':len(s.clauses),
         'alpha_collisions_tested':len(collisions),'behavioural_separators':len(separated),
         'separator':separated[0] if separated else None,'expired':s.expired()}
    Path(a.output).parent.mkdir(parents=True,exist_ok=True)
    Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('ALPHA_BEHAVIOURAL_SEPARATOR',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__':main()
