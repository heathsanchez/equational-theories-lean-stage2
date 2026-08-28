#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
SOLVER=ROOT/'submissions/mathgraph/solver.py'
HELPER_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/normal0040-alpha-self-overlap-20260826/experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
RID='evaluation_normal_0040'

def load(path,name):
    s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True)
    ap.add_argument('--frontier-seconds',type=float,default=30); ap.add_argument('--given-seconds',type=float,default=10)
    ap.add_argument('--frontier-rounds',type=int,default=3); ap.add_argument('--given-steps',type=int,default=16)
    ap.add_argument('--candidate-budget',type=int,default=512); ap.add_argument('--behavioural-keep',type=int,default=64)
    ap.add_argument('--probe-partners',type=int,default=64); a=ap.parse_args()
    m=load(SOLVER,'mg_behavioural_exchange')
    hp=ROOT/'experiments/mathgraph/_runtime_behavioural_exchange_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mg_behavioural_exchange_helper'); row=h.load_row(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
        base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':128,'new_clauses_per_round':64,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
        def setup(seconds):
            lim=dict(base); lim['seconds']=seconds
            eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,lim); s=eng.search; orig=s.critical_pair
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
            s.critical_pair=lambda o,i,oi,ii,path: orig(expand_recipe(o),expand_recipe(i),oi,ii,path)
            return eng,s,orig,expand_recipe
        def orient(c,rev):return c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
        def exact_target(r):return (r.lhs,r.rhs)==target[:2] or (r.rhs,r.lhs)==target[:2]
        def finish(eng,s,r):
            rr=eng.inline_recipe(r)
            if (rr.lhs,rr.rhs)==(target[1],target[0]):rr=m.Recipe(rr.rhs,rr.lhs,'symmetry',(rr,))
            if (rr.lhs,rr.rhs)!=target[:2]:return None
            nodes,root=s.compile(rr)
            if not m.replay_dag(source,nodes,root,maximum_term_size=300,maximum_nodes=60000):return None
            code,_=m.make_dag_certificate(target,nodes,root)
            if hasattr(m,'_mg_elide_have_types'):
                old=code.splitlines(); new=m._mg_elide_have_types(code).splitlines(); code='\n'.join(o if ':=' in o and o.rstrip().endswith(':= rfl') else n for o,n in zip(old,new))+'\n'
            from dataclasses import replace
            from judge.verify import _resolve_config,verify_answer
            jr=verify_answer(row,json.dumps({'verdict':'true','code':code}),config=replace(_resolve_config(None),max_code_length=100000))
            return {'judge_status':jr.get('status'),'judge_error_code':jr.get('error_code'),'judge_message':jr.get('message'),'certificate_bytes':len(code.encode()),'proof_nodes':len(nodes)}

        # Portfolio A: streaming frontier, no named intermediates.
        ef,sf,origf,expf=setup(a.frontier_seconds); enumf=0; batch=128
        for _ in range(a.frontier_rounds):
            rules=sf.rules(); snap=list(rules); props=[]
            for oi,o in enumerate(snap):
                for ii,i in enumerate(snap):
                    for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                        if sf.expired():break
                        q=sf.critical_pair(o,i,oi,ii,path)
                        if q is None:continue
                        q=sf.interreduce(q,rules); props.append((sf.target_score(q),q)); enumf+=1
                        if len(props)>=batch:
                            props.sort(key=lambda x:x[0]); added=0
                            for _,z in props:
                                if sf.add_clause(z):sf.superpositions+=1; added+=1
                                if added>=64:break
                            props=[]; rules=sf.rules()
                    if sf.expired():break
                if sf.expired():break
            if props and not sf.expired():
                props.sort(key=lambda x:x[0]); added=0
                for _,z in props:
                    if sf.add_clause(z):sf.superpositions+=1; added+=1
                    if added>=64:break
            if sf.expired():break

        # Portfolio B: bounded given-clause activation, no named intermediates.
        eg,sg,origg,expg=setup(a.given_seconds)
        def variants(s,c):
            o=s.orient(c)
            if o is not None:return [o]
            z=[]
            if c.lhs[0]!='var':z.append(c)
            if c.rhs[0]!='var':z.append(m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
            return z
        def rkey(s,r):return (s.alpha_signature(r.lhs,r.rhs),r.lhs,r.rhs)
        pending=[]; queued=set(); processed=set(); active=[]
        def enqueue(r):
            k=rkey(sg,r)
            if k in queued or k in processed:return
            queued.add(k); pending.append(r)
        for r in sg.rules():enqueue(r)
        givens=0; enumg=0
        while pending and not sg.expired() and givens<a.given_steps:
            pending.sort(key=sg.target_score); g=pending.pop(0); k=rkey(sg,g); queued.discard(k)
            if k in processed:continue
            processed.add(k); givens+=1; rules=sg.rules(); props=[]; pairings=[]
            for p in active:pairings.extend(((g,p),(p,g)))
            pairings.append((g,g))
            for oi,(o,i) in enumerate(pairings):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    if sg.expired():break
                    q=sg.critical_pair(o,i,oi,oi+1,path)
                    if q is None:continue
                    q=sg.interreduce(q,rules); props.append((sg.target_score(q),q)); enumg+=1
                if sg.expired():break
            props.sort(key=lambda x:x[0]); added=0
            for _,q in props:
                before=len(sg.clauses)
                if sg.add_clause(q):
                    sg.superpositions+=1; added+=1
                    for c in sg.clauses[before:]:
                        for r in variants(sg,c):enqueue(r)
                    if added>=64:break
            active.append(g)

        # Candidate generation is broad, but retention is behavioural: a candidate must add
        # a one-step future signature not already represented by the current interface.
        pool=[expf(c) for c in sf.clauses]+[expf(expg(c)) for c in sg.clauses]
        probes=sorted(pool,key=sf.target_score)[:a.probe_partners]
        def sig_of(q):return str(sf.alpha_signature(q.lhs,q.rhs))
        def future_signature(rule):
            out=set(); target_child=None; calls=0
            for pi,p in enumerate(probes):
                for A,B in ((rule,p),(p,rule)):
                    for ar in (False,True):
                        aa=orient(A,ar)
                        for br in (False,True):
                            bb=orient(B,br)
                            for path in m.nonvariable_positions(aa.lhs,maximum_depth=6,include_root=True):
                                z=origf(aa,bb,0,pi,path)
                                if z is None:continue
                                calls+=1; out.add(sig_of(z))
                                if exact_target(z):target_child=z
            return out,target_child,calls

        baseline=set(); baseline_calls=0
        for r in probes:
            f,_,n=future_signature(r); baseline.update(f); baseline_calls+=n

        raw=[]; cross_enum=0
        for ai,A0 in enumerate(sf.clauses):
            A=expf(A0)
            for bi,B0 in enumerate(sg.clauses):
                B=expf(expg(B0))
                for ar in (False,True):
                    aa=orient(A,ar)
                    for br in (False,True):
                        bb=orient(B,br)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                            q=origf(aa,bb,ai,bi,path)
                            if q is None:continue
                            cross_enum+=1; raw.append((sf.target_score(q),q))
        raw.sort(key=lambda x:x[0]); candidates=[]; seen=set()
        for score,q in raw:
            k=(sf.alpha_signature(q.lhs,q.rhs),q.lhs,q.rhs)
            if k in seen:continue
            seen.add(k); candidates.append((score,q))
            if len(candidates)>=a.candidate_budget:break

        retained=[]; behavioural_tests=0; future_calls=0; novelty_sizes=[]; target_recipe=None; target_origin=None
        current=set(baseline)
        for _,q in candidates:
            fp,child,n=future_signature(q); behavioural_tests+=1; future_calls+=n
            novelty=fp-current
            if not novelty:continue
            retained.append(q); novelty_sizes.append(len(novelty)); current.update(fp)
            if child is not None:
                target_recipe=child; target_origin='behavioural-future'; break
            if len(retained)>=a.behavioural_keep:break

        # If no target appeared during the signature probe, give retained separators one shared closure pass.
        closure_enum=0
        if target_recipe is None:
            partners=pool+retained
            for ni,N in enumerate(retained):
                for pi,P in enumerate(partners):
                    for A,B,label in ((N,P,'separator-partner'),(P,N,'partner-separator')):
                        for ar in (False,True):
                            aa=orient(A,ar)
                            for br in (False,True):
                                bb=orient(B,br)
                                for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                                    z=origf(aa,bb,ni,pi,path)
                                    if z is None:continue
                                    closure_enum+=1
                                    if exact_target(z):target_recipe=z; target_origin=label; break
                                if target_recipe:break
                            if target_recipe:break
                        if target_recipe:break
                    if target_recipe:break
                if target_recipe:break
        judged=finish(ef,sf,target_recipe) if target_recipe is not None else None
        out={'id':RID,'frontier_clauses':len(sf.clauses),'frontier_enumerated':enumf,'given_clauses':len(sg.clauses),'given_steps':givens,'given_enumerated':enumg,'cross_enumerated':cross_enum,'candidate_budget':len(candidates),'probe_partners':len(probes),'baseline_future_signatures':len(baseline),'baseline_future_calls':baseline_calls,'behavioural_tests':behavioural_tests,'future_calls':future_calls,'behavioural_retained':len(retained),'novelty_sizes':novelty_sizes,'closure_enumerated':closure_enum,'target_found':target_recipe is not None,'target_origin':target_origin,'judge':judged}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('BEHAVIOURAL_SEPARATOR_EXCHANGE',json.dumps(out,sort_keys=True),flush=True)
    finally:hp.unlink(missing_ok=True)
if __name__=='__main__':main()
