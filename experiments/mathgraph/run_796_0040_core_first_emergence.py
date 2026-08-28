#!/usr/bin/env python3
"""Core-first MSI experiment for evaluation_normal_0040.

Deliberately strips away portfolio/bridge/target-distance retention heuristics.
The developmental state is only a quotient induced by protected continuations:

    x ~_B y iff every retained continuation gives the same verifier-visible outcome.

Start with B empty (one class). Generate proof situations by ordinary legal
superposition. Search for a continuation that separates a currently collapsed
pair; retain only that separator; recompute the quotient; repeat.

No Vampire IDs, named intermediates, frontier-vs-given labels, bridge scores,
or target-distance ranking are used to refine the representation. The public
theorem target is used only as the terminal verifier condition.
"""
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
    ap.add_argument('--seconds',type=float,default=150); ap.add_argument('--navigation-seconds',type=float,default=150); ap.add_argument('--seed-rounds',type=int,default=4)
    ap.add_argument('--states',type=int,default=96); ap.add_argument('--continuations',type=int,default=96)
    ap.add_argument('--max-separators',type=int,default=24); ap.add_argument('--closure-rounds',type=int,default=5)
    a=ap.parse_args(); m=load(SOLVER,'mg_core_first')
    hp=ROOT/'experiments/mathgraph/_runtime_core_first_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mg_core_first_helper'); row=h.load_row(a.input)
        source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
        lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'seconds':a.seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':128,'new_clauses_per_round':96,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
        eng=m.TargetGroundedRefutation(source,target,time.monotonic()+a.seconds,lim); s=eng.search; orig=s.critical_pair
        def orient(c,rev): return c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
        def key(r): return (s.alpha_signature(r.lhs,r.rhs),r.lhs,r.rhs)
        def sig(r): return str(s.alpha_signature(r.lhs,r.rhs))
        def exact_target(r): return (r.lhs,r.rhs)==target[:2] or (r.rhs,r.lhs)==target[:2]

        # Build a neutral population: exhaustive bounded legal expansion, retaining
        # alpha-distinct situations by structural size only. No target score.
        enum=0
        for _ in range(a.seed_rounds):
            if s.expired(): break
            rules=s.rules(); snap=list(rules); props=[]
            for oi,o in enumerate(snap):
                for ii,i in enumerate(snap):
                    for path in m.nonvariable_positions(o.lhs,maximum_depth=10,include_root=True):
                        if s.expired(): break
                        q=orig(o,i,oi,ii,path)
                        if q is None: continue
                        q=s.interreduce(q,rules); enum+=1
                        props.append((m.term_size(q.lhs)+m.term_size(q.rhs),str(s.alpha_signature(q.lhs,q.rhs)),q))
                    if s.expired(): break
                if s.expired(): break
            props.sort(key=lambda x:(x[0],x[1])); added=0
            for _,__,q in props:
                if s.add_clause(q): added+=1
                if added>=96: break

        population=[]; seen=set()
        for r in s.rules():
            k=key(r)
            if k not in seen: seen.add(k); population.append(r)
        population.sort(key=lambda r:(m.term_size(r.lhs)+m.term_size(r.rhs),sig(r)))
        population=population[:a.states]
        contexts=population[:a.continuations]

        # Outcome of applying one continuation to one state: the SET of verified
        # legal child signatures. This is the only observable used by the quotient.
        cache={}; calls=0
        def outcome(x,c):
            nonlocal calls
            ck=(key(x),key(c))
            if ck in cache:return cache[ck]
            out=set(); witness=None
            for A,B in ((x,c),(c,x)):
                for ar in (False,True):
                    aa=orient(A,ar)
                    for br in (False,True):
                        bb=orient(B,br)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=7,include_root=True):
                            z=orig(aa,bb,0,0,path)
                            if z is None:continue
                            calls+=1; out.add(sig(z))
                            if exact_target(z):witness=z
            v=(tuple(sorted(out)),witness); cache[ck]=v; return v

        protected=[]; histories=[]
        def fingerprint(x): return tuple(outcome(x,c)[0] for c in protected)
        target_recipe=None; target_origin=None
        # Counterexample-guided partition refinement. A separator is retained iff
        # it distinguishes a pair still identified by the current quotient.
        for step in range(a.max_separators):
            classes={}
            for x in population: classes.setdefault(fingerprint(x),[]).append(x)
            ambiguous=[xs for xs in classes.values() if len(xs)>1]
            found=None
            for xs in ambiguous:
                for i in range(len(xs)):
                    for j in range(i+1,len(xs)):
                        x,y=xs[i],xs[j]
                        for c in contexts:
                            if c in protected:continue
                            ox,wx=outcome(x,c); oy,wy=outcome(y,c)
                            if wx is not None: target_recipe=wx; target_origin='separator-probe'
                            if wy is not None: target_recipe=wy; target_origin='separator-probe'
                            if ox!=oy:
                                found=(x,y,c,len(ox),len(oy)); break
                        if found:break
                    if found:break
                if found:break
            histories.append({'step':step,'classes':len(classes),'ambiguous_classes':len(ambiguous),'separator_found':found is not None})
            if target_recipe is not None or found is None:break
            protected.append(found[2])

        # Give navigation its own fresh budget. The representation is now frozen:
        # no separator, feature, score, or proof-search heuristic is added here.
        s.deadline=time.monotonic()+a.navigation_seconds

        # Dynamics on the learned quotient. Add legal children, then only retain a
        # child when its protected fingerprint is a new interface state. This is
        # quotient navigation, not clause scoring.
        reps={fingerprint(x):x for x in population}; closure_enum=0
        for rnd in range(a.closure_rounds):
            if target_recipe is not None or s.expired():break
            new=[]
            current=list(reps.values())
            for xi,x in enumerate(current):
                for ci,c in enumerate(current):
                    for A,B in ((x,c),(c,x)):
                        for ar in (False,True):
                            aa=orient(A,ar)
                            for br in (False,True):
                                bb=orient(B,br)
                                for path in m.nonvariable_positions(aa.lhs,maximum_depth=9,include_root=True):
                                    z=orig(aa,bb,xi,ci,path)
                                    if z is None:continue
                                    closure_enum+=1
                                    if exact_target(z):target_recipe=z; target_origin='quotient-dynamics';break
                                    fp=fingerprint(z)
                                    if fp not in reps:
                                        reps[fp]=z; new.append(z)
                                if target_recipe:break
                            if target_recipe:break
                        if target_recipe:break
                    if target_recipe:break
                if target_recipe:break
            histories.append({'closure_round':rnd,'interface_states':len(reps),'new_interface_states':len(new)})
            if not new:break

        # Replay/judge only if terminal target was reached.
        judged=None
        if target_recipe is not None:
            rr=eng.inline_recipe(target_recipe)
            if (rr.lhs,rr.rhs)==(target[1],target[0]):rr=m.Recipe(rr.rhs,rr.lhs,'symmetry',(rr,))
            if (rr.lhs,rr.rhs)==target[:2]:
                nodes,root=s.compile(rr)
                if m.replay_dag(source,nodes,root,maximum_term_size=300,maximum_nodes=60000):
                    code,_=m.make_dag_certificate(target,nodes,root)
                    if hasattr(m,'_mg_elide_have_types'):
                        old=code.splitlines(); new=m._mg_elide_have_types(code).splitlines(); code='\n'.join(o if ':=' in o and o.rstrip().endswith(':= rfl') else n for o,n in zip(old,new))+'\n'
                    from dataclasses import replace
                    from judge.verify import _resolve_config,verify_answer
                    jr=verify_answer(row,json.dumps({'verdict':'true','code':code}),config=replace(_resolve_config(None),max_code_length=100000))
                    judged={'status':jr.get('status'),'error_code':jr.get('error_code'),'proof_nodes':len(nodes),'certificate_bytes':len(code.encode())}

        final_classes=len({fingerprint(x) for x in population})
        out={'id':RID,'principle':'quotient+continuation+verified-separator only','seed_enumerated':enum,'population':len(population),'candidate_continuations':len(contexts),'protected_separators':len(protected),'protected_separator_signatures':[sig(c) for c in protected],'final_population_classes':final_classes,'future_calls':calls,'closure_enumerated':closure_enum,'navigation_seconds':a.navigation_seconds,'interface_states_after_navigation':len(reps),'target_found':target_recipe is not None,'target_origin':target_origin,'judge':judged,'history':histories}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True);Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print('CORE_FIRST_EMERGENCE',json.dumps(out,sort_keys=True),flush=True)
    finally:hp.unlink(missing_ok=True)
if __name__=='__main__':main()
