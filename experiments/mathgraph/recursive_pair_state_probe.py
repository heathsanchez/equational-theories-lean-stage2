#!/usr/bin/env python3
import argparse, importlib.util, json, time, itertools


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True)
    a=ap.parse_args(); m=load(a.solver); row=json.load(open(a.row))
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    def setup(goal,seconds):
        lim=dict(base); lim['seconds']=seconds; e=m.TargetGroundedRefutation(source,goal,time.monotonic()+seconds,lim); return e,e.search
    def orient(q,r): return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
    def exact(e,q):
        z=e.inline_recipe(q); return (z.lhs,z.rhs)==target[:2] or (z.lhs,z.rhs)==(target[1],target[0])
    def replay_target(e,s,q):
        q=e.inline_recipe(q)
        if (q.lhs,q.rhs)==(target[1],target[0]): q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)!=target[:2]: return False,0
        nn,rr=s.compile(q); return m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000),len(nn)

    e,s=setup(target,1200.0); pre=[]
    for _ in range(3):
        rules=s.rules(); snap=list(rules); props=[]; proposed=0; stop=False
        for oi,o in enumerate(snap):
            if stop: break
            for ii,i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append((s.target_score(c),c)); proposed+=1
                    if proposed>=512: stop=True; break
        props.sort(key=lambda z:z[0]); added=0
        for _,q in props:
            if s.add_clause(q): s.superpositions+=1; added+=1
            if added>=64: break
        pre.append({'proposed':proposed,'added':added,'clauses':len(s.clauses)})

    rules=s.rules(); partners=sorted(rules,key=s.target_score)[:12]
    seen=set(); cand=[]
    for oi,o in enumerate(rules):
        if len(cand)>=64: break
        for ii,i in enumerate(rules):
            if len(cand)>=64: break
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules)
                if c.lhs==c.rhs: continue
                k=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if k in seen: continue
                seen.add(k); cand.append(c)
                if len(cand)>=64: break
    cand=sorted(cand,key=s.target_score)[:32]

    calls_ind=calls_pair=calls_triple=0; exact_child=None
    def sig(q): return str(s.alpha_signature(q.lhs,q.rhs))
    def individual_future(q,cap=16):
        nonlocal calls_ind, exact_child
        out=[]; ss=set()
        for pi,p in enumerate(partners):
            for a0,b0 in ((q,p),(p,q)):
                for ar in (False,True):
                    aa=orient(a0,ar)
                    for br in (False,True):
                        bb=orient(b0,br)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=7,include_root=True):
                            c=s.critical_pair(aa,bb,0,pi,path)
                            if c is None: continue
                            calls_ind+=1; c=s.interreduce(c,rules); k=sig(c)
                            if k in ss: continue
                            ss.add(k); out.append(c)
                            if exact(e,c): exact_child=c; return out
        out.sort(key=s.target_score); return out[:cap]
    indiv_cache={}
    def indiv(q):
        k=(sig(q),q.lhs,q.rhs)
        if k not in indiv_cache: indiv_cache[k]={sig(x) for x in individual_future(q)}
        return indiv_cache[k]
    def relational(q1,q2,cap=12,triple=False):
        nonlocal calls_pair,calls_triple,exact_child
        out=[]; ss=set()
        for a0,b0 in ((q1,q2),(q2,q1)):
            for ar in (False,True):
                aa=orient(a0,ar)
                for br in (False,True):
                    bb=orient(b0,br)
                    for path in m.nonvariable_positions(aa.lhs,maximum_depth=8 if not triple else 6,include_root=True):
                        c=s.critical_pair(aa,bb,0,1,path)
                        if c is None: continue
                        if triple: calls_triple+=1
                        else: calls_pair+=1
                        c=s.interreduce(c,rules); k=sig(c)
                        if k in ss: continue
                        ss.add(k); out.append(c)
                        if exact(e,c): exact_child=c; return out
        if not triple:
            base_sig=indiv(q1)|indiv(q2)
            out=[x for x in out if sig(x) not in base_sig]
        out.sort(key=s.target_score); return out[:cap]

    states=[]
    for i in range(len(cand)):
        for j in range(i+1,len(cand)):
            nov=relational(cand[i],cand[j],12)
            if exact_child is not None: break
            if nov: states.append((len(nov),min(s.target_score(x) for x in nov),cand[i],cand[j],nov))
        if exact_child is not None: break
    states.sort(key=lambda z:(-z[0],z[1])); frontier=states[:4]; trace=[]
    for generation in range(2):
        if exact_child is not None or not frontier: break
        next_states=[]; produced=0
        for _,_,q1,q2,nov in frontier:
            pool=nov[:6]; produced+=len(pool)
            for i in range(len(pool)):
                for j in range(i+1,len(pool)):
                    nov2=relational(pool[i],pool[j],10)
                    if exact_child is not None: break
                    if nov2: next_states.append((len(nov2),min(s.target_score(x) for x in nov2),pool[i],pool[j],nov2))
                if exact_child is not None: break
            if exact_child is not None: break
        next_states.sort(key=lambda z:(-z[0],z[1]))
        trace.append({'generation':generation+1,'input_states':len(frontier),'children':produced,'next_states':len(next_states),'max_novelty':max([x[0] for x in next_states],default=0)})
        frontier=next_states[:4]

    # Infer whether arity 3 adds information beyond every constituent pair.
    triple_records=[]
    if exact_child is None:
        tcand=cand[:10]
        pair_direct={}
        for i,j in itertools.combinations(range(len(tcand)),2):
            pair_direct[(i,j)]=relational(tcand[i],tcand[j],8)
            if exact_child is not None: break
        if exact_child is None:
            for i,j,k in itertools.combinations(range(len(tcand)),3):
                baseline={sig(x) for x in pair_direct[(i,j)]+pair_direct[(i,k)]+pair_direct[(j,k)]}
                novel=[]; ns=set()
                for a,b,cidx in ((i,j,k),(i,k,j),(j,k,i)):
                    for child in pair_direct[(min(a,b),max(a,b))][:4]:
                        for z in relational(child,tcand[cidx],8,True):
                            kz=sig(z)
                            if kz in baseline or kz in ns: continue
                            ns.add(kz); novel.append(z)
                            if exact_child is not None: break
                        if exact_child is not None: break
                    if exact_child is not None: break
                if novel:
                    novel.sort(key=s.target_score); triple_records.append((len(novel),min(s.target_score(x) for x in novel),i,j,k))
                if exact_child is not None: break
    triple_records.sort(key=lambda z:(-z[0],z[1],z[2],z[3],z[4]))

    result={'id':row['id'],'pre_trace':pre,'candidates':len(cand),'initial_pair_states':len(states),'initial_max_novelty':max([x[0] for x in states],default=0),'recursive_trace':trace,'individual_calls':calls_ind,'pair_calls':calls_pair,'triple_calls':calls_triple,'triple_states':len(triple_records),'max_triple_only_novelty':max([x[0] for x in triple_records],default=0),'top_triples':[{'i':x[2],'j':x[3],'k':x[4],'novelty':x[0]} for x in triple_records[:5]],'exact_child':exact_child is not None,'exact_child_replay':False}
    if exact_child is not None:
        ok,n=replay_target(e,s,exact_child); result['exact_child_replay']=ok; result['exact_child_nodes']=n
    print('RECURSIVE_PAIR_STATE '+json.dumps(result,sort_keys=True),flush=True)

if __name__=='__main__': main()
