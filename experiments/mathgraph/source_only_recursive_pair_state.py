#!/usr/bin/env python3
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); neutral=m.parse_equation('x = x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':90,'maximum_replay_term_size':360,'maximum_depth':14,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':80,'maximum_clauses':18000,'normalization_steps':320,'maximum_proof_nodes':90000,'seconds':35.0})
    e=m.TargetGroundedRefutation(source,neutral,time.monotonic()+35.0,base); s=e.search
    def orient(q,r): return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
    def arity(q): return len(m.term_variables(q.lhs)|m.term_variables(q.rhs))
    def sig(q): return str(s.alpha_signature(q.lhs,q.rhs))
    def skey(q): return (m.term_size(q.lhs)+m.term_size(q.rhs),arity(q),sig(q),m.render_term(q.lhs),m.render_term(q.rhs))
    def joint(q1,q2): return len(m.term_variables(q1.lhs)|m.term_variables(q1.rhs)|m.term_variables(q2.lhs)|m.term_variables(q2.rhs))

    t0=time.monotonic(); pre=[]
    for gen in range(1,4):
        rules=s.rules(); snap=list(rules); props=[]; proposed=0; stop=False
        for oi,o in enumerate(snap):
            if stop: break
            for ii,i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=14,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append(c); proposed+=1
                    if proposed>=1024: stop=True; break
        buckets={1:[],2:[],3:[],4:[]}
        for q in props: buckets[min(4,max(1,arity(q)))].append(q)
        for xs in buckets.values(): xs.sort(key=skey)
        selected=[]
        for aa,n in ((1,20),(2,24),(3,24),(4,12)): selected.extend(buckets[aa][:n])
        if len(selected)<80:
            used={id(q) for q in selected}; selected.extend(sorted((q for q in props if id(q) not in used),key=skey)[:80-len(selected)])
        added=0
        for q in selected:
            if s.add_clause(q): s.superpositions+=1; added+=1
        pre.append({'generation':gen,'proposed':proposed,'added':added,'clauses':len(s.clauses)})

    rules=s.rules(); partners=sorted(rules,key=skey)[:12]
    raw=[]; seen=set()
    for q in rules:
        k=(sig(q),q.lhs,q.rhs)
        if q.lhs!=q.rhs and k not in seen: seen.add(k); raw.append(q)
    buckets={1:[],2:[],3:[],4:[]}
    for q in raw: buckets[min(4,max(1,arity(q)))].append(q)
    for xs in buckets.values(): xs.sort(key=skey)
    cand=[]
    for aa,n in ((1,8),(2,8),(3,8),(4,8)): cand.extend(buckets[aa][:n])
    cand=sorted(cand,key=skey)[:32]

    calls_ind=calls_pair=0
    indiv_cache={}
    def individual(q,cap=16):
        nonlocal calls_ind
        k=(sig(q),q.lhs,q.rhs)
        if k in indiv_cache: return indiv_cache[k]
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
                            calls_ind+=1; c=s.interreduce(c,rules)
                            if c.lhs==c.rhs: continue
                            z=sig(c)
                            if z in ss: continue
                            ss.add(z); out.append(c)
        out.sort(key=skey); out=out[:cap]; indiv_cache[k]=(out,{sig(x) for x in out}); return indiv_cache[k]

    def relational(q1,q2,cap=12):
        nonlocal calls_pair
        out=[]; ss=set()
        for a0,b0 in ((q1,q2),(q2,q1)):
            for ar in (False,True):
                aa=orient(a0,ar)
                for br in (False,True):
                    bb=orient(b0,br)
                    for path in m.nonvariable_positions(aa.lhs,maximum_depth=8,include_root=True):
                        c=s.critical_pair(aa,bb,0,1,path)
                        if c is None: continue
                        calls_pair+=1; c=s.interreduce(c,rules)
                        if c.lhs==c.rhs: continue
                        z=sig(c)
                        if z in ss: continue
                        ss.add(z); out.append(c)
        baseline=individual(q1)[1]|individual(q2)[1]
        out=[x for x in out if sig(x) not in baseline]
        out.sort(key=skey); return out[:cap]

    states=[]
    for i in range(len(cand)):
        for j in range(i+1,len(cand)):
            nov=relational(cand[i],cand[j],12)
            if nov: states.append({'a':cand[i],'b':cand[j],'nov':nov,'novelty':len(nov),'joint_arity':joint(cand[i],cand[j])})
    states.sort(key=lambda z:(-z['novelty'],-z['joint_arity'],skey(z['a']),skey(z['b'])))
    frontier=states[:6]; trace=[]; all_replayed=0; endpoint_arity={}
    for generation in range(1,4):
        if not frontier: break
        next_states=[]; child_count=0; replayed=0; child_ar={}
        for st in frontier:
            pool=st['nov'][:6]; child_count+=len(pool)
            for q in pool:
                ns,r=s.compile(q)
                if m.replay_dag(source,ns,r,maximum_term_size=360,maximum_nodes=90000):
                    replayed+=1; all_replayed+=1; aa=arity(ns[r]); child_ar[aa]=child_ar.get(aa,0)+1; endpoint_arity[aa]=endpoint_arity.get(aa,0)+1
            for i in range(len(pool)):
                for j in range(i+1,len(pool)):
                    nov2=relational(pool[i],pool[j],10)
                    if nov2: next_states.append({'a':pool[i],'b':pool[j],'nov':nov2,'novelty':len(nov2),'joint_arity':joint(pool[i],pool[j])})
        next_states.sort(key=lambda z:(-z['novelty'],-z['joint_arity'],skey(z['a']),skey(z['b'])))
        trace.append({'generation':generation,'input_states':len(frontier),'children':child_count,'replayed_children':replayed,'child_endpoint_arity':child_ar,'next_states':len(next_states),'max_novelty':max([z['novelty'] for z in next_states],default=0),'max_joint_arity':max([z['joint_arity'] for z in next_states],default=0)})
        frontier=next_states[:6]

    result={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'candidates':len(cand),'initial_states':len(states),'initial_max_novelty':max([z['novelty'] for z in states],default=0),'initial_max_joint_arity':max([z['joint_arity'] for z in states],default=0),'recursive_trace':trace,'individual_calls':calls_ind,'pair_calls':calls_pair,'replayed_children_total':all_replayed,'endpoint_arity':endpoint_arity}
    print('SOURCE_ONLY_RECURSIVE_PAIR_STATE '+json.dumps(result,sort_keys=True),flush=True)

if __name__=='__main__': main()
