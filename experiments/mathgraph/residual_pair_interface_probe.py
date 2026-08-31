#!/usr/bin/env python3
import argparse, importlib.util, json, time


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

    calls_ind=calls_pair=0; exact_child=None
    def sig(q): return str(s.alpha_signature(q.lhs,q.rhs))
    def children_with(q,ps,cap=24):
        nonlocal calls_ind, exact_child
        out=[]; ss=set()
        for pi,p in enumerate(ps):
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
    indiv=[]
    for q in cand:
        xs=children_with(q,partners,24); indiv.append({sig(x) for x in xs})
        if exact_child is not None: break

    pair_records=[]; relational_children=[]
    if exact_child is None:
        for i in range(len(cand)):
            for j in range(i+1,len(cand)):
                q1,q2=cand[i],cand[j]; out=[]; ss=set()
                for a0,b0 in ((q1,q2),(q2,q1)):
                    for ar in (False,True):
                        aa=orient(a0,ar)
                        for br in (False,True):
                            bb=orient(b0,br)
                            for path in m.nonvariable_positions(aa.lhs,maximum_depth=8,include_root=True):
                                c=s.critical_pair(aa,bb,i,j,path)
                                if c is None: continue
                                calls_pair+=1; c=s.interreduce(c,rules); k=sig(c)
                                if k in ss: continue
                                ss.add(k); out.append(c)
                                if exact(e,c): exact_child=c; break
                            if exact_child is not None: break
                        if exact_child is not None: break
                    if exact_child is not None: break
                baseline=indiv[i] | indiv[j]
                novel=[x for x in out if sig(x) not in baseline]
                if novel:
                    novel.sort(key=s.target_score)
                    pair_records.append((len(novel), min(s.target_score(x) for x in novel), i, j, novel[:4]))
                    relational_children.extend(novel)
                if exact_child is not None: break
            if exact_child is not None: break

    pair_records.sort(key=lambda z:(-z[0],z[1],z[2],z[3]))
    result={'id':row['id'],'pre_trace':pre,'candidates':len(cand),'partners':len(partners),'individual_calls':calls_ind,'pair_calls':calls_pair,'relational_pairs':len(pair_records),'max_relational_novelty':max([x[0] for x in pair_records],default=0),'exact_child':exact_child is not None,'exact_child_replay':False,'target':{'found':False,'replay':False}}
    if exact_child is not None:
        ok,n=replay_target(e,s,exact_child); result['exact_child_replay']=ok; result['exact_child_nodes']=n
    if exact_child is None and pair_records:
        # Keep product structure through selection: choose top 4 pair states, then seed
        # both coordinates plus their genuinely pair-only relational consequences.
        seeds=[]; used=set(); chosen=[]
        for novelty,best,i,j,novels in pair_records[:4]:
            chosen.append({'i':i,'j':j,'novelty':novelty})
            for q in (cand[i],cand[j],*novels[:2]):
                k=(s.alpha_signature(q.lhs,q.rhs),q.lhs,q.rhs)
                if k not in used: used.add(k); seeds.append(q)
        te,ts=setup(target,420.0); added=[bool(ts.add_clause(q)) for q in seeds]
        tq=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
        out={'found':tq is not None,'replay':False,'pair_states':chosen,'seeds':len(seeds),'added':sum(added),'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
        if tq is not None:
            ok,n=replay_target(te,ts,tq); out['replay']=ok; out['proof_nodes']=n
        result['target']=out
    print('RESIDUAL_PAIR_INTERFACE '+json.dumps(result,sort_keys=True),flush=True)


if __name__=='__main__': main()
