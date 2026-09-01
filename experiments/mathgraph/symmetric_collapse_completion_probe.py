#!/usr/bin/env python3
import argparse, importlib.util, json, time

def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--row',required=True);ap.add_argument('--seconds',type=float,default=90.0);a=ap.parse_args()
    m=load(a.solver);row=json.load(open(a.row));source=m.parse_equation(row['equation1']);actual=m.parse_equation(row['equation2']);collapse_target=m.parse_equation('x = y')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE);base.update({'maximum_term_size':110,'maximum_replay_term_size':420,'maximum_depth':16,'maximum_rules':1600,'maximum_rounds':256,'new_clauses_per_round':128,'maximum_clauses':24000,'normalization_steps':512,'maximum_proof_nodes':120000})
    def setup(goal,sec):
        lim=dict(base);lim['seconds']=sec;e=m.TargetGroundedRefutation(source,goal,time.monotonic()+sec,lim);return e,e.search
    t0=time.monotonic();e,s=setup(collapse_target,a.seconds)
    initial=list(s.rules());sym_added=0
    for q in initial:
        rev=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if s.add_clause(rev):sym_added+=1
    # Seed one exhaustive symmetric self-overlap generation before the normal engine.
    rules=s.rules();props=[];proposed=0
    for oi,o in enumerate(list(rules)):
        for ii,i in enumerate(list(rules)):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=16,include_root=True):
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None:continue
                c=s.interreduce(c,rules)
                if c.lhs==c.rhs:continue
                props.append((s.target_score(c),m.term_size(c.lhs)+m.term_size(c.rhs),c));proposed+=1
                if proposed>=4096:break
            if proposed>=4096:break
        if proposed>=4096:break
    props.sort(key=lambda z:(z[0],z[1]));seeded=0
    for _,_,q in props:
        if s.add_clause(q):s.superpositions+=1;seeded+=1
        if seeded>=256:break
    q=s.collapse_proof() or s.target_proof(s.rules()) or s.solve();collapse_replay=False;collapse_nodes=None
    if q is not None:
        q=e.inline_recipe(q)
        if (q.lhs,q.rhs)==(collapse_target[1],collapse_target[0]):q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)==collapse_target[:2]:
            nn,rr=s.compile(q);collapse_replay=m.replay_dag(source,nn,rr,maximum_term_size=420,maximum_nodes=120000);collapse_nodes=len(nn)
    actual_replay=False;actual_nodes=None;cert_bytes=None
    if collapse_replay:
        # A fresh actual-target engine gets the proof-bearing universal collapse clause.
        ae,asrch=setup(actual,min(30.0,a.seconds));asrch.add_clause(q)
        z=asrch.collapse_proof() or asrch.target_proof(asrch.rules()) or asrch.solve()
        if z is not None:
            z=ae.inline_recipe(z)
            if (z.lhs,z.rhs)==(actual[1],actual[0]):z=m.Recipe(z.rhs,z.lhs,'symmetry',(z,))
            if (z.lhs,z.rhs)==actual[:2]:
                nn,rr=asrch.compile(z);actual_replay=m.replay_dag(source,nn,rr,maximum_term_size=420,maximum_nodes=120000);actual_nodes=len(nn)
                if actual_replay:
                    code,_=m.make_dag_certificate(actual,nn,rr);cert_bytes=len(code.encode())
    print('SYMMETRIC_COLLAPSE_COMPLETION '+json.dumps({'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'initial_rules':len(initial),'sym_added':sym_added,'proposed':proposed,'seeded':seeded,'collapse_found':q is not None,'collapse_replay':collapse_replay,'collapse_nodes':collapse_nodes,'actual_replay':actual_replay,'actual_nodes':actual_nodes,'certificate_bytes':cert_bytes,'rounds':s.rounds,'superpositions':s.superpositions,'clauses':len(s.clauses)},sort_keys=True),flush=True)
if __name__=='__main__':main()
