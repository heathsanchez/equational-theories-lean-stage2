#!/usr/bin/env python3
"""Fast attachment test: preserve discovered interface relations instead of flattening a law bag.
Discovery is source-only. The target is revealed only after the replay-certified interface graph exists.
"""
import argparse, importlib.util, json, time

def load(path):
    sp=importlib.util.spec_from_file_location('mgsolver',path); m=importlib.util.module_from_spec(sp); sp.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); neutral=m.parse_equation('x = x'); target=m.parse_equation('x = x * x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    def setup(goal,sec):
        lim=dict(base); lim['seconds']=sec; e=m.TargetGroundedRefutation(source,goal,time.monotonic()+sec,lim); return e,e.search
    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names: names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))
    def skey(s,q): return (m.term_size(q.lhs)+m.term_size(q.rhs),str(s.alpha_signature(q.lhs,q.rhs)),m.render_term(q.lhs),m.render_term(q.rhs))
    t0=time.monotonic(); e,s=setup(neutral,20.0); pre=[]
    # Source-only three-generation development.
    for gen in range(1,4):
        rules=s.rules(); snap=list(rules); props=[]; proposed=0; stop=False
        for oi,o in enumerate(snap):
            if stop: break
            for ii,i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    props.append(s.interreduce(c,rules)); proposed+=1
                    if proposed>=512: stop=True; break
        props.sort(key=lambda q:skey(s,q)); added=0
        for q in props:
            if s.add_clause(q): s.superpositions+=1; added+=1
            if added>=64: break
        pre.append({'generation':gen,'proposed':proposed,'added':added,'clauses':len(s.clauses)})
    # Build replay-certified unary interface nodes, retaining their proof-bearing recipes.
    seen=set(); nodes=[]; rules=s.rules(); s.deadline=time.monotonic()+12.0; census=0
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired() or census>=176: break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules); vs=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in vs): continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen: continue
                seen.add(key); census+=1
                nn,rr=s.compile(c)
                if not m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000): continue
                ep=(nn[rr].lhs,nn[rr].rhs); act=canon(ep[0],ep[1])
                if act[2]!=('x',): continue
                nodes.append({'recipe':c,'lhs':act[0],'rhs':act[1],'size':m.term_size(act[0])+m.term_size(act[1]),'proof_nodes':len(nn)})
            if s.expired() or census>=176: break
        if s.expired() or census>=176: break
    # Deduplicate endpoints, but keep the cheapest proof-bearing representative.
    best={}
    for n in nodes:
        k=(m.render_term(n['lhs']),m.render_term(n['rhs']))
        if k not in best or n['proof_nodes']<best[k]['proof_nodes']: best[k]=n
    nodes=sorted(best.values(),key=lambda n:(n['size'],n['proof_nodes'],m.render_term(n['lhs']),m.render_term(n['rhs'])))[:48]
    # STRUCTURED ATTACHMENT: materialize nodes as a graph, then generate labelled edges
    # by pairwise critical interaction. Children remain attached to their parent pair.
    ge,gs=setup(neutral,18.0)
    for n in nodes: gs.add_clause(n['recipe'])
    graph_edges=[]; frontier=[]; grules=gs.rules(); cap=512
    for ai,a0 in enumerate(nodes):
        if len(graph_edges)>=cap: break
        for bi,b0 in enumerate(nodes):
            if len(graph_edges)>=cap: break
            # Interact proof-bearing parent recipes directly; do not flatten their endpoints.
            parents=[a0['recipe'],b0['recipe']]
            for oi,o in enumerate(parents):
                for ii,i in enumerate(parents):
                    for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                        c=gs.critical_pair(o,i,oi,ii,path)
                        if c is None: continue
                        c=gs.interreduce(c,grules)
                        if c.lhs==c.rhs: continue
                        nn,rr=gs.compile(c)
                        if not m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000): continue
                        graph_edges.append((ai,bi,c)); frontier.append(c)
                        if len(graph_edges)>=cap: break
                    if len(graph_edges)>=cap: break
                if len(graph_edges)>=cap: break
    # Only now reveal target. Rank graph children by target relevance and attach a small
    # structured neighbourhood, preserving each child's derivational recipe.
    def tscore(q):
        try: return m.target_score(q,target[0],target[1])
        except TypeError: return m.target_score(q.lhs,q.rhs,target[0],target[1])
    frontier.sort(key=lambda q:(tscore(q),m.term_size(q.lhs)+m.term_size(q.rhs),m.render_term(q.lhs),m.render_term(q.rhs)))
    attempts=[]; recovered=False
    for k in (8,16,32,64):
        te,ts=setup(target,8.0)
        # Seed parent nodes for selected edges plus their relational children.
        selected=frontier[:k]
        for q in selected: ts.add_clause(q)
        tq=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve(); replay=False; pn=None
        if tq is not None:
            q=te.inline_recipe(tq)
            if (q.lhs,q.rhs)==(target[1],target[0]): q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
            if (q.lhs,q.rhs)==target[:2]:
                nn,rr=ts.compile(q); replay=m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000); pn=len(nn)
        attempts.append({'k':k,'found':tq is not None,'replay':replay,'proof_nodes':pn})
        if replay: recovered=True; break
    out={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'interface_nodes':len(nodes),'graph_edges':len(graph_edges),'attempts':attempts,'recovered':recovered}
    print('STRUCTURED_INTERFACE_ATTACHMENT '+json.dumps(out,sort_keys=True),flush=True)
    if not recovered: raise SystemExit(2)
if __name__=='__main__': main()
