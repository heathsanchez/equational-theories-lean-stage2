#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import sys
import time
from itertools import product
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('normal0040_context_bridge_helper', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

ROOT = Path('/tmp/sair_stage1_eval/evaluation_normal.jsonl')
OUT = Path('experiments/mathgraph/results/normal0040-target-context-bridge.json')
RID = 'evaluation_normal_0040'
MAX_NODES = 90000
MAX_TERM_SIZE = 96
BEAM = 220
CONG_BEAM = 64
TERM_BEAM = 30
ROUNDS = 5
SECONDS = 35.0


def load_row():
    for line_no, line in enumerate(ROOT.read_text().splitlines(), 1):
        if not line.strip():
            continue
        row = json.loads(line)
        rid = row.get('id') or row.get('problem_id') or row.get('name') or f'evaluation_normal_{line_no-1:04d}'
        if rid == RID:
            return row
    raise RuntimeError('missing ' + RID)


def fields(row):
    def pick(*ks):
        for k in ks:
            if isinstance(row.get(k), str): return row[k]
    return pick('equation1','equation_1','source','hypothesis','lhs_equation'), pick('equation2','equation_2','target','conclusion','rhs_equation')


def main():
    m = h.load_solver(); row = load_row(); e1,e2 = fields(row)
    source = m.parse_equation(e1); target = m.parse_equation(e2); tl,tr = target[:2]
    deadline = time.monotonic() + SECONDS
    nodes=[]; depth=[]; best={}; source_cache=set()

    def add(n,d):
        if len(nodes)>=MAX_NODES: return None
        if m.term_size(n.lhs)>MAX_TERM_SIZE or m.term_size(n.rhs)>MAX_TERM_SIZE: return None
        key=(n.lhs,n.rhs); old=best.get(key)
        if old is not None and depth[old] <= d: return old
        nodes.append(n); depth.append(d); i=len(nodes)-1; best[key]=i; return i
    def M(a,b): return ('op',a,b)
    def R(t,d=0): return add(m.EqualityNode(t,t,'reflexivity',constructor='target-context-bridge'),d)
    def S(i,d):
        if i is None:return None
        p=nodes[i]; return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='target-context-bridge'),d)
    def T(i,j,d):
        if i is None or j is None:return None
        a,b=nodes[i],nodes[j]
        if a.rhs!=b.lhs:return None
        return add(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j),constructor='target-context-bridge'),d)
    def C(i,j,d):
        if i is None or j is None:return None
        a,b=nodes[i],nodes[j]
        lhs=M(a.lhs,b.lhs); rhs=M(a.rhs,b.rhs)
        if m.term_size(lhs)>MAX_TERM_SIZE or m.term_size(rhs)>MAX_TERM_SIZE:return None
        i1=add(m.EqualityNode(M(a.lhs,b.lhs),M(a.rhs,b.lhs),'congruence on left child',parents=(i,),context=('left',b.lhs),constructor='target-context-bridge'),d)
        if i1 is None:return None
        i2=add(m.EqualityNode(M(a.rhs,b.lhs),M(a.rhs,b.rhs),'congruence on right child',parents=(j,),context=('right',a.rhs),constructor='target-context-bridge'),d)
        return T(i1,i2,d)
    def H(args,d):
        sl,sr,sv=source; mp=dict(zip(sv,args)); key=tuple(mp[v] for v in sv)
        if key in source_cache:return None
        source_cache.add(key); lhs=m.substitute(sl,mp); rhs=m.substitute(sr,mp)
        return add(m.EqualityNode(lhs,rhs,'source instance',substitution=tuple((v,mp[v]) for v in sv),constructor='target-context-bridge'),d)

    target_terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr)); variables={('var',v) for v in source[2]}|{('var',v) for v in target[2]}
    vocab=sorted(target_terms|variables,key=lambda t:(m.term_size(t),m.render_term(t)))
    for t in vocab:R(t)
    sv=source[2]; fills=vocab[:14]
    for pattern in source[:2]:
        for concrete in vocab:
            partial={}
            if not m.match_term(pattern,concrete,partial):continue
            missing=[v for v in sv if v not in partial]
            for fill in product(fills,repeat=len(missing)):
                if time.monotonic()>=deadline or len(nodes)>=12000:break
                mp=dict(partial);mp.update(zip(missing,fill));H(tuple(mp[v] for v in sv),0)

    def score(i):
        n=nodes[i]; direct=m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr); sym=m.structural_distance(n.rhs,tl)+m.structural_distance(n.lhs,tr)
        exposed=sum(t in target_terms for t in m.walk_subterms(n.lhs))+sum(t in target_terms for t in m.walk_subterms(n.rhs))
        return (0 if (n.lhs,n.rhs)==(tl,tr) else 1,min(direct,sym),-exposed,m.term_size(n.lhs)+m.term_size(n.rhs),depth[i],i)

    for r in range(1,ROUNDS+1):
        if best.get((tl,tr)) is not None or time.monotonic()>=deadline:break
        ranked=sorted(set(best.values()),key=score)[:BEAM]
        for i in ranked:S(i,r)
        ranked=sorted(set(best.values()),key=score)[:BEAM]; by_lhs={};by_rhs={}
        for i in ranked:
            by_lhs.setdefault(nodes[i].lhs,[]).append(i);by_rhs.setdefault(nodes[i].rhs,[]).append(i)
        for mid,lefts in by_rhs.items():
            for i in lefts[:12]:
                for j in by_lhs.get(mid,[])[:12]:T(i,j,r)
        cr=sorted(set(best.values()),key=score)[:CONG_BEAM]
        for i in cr:
            for j in cr:
                if time.monotonic()>=deadline:break
                C(i,j,r)
        dyn=[];seen=set()
        for i in sorted(set(best.values()),key=score)[:BEAM]:
            for side in (nodes[i].lhs,nodes[i].rhs):
                for t in m.walk_subterms(side):
                    if t not in seen and m.term_size(t)<=28:seen.add(t);dyn.append(t)
        dyn=sorted(dyn,key=lambda t:(min(m.structural_distance(t,tl),m.structural_distance(t,tr)),m.term_size(t),m.render_term(t)))[:TERM_BEAM]
        for pattern in source[:2]:
            for concrete in dyn:
                partial={}
                if not m.match_term(pattern,concrete,partial):continue
                missing=[v for v in sv if v not in partial]
                for fill in product(dyn[:12],repeat=len(missing)):
                    if time.monotonic()>=deadline:break
                    mp=dict(partial);mp.update(zip(missing,fill));H(tuple(mp[v] for v in sv),r)
        print('BASE_ROUND',json.dumps({'round':r,'nodes':len(nodes),'equalities':len(best),'best_score':list(score(sorted(set(best.values()),key=score)[0]))}),flush=True)

    baseline=best.get((tl,tr)); pre_bridge_nodes=len(nodes)

    # Ensure both orientations of every verified equality are addressable.
    for i in list(set(best.values())):
        if time.monotonic()>=deadline:break
        S(i,ROUNDS+1)

    # Target-directed recursive context synthesis. Unlike beam congruence, this asks
    # specifically whether the exact target equality can be assembled from already
    # verified child equalities, regardless of their global rank.
    memo={}; constructing=set()
    def derive(a,b,d=ROUNDS+2):
        key=(a,b)
        if key in best:return best[key]
        if a==b:return R(a,d)
        if key in memo:return memo[key]
        if key in constructing:return None
        constructing.add(key); ans=None
        if isinstance(a,tuple) and isinstance(b,tuple) and len(a)>=3 and len(b)>=3 and a[0]=='op' and b[0]=='op':
            li=derive(a[1],b[1],d); ri=derive(a[2],b[2],d)
            if li is not None and ri is not None: ans=C(li,ri,d)
        constructing.remove(key); memo[key]=ans
        return ans

    direct_context=derive(tl,tr)

    # Full verified endpoint bridge: look for tl = u and u = tr across the complete
    # equality set, with target-directed context synthesis allowed on either leg.
    bridge=None; bridge_mid=None
    if direct_context is None:
        endpoints=set()
        for i in set(best.values()): endpoints.add(nodes[i].lhs);endpoints.add(nodes[i].rhs)
        mids=sorted(endpoints,key=lambda u:(m.structural_distance(tl,u)+m.structural_distance(u,tr),m.term_size(u),m.render_term(u)))[:5000]
        for u in mids:
            if time.monotonic()>=deadline:break
            a=derive(tl,u); b=derive(u,tr)
            if a is not None and b is not None:
                bridge=T(a,b,ROUNDS+3);bridge_mid=u;break

    root=best.get((tl,tr)); replayed=False; replay_error=None
    if root is not None:
        try: replayed=bool(m.replay_dag(source,nodes,root,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES))
        except Exception as exc: replay_error=type(exc).__name__+': '+str(exc)

    closest=[]
    for i in sorted(set(best.values()),key=score)[:12]:
        n=nodes[i];closest.append({'lhs':m.render_term(n.lhs),'rhs':m.render_term(n.rhs),'kind':n.kind,'depth':depth[i],'score':list(score(i)[:-1])})
    out={'schema':'mathgraph.normal0040-target-context-bridge.v1','id':RID,'equation1':e1,'equation2':e2,'baseline_found_before_bridge':baseline is not None,'pre_bridge_nodes':pre_bridge_nodes,'post_bridge_nodes':len(nodes),'direct_context_found':direct_context is not None,'bridge_mid':m.render_term(bridge_mid) if bridge_mid is not None else None,'found':root is not None,'replayed':replayed,'replay_error':replay_error,'closest':closest,'memo_attempts':len(memo)}
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('CONTEXT_BRIDGE_SUMMARY',json.dumps(out,sort_keys=True),flush=True)
    if root is not None and not replayed:raise SystemExit(3)

if __name__=='__main__':main()
