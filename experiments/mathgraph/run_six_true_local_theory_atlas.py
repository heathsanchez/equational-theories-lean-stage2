#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import sys
import time
from itertools import product
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('six_true_local_theory_helper', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

ROOT = Path('/tmp/sair_stage1_eval')
OUT = Path('experiments/mathgraph/results/six-true-local-theory-atlas.json')
TARGET_IDS = {
    'evaluation_hard_0196',
    'evaluation_normal_0036',
    'evaluation_normal_0040',
    'evaluation_normal_0158',
    'evaluation_order5_0014',
    'evaluation_order5_0042',
}
MAX_NODES = 70000
MAX_TERM_SIZE = 80
BEAM = 180
CONG_BEAM = 56
TERM_BEAM = 28
ROUNDS = 7
SECONDS = 28.0


def load_rows():
    found = {}
    for p in sorted(ROOT.glob('evaluation_*.jsonl')):
        subset = p.stem
        for line_no, line in enumerate(p.read_text().splitlines(), 1):
            if not line.strip():
                continue
            row = json.loads(line)
            rid = row.get('id') or row.get('problem_id') or row.get('name')
            if rid is None:
                # Published files are ordered evaluation_*_0000, ...; keep this
                # fallback so the atlas remains robust to schema-only releases.
                rid = f'{subset}_{line_no-1:04d}'
            if rid in TARGET_IDS:
                found[rid] = row
    missing = sorted(TARGET_IDS - set(found))
    if missing:
        raise RuntimeError('missing public evaluation rows: ' + ', '.join(missing))
    return found


def equation_fields(row):
    def pick(*keys):
        for k in keys:
            if k in row and row[k] is not None:
                return row[k]
        return None
    a = pick('equation1', 'equation_1', 'source', 'hypothesis', 'lhs_equation')
    b = pick('equation2', 'equation_2', 'target', 'conclusion', 'rhs_equation')
    if not isinstance(a, str) or not isinstance(b, str):
        raise RuntimeError('cannot locate equation fields; keys=' + repr(sorted(row)))
    return a, b


def solve_one(m, rid, row):
    eq1, eq2 = equation_fields(row)
    source = m.parse_equation(eq1)
    target = m.parse_equation(eq2)
    tl, tr = target[:2]
    deadline = time.monotonic() + SECONDS
    nodes = []
    depth = []
    best = {}
    source_cache = set()

    def add(node, d):
        if len(nodes) >= MAX_NODES:
            return None
        if m.term_size(node.lhs) > MAX_TERM_SIZE or m.term_size(node.rhs) > MAX_TERM_SIZE:
            return None
        key = (node.lhs, node.rhs)
        old = best.get(key)
        if old is not None and depth[old] <= d:
            return old
        nodes.append(node); depth.append(d)
        i = len(nodes) - 1; best[key] = i
        return i

    def M(a, b): return ('op', a, b)
    def R(t, d=0):
        return add(m.EqualityNode(t, t, 'reflexivity', constructor='six-true-local-theory'), d)
    def S(i, d):
        if i is None: return None
        p = nodes[i]
        return add(m.EqualityNode(p.rhs, p.lhs, 'symmetry', parents=(i,), constructor='six-true-local-theory'), d)
    def T(i, j, d):
        if i is None or j is None: return None
        a, b = nodes[i], nodes[j]
        if a.rhs != b.lhs: return None
        return add(m.EqualityNode(a.lhs, b.rhs, 'transitivity', parents=(i, j), constructor='six-true-local-theory'), d)
    def C(i, j, d):
        if i is None or j is None: return None
        a, b = nodes[i], nodes[j]
        lhs, rhs = M(a.lhs, b.lhs), M(a.rhs, b.rhs)
        if m.term_size(lhs) > MAX_TERM_SIZE or m.term_size(rhs) > MAX_TERM_SIZE:
            return None
        i1 = add(m.EqualityNode(M(a.lhs,b.lhs), M(a.rhs,b.lhs), 'congruence on left child', parents=(i,), context=('left',b.lhs), constructor='six-true-local-theory'), d)
        if i1 is None: return None
        i2 = add(m.EqualityNode(M(a.rhs,b.lhs), M(a.rhs,b.rhs), 'congruence on right child', parents=(j,), context=('right',a.rhs), constructor='six-true-local-theory'), d)
        return T(i1, i2, d)
    def H(args, d):
        sl, sr, sv = source
        if len(args) != len(sv): return None
        mp = dict(zip(sv, args))
        key = tuple(mp[v] for v in sv)
        if key in source_cache: return None
        source_cache.add(key)
        lhs, rhs = m.substitute(sl, mp), m.substitute(sr, mp)
        return add(m.EqualityNode(lhs, rhs, 'source instance', substitution=tuple((v,mp[v]) for v in sv), constructor='six-true-local-theory'), d)

    target_terms = set(m.walk_subterms(tl)) | set(m.walk_subterms(tr))
    variables = {('var', v) for v in source[2]} | {('var', v) for v in target[2]}
    vocabulary = sorted(target_terms | variables, key=lambda t:(m.term_size(t),m.render_term(t)))
    for t in vocabulary: R(t)

    def score(i):
        n = nodes[i]
        direct = m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr)
        sym = m.structural_distance(n.rhs,tl)+m.structural_distance(n.lhs,tr)
        exposed = sum(t in target_terms for t in m.walk_subterms(n.lhs)) + sum(t in target_terms for t in m.walk_subterms(n.rhs))
        exact = 0 if (n.lhs,n.rhs)==(tl,tr) else 1
        return (exact, min(direct,sym), -exposed, m.term_size(n.lhs)+m.term_size(n.rhs), depth[i], i)

    # Target-matched source instances are the initial local theory.
    sv = source[2]
    fills = vocabulary[:14]
    for pattern in source[:2]:
        for concrete in vocabulary:
            partial = {}
            if not m.match_term(pattern, concrete, partial):
                continue
            missing = [v for v in sv if v not in partial]
            for fill in product(fills, repeat=len(missing)):
                if time.monotonic() >= deadline or len(nodes) >= 12000: break
                mp = dict(partial); mp.update(zip(missing, fill))
                H(tuple(mp[v] for v in sv), 0)
            if time.monotonic() >= deadline or len(nodes) >= 12000: break
        if time.monotonic() >= deadline or len(nodes) >= 12000: break

    snapshots=[]; found = best.get((tl,tr))
    for r in range(1, ROUNDS+1):
        if found is not None or len(nodes)>=MAX_NODES or time.monotonic()>=deadline:
            break
        ranked = sorted(set(best.values()), key=score)[:BEAM]
        for i in ranked: S(i,r)
        # Exact composition is the cheapest bridge constructor.
        ranked = sorted(set(best.values()), key=score)[:BEAM]
        by_lhs={}; by_rhs={}
        for i in ranked:
            by_lhs.setdefault(nodes[i].lhs,[]).append(i); by_rhs.setdefault(nodes[i].rhs,[]).append(i)
        for mid, lefts in list(by_rhs.items()):
            for i in lefts[:10]:
                for j in by_lhs.get(mid,[])[:10]: T(i,j,r)
        # Bounded binary congruence gives explicit local contexts.
        cr = sorted(set(best.values()), key=score)[:CONG_BEAM]
        for i in cr:
            for j in cr:
                if time.monotonic()>=deadline or len(nodes)>=MAX_NODES: break
                C(i,j,r)
            if time.monotonic()>=deadline or len(nodes)>=MAX_NODES: break

        # Re-enter the source from terms made visible by the best verified programs.
        ranked2 = sorted(set(best.values()), key=score)[:BEAM]
        dyn=[]; seen=set()
        for i in ranked2:
            for side in (nodes[i].lhs,nodes[i].rhs):
                for t in m.walk_subterms(side):
                    if t not in seen and m.term_size(t)<=28:
                        seen.add(t); dyn.append(t)
        dyn = sorted(dyn, key=lambda t:(min(m.structural_distance(t,tl),m.structural_distance(t,tr)),m.term_size(t),m.render_term(t)))[:TERM_BEAM]
        fill2=dyn[:12]
        for pattern in source[:2]:
            for concrete in dyn:
                partial={}
                if not m.match_term(pattern,concrete,partial): continue
                missing=[v for v in sv if v not in partial]
                for fill in product(fill2, repeat=len(missing)):
                    if time.monotonic()>=deadline or len(nodes)>=MAX_NODES: break
                    mp=dict(partial); mp.update(zip(missing,fill)); H(tuple(mp[v] for v in sv),r)
                if time.monotonic()>=deadline or len(nodes)>=MAX_NODES: break
            if time.monotonic()>=deadline or len(nodes)>=MAX_NODES: break
        found=best.get((tl,tr))
        reachable_terms=set()
        for i in sorted(set(best.values()), key=score)[:500]:
            reachable_terms.update(m.walk_subterms(nodes[i].lhs)); reachable_terms.update(m.walk_subterms(nodes[i].rhs))
        missing_terms=sorted(target_terms-reachable_terms,key=lambda t:(m.term_size(t),m.render_term(t)))
        snapshots.append({'round':r,'nodes':len(nodes),'equalities':len(best),'source_instances':len(source_cache),'dynamic_terms':len(dyn),'missing_target_terms':[m.render_term(t) for t in missing_terms[:12]],'best_score':list(score(sorted(set(best.values()),key=score)[0])) if best else None,'found':found is not None})
        print('LOCAL_THEORY_ROUND',rid,json.dumps(snapshots[-1],sort_keys=True),flush=True)

    replayed=False; replay_error=None
    if found is not None:
        try:
            replayed=bool(m.replay_dag(source,nodes,found,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES))
        except Exception as exc:
            replay_error=type(exc).__name__+': '+str(exc)

    # Report closest verified equalities as a residual interface for the next constructor.
    closest=[]
    for i in sorted(set(best.values()),key=score)[:8]:
        n=nodes[i]
        closest.append({'lhs':m.render_term(n.lhs),'rhs':m.render_term(n.rhs),'kind':n.kind,'depth':depth[i],'score':list(score(i)[:-1])})
    return {'id':rid,'equation1':eq1,'equation2':eq2,'found':found is not None,'replayed':replayed,'replay_error':replay_error,'nodes':len(nodes),'unique_equalities':len(best),'source_instances':len(source_cache),'snapshots':snapshots,'closest_verified_equalities':closest}


def main():
    rows=load_rows(); m=h.load_solver()
    out={'schema':'mathgraph.six-true-local-theory-atlas.v1','constructor_language':['source-instance','reflexivity','symmetry','transitivity','binary-congruence','dynamic-source-reentry'],'ids':sorted(TARGET_IDS),'results':[]}
    for rid in sorted(TARGET_IDS):
        rec=solve_one(m,rid,rows[rid]); out['results'].append(rec)
        print('LOCAL_THEORY_RESIDUAL',json.dumps({'id':rid,'found':rec['found'],'replayed':rec['replayed'],'nodes':rec['nodes'],'source_instances':rec['source_instances'],'last':rec['snapshots'][-1] if rec['snapshots'] else None},sort_keys=True),flush=True)
    out['summary']={'found':sum(int(r['found']) for r in out['results']),'replayed':sum(int(r['replayed']) for r in out['results']),'total':len(out['results'])}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('LOCAL_THEORY_SUMMARY',json.dumps(out['summary'],sort_keys=True),flush=True)

if __name__=='__main__': main()
