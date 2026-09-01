#!/usr/bin/env python3
import argparse, importlib.util, json, time
from collections import deque


def load(path):
    spec = importlib.util.spec_from_file_location('mgsolver', path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--solver', required=True)
    ap.add_argument('--row', required=True)
    a = ap.parse_args()
    m = load(a.solver)
    row = json.load(open(a.row))
    source = m.parse_equation(row['equation1'])
    neutral = m.parse_equation('x = x')
    target = m.parse_equation('x = x * x')

    base = dict(m.COMPACT_SUPERPOSITION_PROBE)
    base.update({
        'maximum_term_size': 75,
        'maximum_replay_term_size': 400,
        'maximum_depth': 12,
        'maximum_rules': 896,
        'maximum_rounds': 96,
        'new_clauses_per_round': 64,
        'maximum_clauses': 14000,
        'normalization_steps': 256,
        'maximum_proof_nodes': 90000,
    })

    def setup(goal, sec):
        lim = dict(base)
        lim['seconds'] = sec
        e = m.TargetGroundedRefutation(source, goal, time.monotonic() + sec, lim)
        return e, e.search

    def canon(lhs, rhs):
        names = {}
        def f(t):
            if t[0] == 'var':
                if t[1] not in names:
                    names[t[1]] = chr(ord('x') + len(names))
                return ('var', names[t[1]])
            return ('op', f(t[1]), f(t[2]))
        cl, cr = f(lhs), f(rhs)
        return cl, cr, tuple(dict.fromkeys(names.values())), dict(names)

    def skey(s, q):
        return (
            m.term_size(q.lhs) + m.term_size(q.rhs),
            str(s.alpha_signature(q.lhs, q.rhs)),
            m.render_term(q.lhs), m.render_term(q.rhs),
        )

    def partial_subst(t, mp):
        if t[0] == 'var':
            return mp.get(t[1], t)
        return ('op', partial_subst(t[1], mp), partial_subst(t[2], mp))

    def tkey(t):
        return (m.term_size(t), m.render_term(t))

    t0 = time.monotonic()
    e, s = setup(neutral, 20.0)
    pre = []
    for gen in range(1, 4):
        rules = s.rules(); snap = list(rules); props = []; proposed = 0; stop = False
        for oi, o in enumerate(snap):
            if stop: break
            for ii, i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs, maximum_depth=12, include_root=True):
                    c = s.critical_pair(o, i, oi, ii, path)
                    if c is None: continue
                    c = s.interreduce(c, rules); props.append(c); proposed += 1
                    if proposed >= 512:
                        stop = True; break
        props.sort(key=lambda q: skey(s, q)); added = 0
        for q in props:
            if s.add_clause(q):
                s.superpositions += 1; added += 1
            if added >= 64: break
        pre.append({'generation': gen, 'proposed': proposed, 'added': added, 'clauses': len(s.clauses)})

    seen = set(); spectrum = {}; census = replayed = projected = 0
    rules = s.rules(); s.deadline = time.monotonic() + 12.0
    for oi, o in enumerate(rules):
        for ii, i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs, maximum_depth=12, include_root=True):
                if s.expired() or census >= 176: break
                c = s.critical_pair(o, i, oi, ii, path)
                if c is None: continue
                c = s.interreduce(c, rules)
                names = m.term_variables(c.lhs) | m.term_variables(c.rhs)
                if c.lhs == c.rhs or any(v.startswith('@') for v in names): continue
                key = (s.alpha_signature(c.lhs, c.rhs), c.lhs, c.rhs)
                if key in seen: continue
                seen.add(key); census += 1
                ns, r = s.compile(c)
                if not m.replay_dag(source, ns, r, maximum_term_size=400, maximum_nodes=90000): continue
                replayed += 1
                raw = canon(c.lhs, c.rhs)
                pe, ps = setup(raw, 2.0)
                pn, pr = ps.compile(c)
                if not m.replay_dag(source, pn, pr, maximum_term_size=400, maximum_nodes=90000): continue
                projected += 1
                ep = (pn[pr].lhs, pn[pr].rhs)
                act = canon(ep[0], ep[1])
                if act[2] != ('x',): continue
                k = (m.render_term(act[0]), m.render_term(act[1]))
                rec = {
                    'lhs_t': act[0], 'rhs_t': act[1], 'lhs': k[0], 'rhs': k[1],
                    'proof_nodes': len(pn), 'raw_lhs': m.render_term(ep[0]),
                    'raw_rhs': m.render_term(ep[1]), 'proof': pn, 'root': pr,
                    'raw_to_canon': act[3],
                }
                prev = spectrum.get(k)
                if prev is None or rec['proof_nodes'] < prev['proof_nodes']:
                    spectrum[k] = rec
            if s.expired() or census >= 176: break
        if s.expired() or census >= 176: break

    ordered = sorted(
        spectrum.values(),
        key=lambda r: (m.term_size(r['lhs_t']) + m.term_size(r['rhs_t']), r['proof_nodes'], r['lhs'], r['rhs'])
    )[:32]

    x = ('var', 'x'); xx = ('op', x, x)
    universe = {x, xx}
    def addsubs(t):
        universe.add(t)
        if t[0] == 'op':
            addsubs(t[1]); addsubs(t[2])
    for r in ordered:
        addsubs(r['lhs_t']); addsubs(r['rhs_t'])
    simple = sorted(universe, key=tkey)[:24]
    for u in simple:
        for v in simple:
            z = ('op', u, v)
            if m.term_size(z) <= 15: universe.add(z)
    universe = set(sorted(universe, key=tkey)[:256])

    nodes = []
    adj = {t: [] for t in universe}
    parent = {t: t for t in universe}; rank = {t: 0 for t in universe}

    def ensure(t):
        if t not in parent:
            parent[t] = t; rank[t] = 0; adj[t] = []; universe.add(t)
        if t[0] == 'op':
            ensure(t[1]); ensure(t[2])

    def find(t):
        p = parent[t]
        if p != t: parent[t] = find(p)
        return parent[t]

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra == rb: return False
        if rank[ra] < rank[rb]: ra, rb = rb, ra
        parent[rb] = ra
        if rank[ra] == rank[rb]: rank[ra] += 1
        return True

    def add_explicit_edge(a, b, root, why):
        ensure(a); ensure(b)
        if nodes[root].lhs != a or nodes[root].rhs != b:
            raise RuntimeError('proof endpoint mismatch')
        adj[a].append((b, root, False, why))
        adj[b].append((a, root, True, why))
        return union(a, b)

    def clone_instantiated_proof(rec, T):
        raw_map = {raw: T for raw, cv in rec['raw_to_canon'].items() if cv == 'x'}
        old = rec['proof']; offset = len(nodes)
        for n in old:
            ctx = n.context
            if ctx is not None:
                ctx = (ctx[0], partial_subst(ctx[1], raw_map))
            subst = tuple((v, partial_subst(val, raw_map)) for v, val in n.substitution)
            term_origins = tuple(
                (v, partial_subst(val, raw_map), tuple(pid + offset for pid in origins))
                for v, val, origins in n.term_origins
            ) if n.term_origins else ()
            context_record = None
            if n.context_record is not None:
                rt, path, orig, repl, result = n.context_record
                context_record = (
                    partial_subst(rt, raw_map), path,
                    partial_subst(orig, raw_map), partial_subst(repl, raw_map),
                    partial_subst(result, raw_map),
                )
            overlap_record = None
            if n.overlap_record is not None:
                rec0 = list(n.overlap_record)
                for idx in (5, 6, 7, 8, 9):
                    rec0[idx] = partial_subst(rec0[idx], raw_map)
                rec0[0] += offset; rec0[1] += offset
                overlap_record = tuple(rec0)
            nodes.append(m.EqualityNode(
                partial_subst(n.lhs, raw_map), partial_subst(n.rhs, raw_map), n.kind,
                parents=tuple(p + offset for p in n.parents), substitution=subst,
                context=ctx, orientation=n.orientation, generation=n.generation,
                term_origins=term_origins, constructor=n.constructor,
                derivation_depth=n.derivation_depth,
                context_record=context_record, overlap_record=overlap_record,
            ))
        root = rec['root'] + offset
        return root

    def oriented(root, reverse):
        if not reverse: return root
        p = nodes[root]
        nodes.append(m.EqualityNode(p.rhs, p.lhs, 'symmetry', parents=(root,)))
        return len(nodes) - 1

    def path_proof(a, b):
        if a == b:
            nodes.append(m.EqualityNode(a, a, 'reflexivity'))
            return len(nodes) - 1
        q = deque([a]); prev = {a: None}; pedge = {}
        while q:
            u = q.popleft()
            if u == b: break
            for v, root, rev, why in adj.get(u, ()):
                if v not in prev:
                    prev[v] = u; pedge[v] = (root, rev); q.append(v)
        if b not in prev: return None
        parts = []; cur = b
        while prev[cur] is not None:
            root, rev = pedge[cur]; parts.append(oriented(root, rev)); cur = prev[cur]
        parts.reverse(); root = parts[0]
        for nxt in parts[1:]:
            l, r = nodes[root], nodes[nxt]
            if l.rhs != r.lhs: raise RuntimeError('path transitivity mismatch')
            nodes.append(m.EqualityNode(l.lhs, r.rhs, 'transitivity', parents=(root, nxt)))
            root = len(nodes) - 1
        return root

    bases = sorted(list(universe), key=tkey)[:96]
    instantiated = 0; base_edges = 0
    endpoint_seen = set()
    for idx, rec in enumerate(ordered):
        for T in bases:
            l = partial_subst(rec['lhs_t'], {'x': T})
            rr = partial_subst(rec['rhs_t'], {'x': T})
            if max(m.term_size(l), m.term_size(rr)) > 31: continue
            ek = (l, rr)
            if ek in endpoint_seen or (rr, l) in endpoint_seen: continue
            endpoint_seen.add(ek)
            root = clone_instantiated_proof(rec, T)
            if nodes[root].lhs != l or nodes[root].rhs != rr:
                raise RuntimeError('instantiated law endpoint mismatch')
            if not m.replay_dag(source, nodes, root, maximum_term_size=400, maximum_nodes=90000):
                raise RuntimeError('instantiated law replay failed')
            add_explicit_edge(l, rr, root, {'kind': 'law_subst', 'law': idx, 'subst': m.render_term(T)})
            instantiated += 1; base_edges += 1

    congruence_edges = 0
    for _round in range(6):
        changed = False
        ops = [t for t in list(universe) if t[0] == 'op']
        buckets = {}
        for t in ops:
            sig = (find(t[1]), find(t[2]))
            if sig not in buckets:
                buckets[sig] = t; continue
            u = buckets[sig]
            if find(t) == find(u): continue
            left_root = path_proof(t[1], u[1])
            right_root = path_proof(t[2], u[2])
            if left_root is None or right_root is None:
                continue
            if t[1] == u[1]:
                p1 = None
            else:
                nodes.append(m.EqualityNode(
                    t, ('op', u[1], t[2]), 'congruence on left child',
                    parents=(left_root,), context=('left', t[2])
                ))
                p1 = len(nodes) - 1
            mid = ('op', u[1], t[2])
            if t[2] == u[2]:
                p2 = None
            else:
                nodes.append(m.EqualityNode(
                    mid, u, 'congruence on right child',
                    parents=(right_root,), context=('right', u[1])
                ))
                p2 = len(nodes) - 1
            if p1 is None: root = p2
            elif p2 is None: root = p1
            else:
                nodes.append(m.EqualityNode(t, u, 'transitivity', parents=(p1, p2)))
                root = len(nodes) - 1
            if root is None: continue
            if not m.replay_dag(source, nodes, root, maximum_term_size=400, maximum_nodes=90000):
                raise RuntimeError('congruence replay failed')
            if add_explicit_edge(t, u, root, {'kind': 'congruence'}):
                congruence_edges += 1; changed = True
        if not changed: break

    connected = find(x) == find(xx)
    final_root = path_proof(x, xx) if connected else None
    replay = final_root is not None and m.replay_dag(
        source, nodes, final_root, maximum_term_size=400, maximum_nodes=90000
    )
    certificate_bytes = None
    if replay:
        code, _ = m.make_dag_certificate(target, nodes, final_root)
        certificate_bytes = len(code.encode())

    result = {
        'id': row['id'], 'elapsed': round(time.monotonic() - t0, 4),
        'pre_trace': pre, 'census': census, 'replayed': replayed,
        'projected': projected, 'interfaces': len(spectrum), 'selected': len(ordered),
        'graph_nodes': len(universe), 'base_edges': base_edges,
        'instantiated_edges': instantiated, 'congruence_edges': congruence_edges,
        'connected_idempotence': connected, 'direct_replay': replay,
        'proof_nodes_total': len(nodes), 'final_root': final_root,
        'certificate_bytes': certificate_bytes,
        'target_revealed_after_closure': True,
    }
    print('SOURCE_ONLY_PROOF_CARRYING_INTERFACE_GRAPH ' + json.dumps(result, sort_keys=True), flush=True)
    if not replay: raise SystemExit(2)


if __name__ == '__main__':
    main()
