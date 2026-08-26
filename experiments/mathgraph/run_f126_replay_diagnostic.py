#!/usr/bin/env python3
import argparse, importlib.util, json, time, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / 'submissions/mathgraph/solver.py'
HELPER_URL = 'https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/normal0040-alpha-self-overlap-20260826/experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
TRACE_URL = 'https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID = 'evaluation_normal_0040'

def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def alpha_sig(rigid, a, b):
    names = {}
    x = rigid.alpha_canonical_term(a, names)
    y = rigid.alpha_canonical_term(b, names)
    return min((x, y), (y, x))

def node_record(m, node_id, node):
    return {
        'id': node_id,
        'kind': node.kind,
        'lhs': m.render_term(node.lhs),
        'rhs': m.render_term(node.rhs),
        'parents': list(node.parents),
        'substitution': [(v, m.render_term(t)) for v, t in node.substitution],
        'orientation': bool(node.orientation),
        'generation': node.generation,
        'constructor': node.constructor,
        'context': node.context,
        'overlap_record': repr(node.overlap_record),
    }

def first_bad(m, source, nodes):
    for i in range(len(nodes)):
        prefix = nodes[:i+1]
        if not m.replay_dag(source, prefix, i, maximum_term_size=260, maximum_nodes=50000):
            return node_record(m, i, nodes[i])
    return None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--input', required=True)
    ap.add_argument('--output', required=True)
    args = ap.parse_args()
    m = load(SOLVER, 'mg_f126_diag')
    hp = ROOT / 'experiments/mathgraph/_runtime_old_0040_helper.py'
    hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h = load(hp, 'mg_old_helper_f126')
        row = h.load_row(args.input)
        source = m.parse_equation(row['equation1'])
        target = m.parse_equation(row['equation2'])
        limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
        limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
        engine = m.TargetGroundedRefutation(source, target, time.monotonic()+15.0, limits)
        engine.solve()
        rigid = m.RigidSuperpositionModule()
        trace = json.load(urllib.request.urlopen(TRACE_URL))
        proof = next(r['proof'] for r in trace['rows'] if r['id'] == RID)
        defs, wanted = {}, {}
        for block in h.fof_blocks(proof):
            q = h.parse_fof(block)
            if not q:
                continue
            fid, kind, formula, _ = q
            try:
                eq = h.formula_equality(formula)
            except Exception:
                eq = None
            if eq is None:
                continue
            x, y = eq
            if kind == 'definition':
                if x[0] == 'var' and x[1].startswith('sF'):
                    defs[x[1]] = y
                elif y[0] == 'var' and y[1].startswith('sF'):
                    defs[y[1]] = x
            elif fid in ('f15','f81','f95','f126'):
                wanted[fid] = (h.map_rigids(h.inline_defs(x, defs), target[2]), h.map_rigids(h.inline_defs(y, defs), target[2]))

        def inline_clause(c):
            return (h.inline_engine_names(c.lhs, engine.reverse_constants), h.inline_engine_names(c.rhs, engine.reverse_constants))
        def orient(c, reverse):
            return c if not reverse else m.Recipe(c.rhs, c.lhs, 'symmetry', (c,))
        def materialized_cover(fid):
            goal = wanted[fid]
            for c in engine.search.clauses:
                x, y = inline_clause(c)
                for rev, (u, v) in enumerate(((x,y),(y,x))):
                    sub = {}
                    if rigid.match_term(u, goal[0], sub) and rigid.match_term(v, goal[1], sub):
                        return engine.search.instantiate(orient(c, bool(rev)), sub), {'reverse':bool(rev),'sub':{k:h.render_term(v) if hasattr(h,'render_term') else repr(v) for k,v in sub.items()}}
            return None, None

        f81, f81_meta = materialized_cover('f81')
        f15, f15_meta = materialized_cover('f15')
        out = {'id':RID,'f81_cover':f81_meta,'f15_cover':f15_meta,'f95':None,'f15':None,'candidates':[]}
        if f15:
            n,r = engine.search.compile(f15)
            out['f15'] = {'nodes':len(n),'replay':m.replay_dag(source,n,r,maximum_term_size=260,maximum_nodes=50000),'first_bad':first_bad(m,source,n)}
        p95 = None
        if f81:
            for lr in (False,True):
                if p95: break
                for rr in (False,True):
                    left, right = orient(f81,lr), orient(f81,rr)
                    for path in rigid.nonvariable_positions(left.lhs, maximum_depth=limits['maximum_depth'], include_root=True):
                        p = engine.search.critical_pair(left,right,0,1,path)
                        if p is None: continue
                        x,y = inline_clause(p)
                        if alpha_sig(rigid,x,y) == alpha_sig(rigid,wanted['f95'][0],wanted['f95'][1]):
                            p95 = p; break
                    if p95: break
        if p95:
            n,r = engine.search.compile(p95)
            out['f95'] = {'nodes':len(n),'replay':m.replay_dag(source,n,r,maximum_term_size=260,maximum_nodes=50000),'first_bad':first_bad(m,source,n)}
        if f15 and p95:
            for base_left, base_right, label in ((f15,p95,'f15-p95'),(p95,f15,'p95-f15')):
                for lr in (False,True):
                    left = orient(base_left,lr)
                    paths = tuple(rigid.nonvariable_positions(left.lhs, maximum_depth=limits['maximum_depth'], include_root=True))
                    for rr in (False,True):
                        right = orient(base_right,rr)
                        for path in paths:
                            q = engine.search.critical_pair(left,right,0,1,path)
                            if q is None: continue
                            x,y = inline_clause(q)
                            if alpha_sig(rigid,x,y) != alpha_sig(rigid,wanted['f126'][0],wanted['f126'][1]):
                                continue
                            nodes,root = engine.search.compile(q)
                            rec = {'order':label,'left_rev':lr,'right_rev':rr,'path':list(path),'nodes':len(nodes),'root':root,'replay':m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000),'first_bad':first_bad(m,source,nodes)}
                            if rec['first_bad']:
                                i = rec['first_bad']['id']
                                rec['before_bad'] = node_record(m,i-1,nodes[i-1]) if i else None
                            out['candidates'].append(rec)
        Path(args.output).parent.mkdir(parents=True, exist_ok=True)
        Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
        print('F126_REPLAY_DIAGNOSTIC', json.dumps(out,sort_keys=True), flush=True)
    finally:
        hp.unlink(missing_ok=True)

if __name__ == '__main__':
    main()
