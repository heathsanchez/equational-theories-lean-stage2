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
    n = {}
    x = rigid.alpha_canonical_term(a, n); y = rigid.alpha_canonical_term(b, n)
    return min((x, y), (y, x))

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--input', required=True); ap.add_argument('--output', required=True)
    a = ap.parse_args()
    m = load(SOLVER, 'mg796mo')
    hp = ROOT / 'experiments/mathgraph/_runtime_old_0040_helper.py'
    hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h = load(hp, 'mgoldhelper2')
        row = h.load_row(a.input)
        source = m.parse_equation(row['equation1']); target = m.parse_equation(row['equation2'])
        limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
        limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
        engine = m.TargetGroundedRefutation(source, target, time.monotonic()+15.0, limits)
        baseline = engine.solve()
        rigid = m.RigidSuperpositionModule()
        trace = json.load(urllib.request.urlopen(TRACE_URL)); proof = next(r['proof'] for r in trace['rows'] if r['id']==RID)
        defs={}; wanted={}
        for block in h.fof_blocks(proof):
            q=h.parse_fof(block)
            if not q: continue
            fid,kind,formula,tail=q
            try: eq=h.formula_equality(formula)
            except Exception: eq=None
            if eq is None: continue
            x,y=eq
            if kind=='definition':
                if x[0]=='var' and x[1].startswith('sF'): defs[x[1]]=y
                elif y[0]=='var' and y[1].startswith('sF'): defs[y[1]]=x
            elif fid in ('f81','f95'):
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]), h.map_rigids(h.inline_defs(y,defs),target[2]))
        f81,f95=wanted['f81'],wanted['f95']
        cover=sub=None; rev=False
        for c in engine.search.clauses:
            x=h.inline_engine_names(c.lhs,engine.reverse_constants); y=h.inline_engine_names(c.rhs,engine.reverse_constants)
            for r,(u,v) in enumerate(((x,y),(y,x))):
                s={}
                if rigid.match_term(u,f81[0],s) and rigid.match_term(v,f81[1],s): cover=c; sub=s; rev=bool(r); break
            if cover: break
        out={'id':RID,'baseline_found':bool(baseline),'cover_found':bool(cover),'f95_found':False,'f95_replay':False,'continued_recipe':False,'continued_replay':False}
        if cover:
            base=cover if not rev else m.Recipe(cover.rhs,cover.lhs,'symmetry',(cover,))
            mat=engine.search.instantiate(base,sub)
            for path in rigid.nonvariable_positions(mat.lhs, maximum_depth=limits['maximum_depth'], include_root=True):
                p=engine.search.critical_pair(mat,mat,0,0,path)
                if p is None: continue
                x=h.inline_engine_names(p.lhs,engine.reverse_constants); y=h.inline_engine_names(p.rhs,engine.reverse_constants)
                if alpha_sig(rigid,x,y)!=alpha_sig(rigid,f95[0],f95[1]): continue
                out['f95_found']=True
                nodes,root=engine.search.compile(p)
                out['f95_replay']=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000))
                added=engine.search.add_clause(p)
                out['f95_added']=bool(added)
                engine.deadline=time.monotonic()+30.0; engine.search.deadline=engine.deadline
                recipe=engine.search.solve()
                out['continued_recipe']=bool(recipe)
                if recipe:
                    nodes2,root2=engine.search.compile(recipe)
                    out['continued_nodes']=len(nodes2)
                    out['continued_replay']=bool(m.replay_dag(source,nodes2,root2,maximum_term_size=260,maximum_nodes=50000))
                break
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
        print('MATERIALIZE_OVERLAP_CONTINUE',json.dumps(out,sort_keys=True),flush=True)
    finally:
        hp.unlink(missing_ok=True)
if __name__=='__main__': main()
