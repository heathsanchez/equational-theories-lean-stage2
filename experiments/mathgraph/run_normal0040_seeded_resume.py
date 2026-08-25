#!/usr/bin/env python3
import argparse, importlib.util, json, re, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'

def load_solver():
    spec=importlib.util.spec_from_file_location('mg_seeded_resume_solver',SOLVER)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def load_helper():
    p=Path(__file__).with_name('run_normal0040_alpha_helpers.py')
    spec=importlib.util.spec_from_file_location('mg_alpha_helpers',p)
    h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h); return h

def alpha_sig(rigid,a,b):
    names={}; x=rigid.alpha_canonical_term(a,names); y=rigid.alpha_canonical_term(b,names); return (x,y)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
    m=load_solver(); h=load_helper(); row=h.load_row(a.input,RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    engine=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits)
    baseline=engine.solve()
    rigid=m.RigidSuperpositionModule()
    trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
    wanted=h.extract_wanted(proof,target[2],m,('f81','f95'))
    f81,f95=wanted['f81'],wanted['f95']
    cover=None; cover_map=None; cover_rev=False
    for c in engine.search.clauses:
        x=h.inline_engine_names(c.lhs,engine.reverse_constants); y=h.inline_engine_names(c.rhs,engine.reverse_constants)
        for rev,(u,v) in enumerate(((x,y),(y,x))):
            subst={}
            if rigid.match_term(u,f81[0],subst) and rigid.match_term(v,f81[1],subst):
                cover=(c,x,y); cover_map=subst; cover_rev=bool(rev); break
        if cover: break
    out={'id':RID,'baseline_found':bool(baseline),'cover_found':bool(cover),'f95_generated':False,'seed_added':False,'seeded_found':False,'seeded_replay_ok':False,'proof_nodes':None}
    if cover:
        c,_,_=cover; base=c if not cover_rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,)); mat=engine.search.instantiate(base,cover_map)
        target_sig=alpha_sig(rigid,*f95)
        seed=None
        for path in rigid.nonvariable_positions(mat.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
            p=engine.search.critical_pair(mat,mat,0,0,path)
            if p is None: continue
            ix=h.inline_engine_names(p.lhs,engine.reverse_constants); iy=h.inline_engine_names(p.rhs,engine.reverse_constants)
            if alpha_sig(rigid,ix,iy)==target_sig or alpha_sig(rigid,iy,ix)==target_sig:
                seed=p; out['f95_generated']=True; break
        if seed is not None:
            out['seed_added']=bool(engine.search.add_clause(seed))
            # Resume from the now-augmented symbolic theory. TargetGroundedRefutation
            # owns the normal inline/replay conversion, so this is the causal test.
            found=engine.solve(); out['seeded_found']=bool(found)
            if found is not None:
                nodes,root=found; out['proof_nodes']=len(m.proof_node_ids(nodes,root))
                out['seeded_replay_ok']=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000) and (nodes[root].lhs,nodes[root].rhs)==target[:2])
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('NORMAL0040_SEEDED_RESUME',json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__': main()
