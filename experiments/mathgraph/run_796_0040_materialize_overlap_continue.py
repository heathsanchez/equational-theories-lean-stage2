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
            elif fid in ('f15','f20','f27','f81','f95','f123','f126','f130','f148','f150','f196'):
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]), h.map_rigids(h.inline_defs(y,defs),target[2]))

        def inline_clause(c):
            return (h.inline_engine_names(c.lhs,engine.reverse_constants), h.inline_engine_names(c.rhs,engine.reverse_constants))

        def orient(c, reverse):
            return c if not reverse else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))

        def replay_recipe(recipe):
            inlined = engine.inline_recipe(recipe)
            nodes, root = engine.search.compile(inlined)
            return bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)), len(nodes)

        def materialized_cover(fid):
            goal = wanted[fid]
            for c in engine.search.clauses:
                x,y=inline_clause(c)
                for rev,(u,v) in enumerate(((x,y),(y,x))):
                    sub={}
                    if rigid.match_term(u,goal[0],sub) and rigid.match_term(v,goal[1],sub):
                        return engine.search.instantiate(orient(c,bool(rev)),sub), True
            return None, False

        def derive_pair(left_base, right_base, child_fid, labels=('left-right','right-left')):
            details=[]
            for base_left,base_right,label in ((left_base,right_base,labels[0]),(right_base,left_base,labels[1])):
                for left_rev in (False,True):
                    left=orient(base_left,left_rev)
                    paths=tuple(rigid.nonvariable_positions(left.lhs, maximum_depth=limits['maximum_depth'], include_root=True))
                    for right_rev in (False,True):
                        right=orient(base_right,right_rev)
                        for path in paths:
                            q=engine.search.critical_pair(left,right,0,1,path)
                            if q is None: continue
                            x,y=inline_clause(q)
                            if alpha_sig(rigid,x,y)!=alpha_sig(rigid,wanted[child_fid][0],wanted[child_fid][1]): continue
                            ok,ncount=replay_recipe(q)
                            details.append({'order':label,'left_rev':left_rev,'right_rev':right_rev,'path':list(path),'replay':ok,'nodes':ncount})
                            if ok:
                                return q,details
            return None,details

        f81mat, f81cover = materialized_cover('f81')
        out={'id':RID,'baseline_found':bool(baseline),'covers':{'f81':f81cover,'f15':False,'f20':False,'f27':False},'f95_found':False,'f95_replay':False,'f95_added':False,'pair_descendants':{'f123':False,'f126':False,'f130':False,'f148':False,'f150':False,'f196':False},'pair_replay':{'f123':False,'f126':False,'f130':False,'f148':False,'f150':False,'f196':False},'pair_details':{},'continued_recipe':False,'continued_replay':False}
        p95=None
        if f81mat:
            for outer_rev in (False,True):
                if p95: break
                for inner_rev in (False,True):
                    left=orient(f81mat,outer_rev); right=orient(f81mat,inner_rev)
                    for path in rigid.nonvariable_positions(left.lhs, maximum_depth=limits['maximum_depth'], include_root=True):
                        p=engine.search.critical_pair(left,right,0,1,path)
                        if p is None: continue
                        x,y=inline_clause(p)
                        if alpha_sig(rigid,x,y)!=alpha_sig(rigid,wanted['f95'][0],wanted['f95'][1]): continue
                        p95=p; out['f95_found']=True
                        out['f95_replay'], _ = replay_recipe(p)
                        out['f95_added']=bool(engine.search.add_clause(p))
                        break
                    if p95: break

        if p95:
            mats={}
            for fid in ('f15','f20','f27'):
                mats[fid], out['covers'][fid] = materialized_cover(fid)
            derived={}
            targets=(('f27','f123'),('f15','f126'))
            for parent_fid, child_fid in targets:
                parent=mats.get(parent_fid)
                if parent is None: continue
                found,details=derive_pair(parent,p95,child_fid,(f'{parent_fid}-f95',f'f95-{parent_fid}'))
                out['pair_details'][child_fid]=details
                if details: out['pair_descendants'][child_fid]=True
                if found:
                    derived[child_fid]=found
                    out['pair_replay'][child_fid]=True
                    engine.search.add_clause(found)

            if derived.get('f123') is not None and derived.get('f126') is not None:
                f130,details=derive_pair(derived['f123'],derived['f126'],'f130',('f123-f126','f126-f123'))
                out['pair_details']['f130']=details
                if details: out['pair_descendants']['f130']=True
                if f130:
                    derived['f130']=f130
                    out['pair_replay']['f130']=True
                    out['f130_added']=bool(engine.search.add_clause(f130))

            if mats.get('f20') is not None and derived.get('f126') is not None:
                f148,details=derive_pair(mats['f20'],derived['f126'],'f148',('f20-f126','f126-f20'))
                out['pair_details']['f148']=details
                if details: out['pair_descendants']['f148']=True
                if f148:
                    derived['f148']=f148
                    out['pair_replay']['f148']=True
                    out['f148_added']=bool(engine.search.add_clause(f148))

            if derived.get('f130') is not None:
                f150,details=derive_pair(derived['f130'],derived['f130'],'f150',('f130-f130-a','f130-f130-b'))
                out['pair_details']['f150']=details
                if details: out['pair_descendants']['f150']=True
                if f150:
                    derived['f150']=f150
                    out['pair_replay']['f150']=True
                    out['f150_added']=bool(engine.search.add_clause(f150))

            if derived.get('f148') is not None and derived.get('f150') is not None:
                f196,details=derive_pair(derived['f148'],derived['f150'],'f196',('f148-f150','f150-f148'))
                out['pair_details']['f196']=details
                if details: out['pair_descendants']['f196']=True
                if f196:
                    derived['f196']=f196
                    out['pair_replay']['f196']=True
                    out['f196_added']=bool(engine.search.add_clause(f196))

            engine.deadline=time.monotonic()+30.0; engine.search.deadline=engine.deadline
            recipe=engine.search.solve()
            out['continued_recipe']=bool(recipe)
            if recipe:
                inlined2=engine.inline_recipe(recipe)
                nodes2,root2=engine.search.compile(inlined2)
                out['continued_nodes']=len(nodes2)
                out['continued_replay']=bool(m.replay_dag(source,nodes2,root2,maximum_term_size=260,maximum_nodes=50000))

        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
        print('MATERIALIZED_PARENT_PAIR_0040',json.dumps(out,sort_keys=True),flush=True)
    finally:
        hp.unlink(missing_ok=True)
if __name__=='__main__': main()
