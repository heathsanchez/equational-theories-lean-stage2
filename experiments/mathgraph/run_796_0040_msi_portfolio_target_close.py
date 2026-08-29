#!/usr/bin/env python3
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_796_0040_cross_portfolio_bridge.py'

ap = argparse.ArgumentParser()
ap.add_argument('--input', required=True)
ap.add_argument('--output', required=True)
ap.add_argument('--frontier-seconds', type=float, default=120)
ap.add_argument('--given-seconds', type=float, default=10)
a = ap.parse_args()

s = SRC.read_text()

# Keep the successful independent-frontier fix from the verified bridge run.
old_tail = """                    if stop:break\n                if stop:break\n            if f217 is not None or sf.expired():break\n        # Independent given-clause search, stop as soon as f258 is retained.\n"""
new_tail = """                    if stop:break\n                if stop:break\n            if not stop and props:\n                props.sort(key=lambda x:x[0]); added=0\n                for _,q in props:\n                    before=len(sf.clauses)\n                    if sf.add_clause(q):\n                        sf.superpositions+=1; added+=1\n                        for c in sf.clauses[before:]:\n                            if matchf(c,'f217') and f217 is None:f217=c\n                        if f217 is not None or added>=64:break\n                props=[]\n            if f217 is not None or sf.expired():break\n        # Independent given-clause search, stop as soon as f258 is retained.\n"""
if old_tail not in s:
    raise SystemExit('expected frontier tail not found')
s = s.replace(old_tail, new_tail, 1)

# Extend diagnostic labels only: search remains unguided by these IDs.
s = s.replace("elif fid in {'f217','f258','f259'}:", "elif fid in {'f15','f217','f258','f259','f278'}:", 1)

old_out = """        out={'id':RID,'frontier_f217':f217 is not None,'frontier_rounds':rounds,'frontier_enumerated':enumf,'frontier_clauses':len(sf.clauses),'given_f258':f258 is not None,'given_steps':givens,'given_enumerated':enumg,'given_clauses':len(sg.clauses),'cross_f259':bridge is not None,'cross_details':details}\n        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\\n'); print('CROSS_PORTFOLIO_BRIDGE',json.dumps(out,sort_keys=True),flush=True)\n"""
new_out = """        # One-step target closure.  This is not a hard-coded proof: f15 is\n        # recovered from the live frontier clause set by matching the target-\n        # grounded diagnostic equation, and every orientation/path is tried.\n        def cover_frontier(fid):\n            goal=wanted[fid]\n            for c in sf.clauses:\n                x,y=(h.inline_engine_names(c.lhs,ef.reverse_constants),h.inline_engine_names(c.rhs,ef.reverse_constants))\n                for rev,(u,v) in enumerate(((x,y),(y,x))):\n                    sub={}\n                    if rigid.match_term(u,goal[0],sub) and rigid.match_term(v,goal[1],sub):\n                        basec=c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))\n                        return sf.instantiate(basec,sub)\n            return None\n        def compact_certificate(code):\n            if not hasattr(m,'_mg_elide_have_types'):\n                return code\n            original=code.splitlines()\n            compact=m._mg_elide_have_types(code).splitlines()\n            if len(original)!=len(compact):\n                return code\n            # Lean sometimes needs the proposition annotation on an rfl have.\n            # This is the exact safety rule used by the earlier officially\n            # accepted generic-expansion certificate.\n            for i,(before,after) in enumerate(zip(original,compact)):\n                if after.lstrip().startswith('have ') and after.rstrip().endswith(':= rfl') and ' : ' in before and ' := ' in before:\n                    compact[i]=before\n            return '\\n'.join(compact)+'\\n'\n        f15=cover_frontier('f15')\n        f278=None; close_details=[]; judge_status=None; judge_error=None; judge_message=None; cert_bytes=None; proof_nodes=None; target_hit=False; close_replay=False\n        if bridge is not None and f15 is not None:\n            for A,B,label in ((f15,bridge,'15x259'),(bridge,f15,'259x15')):\n                A=expf(A); B=expf(B)\n                for ar in (False,True):\n                    aa=orient(A,ar)\n                    for br in (False,True):\n                        bb=orient(B,br)\n                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):\n                            q=origf(aa,bb,0,1,path)\n                            if q is None or not matchf(q,'f278'): continue\n                            nodes,root=sf.compile(ef.inline_recipe(q))\n                            ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=300,maximum_nodes=60000))\n                            close_details.append({'order':label,'left_rev':ar,'right_rev':br,'path':list(path),'replay':ok,'nodes':len(nodes)})\n                            if ok:\n                                f278=q; close_replay=True; proof_nodes=len(nodes); break\n                        if f278: break\n                    if f278: break\n                if f278: break\n        if f278 is not None:\n            rr=ef.inline_recipe(f278)\n            if (rr.lhs,rr.rhs)==(target[1],target[0]): rr=m.Recipe(rr.rhs,rr.lhs,'symmetry',(rr,))\n            nodes,root=sf.compile(rr)\n            target_hit=(nodes[root].lhs,nodes[root].rhs)==target[:2]\n            if target_hit and bool(m.replay_dag(source,nodes,root,maximum_term_size=300,maximum_nodes=60000)):\n                code,_=m.make_dag_certificate(target,nodes,root)\n                code=compact_certificate(code)\n                cert_bytes=len(code.encode('utf-8'))\n                if cert_bytes<=100000:\n                    from dataclasses import replace\n                    from judge.verify import _resolve_config, verify_answer\n                    cfg=replace(_resolve_config(None),max_code_length=100000)\n                    jr=verify_answer(row,json.dumps({'verdict':'true','code':code}),config=cfg)\n                    judge_status=jr.get('status'); judge_error=jr.get('error_code'); judge_message=jr.get('message')\n        out={'id':RID,'frontier_f217':f217 is not None,'frontier_rounds':rounds,'frontier_enumerated':enumf,'frontier_clauses':len(sf.clauses),'given_f258':f258 is not None,'given_steps':givens,'given_enumerated':enumg,'given_clauses':len(sg.clauses),'cross_f259':bridge is not None,'cross_details':details,'frontier_f15':f15 is not None,'close_f278':f278 is not None,'close_details':close_details,'close_replay':close_replay,'target_hit':target_hit,'proof_nodes':proof_nodes,'certificate_bytes':cert_bytes,'judge_status':judge_status,'judge_error_code':judge_error,'judge_message':judge_message}\n        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\\n'); print('MSI_PORTFOLIO_TARGET_CLOSE',json.dumps(out,sort_keys=True),flush=True)\n"""
if old_out not in s:
    raise SystemExit('expected output block not found')
s = s.replace(old_out, new_out, 1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_msi_target_close_runtime.py', prefix='_msi_', dir=SRC.parent, delete=False) as fh:
    fh.write(s)
    patched=Path(fh.name)
try:
    cmd=[sys.executable,str(patched),'--input',a.input,'--output',a.output,'--frontier-seconds',str(a.frontier_seconds),'--given-seconds',str(a.given_seconds)]
    raise SystemExit(subprocess.call(cmd,cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)
