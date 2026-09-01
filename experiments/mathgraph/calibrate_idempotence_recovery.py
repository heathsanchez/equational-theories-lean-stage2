#!/usr/bin/env python3
"""Calibrate a fast source-only search against the known 0036 idempotence law.

This is a positive-control gate, not a solver.  It ignores the real target and
asks whether the current generic EqualitySearch kernel can recover x = x◇x from
the source under increasing bounded budgets.  A negative is not interpreted as
absence of the law; it means this kernel is too weak for trusted microprobes.
"""

import argparse, importlib.util, json, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions/mathgraph/solver.py"


def load_solver():
    spec = importlib.util.spec_from_file_location("mgsolver", SOLVER)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def source_text(row):
    for k in ("equation1", "source", "eq1"):
        if isinstance(row.get(k), str): return row[k]
    raise KeyError("source equation not found")


def unpack(search, raw):
    if raw is None or raw is False: return None
    if isinstance(raw, int): return search.nodes, raw
    if isinstance(raw, tuple) and len(raw) == 2:
        a,b=raw
        if isinstance(a,list) and isinstance(b,int): return a,b
        if isinstance(a,int) and isinstance(b,list): return b,a
    return None


def main():
    ap=argparse.ArgumentParser(); ap.add_argument("corpus",type=Path); args=ap.parse_args()
    m=load_solver(); rows=[json.loads(x) for x in args.corpus.read_text().splitlines() if x.strip()]
    row=next(r for r in rows if r.get("id")=="order5_normal_0036")
    source=m.parse_equation(source_text(row))
    x=("var","x"); target=(x,("op",x,x),("x",))
    budgets=[
      (0.05, {"max_term_size":11,"max_pool_terms":18,"max_core_terms":5,"max_source_attempts":12000,"max_source_edges":420,"max_derivation_nodes":1400,"max_graph_edges":1100,"max_congruence_rounds":2}),
      (0.25, {"max_term_size":13,"max_pool_terms":28,"max_core_terms":7,"max_source_attempts":50000,"max_source_edges":900,"max_derivation_nodes":2800,"max_graph_edges":2400,"max_congruence_rounds":3}),
      (1.0, {"max_term_size":17,"max_pool_terms":40,"max_core_terms":9,"max_source_attempts":200000,"max_source_edges":1600,"max_derivation_nodes":4500,"max_graph_edges":4000,"max_congruence_rounds":3}),
      (5.0, {"max_term_size":25,"max_pool_terms":56,"max_core_terms":12,"max_source_attempts":600000,"max_source_edges":3200,"max_derivation_nodes":9000,"max_graph_edges":8000,"max_congruence_rounds":4}),
      (15.0,{"max_term_size":35,"max_pool_terms":72,"max_core_terms":14,"max_source_attempts":1200000,"max_source_edges":6000,"max_derivation_nodes":16000,"max_graph_edges":14000,"max_congruence_rounds":5}),
    ]
    out=[]
    for seconds,limits in budgets:
        t0=time.monotonic(); s=m.EqualitySearch(source,target,time.monotonic()+seconds,limits); raw=s.solve(); got=unpack(s,raw)
        ok=False; nodes=0
        if got is not None:
            ns,root=got; ok=bool(m.replay_dag(source,ns,root)); nodes=len(ns) if ok else 0
        rec={"seconds":seconds,"elapsed":round(time.monotonic()-t0,4),"recovered":ok,"proof_nodes":nodes,"graph_edges":getattr(s,"graph_edges",None),"exhaustion":getattr(s,"exhaustion",None)}
        out.append(rec); print("IDEMPOTENCE_CALIBRATION_STEP "+json.dumps(rec,sort_keys=True),flush=True)
        if ok: break
    summary={"id":row["id"],"law":"x = (x ◇ x)","recovered":any(r["recovered"] for r in out),"steps":out}
    print("IDEMPOTENCE_CALIBRATION "+json.dumps(summary,sort_keys=True),flush=True)
    if not summary["recovered"]:
        raise SystemExit(2)

if __name__=="__main__": main()
