#!/usr/bin/env python3
import importlib.util, subprocess, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE / 'run_residual3_first_divergence.py'
spec = importlib.util.spec_from_file_location('base_div', BASE)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def vampire_trace(m, r):
    source = m.parse_equation(r['equation1'])
    target = m.parse_equation(r['equation2'])
    problem = f"fof(source,axiom,({base.quantified(source)})).\nfof(target,conjecture,({base.quantified(target)})).\n"
    with tempfile.NamedTemporaryFile(mode='w', suffix='.p', dir='/tmp', delete=True) as h:
        h.write(problem); h.flush()
        run = subprocess.run(['vampire','--mode','casc','--time_limit','20','--proof','tptp',h.name], capture_output=True, text=True, timeout=22)
    out = run.stdout + run.stderr
    proof = [x for x in out.splitlines() if x.startswith(('fof(', 'cnf('))]
    if not proof:
        print('VAMPIRE_RAW_HEAD', '\n'.join(out.splitlines()[:80]), flush=True)
    return source, target, proof, out


def parse_tptp(line):
    if line.startswith('fof('): off = 4
    elif line.startswith('cnf('): off = 4
    else: return None
    body = line[off:]
    if body.endswith(').'): body = body[:-2]
    parts = base.split_top(body, ',')
    if len(parts) < 3: return None
    formula = base.strip_outer(parts[2])
    tail = ','.join(parts[3:])
    import re
    mm = re.search(r'inference\(([^,\]]+)', tail)
    inf = mm.group(1) if mm else None
    return formula, inf

base.vampire_trace = vampire_trace
base.parse_fof = parse_tptp
base.main()
