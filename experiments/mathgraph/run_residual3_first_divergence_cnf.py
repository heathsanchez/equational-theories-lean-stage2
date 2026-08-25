#!/usr/bin/env python3
import importlib.util, subprocess, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE / 'run_residual3_first_divergence.py'
spec = importlib.util.spec_from_file_location('base_div', BASE)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)

_seen = 0


def _collect_tptp_statements(text):
    statements = []
    buf = []
    depth = 0
    active = False
    for raw in text.splitlines():
        line = raw.strip()
        if not active:
            if not line.startswith(('fof(', 'cnf(')):
                continue
            active = True
            buf = []
            depth = 0
        buf.append(line)
        depth += line.count('(') - line.count(')')
        if depth == 0 and line.endswith('.'):
            statements.append(' '.join(buf))
            buf = []
            active = False
            depth = 0
    if active and buf:
        print('UNTERMINATED_TPTP', ' '.join(buf[:8]), flush=True)
    return statements


def vampire_trace(m, r):
    source = m.parse_equation(r['equation1'])
    target = m.parse_equation(r['equation2'])
    problem = f"fof(source,axiom,({base.quantified(source)})).\nfof(target,conjecture,({base.quantified(target)})).\n"
    with tempfile.NamedTemporaryFile(mode='w', suffix='.p', dir='/tmp', delete=True) as h:
        h.write(problem); h.flush()
        run = subprocess.run(['vampire','--mode','casc','--time_limit','20','--proof','tptp',h.name], capture_output=True, text=True, timeout=22)
    out = run.stdout + run.stderr
    proof = _collect_tptp_statements(out)
    if not proof:
        print('VAMPIRE_RAW_HEAD', '\n'.join(out.splitlines()[:100]), flush=True)
    else:
        print('VAMPIRE_STATEMENTS', r['id'], len(proof), flush=True)
        print('VAMPIRE_PROOF_HEAD', r['id'], '\n'.join(proof[:8]), flush=True)
    return source, target, proof, out


def parse_tptp(line):
    global _seen
    if line.startswith('fof('): off = 4
    elif line.startswith('cnf('): off = 4
    else: return None
    body = line[off:]
    if body.endswith(').'): body = body[:-2]
    parts = base.split_top(body, ',')
    if len(parts) < 3:
        print('PARSE_PARTS_FAIL', line[:1000], flush=True)
        return None
    formula = base.strip_outer(parts[2])
    tail = ','.join(parts[3:])
    import re
    mm = re.search(r'inference\(([^,\]]+)', tail)
    inf = mm.group(1) if mm else None
    if _seen < 60:
        print('PROOF_FORMULA', repr(formula), 'INF', inf, 'EQ', base.find_top_equality(formula), flush=True)
        _seen += 1
    return formula, inf

base.vampire_trace = vampire_trace
base.parse_fof = parse_tptp
base.main()
