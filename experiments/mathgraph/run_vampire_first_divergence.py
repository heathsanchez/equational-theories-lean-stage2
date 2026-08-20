#!/usr/bin/env python3
import argparse, importlib.util, json, re, sys, time, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / 'submissions/mathgraph/solver.py'
TRACE_URL = 'https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'


def load_solver():
    spec = importlib.util.spec_from_file_location('mg_divergence_solver', SOLVER)
    m = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = m
    spec.loader.exec_module(m)
    return m


class P:
    def __init__(self, s): self.s, self.i = s, 0
    def ws(self):
        while self.i < len(self.s) and self.s[self.i].isspace(): self.i += 1
    def name(self):
        self.ws(); j = self.i
        while self.i < len(self.s) and (self.s[self.i].isalnum() or self.s[self.i] in '_$@'):
            self.i += 1
        if self.i == j: raise ValueError('name')
        return self.s[j:self.i]
    def term(self):
        n = self.name(); self.ws()
        if self.i < len(self.s) and self.s[self.i] == '(':
            self.i += 1; a = self.term(); self.ws()
            if self.s[self.i] != ',': raise ValueError('comma')
            self.i += 1; b = self.term(); self.ws()
            if self.s[self.i] != ')': raise ValueError('close')
            self.i += 1
            if n != 'f': raise ValueError('non-f function')
            return ('op', a, b)
        return ('var', n)


def parse_term(s):
    p = P(s.strip()); t = p.term(); p.ws()
    if p.i != len(p.s): raise ValueError('trailing')
    return t


def strip_outer(s):
    s = s.strip()
    changed = True
    while changed and len(s) >= 2 and s[0] == '(' and s[-1] == ')':
        depth = 0; changed = False
        for i, c in enumerate(s):
            if c == '(': depth += 1
            elif c == ')':
                depth -= 1
                if depth == 0:
                    if i == len(s) - 1:
                        s = s[1:-1].strip(); changed = True
                    break
    return s


def split_top_level(s, sep=','):
    out = []; start = 0; depth = 0; brackets = 0
    for i, c in enumerate(s):
        if c == '(': depth += 1
        elif c == ')': depth -= 1
        elif c == '[': brackets += 1
        elif c == ']': brackets -= 1
        elif c == sep and depth == 0 and brackets == 0:
            out.append(s[start:i].strip()); start = i + 1
    out.append(s[start:].strip())
    return out


def fof_blocks(proof):
    out = []; start = 0
    while True:
        i = proof.find('fof(', start)
        if i < 0: break
        depth = 0; j = i + 3
        while j < len(proof):
            if proof[j] == '(': depth += 1
            elif proof[j] == ')':
                depth -= 1
                if depth == 0:
                    out.append(proof[i:j+1]); start = j + 1; break
            j += 1
        else: break
    return out


def parse_fof(block):
    inner = block[4:-1]
    parts = split_top_level(inner)
    if len(parts) < 3: return None
    return parts[0], parts[1], parts[2], parts[3:]


def formula_equality(formula):
    s = strip_outer(formula)
    q = re.match(r'^[!?]\s*\[[^\]]*\]\s*:\s*(.*)$', s, re.S)
    if q: s = strip_outer(q.group(1))
    depth = 0
    for i, c in enumerate(s):
        if c == '(': depth += 1
        elif c == ')': depth -= 1
        elif c == '=' and depth == 0 and not (i and s[i-1] == '!'):
            return parse_term(s[:i]), parse_term(s[i+1:])
    return None


def inline_defs(term, defs, seen=None):
    seen = set() if seen is None else seen
    if term[0] == 'var' and term[1] in defs and term[1] not in seen:
        return inline_defs(defs[term[1]], defs, seen | {term[1]})
    if term[0] == 'op':
        return ('op', inline_defs(term[1], defs, seen), inline_defs(term[2], defs, seen))
    return term


def map_vampire_rigids(term, target_vars):
    if term[0] == 'var':
        n = term[1]
        m = re.fullmatch(r'sK(\d+)', n)
        if m:
            i = int(m.group(1))
            return ('var', '@' + (target_vars[i] if i < len(target_vars) else 'sk' + str(i)))
        return term
    return ('op', map_vampire_rigids(term[1], target_vars), map_vampire_rigids(term[2], target_vars))


def inline_engine_names(term, reverse_constants, seen=None):
    seen = set() if seen is None else seen
    if term[0] == 'var' and term[1] in reverse_constants and term[1] not in seen:
        return inline_engine_names(reverse_constants[term[1]], reverse_constants, seen | {term[1]})
    if term[0] == 'op':
        return ('op', inline_engine_names(term[1], reverse_constants, seen), inline_engine_names(term[2], reverse_constants, seen))
    return term


def sig(rigid_module, a, b):
    names = {}
    x = rigid_module.alpha_canonical_term(a, names)
    y = rigid_module.alpha_canonical_term(b, names)
    return min((x, y), (y, x))


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--input', required=True); ap.add_argument('--output', required=True); args = ap.parse_args()
    m = load_solver(); rows = json.load(open(args.input)); row = next(r for r in rows if r['id'] == 'evaluation_order5_0014')
    source = m.parse_equation(row['equation1']); target = m.parse_equation(row['equation2'])
    limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    engine = m.TargetGroundedRefutation(source, target, time.monotonic()+15.0, limits)
    found = engine.solve()
    rigid = m.RigidSuperpositionModule()
    clause_sigs = set()
    for c in engine.search.clauses:
        a = inline_engine_names(c.lhs, engine.reverse_constants)
        b = inline_engine_names(c.rhs, engine.reverse_constants)
        clause_sigs.add(sig(rigid, a, b))

    trace = json.load(urllib.request.urlopen(TRACE_URL))
    proof = next(r['proof'] for r in trace['rows'] if r['id'] == row['id'])
    defs = {}; audited = []; first = None; parse_failures = []
    for block in fof_blocks(proof):
        parsed = parse_fof(block)
        if not parsed: continue
        fid, kind, formula, tail = parsed
        try: eq = formula_equality(formula)
        except Exception as e:
            eq = None; parse_failures.append({'id':fid,'error':type(e).__name__})
        if eq is None: continue
        a, b = eq
        if kind == 'definition':
            if a[0] == 'var' and a[1].startswith('sF'): defs[a[1]] = b
            elif b[0] == 'var' and b[1].startswith('sF'): defs[b[1]] = a
            continue
        joined = ','.join(tail)
        mi = re.search(r'inference\(([^,\]]+)', joined)
        inf = mi.group(1) if mi else ''
        if inf not in ('superposition','forward_demodulation'): continue
        ia = map_vampire_rigids(inline_defs(a, defs), target[2])
        ib = map_vampire_rigids(inline_defs(b, defs), target[2])
        present = sig(rigid, ia, ib) in clause_sigs
        rec = {'id':fid,'inference':inf,'present':present,'lhs':m.render_term(ia),'rhs':m.render_term(ib),'lhs_size':m.term_size(ia),'rhs_size':m.term_size(ib)}
        audited.append(rec)
        if first is None and not present: first = rec

    out = {
        'solver_found': bool(found), 'clauses': len(engine.search.clauses), 'rounds': engine.search.rounds,
        'superpositions': engine.search.superpositions, 'reductions': engine.search.reductions,
        'audited_steps': len(audited), 'present_steps': sum(x['present'] for x in audited),
        'first_missing': first, 'parse_failures': parse_failures, 'steps': audited,
    }
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True))
    print(json.dumps(out, indent=2, sort_keys=True))

if __name__ == '__main__': main()
