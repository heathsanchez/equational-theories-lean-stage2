import contextlib
import hashlib
import importlib.util
import io
import json
import re
import sys
import tempfile
import time
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / 'submissions/mathgraph/solver.py'
OUT = ROOT / 'experiments/mathgraph/results/compact-retry-pseudo-hidden-ab.json'
SPLITS = ('normal', 'hard1', 'hard2', 'hard3')
PER_CLASS_PER_SPLIT = 12
TIMEOUT_SECONDS = 2.0

INSERT_AFTER = '''    if compact_recipe is not None and finish_compact_superposition_candidate(\n        source, target, compact_search, compact_recipe\n    ):\n        return\n'''
RETRY = '''\n    # Sealed pseudo-hidden candidate: repeat the same production compact\n    # superposition engine from a fresh state with the empirically sufficient\n    # 0.15 second deadline. Every candidate is independently replayed.\n    retry_seconds = min(0.15, max(0.05, timeout / 10.0))\n    try:\n        retry_search = CompactSuperposition(\n            sys.modules[__name__], source, target,\n            time.monotonic() + retry_seconds, compact_limits,\n        )\n        retry_recipe = retry_search.solve()\n    except (\n        KeyError, IndexError, MemoryError, RecursionError, TypeError, ValueError\n    ):\n        retry_recipe = None\n    if retry_recipe is not None and finish_compact_superposition_candidate(\n        source, target, retry_search, retry_recipe\n    ):\n        return\n'''


def candidate_path():
    text = SOLVER.read_text(encoding='utf-8')
    count = text.count(INSERT_AFTER)
    if count != 1:
        raise RuntimeError(f'expected one compact insertion point, found {count}')
    text = text.replace(INSERT_AFTER, INSERT_AFTER + RETRY, 1)
    path = ROOT / 'experiments/mathgraph/_solver_compact_retry_candidate.py'
    path.write_text(text, encoding='utf-8')
    return path


def load_rows():
    by_split = {}
    for split in SPLITS:
        path = ROOT / f'examples/problems/{split}.jsonl'
        by_split[split] = [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]
    return by_split


def stable_key(row):
    return hashlib.sha256(row['id'].encode('utf-8')).hexdigest()


def balanced_sample(rows):
    selected = []
    for answer in (True, False):
        pool = sorted((r for r in rows if bool(r['answer']) is answer), key=stable_key)
        selected.extend(pool[:PER_CLASS_PER_SPLIT])
    return sorted(selected, key=lambda r: (stable_key(r), r['id']))


def load_solver(path):
    spec = importlib.util.spec_from_file_location('mg_compact_retry_candidate', path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def internal_certificate_verdict(mod, row):
    captured = []
    def fake_judge(verdict, code):
        captured.append({'verdict': verdict, 'code_bytes': len(code.encode('utf-8')) if isinstance(code, str) else None})
        return {'status': 'accepted'}
    old_judge, old_stdin = mod.judge, sys.stdin
    startup = {'problem': {'id': row['id'], 'equation1': row['equation1'], 'equation2': row['equation2']},
               'budget': {'timeout_seconds': TIMEOUT_SECONDS, 'max_code_length': 100000, 'max_false_cert_bytes': 20000}}
    stderr = io.StringIO(); started = time.monotonic(); error = None
    try:
        mod.judge = fake_judge
        sys.stdin = io.StringIO(json.dumps(startup) + '\n')
        with contextlib.redirect_stderr(stderr), contextlib.redirect_stdout(io.StringIO()):
            mod.run_solo()
    except Exception as exc:
        error = f'{type(exc).__name__}: {exc}'
    finally:
        mod.judge, sys.stdin = old_judge, old_stdin
    metrics = []
    for line in stderr.getvalue().splitlines():
        if line.startswith('MATHGRAPH_METRICS '):
            try: metrics.append(json.loads(line.split(' ', 1)[1]))
            except Exception: pass
    route = None
    for item in reversed(metrics):
        if item.get('found') is True:
            route = item.get('portfolio') or item.get('route') or item.get('name')
            if route: break
    verdict = captured[0]['verdict'] if captured else None
    return {'verdict': verdict, 'answered': verdict in ('true','false'), 'seconds': time.monotonic()-started,
            'code_bytes': captured[0]['code_bytes'] if captured else None, 'route_metric': route, 'error': error}


def summarize(rows, key):
    groups = defaultdict(list)
    for r in rows: groups[r[key]].append(r)
    out = {}
    for name, xs in groups.items():
        answered = sum(x['answered'] for x in xs); correct = sum(x['correct'] for x in xs); wrong = sum(x['wrong'] for x in xs)
        out[str(name)] = {'n': len(xs), 'answered': answered, 'coverage': answered/len(xs), 'correct': correct,
                          'wrong_answered': wrong, 'answered_precision': correct/answered if answered else None}
    return out


def main():
    path = candidate_path(); by_split = load_rows(); mod = load_solver(path)
    sample = []
    for split in SPLITS:
        for row in balanced_sample(by_split[split]): sample.append(dict(row) | {'split': split})
    results = []
    for row in sample:
        pred = internal_certificate_verdict(mod, row); expected = 'true' if row['answer'] else 'false'; verdict = pred['verdict']
        result = {'id': row['id'], 'split': row['split'], 'expected': expected, **pred}
        result['correct'] = verdict == expected; result['wrong'] = verdict is not None and verdict != expected
        results.append(result)
        print('COMPACT_RETRY_AB_CASE ' + json.dumps({k: result[k] for k in ('id','split','expected','verdict','correct','seconds','route_metric','error')}, sort_keys=True), flush=True)
    answered = sum(r['answered'] for r in results); correct = sum(r['correct'] for r in results); wrong = sum(r['wrong'] for r in results)
    summary = {'schema':'mathgraph.compact-retry-pseudo-hidden-ab.v1','baseline':{'answered':85,'correct':85,'wrong':0},
               'candidate':{'n':len(results),'answered':answered,'correct':correct,'wrong':wrong},
               'by_split':summarize(results,'split'),
               'failures':[r for r in results if not r['correct']],
               'hard2_0199':next(r for r in results if r['id']=='hard2_0199'),
               'promotion': answered >= 86 and correct == answered and wrong == 0}
    OUT.parent.mkdir(parents=True, exist_ok=True); OUT.write_text(json.dumps(summary, indent=2, sort_keys=True)+'\n')
    print('COMPACT_RETRY_AB_SUMMARY ' + json.dumps(summary, sort_keys=True), flush=True)
    path.unlink(missing_ok=True)
    if wrong or any(r['error'] for r in results): raise SystemExit('FAIL: wrong answer or execution error')

if __name__ == '__main__': main()
