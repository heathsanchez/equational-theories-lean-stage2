import contextlib
import hashlib
import importlib.util
import io
import json
import re
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / 'submissions/mathgraph/solver.py'
OUT = ROOT / 'experiments/mathgraph/results/pseudo-hidden-generalization-gate.json'
SPLITS = ('normal', 'hard1', 'hard2', 'hard3')
PER_CLASS_PER_SPLIT = 12
TIMEOUT_SECONDS = 2.0


def load_rows():
    by_split = {}
    for split in SPLITS:
        path = ROOT / f'examples/problems/{split}.jsonl'
        rows = [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]
        by_split[split] = rows
    return by_split


def stable_key(row):
    return hashlib.sha256(row['id'].encode('utf-8')).hexdigest()


def balanced_sample(rows):
    selected = []
    for answer in (True, False):
        pool = sorted((r for r in rows if bool(r['answer']) is answer), key=stable_key)
        selected.extend(pool[:PER_CLASS_PER_SPLIT])
    return sorted(selected, key=lambda r: (stable_key(r), r['id']))


def equation_vars(text):
    # Equation syntax uses x,y,z,w,u style variable names and the diamond symbol.
    return set(re.findall(r'\b[a-z]\b', text))


def lhs_is_var(text):
    lhs = text.split('=', 1)[0].strip()
    return bool(re.fullmatch(r'[a-z]', lhs))


def op_bucket(n):
    if n <= 6:
        return 'ops<=6'
    if n <= 9:
        return 'ops7-9'
    return 'ops>=10'


def load_solver():
    spec = importlib.util.spec_from_file_location('mg_pseudo_hidden', SOLVER)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def internal_certificate_verdict(mod, row):
    captured = []
    def fake_judge(verdict, code):
        captured.append({'verdict': verdict, 'code_bytes': len(code.encode('utf-8')) if isinstance(code, str) else None})
        return {'status': 'accepted'}

    old_judge = mod.judge
    old_stdin = sys.stdin
    stderr = io.StringIO()
    startup = {
        'problem': {
            'id': row['id'],
            'equation1': row['equation1'],
            'equation2': row['equation2'],
        },
        'budget': {
            'timeout_seconds': TIMEOUT_SECONDS,
            'max_code_length': 100000,
            'max_false_cert_bytes': 20000,
        },
    }
    started = time.monotonic()
    error = None
    try:
        mod.judge = fake_judge
        sys.stdin = io.StringIO(json.dumps(startup) + '\n')
        with contextlib.redirect_stderr(stderr), contextlib.redirect_stdout(io.StringIO()):
            mod.run_solo()
    except Exception as exc:
        error = f'{type(exc).__name__}: {exc}'
    finally:
        mod.judge = old_judge
        sys.stdin = old_stdin
    elapsed = time.monotonic() - started
    verdict = captured[0]['verdict'] if captured else None
    metrics = []
    for line in stderr.getvalue().splitlines():
        if line.startswith('MATHGRAPH_METRICS '):
            try:
                metrics.append(json.loads(line.split(' ', 1)[1]))
            except Exception:
                pass
    route = None
    for item in reversed(metrics):
        if item.get('found') is True:
            route = item.get('portfolio') or item.get('route') or item.get('name')
            if route:
                break
    return {
        'verdict': verdict,
        'answered': verdict in ('true', 'false'),
        'code_bytes': captured[0]['code_bytes'] if captured else None,
        'seconds': elapsed,
        'route_metric': route,
        'error': error,
    }


def summarize(rows, key):
    groups = defaultdict(list)
    for r in rows:
        groups[r[key]].append(r)
    out = {}
    for name, xs in sorted(groups.items(), key=lambda kv: str(kv[0])):
        total = len(xs)
        answered = sum(x['answered'] for x in xs)
        correct = sum(x['correct'] for x in xs)
        wrong = sum(x['wrong'] for x in xs)
        out[str(name)] = {
            'n': total,
            'answered': answered,
            'coverage': answered / total if total else 0.0,
            'correct': correct,
            'accuracy_with_abstention_wrong': correct / total if total else 0.0,
            'wrong_answered': wrong,
            'answered_precision': (correct / answered) if answered else None,
        }
    return out


def main():
    by_split = load_rows()
    all_rows = [r | {'split': split} for split, rows in by_split.items() for r in rows]

    # Full-public distribution census (no solver execution required).
    id_splits = defaultdict(set)
    for r in all_rows:
        id_splits[r['eq1_id']].add(r['split'])
        id_splits[r['eq2_id']].add(r['split'])
    public_census = {}
    for split, rows in by_split.items():
        public_census[split] = {
            'n': len(rows),
            'true': sum(bool(r['answer']) for r in rows),
            'false': sum(not bool(r['answer']) for r in rows),
            'unique_eq1': len({r['eq1_id'] for r in rows}),
            'unique_eq2': len({r['eq2_id'] for r in rows}),
            'both_ids_split_private': sum(
                len(id_splits[r['eq1_id']]) == 1 and len(id_splits[r['eq2_id']]) == 1
                for r in rows
            ),
        }

    # Deterministic balanced pseudo-hidden sample: 12 TRUE + 12 FALSE per stratum.
    sample = []
    for split in SPLITS:
        for r in balanced_sample(by_split[split]):
            rr = dict(r)
            rr['split'] = split
            sample.append(rr)

    mod = load_solver()
    results = []
    for i, row in enumerate(sample, 1):
        pred = internal_certificate_verdict(mod, row)
        expected = 'true' if row['answer'] else 'false'
        total_ops = row['equation1'].count('◇') + row['equation2'].count('◇')
        variables = equation_vars(row['equation1']) | equation_vars(row['equation2'])
        shape = ('V' if lhs_is_var(row['equation1']) else 'O') + ('V' if lhs_is_var(row['equation2']) else 'O')
        novelty = (
            'both_private' if len(id_splits[row['eq1_id']]) == 1 and len(id_splits[row['eq2_id']]) == 1
            else 'cross_split_reuse'
        )
        verdict = pred['verdict']
        result = {
            'id': row['id'], 'split': row['split'], 'expected': expected,
            'eq1_id': row['eq1_id'], 'eq2_id': row['eq2_id'],
            'answer_family': expected,
            'op_bucket': op_bucket(total_ops),
            'variable_count': len(variables),
            'lhs_shape': shape,
            'id_novelty': novelty,
            **pred,
        }
        result['correct'] = verdict == expected
        result['wrong'] = verdict is not None and verdict != expected
        results.append(result)
        print('PSEUDO_HIDDEN_CASE', json.dumps({k: result[k] for k in (
            'id','split','expected','verdict','correct','seconds','op_bucket','variable_count','lhs_shape','id_novelty','route_metric','error'
        )}, sort_keys=True), flush=True)

    total = len(results)
    answered = sum(r['answered'] for r in results)
    correct = sum(r['correct'] for r in results)
    wrong = sum(r['wrong'] for r in results)
    errors = [r['id'] for r in results if r['error']]
    summary = {
        'schema': 'mathgraph.pseudo-hidden-generalization-gate.v1',
        'method': 'production run_solo with internal certificate checks intact; final judge acknowledgement replaced by recorder',
        'timeout_seconds': TIMEOUT_SECONDS,
        'sample_design': f'deterministic {PER_CLASS_PER_SPLIT} TRUE + {PER_CLASS_PER_SPLIT} FALSE per split',
        'public_census': public_census,
        'overall': {
            'n': total,
            'answered': answered,
            'coverage': answered / total if total else 0.0,
            'correct': correct,
            'accuracy_with_abstention_wrong': correct / total if total else 0.0,
            'wrong_answered': wrong,
            'answered_precision': correct / answered if answered else None,
            'errors': errors,
        },
        'by_split': summarize(results, 'split'),
        'by_answer': summarize(results, 'answer_family'),
        'by_id_novelty': summarize(results, 'id_novelty'),
        'by_op_bucket': summarize(results, 'op_bucket'),
        'by_variable_count': summarize(results, 'variable_count'),
        'by_lhs_shape': summarize(results, 'lhs_shape'),
        'route_counts': dict(Counter(r['route_metric'] or 'unattributed' for r in results if r['answered'])),
        'failures': [r for r in results if not r['correct']],
        'rows': results,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print('PSEUDO_HIDDEN_SUMMARY', json.dumps({
        'overall': summary['overall'],
        'by_split': summary['by_split'],
        'by_answer': summary['by_answer'],
        'by_id_novelty': summary['by_id_novelty'],
        'route_counts': summary['route_counts'],
        'public_census': public_census,
    }, sort_keys=True), flush=True)

    # Wrong answered certificates are a hard stop; abstentions are the research target.
    if wrong or errors:
        raise SystemExit(f'FAIL: wrong_answered={wrong} errors={len(errors)}')


if __name__ == '__main__':
    main()
