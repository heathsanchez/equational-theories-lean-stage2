from pathlib import Path
import json

SRC = Path('experiments/mathgraph/run_2666_tuple_scheduler.py')
text = SRC.read_text()
text = text.replace("'max_term_size':35", "'max_term_size':75")
text = text.replace("maximum_term_size=35", "maximum_term_size=75")
# Preserve the experiment logic exactly, only lift the term-admission/replay ceiling.
ns = {'__name__': '__main__', '__file__': str(SRC)}
exec(compile(text, str(SRC), 'exec'), ns)

src_result = Path('experiments/mathgraph/results/2666-tuple-scheduler.json')
out = json.loads(src_result.read_text())
out['schema'] = 'mathgraph.2666-tuple-scheduler-term75.v1'
out['term_admission_ceiling'] = 75
dst = Path('experiments/mathgraph/results/2666-tuple-scheduler-term75.json')
dst.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
print('TERM75_SUMMARY', json.dumps(out, sort_keys=True))
