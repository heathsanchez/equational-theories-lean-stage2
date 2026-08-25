import importlib.util, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE / 'run_final_lineage_tournament.py'
spec = importlib.util.spec_from_file_location('tournament_base', BASE)
m = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = m
spec.loader.exec_module(m)

def build_arms(tmp):
    a = m.git_show(m.BASE_794)
    b = m.git_show(m.GIVEN_796)
    current = (m.ROOT / m.SOLVER_PATH).read_text(encoding='utf-8')
    arms = {
        'A_794_exact': a,
        'B_796_given_clause': b,
        'C_794_plus_retry': m.add_retry(a),
        'D_796_plus_retry': m.add_retry(b),
        'E_current_research_plus_retry': m.add_retry(current),
    }
    paths = {}
    for name, text in arms.items():
        p = tmp / f'{name}.py'
        p.write_text(text, encoding='utf-8')
        paths[name] = p
        print('ARM_BUILD', name, len(text.encode()), flush=True)
    return paths

m.build_arms = build_arms
m.OUT = m.ROOT / 'experiments/mathgraph/results/final-lineage-tournament-v2.json'
if __name__ == '__main__':
    m.main()
