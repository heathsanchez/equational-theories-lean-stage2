#!/usr/bin/env python3
import argparse
from pathlib import Path

from build_full_residual_candidate import build as build_v1


def build(baseline, runner, output):
    stage = str(Path(output).with_suffix('.v1.py'))
    build_v1(baseline, runner, stage)
    text = Path(stage).read_text()
    old = '''def try_paramodulation_control_candidate(problem, source, target, timeout):\n    if not streaming_singleton_shape(source, target):\n        return False\n'''
    new = '''def try_paramodulation_control_candidate(problem, source, target, timeout):\n    source_left, source_right, source_variables = source\n    target_left, target_right, target_variables = target\n    if not (\n        source_left[0] == "var"\n        and target_left[0] == "var"\n        and 7 <= term_size(source_right) <= 15\n        and 7 <= term_size(target_right) <= 15\n        and variable_occurrence_count(source_right) > len(source_variables)\n        and variable_occurrence_count(target_right) > len(target_variables)\n    ):\n        return False\n'''
    if old not in text:
        raise SystemExit('controller gate marker not found')
    text = text.replace(old, new, 1)
    Path(output).write_text(text)
    Path(stage).unlink(missing_ok=True)
    print(f'candidate_bytes={Path(output).stat().st_size}')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline', default='submissions/mathgraph/solver.py')
    parser.add_argument('--runner', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    build(args.baseline, args.runner, args.output)


if __name__ == '__main__':
    main()
