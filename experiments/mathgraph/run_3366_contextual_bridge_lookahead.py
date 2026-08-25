from pathlib import Path

SRC = Path('experiments/mathgraph/run_3366_iterated_contextual_contraction.py')


def main():
    source = SRC.read_text()
    source = source.replace("OUT = Path('experiments/mathgraph/results/3366-iterated-contextual-contraction.json')", "OUT = Path('experiments/mathgraph/results/3366-contextual-bridge-lookahead.json')", 1)
    source = source.replace('CONTEXT_GENERATIONS = 3', 'CONTEXT_GENERATIONS = 4\n    BRIDGE_GENERATION = 3\n    BRIDGE_SLACK = 8', 1)
    source = source.replace(
        "                            if dist >= previous_best:\n                                continue\n                            strict_count += 1",
        "                            if generation == BRIDGE_GENERATION:\n                                if dist > previous_best + BRIDGE_SLACK:\n                                    continue\n                            else:\n                                if dist >= previous_best:\n                                    continue\n                            strict_count += int(dist < previous_best)",
        1,
    )
    source = source.replace(
        "        improved = best_distance is not None and best_distance < previous_best\n        monotonic = monotonic and improved",
        "        improved = best_distance is not None and best_distance < previous_best\n        bridge_admitted = (\n            generation == BRIDGE_GENERATION\n            and best_distance is not None\n            and best_distance <= previous_best + BRIDGE_SLACK\n        )\n        monotonic = monotonic and (improved or bridge_admitted)",
        1,
    )
    source = source.replace(
        "            'improved': improved,\n            'nodes': len(nodes),",
        "            'improved': improved,\n            'bridge_admitted': bridge_admitted,\n            'bridge_slack': BRIDGE_SLACK if generation == BRIDGE_GENERATION else 0,\n            'nodes': len(nodes),",
        1,
    )
    source = source.replace(
        "        if not retained or not improved:\n            break",
        "        if not retained or (not improved and not bridge_admitted):\n            break",
        1,
    )
    source = source.replace(
        "        previous_best = best_distance",
        "        if generation != BRIDGE_GENERATION:\n            previous_best = best_distance",
        1,
    )
    source = source.replace(
        "        'promotion_gate': bool(\n            (direct_target is not None and direct_target.get('replayed'))\n            or (\n                len(generation_rows) >= 2\n                and all(row['improved'] for row in generation_rows)\n            )\n        ),",
        "        'bridge_generation': BRIDGE_GENERATION,\n        'bridge_slack': BRIDGE_SLACK,\n        'promotion_gate': bool(\n            (direct_target is not None and direct_target.get('replayed'))\n            or (\n                len(generation_rows) >= 4\n                and generation_rows[2].get('bridge_admitted')\n                and generation_rows[3].get('best_distance') is not None\n                and generation_rows[3]['best_distance'] < 100\n            )\n        ),",
        1,
    )
    source = source.replace("result['schema'] = 'mathgraph.3366-iterated-contextual-contraction.v1'", "result['schema'] = 'mathgraph.3366-contextual-bridge-lookahead.v1'", 1)
    source = source.replace("'ITERATED_CONTEXTUAL_SUMMARY'", "'CONTEXTUAL_BRIDGE_SUMMARY'", 1)
    ns = {'__name__': '__main__'}
    exec(compile(source, str(SRC), 'exec'), ns, ns)


if __name__ == '__main__':
    main()
