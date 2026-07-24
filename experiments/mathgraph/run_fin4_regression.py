#!/usr/bin/env python3
"""Official synthetic and metamorphic audits for bounded generic Fin 4."""

import argparse
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"
FROZEN = ROOT / "experiments/mathgraph/regressions/solver_fb671c7.py"
CASES = ROOT / "experiments/mathgraph/regressions/fin4_cases.json"


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def official_verify(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    enriched = dict(problem)
    number = 950000 + sum(ord(char) for char in problem["id"])
    enriched.setdefault("eq1_id", number)
    enriched.setdefault("eq2_id", number + 1)
    answer = json.dumps({"verdict": "false", "code": code})
    result = verify_answer(_to_judge_problem(enriched), answer)
    assert result["status"] == "accepted", (problem["id"], result)
    return result


def search(module, problem, configuration, options=None):
    source = module.parse_equation(problem["equation1"])
    target = module.parse_equation(problem["equation2"])
    arguments = (
        configuration["domain_size"],
        source,
        target,
        time.monotonic() + configuration["seconds"],
        configuration["maximum_states"],
        configuration["maximum_models"],
    )
    selected_options = (
        options if options is not None else configuration.get("options")
    )
    if selected_options is None:
        engine = module.FiniteModelEngine(*arguments)
    else:
        engine = module.FiniteModelEngine(
            *arguments, options=selected_options
        )
    found = engine.search_target_guided()
    return source, target, engine, found


def is_commutative(table, order):
    return all(
        table[order * left + right] == table[order * right + left]
        for left in range(order) for right in range(order)
    )


def is_associative(table, order):
    return all(
        table[order * table[order * x + y] + z]
        == table[order * x + table[order * y + z]]
        for x in range(order)
        for y in range(order)
        for z in range(order)
    )


def mirror_term(term):
    if term[0] == "var":
        return term
    return ("op", mirror_term(term[2]), mirror_term(term[1]))


def rename_term(term, mapping):
    if term[0] == "var":
        return ("var", mapping.get(term[1], term[1]))
    return (
        "op",
        rename_term(term[1], mapping),
        rename_term(term[2], mapping),
    )


def equation_text(module, left, right):
    return module.render_term(left) + " = " + module.render_term(right)


def metamorphic_problems(module, problem):
    source = module.parse_equation(problem["equation1"])
    target = module.parse_equation(problem["equation2"])
    mapping = {"x": "a", "y": "b", "z": "c", "w": "d"}
    return [
        {
            "id": "fin4_meta_variable_rename",
            "equation1": equation_text(
                module,
                rename_term(source[0], mapping),
                rename_term(source[1], mapping),
            ),
            "equation2": equation_text(
                module,
                rename_term(target[0], mapping),
                rename_term(target[1], mapping),
            ),
        },
        {
            "id": "fin4_meta_source_reverse",
            "equation1": equation_text(module, source[1], source[0]),
            "equation2": problem["equation2"],
        },
        {
            "id": "fin4_meta_target_reverse",
            "equation1": problem["equation1"],
            "equation2": equation_text(module, target[1], target[0]),
        },
        {
            "id": "fin4_meta_term_mirror",
            "equation1": equation_text(
                module, mirror_term(source[0]), mirror_term(source[1])
            ),
            "equation2": equation_text(
                module, mirror_term(target[0]), mirror_term(target[1])
            ),
        },
    ]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    module = load_module(SOLVER, "fin4_candidate")
    frozen = load_module(FROZEN, "fin4_frozen")
    cases = json.loads(CASES.read_text(encoding="utf-8"))
    by_id = {case["id"]: case for case in cases}
    probe, fast, medium = module.FIN4_PORTFOLIO[:3]
    positive_ids = [
        case["id"] for case in cases
        if case["id"] not in {
            "fin4_pathological_abstention",
            "fin4_true_control",
            "fin2_fin3_compatibility",
        }
    ]
    records = []
    models = {}
    for case_id in positive_ids:
        problem = by_id[case_id]
        if case_id in {
            "fin4_four_element_witness",
            "fin4_no_idempotent_normalization",
        }:
            continue
        source, target, engine, found = search(module, problem, fast)
        assert found is not None, case_id
        table, witness = found
        assert engine.replay(table, witness), case_id
        official_verify(problem, engine.emit_certificate(table))
        models[case_id] = (source, target, engine, table, witness)
        records.append({
            "id": case_id,
            "official": "accepted",
            "states": engine.partial_states,
            "witness_cardinality": len(set(witness)),
            "certificate_bytes": len(
                engine.emit_certificate(table).encode("utf-8")
            ),
        })

    # A constructed commutative, nonassociative Fin-4 table has no
    # idempotent diagonal entry. It exercises replay/certification without
    # introducing a production model lookup.
    constructed = (
        1, 1, 2, 3,
        1, 2, 3, 0,
        2, 3, 3, 1,
        3, 0, 1, 0,
    )
    no_idem = by_id["fin4_no_idempotent_normalization"]
    source = module.parse_equation(no_idem["equation1"])
    target = module.parse_equation(no_idem["equation2"])
    witness = next(
        assignment
        for assignment in module.product(range(4), repeat=len(target[2]))
        if module.evaluate_compiled(
            module.compile_equation(target), assignment, constructed, 4
        )[0]
        != module.evaluate_compiled(
            module.compile_equation(target), assignment, constructed, 4
        )[1]
    )
    assert is_commutative(constructed, 4)
    assert not is_associative(constructed, 4)
    assert all(constructed[4 * value + value] != value for value in range(4))
    assert module.replay_countermodel(
        source,
        target,
        constructed,
        4,
        witness,
        module.serialize_flat_table(constructed, 4),
    )
    official_verify(no_idem, module.emit_fin_certificate(constructed, 4))
    records.append({
        "id": no_idem["id"],
        "official": "accepted",
        "witness_cardinality": len(set(witness)),
        "certificate_bytes": len(
            module.emit_fin_certificate(constructed, 4).encode("utf-8")
        ),
    })

    four = by_id["fin4_four_element_witness"]
    source = module.parse_equation(four["equation1"])
    target = module.parse_equation(four["equation2"])
    witness4 = (0, 1, 2, 3)
    assert module.replay_countermodel(
        source,
        target,
        constructed,
        4,
        witness4,
        module.serialize_flat_table(constructed, 4),
    )
    official_verify(four, module.emit_fin_certificate(constructed, 4))
    records.append({
        "id": four["id"],
        "official": "accepted",
        "witness_cardinality": 4,
        "certificate_bytes": len(
            module.emit_fin_certificate(constructed, 4).encode("utf-8")
        ),
    })

    genuine = by_id["fin4_genuine_order_four"]
    source = module.parse_equation(genuine["equation1"])
    target = module.parse_equation(genuine["equation2"])
    for order in (2, 3):
        complete = module.FiniteModelEngine(
            order,
            source,
            target,
            time.monotonic() + 4.0,
            0,
            64,
        )
        assert complete.search_complete_enumeration(
            canonical_only=(order == 3)
        ) is None
        assert complete.complete

    nested = models["fin4_nested_support"][2]
    assert nested.support_disjoint_contradictions > 0
    assert nested.term_support_evaluations > 0
    assert nested.support_cache_hits > 0
    assert nested.forced_assignments > 0
    assert models["fin4_target_support_disjoint"][2].target_support_disjoint_guaranteed > 0
    assert models["fin4_source_nogood_reuse"][2].nogoods_reused > 0
    assert models["fin4_scoped_target_nogood_reuse"][2].nogoods_reused > 0

    base = by_id["fin4_genuine_order_four"]
    _, _, candidate_engine, candidate_found = search(module, base, fast)
    frozen_config = {
        "domain_size": 4,
        "seconds": 1.0,
        "maximum_states": 100000,
        "maximum_models": 16,
    }
    _, _, frozen_engine, frozen_found = search(
        frozen, base, frozen_config, options=None
    )
    assert candidate_found is not None and frozen_found is not None
    assert candidate_engine.partial_states < frozen_engine.partial_states

    _, _, source_only, source_found = search(module, base, fast)
    source_only = module.FiniteModelEngine(
        4,
        module.parse_equation(base["equation1"]),
        module.parse_equation(base["equation2"]),
        time.monotonic() + 1.0,
        100000,
        16,
        options=module.FIN4_ENGINE_OPTIONS,
    )
    source_found = source_only.search_partial_source_models()
    assert source_found is not None
    assert candidate_engine.partial_states < source_only.partial_states

    on_source, on_target, symmetry_on, found_on = search(module, base, fast)
    off_options = dict(fast["options"])
    off_options["symmetry_enabled"] = False
    _, _, symmetry_off, found_off = search(
        module, base, fast, off_options
    )
    assert found_on is not None and found_off is not None
    assert symmetry_on.replay(*found_on) and symmetry_off.replay(*found_off)

    table, witness = candidate_found
    corrupted = list(table)
    corrupted[0] = (corrupted[0] + 1) % 4
    assert not module.replay_countermodel(
        on_source,
        on_target,
        corrupted,
        4,
        witness,
        module.serialize_flat_table(table, 4),
    )
    assert not module.replay_countermodel(
        on_source,
        on_target,
        table,
        4,
        witness,
        module.serialize_flat_table(table, 4) + " ",
    )
    candidate_engine.deadline = time.monotonic() - 1.0
    assert candidate_engine.replay(table, witness)

    pathological = by_id["fin4_pathological_abstention"]
    try:
        search(module, pathological, probe)
    except ValueError:
        pass
    else:
        raise AssertionError("pathological variable cap did not abstain")

    true_control = by_id["fin4_true_control"]
    _, _, true_engine, true_found = search(module, true_control, probe)
    assert true_found is None

    compatibility = by_id["fin2_fin3_compatibility"]
    for order in (2, 3):
        source = module.parse_equation(compatibility["equation1"])
        target = module.parse_equation(compatibility["equation2"])
        engine = module.FiniteModelEngine(
            order,
            source,
            target,
            time.monotonic() + 1.0,
            50000,
            16,
        )
        found = (
            engine.search_complete_enumeration(canonical_only=False)
            if order == 2 else engine.search_target_guided()
        )
        assert found is not None and engine.replay(*found)
        official_verify(
            {
                **compatibility,
                "id": compatibility["id"] + f"_fin{order}",
            },
            engine.emit_certificate(found[0]),
        )

    metamorphic = []
    for problem in metamorphic_problems(module, base):
        _, _, engine, found = search(module, problem, fast)
        assert found is not None and engine.replay(*found), problem["id"]
        official_verify(problem, engine.emit_certificate(found[0]))
        metamorphic.append(problem["id"])
    permutation = (2, 0, 3, 1)
    relabelled = module.relabel_table(table, 4, permutation)
    relabelled_witness = tuple(permutation[value] for value in witness)
    assert module.replay_countermodel(
        on_source,
        on_target,
        relabelled,
        4,
        relabelled_witness,
        module.serialize_flat_table(relabelled, 4),
    )

    payload = {
        "cases": len(cases),
        "positive_official_acceptances": len(records),
        "true_false_judge_calls": 0,
        "pathological_abstentions": 1,
        "metamorphic_official_acceptances": metamorphic,
        "candidate_states": candidate_engine.partial_states,
        "frozen_states": frozen_engine.partial_states,
        "source_only_states": source_only.partial_states,
        "records": records,
    }
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8"
    )
    print(
        f"Fin-4 regression: {len(records)} positive certificates accepted, "
        "four metamorphic certificates accepted, one TRUE control emitted "
        "no FALSE call, one pathological input abstained"
    )


if __name__ == "__main__":
    main()
