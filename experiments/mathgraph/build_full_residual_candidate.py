#!/usr/bin/env python3
import argparse
from pathlib import Path

from build_streaming_collapse_candidate import build as build_streaming


HELPERS = r'''

def prepare_embedded_paramodulation_control():
    engine, external_replay = _load_stair_specialist()
    aliases = {
        "Clause": "pm_Clause",
        "all_paths": "pm_all_paths",
        "alpha_key": "pm_alpha_key",
        "can_close": "pm_can_close",
        "clause_weight": "pm_clause_weight",
        "formula": "pm_formula",
        "infer_paramod": "pm_infer_paramod",
        "instantiate_goal": "pm_instantiate_goal",
        "parse_equation": "pm_parse_equation",
        "prove": "pm_prove",
        "quantified_line": "pm_quantified_line",
        "rewrite_sides": "pm_rewrite_sides",
        "term_identical": "pm_term_identical",
        "term_size": "pm_term_size",
        "term_str": "pm_p9p_term_str",
        "translate_proof": "pm_p9t_translate_proof",
        "vars_in_equation": "pm_vars_in_equation",
    }
    for name, source_name in aliases.items():
        engine[name] = engine[source_name]
    return engine, external_replay


def try_paramodulation_control_candidate(problem, source, target, timeout):
    if not streaming_singleton_shape(source, target):
        return False
    total_seconds = min(4.0, max(0.25, timeout / 30.0))
    try:
        engine, external_replay = prepare_embedded_paramodulation_control()
    except (KeyError, RuntimeError, TypeError, ValueError):
        return False
    modes = (
        ("F", min(2.0, total_seconds)),
        ("QL", min(2.0, total_seconds)),
    )
    for mode, seconds in modes:
        if seconds <= 0.05:
            continue
        settings = engine["argparse"].Namespace(
            max_clauses=8000,
            max_weight=36,
            max_term_size=30,
            max_processed=400,
            pair_budget=300,
            timeout=seconds,
            translate=True,
            unordered=False,
            neg_bias=0,
            old_rules_first=False,
            tautology_prune=False,
            forward_subsumption=False,
        )
        if mode == "F":
            options = dict(
                forward_demodulation=True,
                scheduler=False,
                local_demodulation=False,
                dual_retention=False,
            )
        else:
            options = dict(
                forward_demodulation=True,
                scheduler=True,
                local_demodulation=False,
                dual_retention=True,
                per_given_budget=4,
                global_budget=256,
                quotient_mode=True,
                operation_relative_representatives=True,
                lazy_representative_materialization=True,
            )
        try:
            result = ForwardDemodulationRun(
                engine, problem, settings, **options
            ).solve()
        except (
            KeyError, IndexError, MemoryError, RecursionError,
            RuntimeError, TypeError, ValueError,
        ):
            continue
        if not (
            result.get("status") == "proved"
            and result.get("plan_ok")
            and result.get("spec")
            and result.get("code")
        ):
            continue
        try:
            external_ok = bool(external_replay["replay_plan"](result["spec"]))
        except (KeyError, TypeError, ValueError):
            external_ok = False
        if not external_ok:
            continue
        code = result["code"]
        if len(code.encode("utf-8")) > EqualitySearch.MAX_CERTIFICATE_BYTES:
            continue
        print(
            "MATHGRAPH_METRICS " + json.dumps({
                "portfolio": "paramodulation-control-" + mode.lower(),
                "found": True,
                "generated": result.get("generated"),
                "processed": result.get("processed"),
                "forward_demodulations": result.get("forward_demodulations"),
                "proof_ancestry_nodes": result.get("proof_ancestry_nodes"),
                "proof_ancestry_demodulations": result.get(
                    "proof_ancestry_demodulations"
                ),
                "proof_ancestry_superpositions": result.get(
                    "proof_ancestry_superpositions"
                ),
                "certificate_bytes": len(code.encode("utf-8")),
            }, separators=(",", ":")),
            file=sys.stderr,
            flush=True,
        )
        if judge("true", code).get("status") == "accepted":
            return True
    return False
'''


ROUTE = r'''
    # Replay-verified bounded given-clause control.  This is the complementary
    # route for nonlinear collapse implications that do not collapse the whole
    # carrier quickly enough for the streaming singleton constructor.
    if try_paramodulation_control_candidate(
        problem, source, target, timeout
    ):
        return

'''


def extract_controller(text):
    start = text.index("class ForwardDemodulationRun:")
    end = text.index("\ndef run(args):", start)
    return text[start:end].rstrip() + "\n\n"


def build(baseline, runner, output):
    stage = str(Path(output).with_suffix(".streaming.py"))
    build_streaming(baseline, stage)
    text = Path(stage).read_text()
    controller = extract_controller(Path(runner).read_text())
    if "import hashlib\n" not in text:
        marker = "import json\n"
        if marker not in text:
            raise SystemExit("import marker not found")
        text = text.replace(marker, marker + "import hashlib\n", 1)
    helper_marker = "\ndef finish_bridge_ir_candidate(source, target, search, found, portfolio):"
    if helper_marker not in text:
        raise SystemExit("helper marker not found")
    text = text.replace(
        helper_marker,
        "\n" + controller + HELPERS + helper_marker,
        1,
    )
    route_marker = "    stair_seconds = min(2.0, max(0.1, timeout / 50.0))\n"
    if route_marker not in text:
        raise SystemExit("route marker not found")
    text = text.replace(route_marker, ROUTE + route_marker, 1)
    Path(output).write_text(text)
    Path(stage).unlink(missing_ok=True)
    print(f"candidate_bytes={Path(output).stat().st_size}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", default="submissions/mathgraph/solver.py")
    parser.add_argument("--runner", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    build(args.baseline, args.runner, args.output)


if __name__ == "__main__":
    main()
