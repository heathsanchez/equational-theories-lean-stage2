#!/usr/bin/env python3
"""Inject a problem-blind verifier-derived collapse-schema portal.

This is an experimental representation-development layer.  It tries a fixed
small grammar of algebraic collapse laws, but promotes a law only after the
existing proof engine derives it from the source and its proof DAG replays.
No benchmark IDs, equation IDs, or target-specific bridge facts are used.
"""

import argparse
from pathlib import Path

MARKER = "    try:\n        # World A: streaming frontier.\n"

PORTAL = r'''    # Generic regime-development portal.  The schema vocabulary is fixed and
    # problem-blind.  A schema is promoted only if the existing proof engine
    # derives it from the source and the resulting DAG replays independently.
    def prove_regime_schema(goal, seconds):
        limits = dict(base)
        limits["seconds"] = seconds
        engine = TargetGroundedRefutation(
            source, goal, time.monotonic() + seconds, limits
        )
        search = engine.search
        found = search.solve()
        if found is None:
            return None, {"found": False, "replay": False}
        inlined = engine.inline_recipe(found)
        if (inlined.lhs, inlined.rhs) == (goal[1], goal[0]):
            inlined = Recipe(
                inlined.rhs, inlined.lhs, "symmetry", (inlined,)
            )
        if (inlined.lhs, inlined.rhs) != goal[:2]:
            return None, {"found": True, "replay": False, "endpoint": False}
        nodes, root = search.compile(inlined)
        replay_ok = replay_dag(
            source, nodes, root,
            maximum_term_size=300, maximum_nodes=60000,
        )
        if not replay_ok:
            return None, {
                "found": True, "replay": False,
                "proof_nodes": len(nodes),
            }

        # Target grounding may have introduced private reverse constants.
        # Materialize them back to ordinary source-language terms before the
        # proved law is inserted into the original-target proof world.
        def expand_term(term):
            if term[0] == "var" and term[1] in engine.reverse_constants:
                return expand_term(engine.reverse_constants[term[1]])
            if term[0] == "op":
                return ("op", expand_term(term[1]), expand_term(term[2]))
            return term

        def expand_recipe(recipe, cache=None):
            cache = {} if cache is None else cache
            key = id(recipe)
            if key in cache:
                return cache[key]
            parents = tuple(expand_recipe(q, cache) for q in recipe.parents)
            data = recipe.data
            if recipe.kind == "source":
                substitution, reverse = data
                data = (
                    tuple((k, expand_term(v)) for k, v in substitution),
                    reverse,
                )
            elif recipe.kind == "instantiate":
                data = tuple((k, expand_term(v)) for k, v in data)
            elif recipe.kind == "congruence":
                data = (data[0], expand_term(data[1]))
            out = Recipe(
                expand_term(recipe.lhs), expand_term(recipe.rhs),
                recipe.kind, parents, data,
            )
            cache[key] = out
            return out

        return expand_recipe(inlined), {
            "found": True, "replay": True,
            "proof_nodes": len(nodes),
        }

    schema_specs = [
        ("carrier-collapse", "x = y"),
        ("idempotence", "x * x = x"),
        ("left-projection", "x * y = x"),
        ("right-projection", "x * y = y"),
    ]
    schema_trace = []
    certified_laws = []
    for schema_name, schema_text in schema_specs:
        schema_goal = parse_equation(schema_text)
        t_schema = time.monotonic()
        law, info = prove_regime_schema(schema_goal, 30.0)
        rec = {
            "schema": schema_name,
            "text": schema_text,
            "elapsed": round(time.monotonic() - t_schema, 3),
            **info,
        }
        schema_trace.append(rec)
        if law is not None:
            certified_laws.append((schema_name, law))

    restart_info = {
        "certified": len(certified_laws),
        "added": 0,
        "found": False,
        "replay_judge": False,
    }
    if certified_laws:
        warm_engine, warm, _, _ = setup(60.0)
        for _, law in certified_laws:
            if warm.add_clause(law):
                restart_info["added"] += 1
        warm_found = warm.solve()
        restart_info.update({
            "found": warm_found is not None,
            "rounds": warm.rounds,
            "superpositions": warm.superpositions,
            "clauses": len(warm.clauses),
        })
        if warm_found is not None:
            accepted = finish(warm_engine, warm, warm_found)
            restart_info["replay_judge"] = bool(accepted)
            open('/tmp/mathgraph_schema_trace.json', 'w').write(json.dumps({
                "schemas": schema_trace,
                "restart": restart_info,
            }, sort_keys=True))
            if accepted:
                return True

    open('/tmp/mathgraph_schema_trace.json', 'w').write(json.dumps({
        "schemas": schema_trace,
        "restart": restart_info,
    }, sort_keys=True))
    return False

'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("solver")
    args = parser.parse_args()
    path = Path(args.solver)
    source = path.read_text()
    if source.count(MARKER) != 1:
        raise SystemExit(f"expected one portal marker, found {source.count(MARKER)}")
    patched = source.replace(MARKER, PORTAL + MARKER, 1)
    compile(patched, str(path), "exec")
    path.write_text(patched)
    print(f"injected verifier-derived regime schema portal into {path}")


if __name__ == "__main__":
    main()
