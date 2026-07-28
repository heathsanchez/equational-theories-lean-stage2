#!/usr/bin/env python3
"""Diagnostic-only characterization of failed MathGraph TRUE-side traces.

This module never emits Lean, calls the judge, or changes solver routing.  It
loads the frozen production solver as a library and converts its verified
normalization and BridgeIR trace fragments into explicitly non-terminal
CANDIDATE obstruction records.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import math
import random
import statistics
import time
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions/mathgraph/solver.py"
SOLVER_SHA256 = (
    "68729dde1e27c544e5d3e12504ea5878d57ad0af70cf16c80bb238433976dcf8"
)
SCHEMA_VERSION = "mathgraph.residual-characterization.v1"
TAXONOMY_VERSION = "mathgraph.residual-obstruction-taxonomy.v1"

FEATURE_NAMES = (
    "source_size",
    "source_depth",
    "target_left_size",
    "target_right_size",
    "target_depth",
    "source_variables",
    "target_variables",
    "source_repetition_max",
    "target_repetition_max",
    "source_dag_nodes",
    "target_dag_nodes",
    "shared_subterms",
    "vocabulary_overlap",
    "replayed_consequences",
    "decreasing_rules",
    "nonorientable_equalities",
    "overlap_consequences",
    "composed_consequences",
    "critical_pairs",
    "unresolved_critical_pairs",
    "proof_components",
    "initial_matches",
    "closest_skeleton_distance",
    "closest_bound_fraction",
    "closest_unbound_variables",
    "closest_context_depth",
    "legal_bridge_matches",
    "latent_bridge_matches",
    "bridge_candidates",
    "bridge_states",
    "activation_rows",
    "activation_events",
    "productive_activations",
    "normalization_steps",
    "normal_form_distance",
    "normal_form_distance_reduction",
    "bridge_depth",
    "term_growth",
    "shared_outer_context_depth",
    "frontier_left_size",
    "frontier_right_size",
    "frontier_variable_overlap",
    "one_side_instance",
    "proof_frontier_distance",
    "candidate_object_size",
    "candidate_operation_arity",
    "candidate_relation_arity",
    "decomposition_indicator",
    "verified_equality_classes",
    "quotient_source_matches",
    "quotient_only_source_matches",
    "quotient_repeated_variable_matches",
    "quotient_cross_component_matches",
    "best_quotient_match_cost",
)

FEATURE_GROUPS = {
    "equation": tuple(range(0, 13)),
    "consequence": tuple(range(13, 21)),
    "bridge": tuple(range(21, 33)),
    "divergence": tuple(range(33, 43)),
    "proof_graph": (20, 43),
    "counterfactual": tuple(range(44, len(FEATURE_NAMES))),
    "quotient_match": tuple(range(48, len(FEATURE_NAMES))),
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_solver():
    if sha256(SOLVER) != SOLVER_SHA256:
        raise RuntimeError("production solver hash changed")
    spec = importlib.util.spec_from_file_location(
        "residual_characterization_frozen_solver", SOLVER
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def content_hash(module, source_text, target_text):
    source = module.parse_equation(source_text)
    target = module.parse_equation(target_text)
    canonical_source = (
        module.render_term(source[0]) + " = " + module.render_term(source[1])
    )
    canonical_target = (
        module.render_term(target[0]) + " = " + module.render_term(target[1])
    )
    digest = hashlib.sha256(
        (canonical_source + "\0" + canonical_target).encode()
    ).hexdigest()
    return canonical_source, canonical_target, digest


def term_json(module, term):
    return module.render_term(term) if term is not None else None


def repetition_signature(module, equation):
    counts = Counter()
    for side in equation[:2]:
        for term in module.walk_subterms(side):
            if term[0] == "var":
                counts[term[1]] += 1
    return sorted(counts.values(), reverse=True)


def paths(module, term):
    output = []

    def visit(node, path):
        output.append(path)
        if node[0] == "op":
            visit(node[1], path + ("L",))
            visit(node[2], path + ("R",))

    visit(term, ())
    return output


def wildcard_distance(module, pattern, concrete, variables):
    if pattern[0] == "var" and pattern[1] in variables:
        return 0
    if pattern[0] != concrete[0]:
        return module.term_size(pattern) + module.term_size(concrete)
    if pattern[0] == "var":
        return int(pattern != concrete)
    return (
        wildcard_distance(module, pattern[1], concrete[1], variables)
        + wildcard_distance(module, pattern[2], concrete[2], variables)
    )


def common_context(module, left, right):
    path = []
    current_left, current_right = left, right
    while (
        current_left != current_right
        and current_left[0] == "op"
        and current_right[0] == "op"
    ):
        left_same = current_left[1] == current_right[1]
        right_same = current_left[2] == current_right[2]
        if left_same and not right_same:
            path.append("R")
            current_left, current_right = current_left[2], current_right[2]
        elif right_same and not left_same:
            path.append("L")
            current_left, current_right = current_left[1], current_right[1]
        else:
            break
    return tuple(path), current_left, current_right


def alpha_pair(module, left, right):
    names = {}
    return (
        module.render_term(module.alpha_canonical_term(left, names))
        + " = "
        + module.render_term(module.alpha_canonical_term(right, names))
    )


def anti_unify(module, left, right, maximum_variables=6):
    """Least-general tree anti-unifier with explicit back-substitutions."""
    variables = []
    memo = {}
    left_substitution = {}
    right_substitution = {}

    def visit(a, b):
        if a == b:
            return a
        if a[0] == b[0] == "op":
            return ("op", visit(a[1], b[1]), visit(a[2], b[2]))
        key = (a, b)
        if key not in memo:
            if len(variables) >= maximum_variables:
                raise ValueError("anti-unification variable cap")
            name = f"g{len(variables)}"
            memo[key] = ("var", name)
            variables.append(name)
            left_substitution[name] = a
            right_substitution[name] = b
        return memo[key]

    generalized = visit(left, right)
    if generalized[0] == "var":
        return None
    return {
        "generalization": term_json(module, generalized),
        "variables": variables,
        "left_substitution": {
            key: term_json(module, value)
            for key, value in sorted(left_substitution.items())
        },
        "right_substitution": {
            key: term_json(module, value)
            for key, value in sorted(right_substitution.items())
        },
    }


class CapturingBridgeIR:
    """Thin diagnostic wrapper that captures retained verified bridge states."""

    def __init__(self, module, source, target, deadline, configuration):
        base = module.BridgeIR

        class Capture(base):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                self.diagnostic_states = []

            def candidate_states(self, state, opposite_terms):
                result = super().candidate_states(state, opposite_terms)
                self.diagnostic_states.extend(result)
                return result

        self.search = Capture(source, target, deadline, configuration)

    def solve(self):
        return self.search.solve()


def equality_components(nodes):
    adjacency = defaultdict(set)
    for node in nodes:
        adjacency[node.lhs].add(node.rhs)
        adjacency[node.rhs].add(node.lhs)
    components = {}
    component_count = 0
    for term in adjacency:
        if term in components:
            continue
        stack = [term]
        components[term] = component_count
        while stack:
            current = stack.pop()
            for neighbor in adjacency[current]:
                if neighbor not in components:
                    components[neighbor] = component_count
                    stack.append(neighbor)
        component_count += 1
    return components, component_count


def quotient_match_bundle(module, source, target, normalizer_search):
    """Match source-law sides modulo independently replayed equality classes.

    This is diagnostic only.  It records when exact first-order matching fails
    but matching succeeds after replacing subterms by proven-equal members of
    the same class.  It does not add the resulting source instance.
    """
    parent = {}
    members = defaultdict(set)
    adjacency = defaultdict(list)

    def find(term):
        parent.setdefault(term, term)
        if parent[term] != term:
            parent[term] = find(parent[term])
        return parent[term]

    def union(left, right, node_id):
        a, b = find(left), find(right)
        adjacency[left].append((right, node_id))
        adjacency[right].append((left, node_id))
        if a != b:
            if module.render_term(a) > module.render_term(b):
                a, b = b, a
            parent[b] = a

    replay_cap = min(256, len(normalizer_search.nodes))
    prefix_valid = (
        replay_cap > 0
        and module.replay_dag(
            source,
            normalizer_search.nodes,
            0,
            maximum_term_size=
                normalizer_search.configuration["maximum_term_size"],
        )
    )
    replayed = replay_cap if prefix_valid else 0
    if prefix_valid:
        for node_id in range(replay_cap):
            node = normalizer_search.nodes[node_id]
            union(node.lhs, node.rhs, node_id)
    for side in target[:2]:
        for term in module.walk_subterms(side):
            find(term)
    for term in list(parent):
        members[find(term)].add(term)

    def class_id(term):
        return find(term)

    def ematch(pattern, concrete, mapping):
        variables = set(source[2])
        if pattern[0] == "var":
            key = pattern[1]
            value = class_id(concrete)
            previous = mapping.get(key)
            if previous is None:
                mapping[key] = value
                return [mapping]
            return [mapping] if previous == value else []
        alternatives = members.get(class_id(concrete), {concrete})
        output = []
        for candidate in alternatives:
            if candidate[0] != "op":
                continue
            left_maps = ematch(pattern[1], candidate[1], dict(mapping))
            for left_map in left_maps:
                output.extend(ematch(pattern[2], candidate[2], left_map))
        return output

    records = []
    target_components = {
        "left": {class_id(term) for term in module.walk_subterms(target[0])},
        "right": {class_id(term) for term in module.walk_subterms(target[1])},
    }
    for orientation, pattern, replacement in (
        ("forward", source[0], source[1]),
        ("reverse", source[1], source[0]),
    ):
        for target_side, root in (("left", target[0]), ("right", target[1])):
            for path in paths(module, root):
                concrete = module.get_subterm(root, path)
                exact_mapping = {}
                exact = module.match_term(pattern, concrete, exact_mapping)
                for mapping in ematch(pattern, concrete, {}):
                    if set(mapping) != set(source[2]):
                        continue
                    representatives = {
                        variable: min(
                            members.get(eclass, {eclass}),
                            key=lambda term: (
                                module.term_size(term),
                                module.render_term(term),
                            ),
                        )
                        for variable, eclass in mapping.items()
                    }
                    repeated = any(
                        sum(
                            1 for term in module.walk_subterms(pattern)
                            if term == ("var", variable)
                        ) > 1
                        for variable in source[2]
                    )
                    touched = set(mapping.values())
                    cross = bool(
                        touched & target_components["left"]
                        and touched & target_components["right"]
                    )
                    instantiated_replacement = module.substitute(
                        replacement, representatives
                    )
                    records.append({
                        "orientation": orientation,
                        "target_side": target_side,
                        "target_path": list(path),
                        "concrete_subterm": term_json(module, concrete),
                        "exact_syntactic_match": bool(
                            exact and set(exact_mapping) == set(source[2])
                        ),
                        "eclass_substitution": {
                            variable: hashlib.sha256(
                                module.render_term(eclass).encode()
                            ).hexdigest()[:12]
                            for variable, eclass in sorted(mapping.items())
                        },
                        "representatives": {
                            variable: term_json(module, term)
                            for variable, term in sorted(representatives.items())
                        },
                        "instantiated_replacement":
                            term_json(module, instantiated_replacement),
                        "repeated_variable_match": repeated,
                        "cross_target_components": cross,
                        "representative_replacement_cost": sum(
                            int(representatives[variable] != concrete)
                            for variable in representatives
                        ),
                    })
    unique = {}
    for record in records:
        key = json.dumps(record, sort_keys=True)
        unique[key] = record
    ordered = sorted(
        unique.values(),
        key=lambda item: (
            item["exact_syntactic_match"],
            -int(item["cross_target_components"]),
            item["representative_replacement_cost"],
            item["orientation"],
            item["target_side"],
            item["target_path"],
        ),
    )
    quotient_only = [
        item for item in ordered if not item["exact_syntactic_match"]
    ]
    return {
        "status": "DIAGNOSTIC_ONLY",
        "replayed_equalities": replayed,
        "verified_equality_classes": len(set(find(term) for term in parent)),
        "source_matches": len(ordered),
        "quotient_only_source_matches": len(quotient_only),
        "repeated_variable_matches": sum(
            item["repeated_variable_match"] for item in quotient_only
        ),
        "cross_component_matches": sum(
            item["cross_target_components"] for item in quotient_only
        ),
        "best_match": quotient_only[0] if quotient_only else None,
        "matches": quotient_only[:16],
        "proof_claim": False,
    }


def closest_component_gap(module, components, target):
    terms = list(components)
    if not terms:
        return None
    best = None
    for side_name, side in (("left", target[0]), ("right", target[1])):
        for term in terms:
            distance = module.structural_distance(side, term)
            item = (distance, module.term_size(term), module.render_term(term))
            if best is None or item < best[0]:
                best = (item, side_name, side, term, components[term])
    if best is None:
        return None
    return {
        "target_side": best[1],
        "target_term": term_json(module, best[2]),
        "frontier_term": term_json(module, best[3]),
        "component": best[4],
        "structural_distance": best[0][0],
    }


def normalizer_bundle(module, source, target, seconds=0.75):
    configuration = dict(module.NORMALIZATION_PORTFOLIO[1])
    started = time.monotonic()
    search = module.EquationalNormalizer(
        source, target, started + min(seconds, configuration["seconds"]),
        configuration,
    )
    search.generate_consequences()
    search.orient()
    search.select_rulebook()
    left_nf, left_trace, left_exhausted = search.normalize(target[0])
    right_nf, right_trace, right_exhausted = search.normalize(target[1])
    if not search.replay_trace(target[0], left_trace, left_nf):
        raise RuntimeError("left normalization replay failed")
    if not search.replay_trace(target[1], right_trace, right_nf):
        raise RuntimeError("right normalization replay failed")
    components, component_count = equality_components(search.nodes)
    return search, {
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "source_instances": search.source_instances_generated,
        "candidate_equalities": len(search.nodes),
        "replayed_consequences": search.replayed_candidates,
        "replay_failures": search.replay_failures,
        "decreasing_rules": search.decreasing_rules,
        "selected_rules": len(search.selected_rules),
        "nonorientable_equalities": search.nonorientable_equalities,
        "overlap_consequences": search.overlap_candidates,
        "endpoint_compositions": search.composed_consequences,
        "critical_pairs": search.local_critical_pairs,
        "unresolved_critical_pairs": search.unresolved_critical_pairs,
        "initial_matches": (
            len(search.rewrite_candidates(target[0]))
            + len(search.rewrite_candidates(target[1]))
        ),
        "left_normal_form": term_json(module, left_nf),
        "right_normal_form": term_json(module, right_nf),
        "left_steps": len(left_trace),
        "right_steps": len(right_trace),
        "left_exhausted": left_exhausted,
        "right_exhausted": right_exhausted,
        "normal_form_distance": module.structural_distance(left_nf, right_nf),
        "proof_components": component_count,
        "proof_frontier": closest_component_gap(module, components, target),
        "_left_nf": left_nf,
        "_right_nf": right_nf,
        "_left_trace": left_trace,
        "_right_trace": right_trace,
    }


def closest_bridge(module, search, target):
    best = None
    legal_matches = 0
    latent_matches = 0
    target_terms = []
    for side_name, side in (("left", target[0]), ("right", target[1])):
        for path in paths(module, side):
            target_terms.append((side_name, side, path, module.get_subterm(side, path)))
    for equality_index, equality in enumerate(search.bridge_equalities):
        variables = set(equality["variables"])
        replacement_variables = module.term_variables(equality["replacement"])
        for side_name, root, path, selected in target_terms:
            mapping = {}
            exact = module.match_selected_variables(
                equality["pattern"], selected, variables, mapping
            )
            unbound = sorted(replacement_variables - set(mapping))
            if exact and not unbound:
                legal_matches += 1
            if exact and unbound:
                latent_matches += 1
            distance = wildcard_distance(
                module, equality["pattern"], selected, variables
            )
            bound_fraction = (
                len(mapping) / len(variables) if variables else float(exact)
            )
            score = (
                0 if exact else 1,
                len(unbound),
                distance,
                -bound_fraction,
                len(path),
                max(
                    0,
                    module.term_size(equality["replacement"])
                    - module.term_size(selected),
                ),
                equality["proof_cost"],
                equality_index,
            )
            if best is None or score < best[0]:
                predicted = 0
                normalization_executed = False
                if exact and not unbound:
                    try:
                        replacement = module.instantiate_rule_rhs(
                            equality["replacement"], variables, mapping
                        )
                        bridged = module.replace_subterm(root, path, replacement)
                        predicted = len(search.normalizer.rewrite_candidates(bridged))
                        normalization_executed = True
                    except (KeyError, TypeError, ValueError):
                        pass
                best = (
                    score,
                    {
                        "equality_index": equality_index,
                        "equality_provenance": equality["origin"],
                        "orientation": (
                            "reverse" if equality["proof_reverse"] else "forward"
                        ),
                        "match_side": side_name,
                        "target_path": list(path),
                        "pattern": term_json(module, equality["pattern"]),
                        "replacement": term_json(module, equality["replacement"]),
                        "selected_subterm": term_json(module, selected),
                        "matched_variables": {
                            key: term_json(module, value)
                            for key, value in sorted(mapping.items())
                        },
                        "unbound_variables": unbound,
                        "bound_variable_fraction": round(bound_fraction, 6),
                        "skeleton_distance": distance,
                        "context_depth": len(path),
                        "term_growth": max(
                            0,
                            module.term_size(equality["replacement"])
                            - module.term_size(selected),
                        ),
                        "rejection_reason": (
                            None if exact and not unbound
                            else "UNBOUND_REPLACEMENT_VARIABLE"
                            if exact else "SCHEMATIC_MATCH_FAILURE"
                        ),
                        "hypothetical_missing_binding": (
                            unbound[0] if unbound else None
                        ),
                        "predicted_normalizer_matches": predicted,
                        "normalization_executed": normalization_executed,
                        "proof_cost": equality["proof_cost"],
                        "replayed": True,
                    },
                )
    return (best[1] if best else None), legal_matches, latent_matches


def bridge_bundle(module, source, target, seconds=0.75):
    configuration = dict(module.BRIDGE_IR_PORTFOLIO[1])
    started = time.monotonic()
    wrapper = CapturingBridgeIR(
        module, source, target,
        started + min(seconds, configuration["seconds"]),
        configuration,
    )
    found = wrapper.solve()
    search = wrapper.search
    closest, legal, latent = closest_bridge(module, search, target)
    states = sorted(
        search.diagnostic_states,
        key=lambda state: (
            -state["activations"],
            state["proof_cost"],
            state["depth"],
            module.render_term(state["current"]),
        ),
    )
    best_state = states[0] if states else None
    introduced = None
    activated_rules = []
    if best_state and best_state["bridge_steps"]:
        first = best_state["bridge_steps"][0]
        introduced = {
            "direction": (
                "reverse"
                if first["equality"]["proof_reverse"] else "forward"
            ),
            "context_path": list(first["path"]),
            "context_depth": len(first["path"]),
            "bridge_depth": best_state["depth"],
            "introduced_term": term_json(module, first["bridged"]),
            "introduced_term_shape": alpha_pair(
                module, first["before"], first["bridged"]
            ),
            "term_growth": (
                module.term_size(first["bridged"])
                - module.term_size(first["before"])
            ),
            "equality_source_type": first["equality"]["origin"],
            "syntactic_activation": first["activated"],
            "post_bridge_matches": first["post_bridge_matches"],
            "normalization_suffix": [
                {
                    "path": list(step["path"]),
                    "rule_provenance": step["rule"].provenance,
                    "before": term_json(module, step["before"]),
                    "after": term_json(module, step["after"]),
                }
                for step in first["normalization_trace"]
            ],
            "terminal_term": term_json(module, best_state["current"]),
        }
        activated_rules = sorted({
            item["rule_provenance"]
            for item in introduced["normalization_suffix"]
        })
    return search, {
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "bridge_equalities": len(search.bridge_equalities),
        "replayed_bridge_equalities": search.replayed_bridge_equalities,
        "replay_failures": search.bridge_replay_failures,
        "legal_bridge_matches": legal,
        "latent_bridge_matches": latent,
        "bridge_states": len(states),
        "activation_events": search.no_match_activations,
        "activation_row": int(any(state["activations"] for state in states)),
        "productive_activations": sum(
            bool(step["normalization_trace"])
            for state in states for step in state["bridge_steps"]
            if step["activated"]
        ),
        "normalization_steps": sum(
            len(step["normalization_trace"])
            for state in states for step in state["bridge_steps"]
        ),
        "maximum_bridge_depth": search.maximum_bridge_depth,
        "maximum_term_growth": search.maximum_term_growth,
        "shared_normal_form_hit": int(found is not None),
        "closest_replayed_bridge": closest,
        "best_activation": introduced,
        "activated_rule_families": activated_rules,
        "best_terminal_term": (
            term_json(module, best_state["current"]) if best_state else None
        ),
        "_states": states,
    }


def divergence_bundle(module, normalizer, bridge):
    left = normalizer["_left_nf"]
    right = normalizer["_right_nf"]
    state_terms = [
        state["current"] for state in bridge["_states"]
        if state["activations"]
    ]
    if state_terms:
        candidates = []
        for term in state_terms:
            candidates.append((
                module.structural_distance(term, right), term, right
            ))
            candidates.append((
                module.structural_distance(left, term), left, term
            ))
        _, left, right = min(
            candidates,
            key=lambda item: (
                item[0], module.term_size(item[1]) + module.term_size(item[2]),
                module.render_term(item[1]), module.render_term(item[2]),
            ),
        )
    context_path, left_frontier, right_frontier = common_context(
        module, left, right
    )
    generalization = anti_unify(module, left_frontier, right_frontier)
    left_vars = module.term_variables(left_frontier)
    right_vars = module.term_variables(right_frontier)
    one_side_instance = int(
        module.is_subterm(left_frontier, right_frontier)
        or module.is_subterm(right_frontier, left_frontier)
    )
    candidate_operation_arity = 0
    if generalization:
        candidate_operation_arity = min(
            4, len(generalization["variables"])
        )
    return {
        "shared_context_path": list(context_path),
        "shared_outer_context_depth": len(context_path),
        "left_frontier": term_json(module, left_frontier),
        "right_frontier": term_json(module, right_frontier),
        "left_frontier_size": module.term_size(left_frontier),
        "right_frontier_size": module.term_size(right_frontier),
        "size_difference": abs(
            module.term_size(left_frontier) - module.term_size(right_frontier)
        ),
        "depth_difference": abs(
            module.term_depth(left_frontier)
            - module.term_depth(right_frontier)
        ),
        "variable_overlap": len(left_vars & right_vars),
        "repeated_variable_correspondence": (
            sorted(Counter(module.render_term(term) for term in
                           module.walk_subterms(left_frontier)).values())
            == sorted(Counter(module.render_term(term) for term in
                              module.walk_subterms(right_frontier)).values())
        ),
        "one_side_instance_or_subterm": bool(one_side_instance),
        "candidate_equality_anti_unifier": generalization,
        "candidate_operation_signature": (
            {
                "status": "CANDIDATE",
                "arity": candidate_operation_arity,
                "shape": generalization["generalization"],
            }
            if generalization and candidate_operation_arity >= 2 else None
        ),
        "candidate_relation_signature": {
            "status": "CANDIDATE",
            "arity": len(left_vars | right_vars),
            "observations": [
                term_json(module, left_frontier),
                term_json(module, right_frontier),
            ],
        },
        "candidate_case_split": (
            {
                "status": "CANDIDATE",
                "conditions": ["repetition-compatible", "repetition-distinct"],
            }
            if left_vars != right_vars else None
        ),
        "_left": left_frontier,
        "_right": right_frontier,
    }


def counterfactual_objects(module, digest, normalizer, bridge, divergence):
    objects = []
    left = divergence["_left"]
    right = divergence["_right"]
    target_specific = (
        normalizer["normal_form_distance"]
        == module.structural_distance(left, right)
    )

    def add(kind, syntax, latent, effect, reuse, risks, size):
        canonical = json.dumps(
            {"kind": kind, "syntax": syntax}, sort_keys=True
        )
        object_id = hashlib.sha256(
            (digest + "\0" + canonical).encode()
        ).hexdigest()[:24]
        objects.append({
            "status": "CANDIDATE",
            "kind": kind,
            "canonical_object_id": object_id,
            "source_row_hash": digest,
            "verified_frontier": {
                "left": divergence["left_frontier"],
                "right": divergence["right_frontier"],
            },
            "syntax_or_signature": syntax,
            "variables": sorted(
                module.term_variables(left) | module.term_variables(right)
            ),
            "latent_placeholders": latent,
            "supporting_trace_ids": [
                "normalization-frontier",
                "closest-replayed-bridge",
            ],
            "predicted_downstream_effect": effect,
            "minimality_score": round(
                size + 3 * len(latent)
                + (4 if target_specific else 0)
                - min(4, reuse),
                6,
            ),
            "reuse_signature": reuse,
            "risk_flags": risks + (
                ["TARGET_SPECIFIC"] if target_specific else []
            ),
            "proof_claim": False,
        })

    anti = divergence["candidate_equality_anti_unifier"]
    if anti:
        add(
            "SCHEMA",
            {
                "generalization": anti["generalization"],
                "left_frontier": divergence["left_frontier"],
                "right_frontier": divergence["right_frontier"],
            },
            anti["variables"],
            "connect verified normalization frontiers",
            1,
            ["ANTI_UNIFIED_ONLY"],
            (
                module.term_size(left) + module.term_size(right)
                + len(anti["variables"])
            ),
        )
    closest = bridge["closest_replayed_bridge"]
    if closest and closest["unbound_variables"]:
        add(
            "EQUALITY",
            {
                "pattern": closest["pattern"],
                "replacement": closest["replacement"],
                "missing_binding": closest["hypothetical_missing_binding"],
            },
            closest["unbound_variables"],
            "make closest replayed bridge concrete",
            1,
            ["UNBOUND_REPLACEMENT_VARIABLE"],
            (
                len(closest["pattern"]) + len(closest["replacement"])
            ) / 8,
        )
    operation = divergence["candidate_operation_signature"]
    if operation and operation["arity"] >= 2:
        add(
            "DERIVED_OPERATION",
            operation,
            [f"input_{index}" for index in range(operation["arity"])],
            "name repeated latent multi-input frontier shape",
            1,
            ["NO_SEMANTICS", "SINGLE_ROW_SUPPORT"],
            operation["arity"] * 4,
        )
    relation = divergence["candidate_relation_signature"]
    add(
        "INVARIANT",
        relation,
        [],
        "treat divergent frontiers as observationally related",
        1,
        ["RELATION_NOT_PROVED", "SINGLE_ROW_SUPPORT"],
        10 + relation["arity"],
    )
    case = divergence["candidate_case_split"]
    if case:
        add(
            "DECOMPOSITION",
            case,
            [],
            "separate repetition-compatible trace regimes",
            1,
            ["CASES_NOT_PROVED", "POSSIBLY_INSTANCE_SPECIFIC"],
            12,
        )
    if (
        bridge["closest_replayed_bridge"]
        and not bridge["activation_row"]
        and bridge["bridge_states"]
    ):
        add(
            "MULTISTEP_BRIDGE",
            {
                "maximum_depth": 3,
                "first_step": bridge["closest_replayed_bridge"]["pattern"],
            },
            ["step_2", "step_3"],
            "diagnostically reduce frontier distance after two-step failure",
            1,
            ["ALL_STEPS_HYPOTHETICAL"],
            16,
        )
    valid = [
        item for item in objects
        if not (
            item["kind"] == "SCHEMA"
            and item["syntax_or_signature"].get("generalization", "").startswith("g")
        )
    ]
    valid.sort(key=lambda item: (
        item["minimality_score"], item["kind"], item["canonical_object_id"]
    ))
    return valid[:16]


def classify(normalizer, bridge, divergence, objects, quotient=None):
    closest = bridge["closest_replayed_bridge"]
    legal = bridge["legal_bridge_matches"]
    latent = bridge["latent_bridge_matches"]
    relevant = (
        closest is not None and closest["skeleton_distance"] <= 2
    )
    activation = bool(bridge["activation_row"])
    local = (
        activation
        and divergence["shared_outer_context_depth"] >= 1
        and (
            divergence["left_frontier_size"]
            + divergence["right_frontier_size"]
        ) <= 12
    )
    proof_gap = normalizer["proof_frontier"]
    proof_near = (
        proof_gap is not None
        and proof_gap["structural_distance"] <= 2
        and normalizer["proof_components"] >= 2
    )
    if normalizer["candidate_equalities"] == 0:
        primary, stage, confidence = "O1", "F0", 0.95
    elif not relevant and legal == 0 and latent == 0:
        primary, stage, confidence = "O1", "F1", 0.88
    elif latent > 0 and legal == 0:
        primary, stage, confidence = "O3", "F2", 0.90
    elif legal == 0 and relevant:
        primary, stage, confidence = "O2", "F2", 0.82
    elif activation and local:
        primary, stage, confidence = "O4", "F5", 0.90
    elif proof_near:
        primary, stage, confidence = "O9", "F6", 0.78
    elif legal > 0 and not activation and bridge["bridge_states"] > 0:
        primary, stage, confidence = "O8", "F3", 0.68
    elif activation:
        operation = next(
            (item for item in objects if item["kind"] == "DERIVED_OPERATION"),
            None,
        )
        if operation and not local:
            primary, stage, confidence = "O5", "F7", 0.62
        else:
            primary, stage, confidence = "O10", "F8", 0.45
    else:
        primary, stage, confidence = "O10", "F8", 0.35
    tags = []
    if normalizer["initial_matches"] == 0:
        tags.append("NO_TARGET_MATCH")
    if latent:
        tags.extend(["UNBOUND_REPLACEMENT_VARIABLE", "LATENT_TERM_REQUIRED"])
    if activation:
        tags.append("PRODUCTIVE_ACTIVATION")
    if normalizer["normal_form_distance"]:
        tags.append("DISTINCT_NORMAL_FORMS")
    tags.append("LOCAL_DIVERGENCE" if local else "NONLOCAL_DIVERGENCE")
    if any(item["kind"] == "DERIVED_OPERATION" for item in objects):
        tags.append("REPEATED_OPERATOR_SHAPE")
    if any(item["kind"] == "INVARIANT" for item in objects):
        tags.append("RELATIONAL_CONNECTOR")
    if any(item["kind"] == "DECOMPOSITION" for item in objects):
        tags.append("CASE_SPLIT_PATTERN")
    if proof_near:
        tags.append("PROOF_COMPONENT_GAP")
    if quotient and quotient["quotient_only_source_matches"]:
        tags.append("QUOTIENT_SOURCE_MATCH")
    if quotient and quotient["repeated_variable_matches"]:
        tags.append("ECLASS_REPEATED_VARIABLE_MATCH")
    if quotient and quotient["cross_component_matches"]:
        tags.append("CROSS_COMPONENT_SOURCE_INSTANCE")
    if confidence < 0.6:
        tags.append("LOW_CONFIDENCE")
    ambiguity = [primary]
    if confidence < 0.75:
        for candidate in ("O5", "O6", "O7", "O8", "O9", "O10"):
            if candidate != primary:
                ambiguity.append(candidate)
            if len(ambiguity) == 3:
                break
        tags.append("MULTIPLE_PLAUSIBLE_CLASSES")
    return {
        "primary": primary,
        "earliest_failure_stage": stage,
        "confidence": confidence,
        "ambiguity_set": ambiguity,
        "secondary_tags": sorted(set(tags)),
    }


def numeric_features(
    module, source, target, normalizer, bridge, divergence, objects, quotient
):
    source_terms = set(module.walk_subterms(source[0])) | set(
        module.walk_subterms(source[1])
    )
    target_terms = set(module.walk_subterms(target[0])) | set(
        module.walk_subterms(target[1])
    )
    source_rep = repetition_signature(module, source)
    target_rep = repetition_signature(module, target)
    source_compiled = module.compile_equation(source)
    target_compiled = module.compile_equation(target)
    closest = bridge["closest_replayed_bridge"] or {}
    initial_distance = module.structural_distance(target[0], target[1])
    best_terminal = bridge.get("best_terminal_term")
    reduction = 0
    if best_terminal:
        # Rendered terminal terms are intentionally not reparsed as equations;
        # use the verified normal-form distance reduction recorded elsewhere.
        reduction = max(0, initial_distance - normalizer["normal_form_distance"])
    leading = objects[0] if objects else None
    values = (
        module.term_size(source[0]) + module.term_size(source[1]),
        max(module.term_depth(source[0]), module.term_depth(source[1])),
        module.term_size(target[0]),
        module.term_size(target[1]),
        max(module.term_depth(target[0]), module.term_depth(target[1])),
        len(source[2]),
        len(target[2]),
        max(source_rep, default=0),
        max(target_rep, default=0),
        len(source_compiled[0]),
        len(target_compiled[0]),
        len(source_terms & target_terms),
        len(module.term_variables(source[0]) | module.term_variables(source[1])
            & (module.term_variables(target[0]) | module.term_variables(target[1]))),
        normalizer["replayed_consequences"],
        normalizer["decreasing_rules"],
        normalizer["nonorientable_equalities"],
        normalizer["overlap_consequences"],
        normalizer["endpoint_compositions"],
        normalizer["critical_pairs"],
        normalizer["unresolved_critical_pairs"],
        normalizer["proof_components"],
        normalizer["initial_matches"],
        closest.get("skeleton_distance", 99),
        closest.get("bound_variable_fraction", 0),
        len(closest.get("unbound_variables", [])),
        closest.get("context_depth", 0),
        bridge["legal_bridge_matches"],
        bridge["latent_bridge_matches"],
        bridge["bridge_equalities"],
        bridge["bridge_states"],
        bridge["activation_row"],
        bridge["activation_events"],
        bridge["productive_activations"],
        bridge["normalization_steps"],
        normalizer["normal_form_distance"],
        reduction,
        bridge["maximum_bridge_depth"],
        bridge["maximum_term_growth"],
        divergence["shared_outer_context_depth"],
        divergence["left_frontier_size"],
        divergence["right_frontier_size"],
        divergence["variable_overlap"],
        int(divergence["one_side_instance_or_subterm"]),
        (
            normalizer["proof_frontier"]["structural_distance"]
            if normalizer["proof_frontier"] else 99
        ),
        leading["minimality_score"] if leading else 99,
        (
            divergence["candidate_operation_signature"]["arity"]
            if divergence["candidate_operation_signature"] else 0
        ),
        divergence["candidate_relation_signature"]["arity"],
        int(divergence["candidate_case_split"] is not None),
        quotient["verified_equality_classes"],
        quotient["source_matches"],
        quotient["quotient_only_source_matches"],
        quotient["repeated_variable_matches"],
        quotient["cross_component_matches"],
        (
            quotient["best_match"]["representative_replacement_cost"]
            if quotient["best_match"] else 99
        ),
    )
    if len(values) != len(FEATURE_NAMES):
        raise RuntimeError("feature schema mismatch")
    return {
        name: round(float(value), 6)
        for name, value in zip(FEATURE_NAMES, values)
    }


def characterize(module, row, configuration=None):
    configuration = configuration or {}
    source = module.parse_equation(row["equation1"])
    target = module.parse_equation(row["equation2"])
    canonical_source, canonical_target, digest = content_hash(
        module, row["equation1"], row["equation2"]
    )
    started = time.monotonic()
    normalizer_search, normalizer = normalizer_bundle(
        module, source, target,
        seconds=configuration.get("normalizer_seconds", 0.75),
    )
    _, bridge = bridge_bundle(
        module, source, target,
        seconds=configuration.get("bridge_seconds", 0.75),
    )
    quotient = quotient_match_bundle(
        module, source, target, normalizer_search
    )
    divergence = divergence_bundle(module, normalizer, bridge)
    objects = counterfactual_objects(
        module, digest, normalizer, bridge, divergence
    )
    classification = classify(
        normalizer, bridge, divergence, objects, quotient
    )
    features = numeric_features(
        module, source, target, normalizer, bridge, divergence, objects,
        quotient,
    )
    clean_normalizer = {
        key: value for key, value in normalizer.items()
        if not key.startswith("_")
    }
    clean_bridge = {
        key: value for key, value in bridge.items()
        if not key.startswith("_")
    }
    clean_divergence = {
        key: value for key, value in divergence.items()
        if not key.startswith("_")
    }
    strongest = (
        "productive-bridge-normalization"
        if bridge["productive_activations"]
        else "legal-bridge"
        if bridge["legal_bridge_matches"]
        else "replayed-normalization-consequences"
    )
    closest_rejected = bridge["closest_replayed_bridge"]
    record = {
        "schema_version": SCHEMA_VERSION,
        "identity": {
            "opaque_id": row["id"],
            "content_sha256": digest,
        },
        "provenance": {
            "source_group_sha256": hashlib.sha256(
                canonical_source.encode()
            ).hexdigest(),
            "dataset_role": row.get("dataset_role", "unspecified"),
            "origin": row.get("origin", "unspecified"),
            "trace_source": "frozen production solver diagnostics",
            "solver_sha256": SOLVER_SHA256,
            "terminal_status": None,
        },
        "equation_structure": {
            "canonical_source": canonical_source,
            "canonical_target": canonical_target,
            "source_variables": list(source[2]),
            "target_variables": list(target[2]),
            "source_repetition": repetition_signature(module, source),
            "target_repetition": repetition_signature(module, target),
        },
        "verified_consequences": clean_normalizer,
        "normalization_trace": {
            "left_terminal": normalizer["left_normal_form"],
            "right_terminal": normalizer["right_normal_form"],
            "left_steps": normalizer["left_steps"],
            "right_steps": normalizer["right_steps"],
            "distance": normalizer["normal_form_distance"],
        },
        "bridge_trace": clean_bridge,
        "quotient_match_trace": quotient,
        "earliest_failure": {
            "stage": classification["earliest_failure_stage"],
            "strongest_verified_trace": strongest,
            "closest_rejected_trace": closest_rejected,
            "exact_rejection_reason": (
                closest_rejected["rejection_reason"]
                if closest_rejected else "NO_TARGET_RELEVANT_SCHEMA"
            ),
            "later_stages_reached": (
                ["F5"] if bridge["activation_row"] else []
            ),
        },
        "closest_replayed_bridge": closest_rejected,
        "divergence_frontier": clean_divergence,
        "proof_graph_frontier": normalizer["proof_frontier"],
        "counterfactual_objects": objects,
        "primary_obstruction": classification["primary"],
        "secondary_tags": classification["secondary_tags"],
        "confidence": classification["confidence"],
        "ambiguity_set": classification["ambiguity_set"],
        "structural_features": features,
        "cluster_assignment": None,
        "limitations": [
            "Counterfactual objects are unproved CANDIDATE diagnostics.",
            "Bridge and normalizer bounds are frozen and incomplete.",
            "Absence of a trace is not proof of mathematical impossibility.",
        ],
        "diagnostic_seconds": round(time.monotonic() - started, 6),
    }
    if any(
        item.get("status") != "CANDIDATE"
        or item.get("proof_claim") is not False
        for item in record["counterfactual_objects"]
    ):
        raise RuntimeError("counterfactual trust boundary violated")
    return record


def robust_scale(records, feature_names=FEATURE_NAMES):
    columns = {
        name: [row["structural_features"][name] for row in records]
        for name in feature_names
    }
    medians = {
        name: statistics.median(values) for name, values in columns.items()
    }
    scales = {}
    for name, values in columns.items():
        deviations = [abs(value - medians[name]) for value in values]
        mad = statistics.median(deviations)
        scales[name] = mad if mad > 1e-9 else (
            statistics.pstdev(values) if len(values) > 1 else 1.0
        )
        if scales[name] <= 1e-9:
            scales[name] = 1.0
    matrix = [
        [
            (row["structural_features"][name] - medians[name]) / scales[name]
            for name in feature_names
        ]
        for row in records
    ]
    return matrix, medians, scales


def manhattan(left, right):
    return sum(abs(a - b) for a, b in zip(left, right)) / max(1, len(left))


def distance_matrix(matrix):
    return [
        [manhattan(left, right) for right in matrix]
        for left in matrix
    ]


def pam(distances, k, initial=None, maximum_iterations=100):
    n = len(distances)
    if not 1 <= k <= n:
        raise ValueError("invalid k")
    medoids = list(initial or [0])
    while len(medoids) < k:
        candidate = max(
            (index for index in range(n) if index not in medoids),
            key=lambda index: (
                min(distances[index][medoid] for medoid in medoids),
                -index,
            ),
        )
        medoids.append(candidate)
    medoids.sort()
    for _ in range(maximum_iterations):
        assignments = [
            min(
                range(k),
                key=lambda group: (distances[index][medoids[group]], group),
            )
            for index in range(n)
        ]
        changed = False
        for group in range(k):
            members = [
                index for index, assigned in enumerate(assignments)
                if assigned == group
            ]
            if not members:
                continue
            best = min(
                members,
                key=lambda candidate: (
                    sum(distances[candidate][other] for other in members),
                    candidate,
                ),
            )
            if best != medoids[group]:
                medoids[group] = best
                changed = True
        if not changed:
            break
    medoids.sort()
    assignments = [
        min(
            range(k),
            key=lambda group: (distances[index][medoids[group]], group),
        )
        for index in range(n)
    ]
    return medoids, assignments


def silhouette(distances, assignments):
    if len(set(assignments)) < 2:
        return 0.0
    values = []
    for index, own in enumerate(assignments):
        same = [
            other for other, group in enumerate(assignments)
            if group == own and other != index
        ]
        a = (
            sum(distances[index][other] for other in same) / len(same)
            if same else 0.0
        )
        other_means = []
        for group in sorted(set(assignments) - {own}):
            members = [
                other for other, assigned in enumerate(assignments)
                if assigned == group
            ]
            other_means.append(
                sum(distances[index][other] for other in members) / len(members)
            )
        b = min(other_means)
        values.append((b - a) / max(a, b, 1e-9))
    return sum(values) / len(values)


def adjusted_rand(left, right):
    from sklearn.metrics import adjusted_rand_score
    return float(adjusted_rand_score(left, right))


def variation_information(left, right):
    n = len(left)
    left_counts = Counter(left)
    right_counts = Counter(right)
    joint = Counter(zip(left, right))

    def entropy(counts):
        return -sum(
            (count / n) * math.log(count / n)
            for count in counts.values() if count
        )

    mutual = sum(
        (count / n) * math.log(
            (count * n) / (left_counts[a] * right_counts[b])
        )
        for (a, b), count in joint.items() if count
    )
    return entropy(left_counts) + entropy(right_counts) - 2 * mutual


def cluster_discovery(records, seed, bootstrap_replicates=1000):
    from sklearn.cluster import AgglomerativeClustering

    matrix, medians, scales = robust_scale(records)
    distances = distance_matrix(matrix)
    candidates = []
    for k in range(2, min(6, len(records)) + 1):
        medoids, assignments = pam(distances, k)
        sizes = Counter(assignments)
        candidates.append({
            "k": k,
            "medoids": medoids,
            "assignments": assignments,
            "silhouette": silhouette(distances, assignments),
            "minimum_cluster_size": min(sizes.values()),
        })
    eligible = [
        item for item in candidates if item["minimum_cluster_size"] >= 4
    ] or candidates
    selected = max(
        eligible,
        key=lambda item: (
            item["silhouette"],
            item["minimum_cluster_size"],
            -item["k"],
        ),
    )
    hierarchical_portfolio = []
    for k in range(2, min(8, len(records)) + 1):
        assignments = AgglomerativeClustering(
            n_clusters=k,
            metric="precomputed",
            linkage="average",
        ).fit_predict(distances).tolist()
        sizes = Counter(assignments)
        hierarchical_portfolio.append({
            "k": k,
            "assignments": assignments,
            "silhouette": silhouette(distances, assignments),
            "minimum_cluster_size": min(sizes.values()),
        })
    hierarchical_eligible = [
        item for item in hierarchical_portfolio
        if item["minimum_cluster_size"] >= 4
    ] or hierarchical_portfolio
    hierarchical_selected = max(
        hierarchical_eligible,
        key=lambda item: (
            item["silhouette"],
            item["minimum_cluster_size"],
            -item["k"],
        ),
    )
    rng = random.Random(seed)
    ari_values = []
    vi_values = []
    medoid_hits = Counter()
    for _ in range(bootstrap_replicates):
        sample = [rng.randrange(len(records)) for _ in records]
        sample_matrix = [matrix[index] for index in sample]
        sample_distances = distance_matrix(sample_matrix)
        sample_medoids, sample_assignments = pam(
            sample_distances, selected["k"]
        )
        sampled_original_medoids = [sample[index] for index in sample_medoids]
        for medoid in sampled_original_medoids:
            medoid_hits[medoid] += 1
        projected = [
            min(
                range(selected["k"]),
                key=lambda group: (
                    manhattan(vector, matrix[sampled_original_medoids[group]]),
                    group,
                ),
            )
            for vector in matrix
        ]
        ari_values.append(adjusted_rand(selected["assignments"], projected))
        vi_values.append(variation_information(
            selected["assignments"], projected
        ))
    global_distances = [
        distances[i][j]
        for i in range(len(records)) for j in range(i + 1, len(records))
    ]
    within = [
        distances[i][j]
        for i in range(len(records)) for j in range(i + 1, len(records))
        if selected["assignments"][i] == selected["assignments"][j]
    ]
    cluster_ids = [
        f"C{assignment + 1}" for assignment in selected["assignments"]
    ]
    for record, cluster_id in zip(records, cluster_ids):
        record["cluster_assignment"] = {
            "rule_based": record["primary_obstruction"],
            "k_medoids": cluster_id,
        }
    return {
        "feature_names": list(FEATURE_NAMES),
        "medians": medians,
        "scales": scales,
        "portfolio": [
            {
                key: value for key, value in item.items()
                if key != "assignments"
            }
            for item in candidates
        ],
        "hierarchical": {
            "linkage": "average",
            "selected_k": hierarchical_selected["k"],
            "silhouette": hierarchical_selected["silhouette"],
            "minimum_cluster_size":
                hierarchical_selected["minimum_cluster_size"],
            "assignments": {
                record["identity"]["content_sha256"]:
                    f"H{assignment + 1}"
                for record, assignment in zip(
                    records, hierarchical_selected["assignments"]
                )
            },
            "portfolio": [
                {
                    key: value for key, value in item.items()
                    if key != "assignments"
                }
                for item in hierarchical_portfolio
            ],
        },
        "selected_k": selected["k"],
        "medoid_record_hashes": [
            records[index]["identity"]["content_sha256"]
            for index in selected["medoids"]
        ],
        "assignments": {
            record["identity"]["content_sha256"]: cluster_id
            for record, cluster_id in zip(records, cluster_ids)
        },
        "silhouette": selected["silhouette"],
        "bootstrap_replicates": bootstrap_replicates,
        "bootstrap_mean_ari": statistics.mean(ari_values),
        "bootstrap_mean_variation_information": statistics.mean(vi_values),
        "medoid_stability": {
            records[index]["identity"]["content_sha256"]: (
                medoid_hits[index] / bootstrap_replicates
            )
            for index in selected["medoids"]
        },
        "global_pairwise_distance": statistics.mean(global_distances),
        "within_cluster_distance": statistics.mean(within) if within else 0,
        "within_distance_reduction": (
            1 - statistics.mean(within) / statistics.mean(global_distances)
            if within and statistics.mean(global_distances) else 0
        ),
    }


def assign_frozen_clusters(records, discovery_records, artifact):
    names = artifact["feature_names"]
    medians = artifact["medians"]
    scales = artifact["scales"]
    medoid_by_hash = {
        row["identity"]["content_sha256"]: row
        for row in discovery_records
    }
    medoid_vectors = []
    for digest in artifact["medoid_record_hashes"]:
        row = medoid_by_hash[digest]
        medoid_vectors.append([
            (row["structural_features"][name] - medians[name]) / scales[name]
            for name in names
        ])
    confidences = []
    for row in records:
        vector = [
            (row["structural_features"][name] - medians[name]) / scales[name]
            for name in names
        ]
        ranked = sorted(
            (
                (manhattan(vector, medoid), index)
                for index, medoid in enumerate(medoid_vectors)
            )
        )
        nearest, index = ranked[0]
        second = ranked[1][0] if len(ranked) > 1 else nearest + 1
        confidence = max(0.0, min(1.0, (second - nearest) / max(second, 1e-9)))
        confidences.append(confidence)
        row["cluster_assignment"] = {
            "rule_based": row["primary_obstruction"],
            "k_medoids": f"C{index + 1}",
            "distance_to_medoid": round(nearest, 6),
            "assignment_confidence": round(confidence, 6),
            "low_confidence": confidence < 0.25,
        }
    return confidences


def wilson(successes, total, z=1.959963984540054):
    if total == 0:
        return [0.0, 1.0]
    p = successes / total
    denominator = 1 + z * z / total
    center = (p + z * z / (2 * total)) / denominator
    radius = z * math.sqrt(
        p * (1 - p) / total + z * z / (4 * total * total)
    ) / denominator
    return [max(0.0, center - radius), min(1.0, center + radius)]


def family_bootstrap(records, selected_class, seed, replicates=10000):
    groups = defaultdict(list)
    for row in records:
        groups[row["provenance"]["source_group_sha256"]].append(row)
    families = sorted(groups)
    rng = random.Random(seed)
    values = []
    for _ in range(replicates):
        sampled = [rng.choice(families) for _ in families]
        rows = [row for family in sampled for row in groups[family]]
        values.append(
            sum(row["primary_obstruction"] == selected_class for row in rows)
            / max(1, len(rows))
        )
    values.sort()
    return [
        values[int(0.025 * (len(values) - 1))],
        values[int(0.975 * (len(values) - 1))],
    ]


def summarize_classes(records):
    counts = Counter(row["primary_obstruction"] for row in records)
    return {
        key: {
            "count": counts.get(key, 0),
            "share": counts.get(key, 0) / max(1, len(records)),
            "wilson_95": wilson(counts.get(key, 0), len(records)),
            "source_families": len({
                row["provenance"]["source_group_sha256"]
                for row in records if row["primary_obstruction"] == key
            }),
        }
        for key in [f"O{index}" for index in range(1, 11)]
    }


def ablation_stability(records, artifact):
    full_assignments = [
        artifact["assignments"][row["identity"]["content_sha256"]]
        for row in records
    ]
    results = {}
    for omitted, indices in FEATURE_GROUPS.items():
        retained_names = [
            name for index, name in enumerate(FEATURE_NAMES)
            if index not in indices
        ]
        matrix, _, _ = robust_scale(records, retained_names)
        distances = distance_matrix(matrix)
        _, assignments = pam(distances, artifact["selected_k"])
        results[omitted] = {
            "adjusted_rand_index": adjusted_rand(
                full_assignments, assignments
            ),
            "variation_information": variation_information(
                full_assignments, assignments
            ),
        }
    return results


def source_family_leakage(records):
    exact = Counter(
        row["provenance"]["source_group_sha256"] for row in records
    )
    skeleton = Counter()
    rulebook = Counter()
    for row in records:
        source = row["equation_structure"]["canonical_source"]
        skeleton_key = "".join(
            "v" if character.isalpha() else character for character in source
        )
        skeleton[hashlib.sha256(skeleton_key.encode()).hexdigest()] += 1
        signature = (
            row["verified_consequences"]["decreasing_rules"],
            row["verified_consequences"]["selected_rules"],
            row["verified_consequences"]["critical_pairs"],
            row["verified_consequences"]["unresolved_critical_pairs"],
        )
        rulebook[signature] += 1
    return {
        "exact_source_families": len(exact),
        "maximum_exact_family": max(exact.values(), default=0),
        "alpha_source_families": len(exact),
        "source_skeleton_families": len(skeleton),
        "maximum_skeleton_family": max(skeleton.values(), default=0),
        "rulebook_signature_families": len(rulebook),
        "maximum_rulebook_signature_family": max(rulebook.values(), default=0),
    }
