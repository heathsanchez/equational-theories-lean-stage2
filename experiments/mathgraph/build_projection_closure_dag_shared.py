#!/usr/bin/env python3
"""Compress projection-closure certificates by sharing terms in the replayed DAG.

Unlike schematic proof reconstruction, this serializer never changes proof
structure or substitutions.  The Recipe is first compiled and independently
replayed exactly as before.  We then hash-cons composite magma terms appearing
in the validated EqualityNode DAG into local Lean `let` bindings and emit the
same source/symmetry/transitivity/congruence nodes.  No problem IDs, equation
IDs, stored certificates, or named target lemmas are used.
"""

import build_projection_closure_specialist as base

SHARED = r'''    def shared_dag_certificate(nodes, root):
        needed = set()

        def visit(node_id):
            if node_id in needed:
                return
            for parent in nodes[node_id].parents:
                visit(parent)
            needed.add(node_id)

        visit(root)
        ordered = sorted(needed)
        names = {node_id: "p" + str(i) for i, node_id in enumerate(ordered)}
        target_vars = tuple(target[2])
        allowed_vars = set(target_vars)

        composites = set()
        all_seen_vars = set()

        def collect(term):
            if term[0] == "var":
                all_seen_vars.add(term[1])
                return
            composites.add(term)
            collect(term[1])
            collect(term[2])

        for node_id in ordered:
            node = nodes[node_id]
            if node.kind in ("source instance", "source reentry"):
                for _, value in node.substitution:
                    collect(value)
            elif node.kind in (
                "congruence on left child", "congruence on right child"
            ):
                collect(node.context[1])
            elif node.kind not in ("symmetry", "transitivity"):
                collect(node.lhs)
                collect(node.rhs)

        if not all_seen_vars.issubset(allowed_vars):
            return None, 0

        terms = sorted(composites, key=lambda q: (term_size(q), render_term(q)))
        aliases = {term: "t" + str(i) for i, term in enumerate(terms)}

        def render_shared(term, defining=None):
            if term[0] == "var":
                return term[1]
            if term != defining and term in aliases:
                return aliases[term]
            return (
                "(" + render_shared(term[1], defining) + " ◇ "
                + render_shared(term[2], defining) + ")"
            )

        lines = [
            "import JudgeProblem", "", "def submission : Goal := by",
            "  intro G _ h",
        ]
        if target_vars:
            lines.append("  intro " + " ".join(target_vars))
        for term in terms:
            lines.append(
                "  let " + aliases[term] + " := "
                + render_shared(term, defining=term)
            )

        for node_id in ordered:
            node = nodes[node_id]
            name = names[node_id]
            if node.kind in ("source instance", "source reentry"):
                mapping = dict(node.substitution)
                expression = "h" + "".join(
                    " (" + render_shared(mapping[v]) + ")" for v in source[2]
                )
                if node.orientation:
                    expression = "Eq.symm (" + expression + ")"
                lines.append("  have " + name + " := " + expression)
            elif node.kind == "symmetry":
                lines.append(
                    "  have " + name + " := Eq.symm " + names[node.parents[0]]
                )
            elif node.kind == "transitivity":
                lines.append(
                    "  have " + name + " := Eq.trans "
                    + names[node.parents[0]] + " " + names[node.parents[1]]
                )
            elif node.kind == "congruence on left child":
                sibling = render_shared(node.context[1])
                lines.append(
                    "  have " + name
                    + " := congrArg (fun _mg_t => _mg_t ◇ " + sibling + ") "
                    + names[node.parents[0]]
                )
            elif node.kind == "congruence on right child":
                sibling = render_shared(node.context[1])
                lines.append(
                    "  have " + name
                    + " := congrArg (fun _mg_t => " + sibling + " ◇ _mg_t) "
                    + names[node.parents[0]]
                )
            else:
                lines.append(
                    "  have " + name + " : " + render_shared(node.lhs)
                    + " = " + render_shared(node.rhs) + " := rfl"
                )
        lines.append("  exact " + names[root])
        return "\n".join(lines) + "\n", len(ordered)

'''

OLD = '''        code, proof_nodes = make_dag_certificate(target, nodes, root)\n        if "_mg_elide_have_types" in globals():\n            old_lines = code.splitlines()\n            new_lines = _mg_elide_have_types(code).splitlines()\n            code = "\\n".join(\n                old if ":=" in old and old.rstrip().endswith(":= rfl") else new\n                for old, new in zip(old_lines, new_lines)\n            ) + "\\n"\n        code_bytes = len(code.encode("utf-8"))\n'''
NEW = '''        code, proof_nodes = shared_dag_certificate(nodes, root)\n        if not code:\n            return False\n        code_bytes = len(code.encode("utf-8"))\n'''

if base.SPECIALIST.count("    def finish(recipe):\n") != 1:
    raise SystemExit("finish marker not unique")
if base.SPECIALIST.count(OLD) != 1:
    raise SystemExit("expanded certificate block not unique")
base.SPECIALIST = base.SPECIALIST.replace(
    "    def finish(recipe):\n", SHARED + "    def finish(recipe):\n", 1
)
base.SPECIALIST = base.SPECIALIST.replace(OLD, NEW, 1)
base.main()
