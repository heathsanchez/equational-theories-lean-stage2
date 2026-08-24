import importlib.util
import json
import sys
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper_compile', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)


def main():
    equations = h.load_equations()
    m = h.load_solver()
    source = m.parse_equation(equations[2666])
    target = m.parse_equation(equations[2860])
    nodes = []

    def add(node):
        nodes.append(node)
        return len(nodes) - 1

    def term_var(name):
        return ('var', name)

    def M(a, b):
        return ('op', a, b)

    def H(*args):
        sl, sr, vars_ = source
        mapping = dict(zip(vars_, args))
        lhs = m.substitute(sl, mapping)
        rhs = m.substitute(sr, mapping)
        return add(m.EqualityNode(
            lhs, rhs, 'source instance',
            substitution=tuple((v, mapping[v]) for v in vars_),
            constructor='teacher-proof-program',
        ))

    def R(t):
        return add(m.EqualityNode(t, t, 'reflexivity', constructor='teacher-proof-program'))

    def S(pid):
        p = nodes[pid]
        return add(m.EqualityNode(
            p.rhs, p.lhs, 'symmetry', parents=(pid,), constructor='teacher-proof-program'
        ))

    def T(left_id, right_id):
        left, right = nodes[left_id], nodes[right_id]
        if left.rhs != right.lhs:
            raise AssertionError('transitivity mismatch: %s != %s' % (
                m.render_term(left.rhs), m.render_term(right.lhs)
            ))
        return add(m.EqualityNode(
            left.lhs, right.rhs, 'transitivity', parents=(left_id, right_id),
            constructor='teacher-proof-program'
        ))

    def C(left_id, right_id):
        # Upstream congr_op combines a=b and c=d into a◇c=b◇d.
        # MathGraph represents this using its existing unary congruence nodes:
        # a◇c = b◇c, then b◇c = b◇d, followed by transitivity.
        left, right = nodes[left_id], nodes[right_id]
        first = add(m.EqualityNode(
            M(left.lhs, right.lhs), M(left.rhs, right.lhs),
            'congruence on left child', parents=(left_id,),
            context=('left', right.lhs), constructor='teacher-proof-program'
        ))
        second = add(m.EqualityNode(
            M(left.rhs, right.lhs), M(left.rhs, right.rhs),
            'congruence on right child', parents=(right_id,),
            context=('right', left.rhs), constructor='teacher-proof-program'
        ))
        return T(first, second)

    x, y, z = term_var('x'), term_var('y'), term_var('z')
    v0 = M(x, y)
    v1 = M(x, v0)
    v2 = M(v1, z)
    v3 = M(v2, z)
    h4 = H(v3, v0, v0)
    h5 = R(v0)
    v6 = M(v3, v0)
    h7 = H(v2, z, z)

    # Exact upstream MagmaEgg proof term, with C lowered to MathGraph's
    # existing one-sided congruence + transitivity representation.
    p_h_v1zz = H(v1, z, z)
    p_c_h7_h7 = C(h7, h7)
    p_c_inner_rz = C(p_c_h7_h7, R(z))
    p1 = T(p_h_v1zz, p_c_inner_rz)
    p2 = T(p1, S(H(M(v3, v3), z, z)))
    p3 = T(p2, C(h4, h4))
    p4 = C(p3, h5)
    p5 = T(p4, S(H(M(v6, v6), v0, v0)))
    p6 = C(p5, h5)
    p7 = T(H(x, v0, y), p6)
    root = T(p7, S(h4))

    root_node = nodes[root]
    endpoint_match = (root_node.lhs, root_node.rhs) == target[:2]
    endpoint_match_symmetric = (root_node.rhs, root_node.lhs) == target[:2]
    try:
        replayed = bool(m.replay_dag(source, nodes, root, maximum_term_size=512, maximum_nodes=10000))
        replay_error = None
    except Exception as exc:
        replayed = False
        replay_error = type(exc).__name__ + ': ' + str(exc)

    result = {
        'schema': 'mathgraph.2666-2860-proof-program-compile.v1',
        'source_id': 2666,
        'target_id': 2860,
        'node_count': len(nodes),
        'root_lhs': m.render_term(root_node.lhs),
        'root_rhs': m.render_term(root_node.rhs),
        'target_lhs': m.render_term(target[0]),
        'target_rhs': m.render_term(target[1]),
        'endpoint_match': endpoint_match,
        'endpoint_match_symmetric': endpoint_match_symmetric,
        'replayed': replayed,
        'replay_error': replay_error,
        'constructors': sorted({str(getattr(n, 'constructor', None)) for n in nodes}),
        'kinds': sorted({n.kind for n in nodes}),
    }
    out = Path('experiments/mathgraph/results/2666-2860-proof-program-compile.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, sort_keys=True), flush=True)
    if not endpoint_match or not replayed:
        raise SystemExit(2)


if __name__ == '__main__':
    main()
