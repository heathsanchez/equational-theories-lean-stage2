#!/usr/bin/env python3
from pathlib import Path

p = Path('submissions/mathgraph/solver.py')
s = p.read_text()
old = '''    def solve(self):
        recipe = self.search.solve()
        if recipe is None:
            return None
        recipe = self.inline_recipe(recipe)
'''
new = '''    def schematic_target_closure(self):
        \"\"\"Instantiate any derived schematic equality that directly covers the rigid goal.\"\"\"
        target_left = self.encode_rigid(self.target[0])
        target_right = self.encode_rigid(self.target[1])
        for clause in sorted(self.search.clauses, key=self.search.target_score):
            for reverse in (False, True):
                left = clause.rhs if reverse else clause.lhs
                right = clause.lhs if reverse else clause.rhs
                mapping = {}
                if not self.search.m.match_term(left, target_left, mapping):
                    continue
                if not self.search.m.match_term(right, target_right, mapping):
                    continue
                variables = (
                    self.search.m.term_variables(left)
                    | self.search.m.term_variables(right)
                )
                if not variables <= set(mapping):
                    continue
                proof = self.search.instantiate(clause, mapping)
                if reverse:
                    proof = Recipe(
                        proof.rhs, proof.lhs, \"symmetry\", (proof,)
                    )
                if (proof.lhs, proof.rhs) == (target_left, target_right):
                    return proof
        return None

    def solve(self):
        recipe = self.search.solve()
        if recipe is None:
            recipe = self.schematic_target_closure()
        if recipe is None:
            return None
        recipe = self.inline_recipe(recipe)
'''
if old not in s:
    raise SystemExit('target solve block not found or already changed')
p.write_text(s.replace(old, new, 1))
print('patched', p)
