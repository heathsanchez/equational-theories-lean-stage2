import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x y z
  exact h ((x ◇ y)) (z)
