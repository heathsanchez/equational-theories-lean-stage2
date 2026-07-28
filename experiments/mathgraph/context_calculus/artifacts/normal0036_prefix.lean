import JudgeMagma.Magma

example {G : Type} [Magma G]
    (h : ∀ x y z : G, x = ((x ◇ y) ◇ (x ◇ z)) ◇ y) :
    ∀ x y z : G,
      (x ◇ y) ◇ (x ◇ z) =
        (x ◇ (((x ◇ y) ◇ (x ◇ z)) ◇ z)) ◇ y := by
  intro x y z
  let s := (x ◇ y) ◇ (x ◇ z)
  have h₁ :
      s = (((s ◇ y) ◇ (s ◇ z)) ◇ y) :=
    h s y z
  have h₂ :
      (((s ◇ y) ◇ (s ◇ z)) ◇ y) =
        ((x ◇ (s ◇ z)) ◇ y) := by
    exact congrArg
      (fun t : G => (t ◇ (s ◇ z)) ◇ y)
      (h x y z).symm
  exact h₁.trans h₂
