import FilamentFracture.Basic
-- At γ = 0 the block is a Jordan block: (J − b)e₂ = μe₁ ≠ 0 when μ = 1.
example : (!![(0 : ℝ), 1; 0, 0] *ᵥ ![0, 1]) = ![0, 0] := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
