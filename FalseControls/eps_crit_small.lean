import FilamentFracture.Basic
-- At |μ| = 2b the crossing threshold is (√2 − 1)b, not b/10.
example : (√2 - 1) * 1 = (1 : ℝ) / 10 := by
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
