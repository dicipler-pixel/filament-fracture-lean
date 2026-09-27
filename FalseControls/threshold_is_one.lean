import FilamentFracture.Basic
-- The growth threshold is κ = 2, not κ = 1: with b = 1, m = 3/2 the gain never exceeds 1.
example : ∃ t > 0, 1 < FilamentFracture.gain 1 (3 / 2) t :=
  (FilamentFracture.growth_iff 1 (3 / 2) (by norm_num) (by norm_num)).mpr (by norm_num)
