# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* **The interface block is `J_γ = [[b, μ], [γ, b]]`, not `J = [[b, μ], [0, b]]`.** The restriction
  of `K₅(γ)` to `V = span{e₂, e₅}` is `J_γ`; `J` is the case `γ = 0`. The semigroup bound is
  therefore `‖e^{−K₅t}‖ ≥ ‖e^{−J_γt}‖`, and that is what is proved (`semigroup_bound`). Stated
  with `J` in place of `J_γ` it is **false**: at `b = h = c₁ = c₂ = d₁ = q₁ = q₂ = d₂ = 0`,
  `μ = 1`, `γ = −1`, `t = 1` the interface block is the rotation generator `[[0,1],[−1,0]]`, so
  `‖e^{−K₅t}‖ = 1` while `‖e^{−Jt}‖ = (√5 + 1)/2`.
* **`M(t)` is the semigroup norm only for `t ≥ 0`.** `gain_opNorm` proves `M(t) = ‖e^{−tJ}‖` under
  `0 ≤ t`, with `M(t) = e^{−bt}(√(4 + μ²t²) + |μ|t)/2`. The hypothesis is necessary: for `t < 0`
  the norm of `e^{−tJ}` is `e^{−bt}(√(4 + μ²t²) + |μ||t|)/2`, which is larger. The peak time
  `t* = √(m² − 4b²)/(mb)` is proved (`gain_peak`); the closed form of the peak value `M_max` and
  the interface-impulse threshold `κ_r = 2.4852…` are not.
* **`resNorm` is the resolvent norm, and each pseudospectrum is a disk** — both proved
  (`resolvent_opNorm`, `resNorm_lt_iff`, `resNorm_strictAntiOn`). What is not proved: continuity
  or analyticity of `z ↦ (zI − J)⁻¹`, so the disk statement is about the closed form and its
  monotonicity in `|z|`, not about the resolvent as a function on `ℂ` in the operator topology.
* **Singular values are not formalized as a general theory.** What is proved is
  `‖J‖ = (√(m²+4b²)+|m|)/2` and `‖J⁻¹‖ = 1/ε_crit`, hence `ε_crit = 1/‖J⁻¹‖` (`opNorm_J`,
  `opNorm_J_inv`). Reading this as "`ε_crit = σ_min`" uses the standard identity
  `σ_min(A) = 1/‖A⁻¹‖`, which is not itself formalized here, and neither is the minimax
  characterization. `top_singular` proves only that the closed form's square solves the Gram
  characteristic equation; that it is the larger root for `s ≥ 0` is not formalized.
* **The Riesz and Grassmannian construction (Sec. 6), the continuum projection (Sec. 7), the heat
  trace (Sec. 8), the colour-shift hypothesis (Sec. 9) and every statement about the Snake
  filament are outside these proofs.** The paper grades them [C] or [H].
* **The statements are checked against their transcription into Lean, not against the paper's
  prose.** A formally true statement can still differ from what the paper intends; that
  comparison is a reader's job, not the kernel's.
