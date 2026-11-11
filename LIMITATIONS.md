# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* **The semigroup bound holds for `K₅(0)` — as the paper states it in (2.4) — and, more generally,
  with the interface block `J_γ = [[b, μ], [γ, b]]`.** The restriction of `K₅(γ)` to
  `V = span{e₂, e₅}` is `J_γ`, and `J = [[b, μ], [0, b]]` is its `γ = 0` case; the paper's (2.4)
  quantifies over `K₅(0)`, so it is correct as printed, and `semigroup_bound` proves the
  `γ`-general statement, which strengthens (2.4) rather than correcting it. What is **false** is
  the unconditional form with `J` for every `γ`: at `b = h = c₁ = c₂ = d₁ = q₁ = q₂ = d₂ = 0`,
  `μ = 1`, `γ = −1`, `t = 1` the interface block is the rotation generator `[[0,1],[−1,0]]`, so
  `‖e^{−K₅t}‖ = 1` while `‖e^{−Jt}‖ = (√5 + 1)/2`.
* **`M(t)` is the semigroup norm only for `t ≥ 0`.** `gain_opNorm` proves `M(t) = ‖e^{−tJ}‖` under
  `0 ≤ t`, with `M(t) = e^{−bt}(√(4 + μ²t²) + |μ|t)/2`. The hypothesis is necessary: for `t < 0`
  the norm of `e^{−tJ}` is `e^{−bt}(√(4 + μ²t²) + |μ||t|)/2`, which is larger. The peak time
  `t* = √(m² − 4b²)/(mb)` is proved (`gain_peak`) and so is the peak value (4.2) in closed form,
  `M_max = ((m + √(m²−4b²))/(2b))·exp(−√(m²−4b²)/m)` (`gain_max`). The interface-impulse
  threshold `κ_r = 2.48526751266…` is not formalized.
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
