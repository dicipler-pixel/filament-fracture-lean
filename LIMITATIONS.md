# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The semigroup bound `‖e^{−K₅t}‖ ≥ ‖e^{−Jt}‖` is not formalized. The theorems give the
  invariant subspace it rests on, and the exact formula for `M(t)` as a real function.
* `M(t)` is defined by its closed form. The identification of that form with the operator norm
  of `e^{−Jt}` is supported by `top_singular`, but the full operator-norm computation is not
  formalized. The peak time `t*`, `M_max`, and the interface-impulse threshold
  `κ_r = 2.4852…` are not formalized.
* The Riesz and Grassmannian construction (Sec. 6), the continuum projection (Sec. 7), the heat
  trace (Sec. 8), the colour-shift hypothesis (Sec. 9) and every statement about the Snake
  filament are outside these proofs. The paper grades them [C] or [H].
