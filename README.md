<div align="center">

# Five-Dimensional Non-Normal Stability Operator with Gradient-Driven Interface Coupling for Zero-Precursor Filamentary Fractures — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/filament-fracture-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/filament-fracture-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-27-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.21184980-blue)](https://doi.org/10.5281/zenodo.21184980)

Jeromie Beasley

</div>

---

## The idea in one line

A five-dimensional operator can have every eigenvalue safely stable and still amplify a
disturbance, because it carries an exact Jordan block on an invariant two-dimensional interface
subspace. This repository proves the embedding, the factorised characteristic polynomial, the
closed-form resolvent norm equal to `1/ε` on the circle `|z|² = ε|μ| + ε²`, and the threshold
`|μ| > 2b` for transient growth of the closed-form gain `M(t)`. It then identifies those closed
forms with the operator norms they are claimed to be — the resolvent norm, the gain as `‖e^{−tJ}‖`,
`ε_crit` as the least singular value — so the inequalities are about linear maps, not formulae.

## What is proved

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Theorem 1 | `V = span{e₂, e₅}` is invariant: `K₅e₂ = be₂ + γe₅`, `K₅e₅ = μe₂ + be₅` | `K5_invariant` |
| Theorem 1 | At `γ = 0`, `(K₅ − b)e₂ = 0` and `(K₅ − b)e₅ = μe₂`: a length-two Jordan chain | `K5_jordan_chain` |
| Theorem 1 | `det(λI − K₅) = [(λ−b)² − μγ](λ − a)det(λI − B)` | `K5_charpoly` |
| Sec. 3 | The resolvent of `J` is `[[z⁻¹, μz⁻²], [0, z⁻¹]]` | `resolvent` |
| Sec. 3 | The closed-form resolvent norm `(√(4ρ² + m²) + m)/(2ρ²)` (`ρ = \|z\|`, `m = \|μ\|`) equals `1/ε` exactly on the circle `ρ² = εm + ε²` | `pseudospectral_circle` |
| Sec. 3 | `ε_crit = (√(μ²+4b²) − \|μ\|)/2` satisfies `ε_crit · (√(μ²+4b²) + \|μ\|)/2 = b²`; with `σ_max(J) = ‖J‖` and `σ_min = 1/‖J⁻¹‖` proved in the operator-norm layer below, this identifies `ε_crit` as `σ_min(J)`; at `\|μ\| = 2b` it is `(√2 − 1)b` | `eps_crit_sigma_min`, `eps_crit_at_two` |
| Theorem 2 | `σ = (√(4+s²)+s)/2` satisfies `σ⁴ − (2+s²)σ² + 1 = 0`, the characteristic equation of the Gram matrix of `[[1,−s],[0,1]]`; for `s ≥ 0` it is the top singular value in the operator-norm sense (`opNorm_unipotent` below), and that it is the larger quadratic root is not formalized | `top_singular` |
| Theorem 2 | `M(t) = exp(−bt + arsinh(\|μ\|t/2))`, and some `t > 0` has `M(t) > 1` iff `\|μ\| > 2b` | `half_sqrt`, `gain_eq`, `arsinh_le_self`, `growth_iff` |
| Prop. 3 | Diagonal detuning: eigenvector `(−μ, δ)` (linear path); reverse coupling: eigenvectors `(1, ±√(γ/μ))` for `b ± √(μγ)` (square-root path) | `detuning_eigen`, `reverse_eigen` |

The files are [`FilamentFracture/Basic.lean`](FilamentFracture/Basic.lean) (the algebra of Secs. 2–5)
and [`FilamentFracture/OperatorNorm.lean`](FilamentFracture/OperatorNorm.lean) (the operator-norm
layer). What is not proved is in [`LIMITATIONS.md`](LIMITATIONS.md).

## The operator-norm layer

`OperatorNorm.lean` proves that the closed forms of `Basic.lean` are the operator norms they are
claimed to be. Every norm below is the operator norm of the matrix acting on Euclidean space
(`‖A‖ = ‖A.toEuclideanLin.toContinuousLinearMap‖`); `J = [[b, μ], [0, b]]` and
`J_γ = [[b, μ], [γ, b]]` are the restrictions of `K₅` to `V = span{e₂, e₅}` at `γ = 0` and at
general `γ`.

| Result | Theorem |
| :--- | :--- |
| `‖[[1,s],[0,1]]‖ = (√(4+s²)+\|s\|)/2` on `EuclideanSpace ℝ (Fin 2)`, and the same identity over `ℂ` | `opNorm_unipotent`, `complex_opNorm_unipotent` |
| the resolvent of the interface block has norm exactly `resNorm ‖μ‖ ‖z‖` over `ℂ`, `z ≠ 0` | `resolvent_opNorm` |
| each pseudospectrum is a disk: `resNorm m ρ < 1/ε ↔ εm + ε² < ρ²`, and `resNorm m ·` is strictly decreasing in `ρ` | `resNorm_lt_iff`, `resNorm_strictAntiOn` |
| `‖J‖ = (√(m²+4b²)+\|m\|)/2` and `‖J⁻¹‖ = 1/ε_crit`, so `ε_crit = 1/‖J⁻¹‖` is the least singular value | `opNorm_J`, `opNorm_J_inv` |
| `M(t) = ‖e^{−tJ}‖` for `t ≥ 0` — the gain is the semigroup norm | `gain_opNorm` |
| the gain is maximised at `t* = √(m²−4b²)/(mb)` when `m > 2b > 0`, with peak value `M_max = ((m + √(m²−4b²))/(2b))·exp(−√(m²−4b²)/m)` — the paper's (4.2) | `gain_peak`, `gain_max` |
| `‖e^{−tJ_γ}‖ ≤ ‖e^{−tK₅(γ)}‖` for every `γ`: the whole operator amplifies at least as much as the interface it contains | `semigroup_bound` |

Composed with the theorems of `Basic.lean` these give the paper's claims rather than paraphrases
of them: `1 < ‖e^{−t*J}‖` at the peak time whenever `m > 2b`, and `ε_crit · ‖J‖ = b²`.

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and three deliberately false statements that must fail.

## The paper

*Five-Dimensional Non-Normal Stability Operator with Gradient-Driven Interface Coupling for Zero-Precursor Filamentary Fractures*, Jeromie Beasley. DOI
[10.5281/zenodo.21184980](https://doi.org/10.5281/zenodo.21184980) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
