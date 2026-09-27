<div align="center">

# Five-Dimensional Non-Normal Stability Operator with Gradient-Driven Interface Coupling for Zero-Precursor Filamentary Fractures — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/filament-fracture-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/filament-fracture-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-14-2EA043)
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
subspace. This repository proves the embedding, the factorised spectrum, the exact disk-shaped
pseudospectrum, and the threshold `|μ| > 2b` for transient growth.

## What is proved

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Theorem 1 | `V = span{e₂, e₅}` is invariant: `K₅e₂ = be₂ + γe₅`, `K₅e₅ = μe₂ + be₅` | `K5_invariant` |
| Theorem 1 | At `γ = 0`, `(K₅ − b)e₂ = 0` and `(K₅ − b)e₅ = μe₂`: a length-two Jordan chain | `K5_jordan_chain` |
| Theorem 1 | `det(λI − K₅) = [(λ−b)² − μγ](λ − a)det(λI − B)` | `K5_charpoly` |
| Sec. 3 | The resolvent of `J` is `[[z⁻¹, μz⁻²], [0, z⁻¹]]` | `resolvent` |
| Sec. 3 | The resolvent norm is exactly `1/ε` on `|z|² = ε|μ| + ε²`, so the pseudospectrum is a disk | `pseudospectral_circle` |
| Sec. 3 | `ε_crit = (√(μ²+4b²) − |μ|)/2` is `σ_min(J)`; at `|μ| = 2b` it is `(√2 − 1)b` | `eps_crit_sigma_min`, `eps_crit_at_two` |
| Theorem 2 | `(√(4+s²)+s)/2` is the top singular value of `[[1,−s],[0,1]]` | `top_singular` |
| Theorem 2 | `M(t) = exp(−bt + arsinh(|μ|t/2))`, and some `t > 0` has `M(t) > 1` iff `|μ| > 2b` | `half_sqrt`, `gain_eq`, `arsinh_le_self`, `growth_iff` |
| Prop. 3 | Diagonal detuning: eigenvector `(−μ, δ)` (linear path); reverse coupling: eigenvectors `(1, ±√(γ/μ))` for `b ± √(μγ)` (square-root path) | `detuning_eigen`, `reverse_eigen` |

The file is [`FilamentFracture/Basic.lean`](FilamentFracture/Basic.lean). What is not proved is
in [`LIMITATIONS.md`](LIMITATIONS.md).

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
