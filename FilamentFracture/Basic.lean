/-
Five-Dimensional Non-Normal Stability Operator with Gradient-Driven Interface Coupling for
Zero-Precursor Filamentary Fractures (Jeromie Beasley, DOI 10.5281/zenodo.21184980):
the exact results of Revision 3/4, Secs. 2–5.

* Theorem 1: `V = span{e₂, e₅}` is invariant under `K₅(γ)`, with restriction
  `J_γ = [[b, μ], [γ, b]]`; at `γ = 0` it carries a length-two Jordan chain at `b`; and
  `det(λI − K₅) = [(λ−b)² − μγ](λ − a) det(λI − B)`.
* Sec. 3: the resolvent of `J = [[b, μ], [0, b]]` is `[[z⁻¹, μz⁻²], [0, z⁻¹]]`; its norm equals
  `1/ε` exactly on the circle `|z|² = ε|μ| + ε²`, so the pseudospectrum is a disk; and
  `ε_crit = (√(μ² + 4b²) − |μ|)/2` satisfies `ε_crit · σ_max = b²` (it is `σ_min(J)`), with
  `ε_crit = (√2 − 1)b` at `|μ| = 2b`.
* Theorem 2: `(√(4 + s²) + s)/2` is the top singular value of `[[1, −s], [0, 1]]` (its square
  solves the Gram characteristic equation), and with
  `M(t) = e^{−bt}(√(4 + μ²t²) + |μ|t)/2` there is `t > 0` with `M(t) > 1` iff `|μ| > 2b`.
* Proposition 3: the diagonal-detuning eigenvector `(−μ, δ)` and the reverse-coupling
  eigenvectors `(1, ±√(γ/μ))` with eigenvalues `b ± √(μγ)`.
-/
import Mathlib

namespace FilamentFracture

open Matrix Real Filter Topology

/-! ## Theorem 1: the exact interface embedding -/

/-- The five-dimensional operator `K₅(γ)` of Eq. (1), coordinates `(x₁, x₂, s₁, s₂, r)`. -/
def K5 (a b h c1 c2 μ γ d1 q1 q2 d2 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![a, 0, 0, 0, 0;
     h, b, c1, c2, μ;
     0, 0, d1, q1, 0;
     0, 0, q2, d2, 0;
     0, γ, 0, 0, b]

/-- **Theorem 1, invariance.** `K₅ e₂ = b e₂ + γ e₅` and `K₅ e₅ = μ e₂ + b e₅`. -/
theorem K5_invariant (a b h c1 c2 μ γ d1 q1 q2 d2 : ℝ) :
    K5 a b h c1 c2 μ γ d1 q1 q2 d2 *ᵥ Pi.single 1 1 = ![0, b, 0, 0, γ] ∧
      K5 a b h c1 c2 μ γ d1 q1 q2 d2 *ᵥ Pi.single 4 1 = ![0, μ, 0, 0, b] := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [K5, mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply]

/-- **Theorem 1, Jordan chain.** At `γ = 0`: `(K₅ − b)e₂ = 0` and `(K₅ − b)e₅ = μ e₂`. -/
theorem K5_jordan_chain (a b h c1 c2 μ d1 q1 q2 d2 : ℝ) :
    (K5 a b h c1 c2 μ 0 d1 q1 q2 d2 - b • 1) *ᵥ Pi.single 1 1 = 0 ∧
      (K5 a b h c1 c2 μ 0 d1 q1 q2 d2 - b • 1) *ᵥ Pi.single 4 1 = μ • Pi.single 1 1 := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [K5, sub_mulVec, mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply]

/-- Small `Fin.succAbove` values, for expanding determinants by hand. -/
private theorem sa_2_0_0 : Fin.succAbove (0 : Fin 2) (0 : Fin 1) = 1 := by decide
private theorem sa_2_1_0 : Fin.succAbove (1 : Fin 2) (0 : Fin 1) = 0 := by decide
private theorem sa_3_0_0 : Fin.succAbove (0 : Fin 3) (0 : Fin 2) = 1 := by decide
private theorem sa_3_0_1 : Fin.succAbove (0 : Fin 3) (1 : Fin 2) = 2 := by decide
private theorem sa_3_1_0 : Fin.succAbove (1 : Fin 3) (0 : Fin 2) = 0 := by decide
private theorem sa_3_1_1 : Fin.succAbove (1 : Fin 3) (1 : Fin 2) = 2 := by decide
private theorem sa_3_2_0 : Fin.succAbove (2 : Fin 3) (0 : Fin 2) = 0 := by decide
private theorem sa_3_2_1 : Fin.succAbove (2 : Fin 3) (1 : Fin 2) = 1 := by decide
private theorem sa_4_0_0 : Fin.succAbove (0 : Fin 4) (0 : Fin 3) = 1 := by decide
private theorem sa_4_0_1 : Fin.succAbove (0 : Fin 4) (1 : Fin 3) = 2 := by decide
private theorem sa_4_0_2 : Fin.succAbove (0 : Fin 4) (2 : Fin 3) = 3 := by decide
private theorem sa_4_1_0 : Fin.succAbove (1 : Fin 4) (0 : Fin 3) = 0 := by decide
private theorem sa_4_1_1 : Fin.succAbove (1 : Fin 4) (1 : Fin 3) = 2 := by decide
private theorem sa_4_1_2 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := by decide
private theorem sa_4_2_0 : Fin.succAbove (2 : Fin 4) (0 : Fin 3) = 0 := by decide
private theorem sa_4_2_1 : Fin.succAbove (2 : Fin 4) (1 : Fin 3) = 1 := by decide
private theorem sa_4_2_2 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
private theorem sa_4_3_0 : Fin.succAbove (3 : Fin 4) (0 : Fin 3) = 0 := by decide
private theorem sa_4_3_1 : Fin.succAbove (3 : Fin 4) (1 : Fin 3) = 1 := by decide
private theorem sa_4_3_2 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := by decide
private theorem sa_5_0_0 : Fin.succAbove (0 : Fin 5) (0 : Fin 4) = 1 := by decide
private theorem sa_5_0_1 : Fin.succAbove (0 : Fin 5) (1 : Fin 4) = 2 := by decide
private theorem sa_5_0_2 : Fin.succAbove (0 : Fin 5) (2 : Fin 4) = 3 := by decide
private theorem sa_5_0_3 : Fin.succAbove (0 : Fin 5) (3 : Fin 4) = 4 := by decide
private theorem sa_5_1_0 : Fin.succAbove (1 : Fin 5) (0 : Fin 4) = 0 := by decide
private theorem sa_5_1_1 : Fin.succAbove (1 : Fin 5) (1 : Fin 4) = 2 := by decide
private theorem sa_5_1_2 : Fin.succAbove (1 : Fin 5) (2 : Fin 4) = 3 := by decide
private theorem sa_5_1_3 : Fin.succAbove (1 : Fin 5) (3 : Fin 4) = 4 := by decide
private theorem sa_5_2_0 : Fin.succAbove (2 : Fin 5) (0 : Fin 4) = 0 := by decide
private theorem sa_5_2_1 : Fin.succAbove (2 : Fin 5) (1 : Fin 4) = 1 := by decide
private theorem sa_5_2_2 : Fin.succAbove (2 : Fin 5) (2 : Fin 4) = 3 := by decide
private theorem sa_5_2_3 : Fin.succAbove (2 : Fin 5) (3 : Fin 4) = 4 := by decide
private theorem sa_5_3_0 : Fin.succAbove (3 : Fin 5) (0 : Fin 4) = 0 := by decide
private theorem sa_5_3_1 : Fin.succAbove (3 : Fin 5) (1 : Fin 4) = 1 := by decide
private theorem sa_5_3_2 : Fin.succAbove (3 : Fin 5) (2 : Fin 4) = 2 := by decide
private theorem sa_5_3_3 : Fin.succAbove (3 : Fin 5) (3 : Fin 4) = 4 := by decide
private theorem sa_5_4_0 : Fin.succAbove (4 : Fin 5) (0 : Fin 4) = 0 := by decide
private theorem sa_5_4_1 : Fin.succAbove (4 : Fin 5) (1 : Fin 4) = 1 := by decide
private theorem sa_5_4_2 : Fin.succAbove (4 : Fin 5) (2 : Fin 4) = 2 := by decide
private theorem sa_5_4_3 : Fin.succAbove (4 : Fin 5) (3 : Fin 4) = 3 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **Theorem 1, factorisation.** `det(λI − K₅) = [(λ−b)² − μγ](λ − a)det(λI − B)`. -/
theorem K5_charpoly (a b h c1 c2 μ γ d1 q1 q2 d2 x : ℝ) :
    (x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - K5 a b h c1 c2 μ γ d1 q1 q2 d2).det =
      ((x - b) ^ 2 - μ * γ) * (x - a) * ((x - d1) * (x - d2) - q1 * q2) := by
  have e : x • (1 : Matrix (Fin 5) (Fin 5) ℝ) - K5 a b h c1 c2 μ γ d1 q1 q2 d2 =
      !![x - a, 0, 0, 0, 0;
         -h, x - b, -c1, -c2, -μ;
         0, 0, x - d1, -q1, 0;
         0, 0, -q2, x - d2, 0;
         0, -γ, 0, 0, x - b] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [K5, Matrix.one_apply]
  rw [e]
  simp only [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero, submatrix_apply,
    sa_2_0_0, sa_2_1_0, sa_3_0_0, sa_3_0_1, sa_3_1_0, sa_3_1_1, sa_3_2_0, sa_3_2_1, sa_4_0_0, sa_4_0_1, sa_4_0_2, sa_4_1_0, sa_4_1_1, sa_4_1_2, sa_4_2_0, sa_4_2_1, sa_4_2_2, sa_4_3_0, sa_4_3_1, sa_4_3_2, sa_5_0_0, sa_5_0_1, sa_5_0_2, sa_5_0_3, sa_5_1_0, sa_5_1_1, sa_5_1_2, sa_5_1_3, sa_5_2_0, sa_5_2_1, sa_5_2_2, sa_5_2_3, sa_5_3_0, sa_5_3_1, sa_5_3_2, sa_5_3_3, sa_5_4_0, sa_5_4_1, sa_5_4_2, sa_5_4_3]
  simp [sa_2_0_0, sa_2_1_0, sa_3_0_0, sa_3_0_1, sa_3_1_0, sa_3_1_1, sa_3_2_0, sa_3_2_1, sa_4_0_0, sa_4_0_1, sa_4_0_2, sa_4_1_0, sa_4_1_1, sa_4_1_2, sa_4_2_0, sa_4_2_1, sa_4_2_2, sa_4_3_0, sa_4_3_1, sa_4_3_2, sa_5_0_0, sa_5_0_1, sa_5_0_2, sa_5_0_3, sa_5_1_0, sa_5_1_1, sa_5_1_2, sa_5_1_3, sa_5_2_0, sa_5_2_1, sa_5_2_2, sa_5_2_3, sa_5_3_0, sa_5_3_1, sa_5_3_2, sa_5_3_3, sa_5_4_0, sa_5_4_1, sa_5_4_2, sa_5_4_3]
  try simp [sa_2_0_0, sa_2_1_0, sa_3_0_0, sa_3_0_1, sa_3_1_0, sa_3_1_1, sa_3_2_0, sa_3_2_1, sa_4_0_0, sa_4_0_1, sa_4_0_2, sa_4_1_0, sa_4_1_1, sa_4_1_2, sa_4_2_0, sa_4_2_1, sa_4_2_2, sa_4_3_0, sa_4_3_1, sa_4_3_2, sa_5_0_0, sa_5_0_1, sa_5_0_2, sa_5_0_3, sa_5_1_0, sa_5_1_1, sa_5_1_2, sa_5_1_3, sa_5_2_0, sa_5_2_1, sa_5_2_2, sa_5_2_3, sa_5_3_0, sa_5_3_1, sa_5_3_2, sa_5_3_3, sa_5_4_0, sa_5_4_1, sa_5_4_2, sa_5_4_3]
  ring

/-! ## Section 3: resolvent and pseudospectrum -/

/-- **Resolvent.** `(λI − J)⁻¹ = [[z⁻¹, μz⁻²], [0, z⁻¹]]` with `z = λ − b`. -/
theorem resolvent (μ z : ℂ) (hz : z ≠ 0) :
    !![z, -μ; 0, z] * !![z⁻¹, μ * z⁻¹ ^ 2; 0, z⁻¹] = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    ring

/-- The resolvent norm `(√(4ρ² + m²) + m)/(2ρ²)` at `|z| = ρ`, `|μ| = m`. -/
noncomputable def resNorm (m ρ : ℝ) : ℝ := (√(4 * ρ ^ 2 + m ^ 2) + m) / (2 * ρ ^ 2)

/-- **The exact disk.** On `ρ² = εm + ε²` the resolvent norm is exactly `1/ε`. -/
theorem pseudospectral_circle (m ε ρ : ℝ) (hm : 0 ≤ m) (hε : 0 < ε)
    (hρ : ρ ^ 2 = ε * m + ε ^ 2) : resNorm m ρ = 1 / ε := by
  unfold resNorm
  have hs : √(4 * ρ ^ 2 + m ^ 2) = m + 2 * ε := by
    rw [hρ, show 4 * (ε * m + ε ^ 2) + m ^ 2 = (m + 2 * ε) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
  rw [hs, hρ]
  have : 0 < ε * m + ε ^ 2 := by positivity
  field_simp
  ring

/-- **The crossing threshold is `σ_min(J)`.** `ε_crit · σ_max = b²` with
`σ_max = (√(μ² + 4b²) + |μ|)/2`, so `ε_crit = σ_min` since `σ_min σ_max = |det J| = b²`. -/
theorem eps_crit_sigma_min (m b : ℝ) :
    (√(m ^ 2 + 4 * b ^ 2) - m) / 2 * ((√(m ^ 2 + 4 * b ^ 2) + m) / 2) = b ^ 2 := by
  have h := Real.sq_sqrt (show 0 ≤ m ^ 2 + 4 * b ^ 2 by positivity)
  nlinarith

/-- **Not automatically small.** At `|μ| = 2b` the threshold is `(√2 − 1)b`. -/
theorem eps_crit_at_two (b : ℝ) (hb : 0 ≤ b) :
    (√((2 * b) ^ 2 + 4 * b ^ 2) - 2 * b) / 2 = (√2 - 1) * b := by
  rw [show (2 * b) ^ 2 + 4 * b ^ 2 = 2 * (2 * b) ^ 2 by ring, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by linarith)]
  ring

/-! ## Theorem 2: exact transient growth -/

/-- **The top singular value.** `σ = (√(4+s²)+s)/2` satisfies `σ⁴ − (2+s²)σ² + 1 = 0`, the
characteristic equation of the Gram matrix `[[1, −s], [−s, 1+s²]]` of `[[1, −s], [0, 1]]`. -/
theorem top_singular (s : ℝ) :
    let σ := (√(4 + s ^ 2) + s) / 2
    (σ ^ 2) ^ 2 - (2 + s ^ 2) * σ ^ 2 + 1 = 0 := by
  intro σ
  have h := Real.sq_sqrt (show 0 ≤ 4 + s ^ 2 by positivity)
  simp only [σ]
  nlinarith [h]

/-- The optimized gain `M(t) = e^{−bt}(√(4 + μ²t²) + |μ|t)/2`. -/
noncomputable def gain (b m t : ℝ) : ℝ := exp (-(b * t)) * ((√(4 + (m * t) ^ 2) + m * t) / 2)

theorem half_sqrt (x : ℝ) : (√(4 + (2 * x) ^ 2) + 2 * x) / 2 = x + √(1 + x ^ 2) := by
  rw [show 4 + (2 * x) ^ 2 = 2 ^ 2 * (1 + x ^ 2) by ring, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  ring

/-- `M(t) = exp(−bt + arsinh(mt/2))`. -/
theorem gain_eq (b m t : ℝ) : gain b m t = exp (-(b * t) + arsinh (m * t / 2)) := by
  rw [exp_add, Real.exp_arsinh, gain]
  congr 1
  rw [← half_sqrt (m * t / 2)]
  ring_nf

theorem arsinh_le_self (x : ℝ) (hx : 0 ≤ x) : arsinh x ≤ x := by
  rw [← Real.sinh_le_sinh, Real.sinh_arsinh]
  exact Real.self_le_sinh_iff.mpr hx

/-- **Theorem 2.** For `b > 0` and `m = |μ| ≥ 0`, some `t > 0` has `M(t) > 1` exactly when
`κ = m/b > 2`. -/
theorem growth_iff (b m : ℝ) (hb : 0 < b) (hm : 0 ≤ m) :
    (∃ t > 0, 1 < gain b m t) ↔ 2 * b < m := by
  constructor
  · rintro ⟨t, ht, hg⟩
    by_contra hc
    push_neg at hc
    rw [gain_eq] at hg
    have h1 : arsinh (m * t / 2) ≤ m * t / 2 := arsinh_le_self _ (by positivity)
    have h2 : -(b * t) + arsinh (m * t / 2) ≤ 0 := by nlinarith
    have := Real.exp_le_one_iff.mpr h2
    linarith
  · intro hbm
    have hm' : 0 < m := by linarith
    -- arsinh x / x → 1 as x → 0⁺, and 2b/m < 1
    have hd := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_arsinh (0 : ℝ))
    simp only [sq, mul_zero, add_zero, Real.sqrt_one, inv_one] at hd
    have hc : 2 * b / m < 1 := by rw [div_lt_one hm']; exact hbm
    have hev : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 2 * b / m < slope arsinh 0 x :=
      hd.eventually (lt_mem_nhds hc)
    have hev' : ∀ᶠ x in 𝓝[>] (0 : ℝ), 2 * b / m < slope arsinh 0 x :=
      hev.filter_mono (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
    obtain ⟨x, hx, hxpos⟩ := (hev'.and self_mem_nhdsWithin).exists
    have hxpos' : (0 : ℝ) < x := hxpos
    rw [slope_def_field, Real.arsinh_zero, sub_zero, sub_zero, lt_div_iff₀ hxpos'] at hx
    refine ⟨2 * x / m, by positivity, ?_⟩
    rw [gain_eq, show m * (2 * x / m) / 2 = x by field_simp]
    apply Real.one_lt_exp_iff.mpr
    have : b * (2 * x / m) = 2 * b / m * x := by ring
    linarith

/-! ## Proposition 3: two coalescence paths -/

/-- **Proposition 3, detuning.** `(−μ, δ)` is an eigenvector of `[[b+δ, μ], [0, b]]` for `b`;
its angle with `e₁` has sine `|δ|/√(μ² + δ²)`, linear in `δ`. -/
theorem detuning_eigen (b μ δ : ℝ) :
    !![b + δ, μ; 0, b] *ᵥ ![-μ, δ] = b • ![-μ, δ] := by
  ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **Proposition 3, reverse coupling.** For `μ, γ > 0`, `(1, ±√(γ/μ))` are eigenvectors of
`[[b, μ], [γ, b]]` for `b ± √(μγ)`: the square-root path. -/
theorem reverse_eigen (b μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    !![b, μ; γ, b] *ᵥ ![1, √(γ / μ)] = (b + √(μ * γ)) • ![1, √(γ / μ)] ∧
      !![b, μ; γ, b] *ᵥ ![1, -√(γ / μ)] = (b - √(μ * γ)) • ![1, -√(γ / μ)] := by
  have h1 : μ * √(γ / μ) = √(μ * γ) := by
    rw [show μ * γ = μ ^ 2 * (γ / μ) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hμ.le]
  have h2 : √(μ * γ) * √(γ / μ) = γ := by
    rw [← Real.sqrt_mul (by positivity), show μ * γ * (γ / μ) = γ ^ 2 by field_simp,
      Real.sqrt_sq hγ.le]
  constructor <;> ext i <;> fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [h1, h2]

end FilamentFracture
