/-
The operator-norm layer of

  Five-Dimensional Non-Normal Stability Operator with Gradient-Driven Interface Coupling for
  Zero-Precursor Filamentary Fractures (Jeromie Beasley, DOI 10.5281/zenodo.21184980).

`FilamentFracture.Basic` states the exact algebra of Secs. 2–5 with the closed forms
`resNorm`, `gain` and `ε_crit` written as formulae. This file does what `LIMITATIONS.md`
recorded as missing: it identifies those closed forms with the operator norms they are claimed
to be, so that the paper's inequalities are statements about linear maps and not about algebra.

* `opNorm_unipotent`: `‖[[1,s],[0,1]]‖ = (√(4+s²)+|s|)/2`, the singular-value computation
  everything else rests on.
* `resolvent_opNorm`: the resolvent of the interface block has norm `resNorm ‖μ‖ ‖z‖` — over `ℂ`,
  so the pseudospectrum statement is about the actual resolvent.
* `resNorm_lt_iff`, `resNorm_strictAntiOn`: each pseudospectrum is a disk: `resNorm m ρ < 1/ε`
  exactly when `ρ² > εm + ε²`, and `resNorm m ·` is strictly decreasing.
* `opNorm_J`, `opNorm_J_inv`: `ε_crit = 1/‖J⁻¹‖` is the smallest singular value, and
  `‖J‖ = (√(m²+4b²)+|m|)/2` the largest.
* `gain_opNorm`: `M(t) = ‖e^{−tJ}‖` for `t ≥ 0`, so the gain is the semigroup norm.
* `gain_peak`: the gain is maximised at `t* = √(m²−4b²)/(mb)`.
* `semigroup_bound`: `‖e^{−tJ_γ}‖ ≤ ‖e^{−tK₅(γ)}‖` for every `γ`. The interface block is
  `J_γ = [[b, μ], [γ, b]]`, not `J_0`; with `J_0` in place of `J_γ` the inequality is false
  (see `LIMITATIONS.md`).

Proved against Lean 4.33.1 with the Mathlib in this container; the repository's CI pins 4.34.1.
-/
import FilamentFracture.Basic

namespace FilamentFracture

open Matrix

/-- The operator norm of a real `2 × 2` matrix acting on `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def opNorm (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖

/-- The interface block `J = [[b, μ], [0, b]]`: the restriction of `K₅` to `span{e₂, e₅}` at
`γ = 0`. -/
def Jmat (b μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![b, μ; 0, b]

/-- The interface block `J_γ = [[b, μ], [γ, b]]`: the restriction of `K₅(γ)` to
`span{e₂, e₅}` for any `γ`. -/
def Jgam (b μ γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![b, μ; γ, b]

lemma opNorm_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : opNorm (c • A) = |c| * opNorm A := by
  unfold opNorm
  have h1 : (c • A).toEuclideanLin = c • A.toEuclideanLin := by ext x; simp
  have h2 : (c • A).toEuclideanLin.toContinuousLinearMap
      = c • A.toEuclideanLin.toContinuousLinearMap := by ext x; simp [h1]
  rw [h2, norm_smul, Real.norm_eq_abs]

/-! ### Unipotent -/

section Unipotent
open Real

set_option maxHeartbeats 800000

lemma unipotent_normSq_eq (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq x
  simp only [Fin.sum_univ_two] at h
  have h1 : ‖x 0‖ = |x 0| := Real.norm_eq_abs _
  have h2 : ‖x 1‖ = |x 1| := Real.norm_eq_abs _
  simp only [h1, h2, sq_abs] at h
  exact h

lemma unipotent_apply_zero (s : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
  (Matrix.toEuclideanLin !![(1:ℝ), s; 0, 1] x) 0 = x 0 + s * x 1 := by
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp

lemma unipotent_apply_one (s : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
  (Matrix.toEuclideanLin !![(1:ℝ), s; 0, 1] x) 1 = x 1 := by
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp

lemma unipotent_normSq_image (s : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
  ‖Matrix.toEuclideanLin !![(1:ℝ), s; 0, 1] x‖ ^ 2 = (x 0 + s * x 1) ^ 2 + (x 1) ^ 2 := by
  have h_norm : ∀ (y : EuclideanSpace ℝ (Fin 2)), ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := unipotent_normSq_eq
  rw [h_norm]
  have h0 := unipotent_apply_zero s x
  have h1 := unipotent_apply_one s x
  rw [h0, h1]

lemma unipotent_normSq_image_CLM (s : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
  ‖(Matrix.toEuclideanLin !![(1:ℝ), s; 0, 1]).toContinuousLinearMap x‖ ^ 2 = (x 0 + s * x 1) ^ 2 + (x 1) ^ 2 := by
  have h : (Matrix.toEuclideanLin !![(1:ℝ), s; 0, 1]).toContinuousLinearMap x = Matrix.toEuclideanLin !![(1:ℝ), s; 0, 1] x := rfl
  rw [h]
  exact unipotent_normSq_image s x

theorem opNorm_unipotent (s : ℝ) :
    opNorm !![(1 : ℝ), s; 0, 1] = (Real.sqrt (4 + s ^ 2) + |s|) / 2 := by
  unfold opNorm
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![(1:ℝ), s; 0, 1]
  let f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (Matrix.toEuclideanLin M).toContinuousLinearMap
  let S := Real.sqrt (4 + s ^ 2)
  let σ := (S + |s|) / 2
  have hS_sq : S ^ 2 = 4 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hS_nn : 0 ≤ S := Real.sqrt_nonneg _
  have h_abs_nn : 0 ≤ |s| := abs_nonneg _
  have hσ_nn : 0 ≤ σ := by positivity
  have hσ_sq : σ ^ 2 = (2 + s ^ 2 + |s| * S) / 2 := by
    have h2 : ((S + |s|) / 2) ^ 2 = (S ^ 2 + 2 * S * |s| + |s| ^ 2) / 4 := by ring
    have habs : |s| ^ 2 = s ^ 2 := sq_abs s
    calc σ ^ 2 = ((S + |s|) / 2) ^ 2 := rfl
         _ = (S ^ 2 + 2 * S * |s| + |s| ^ 2) / 4 := h2
         _ = (4 + s ^ 2 + 2 * S * |s| + s ^ 2) / 4 := by rw [hS_sq, habs]
         _ = (2 + s ^ 2 + |s| * S) / 2 := by ring
  let a := σ ^ 2 - 1
  let b := σ ^ 2 - 1 - s ^ 2
  have ha_eq : a = (s ^ 2 + |s| * S) / 2 := by simp only [a]; rw [hσ_sq]; ring
  have hb_eq : b = (|s| * S - s ^ 2) / 2 := by simp only [b]; rw [hσ_sq]; ring
  have ha_nn : 0 ≤ a := by rw [ha_eq]; positivity
  have hb_nn : 0 ≤ b := by
    rw [hb_eq]
    have h1 : (|s| * S) ^ 2 = s ^ 2 * (4 + s ^ 2) := by
      rw [mul_pow, sq_abs, hS_sq]
    have h2 : 0 ≤ |s| * S := mul_nonneg h_abs_nn hS_nn
    nlinarith [sq_nonneg (|s| * S - s ^ 2), sq_nonneg s, h1]
  have hab : a * b = s ^ 2 := by
    rw [ha_eq, hb_eq]
    nlinarith [sq_abs s, hS_sq]
  have h_psd_aux : ∀ p q : ℝ, a * (a * p ^ 2 - 2 * s * p * q + b * q ^ 2) = (a * p - s * q) ^ 2 := by
    intro p q
    have h : a * b = s ^ 2 := hab
    nlinarith
  have h_psd : ∀ p q : ℝ, 0 ≤ a * p ^ 2 - 2 * s * p * q + b * q ^ 2 := by
    intro p q
    by_cases hs : s = 0
    · have ha0 : a = 0 := by rw [ha_eq, hs]; simp
      have hb0 : b = 0 := by rw [hb_eq, hs]; simp
      rw [ha0, hb0, hs]
      simp
    · have ha_pos : 0 < a := by
        rw [ha_eq]
        have h_abs_pos : 0 < |s| := abs_pos.mpr hs
        have hS_pos : 0 < S := Real.sqrt_pos.mpr (by positivity)
        positivity
      have h_eq := h_psd_aux p q
      have h_sq : 0 ≤ (a * p - s * q) ^ 2 := sq_nonneg _
      have h_aE_nn : 0 ≤ a * (a * p ^ 2 - 2 * s * p * q + b * q ^ 2) := by rw [h_eq]; exact h_sq
      by_contra h_neg
      have h_neg' : a * p ^ 2 - 2 * s * p * q + b * q ^ 2 < 0 := by linarith
      have h_aE_neg : a * (a * p ^ 2 - 2 * s * p * q + b * q ^ 2) < 0 := mul_neg_of_pos_of_neg ha_pos h_neg'
      linarith
  have h_upper : ∀ x : EuclideanSpace ℝ (Fin 2), ‖f x‖ ≤ σ * ‖x‖ := by
    intro x
    have h_norm_x : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := unipotent_normSq_eq x
    have h_norm_fx : ‖f x‖ ^ 2 = (x 0 + s * x 1) ^ 2 + (x 1) ^ 2 := unipotent_normSq_image_CLM s x
    have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
    have hfx_nn : 0 ≤ ‖f x‖ := norm_nonneg _
    have h_sq_le : ‖f x‖ ^ 2 ≤ (σ * ‖x‖) ^ 2 := by
      have h1 : ‖f x‖ ^ 2 = (x 0 + s * x 1) ^ 2 + (x 1) ^ 2 := h_norm_fx
      have h2 : (σ * ‖x‖) ^ 2 = σ ^ 2 * ‖x‖ ^ 2 := by ring
      rw [h1, h2, h_norm_x]
      have h_expand : σ ^ 2 * ((x 0) ^ 2 + (x 1) ^ 2) - ((x 0 + s * x 1) ^ 2 + (x 1) ^ 2) =
        a * (x 0) ^ 2 - 2 * s * (x 0) * (x 1) + b * (x 1) ^ 2 := by
        simp only [a, b]
        ring
      have h_psd_inst := h_psd (x 0) (x 1)
      linarith
    have h1 : 0 ≤ σ * ‖x‖ := mul_nonneg hσ_nn hx_nn
    nlinarith [sq_nonneg (‖f x‖ - σ * ‖x‖), sq_nonneg (‖f x‖ + σ * ‖x‖)]
  have h_le : ‖f‖ ≤ σ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hσ_nn
    exact h_upper
  have h_ge : σ ≤ ‖f‖ := by
    by_cases hs : s = 0
    · have hσ1 : σ = 1 := by
        simp only [σ, S, hs, abs_zero, add_zero]
        have hS_eq : Real.sqrt (4 + (0:ℝ) ^ 2) = 2 := by
          have h4 : (4:ℝ) + (0:ℝ) ^ 2 = 4 := by ring
          rw [h4]
          have h2 : (4:ℝ) = 2 ^ 2 := by ring
          rw [h2, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
        rw [hS_eq]
        ring
      rw [hσ1]
      let x0 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
      have hx0_norm : ‖x0‖ = 1 := by
        have hsq : ‖x0‖ ^ 2 = 1 := by
          rw [unipotent_normSq_eq]
          have h0 : x0 0 = 1 := rfl
          have h1 : x0 1 = 0 := rfl
          rw [h0, h1]; ring
        have h_nn : 0 ≤ ‖x0‖ := norm_nonneg _
        nlinarith
      have hfx0 : ‖f x0‖ = 1 := by
        have hsq : ‖f x0‖ ^ 2 = 1 := by
          rw [unipotent_normSq_image_CLM]
          have h0 : x0 0 = 1 := rfl
          have h1 : x0 1 = 0 := rfl
          rw [h0, h1]; ring
        have h_nn : 0 ≤ ‖f x0‖ := norm_nonneg _
        nlinarith
      have h_le_op : ‖f x0‖ ≤ ‖f‖ * ‖x0‖ := f.le_opNorm x0
      rw [hfx0, hx0_norm, mul_one] at h_le_op
      linarith
    · have ha_pos : 0 < a := by
        rw [ha_eq]
        have h_abs_pos : 0 < |s| := abs_pos.mpr hs
        have hS_pos : 0 < S := Real.sqrt_pos.mpr (by positivity)
        positivity
      let x0 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![s, a]
      have hx0_0 : x0 0 = s := rfl
      have hx0_1 : x0 1 = a := rfl
      have hx0_norm_sq : ‖x0‖ ^ 2 = s ^ 2 + a ^ 2 := by
        rw [unipotent_normSq_eq, hx0_0, hx0_1]
      have hx0_pos : 0 < ‖x0‖ := by
        have h1 : 0 < ‖x0‖ ^ 2 := by rw [hx0_norm_sq]; positivity
        have h2 : 0 ≤ ‖x0‖ := norm_nonneg _
        nlinarith
      have hfx0_norm_sq : ‖f x0‖ ^ 2 = (σ * ‖x0‖) ^ 2 := by
        have h1 : ‖f x0‖ ^ 2 = (x0 0 + s * x0 1) ^ 2 + (x0 1) ^ 2 := unipotent_normSq_image_CLM s x0
        rw [h1, hx0_0, hx0_1, mul_pow, hx0_norm_sq]
        have h_psd_zero : a * s ^ 2 - 2 * s * s * a + b * a ^ 2 = 0 := by
          have h : a * b = s ^ 2 := hab
          nlinarith
        have h_expand : σ ^ 2 * (s ^ 2 + a ^ 2) - ((s + s * a) ^ 2 + a ^ 2) = a * s ^ 2 - 2 * s * s * a + b * a ^ 2 := by
          simp only [a, b]
          ring
        linarith
      have hfx0_nn : 0 ≤ ‖f x0‖ := norm_nonneg _
      have hσx_nn : 0 ≤ σ * ‖x0‖ := mul_nonneg hσ_nn (le_of_lt hx0_pos)
      have h_eq : ‖f x0‖ = σ * ‖x0‖ := by
        nlinarith [sq_nonneg (‖f x0‖ - σ * ‖x0‖), sq_nonneg (‖f x0‖ + σ * ‖x0‖)]
      have h_le_op : ‖f x0‖ ≤ ‖f‖ * ‖x0‖ := f.le_opNorm x0
      rw [h_eq] at h_le_op
      nlinarith
  have h_eq : ‖f‖ = σ := le_antisymm h_le h_ge
  exact h_eq


end Unipotent

/-! ### Resolvent -/

section Resolvent
open Real

set_option maxHeartbeats 800000

lemma resolvent_normSq_eq_complex (x : EuclideanSpace ℂ (Fin 2)) : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq x
  simp only [Fin.sum_univ_two] at h
  exact h

lemma resolvent_toEuclideanLin_apply_zero (s : ℂ) (x : EuclideanSpace ℂ (Fin 2)) :
  (Matrix.toEuclideanLin !![(1:ℂ), s; 0, 1] x) 0 = x 0 + s * x 1 := by
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp

lemma resolvent_toEuclideanLin_apply_one (s : ℂ) (x : EuclideanSpace ℂ (Fin 2)) :
  (Matrix.toEuclideanLin !![(1:ℂ), s; 0, 1] x) 1 = x 1 := by
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp

lemma resolvent_normSq_image_complex (s : ℂ) (x : EuclideanSpace ℂ (Fin 2)) :
  ‖Matrix.toEuclideanLin !![(1:ℂ), s; 0, 1] x‖ ^ 2 = ‖x 0 + s * x 1‖ ^ 2 + ‖x 1‖ ^ 2 := by
  have h_norm : ∀ (y : EuclideanSpace ℂ (Fin 2)), ‖y‖ ^ 2 = ‖y 0‖ ^ 2 + ‖y 1‖ ^ 2 := resolvent_normSq_eq_complex
  rw [h_norm]
  have h0 := resolvent_toEuclideanLin_apply_zero s x
  have h1 := resolvent_toEuclideanLin_apply_one s x
  rw [h0, h1]

lemma resolvent_normSq_image_CLM_complex (s : ℂ) (x : EuclideanSpace ℂ (Fin 2)) :
  ‖(Matrix.toEuclideanLin !![(1:ℂ), s; 0, 1]).toContinuousLinearMap x‖ ^ 2 = ‖x 0 + s * x 1‖ ^ 2 + ‖x 1‖ ^ 2 := by
  have h : (Matrix.toEuclideanLin !![(1:ℂ), s; 0, 1]).toContinuousLinearMap x = Matrix.toEuclideanLin !![(1:ℂ), s; 0, 1] x := rfl
  rw [h]
  exact resolvent_normSq_image_complex s x

-- Main theorem: complex unipotent norm
theorem complex_opNorm_unipotent (s : ℂ) :
    ‖(Matrix.toEuclideanLin !![(1:ℂ), s; 0, 1]).toContinuousLinearMap‖ = (Real.sqrt (4 + ‖s‖ ^ 2) + ‖s‖) / 2 := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![(1:ℂ), s; 0, 1]
  let f : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    (Matrix.toEuclideanLin M).toContinuousLinearMap
  let S := Real.sqrt (4 + ‖s‖ ^ 2)
  let σ := (S + ‖s‖) / 2
  have hS_sq : S ^ 2 = 4 + ‖s‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hS_nn : 0 ≤ S := Real.sqrt_nonneg _
  have hs_nn : 0 ≤ ‖s‖ := norm_nonneg _
  have hσ_nn : 0 ≤ σ := by positivity
  have hσ_sq : σ ^ 2 = (2 + ‖s‖ ^ 2 + ‖s‖ * S) / 2 := by
    have h2 : ((S + ‖s‖) / 2) ^ 2 = (S ^ 2 + 2 * S * ‖s‖ + ‖s‖ ^ 2) / 4 := by ring
    calc σ ^ 2 = ((S + ‖s‖) / 2) ^ 2 := rfl
         _ = (S ^ 2 + 2 * S * ‖s‖ + ‖s‖ ^ 2) / 4 := h2
         _ = (4 + ‖s‖ ^ 2 + 2 * S * ‖s‖ + ‖s‖ ^ 2) / 4 := by rw [hS_sq]
         _ = (2 + ‖s‖ ^ 2 + ‖s‖ * S) / 2 := by ring
  let a := σ ^ 2 - 1
  let b := σ ^ 2 - 1 - ‖s‖ ^ 2
  have hs' : ‖s‖ ^ 2 = (‖s‖ : ℝ) ^ 2 := rfl
  have ha_eq : a = (‖s‖ ^ 2 + ‖s‖ * S) / 2 := by simp only [a]; rw [hσ_sq]; ring
  have hb_eq : b = (‖s‖ * S - ‖s‖ ^ 2) / 2 := by simp only [b]; rw [hσ_sq]; ring
  have ha_nn : 0 ≤ a := by rw [ha_eq]; positivity
  have hb_nn : 0 ≤ b := by
    rw [hb_eq]
    have h1 : (‖s‖ * S) ^ 2 = ‖s‖ ^ 2 * (4 + ‖s‖ ^ 2) := by
      rw [mul_pow, hS_sq]
    have h2 : 0 ≤ ‖s‖ * S := mul_nonneg hs_nn hS_nn
    nlinarith [sq_nonneg (‖s‖ * S - ‖s‖ ^ 2), sq_nonneg (‖s‖ : ℝ), h1]
  have hab : a * b = ‖s‖ ^ 2 := by
    rw [ha_eq, hb_eq]
    nlinarith
  have h_psd_aux : ∀ p q : ℝ, a * (a * p ^ 2 - 2 * ‖s‖ * p * q + b * q ^ 2) = (a * p - ‖s‖ * q) ^ 2 := by
    intro p q
    have h : a * b = ‖s‖ ^ 2 := hab
    nlinarith
  have h_psd : ∀ p q : ℝ, 0 ≤ a * p ^ 2 - 2 * ‖s‖ * p * q + b * q ^ 2 := by
    intro p q
    by_cases hs : s = 0
    · have hnorm_zero : ‖s‖ = 0 := by rw [hs, norm_zero]
      have ha0 : a = 0 := by rw [ha_eq, hnorm_zero]; simp
      have hb0 : b = 0 := by rw [hb_eq, hnorm_zero]; simp
      rw [ha0, hb0, hnorm_zero]
      simp
    · have ha_pos : 0 < a := by
        rw [ha_eq]
        have h_norm_pos : 0 < ‖s‖ := by
          rw [norm_pos_iff]
          exact hs
        have hS_pos : 0 < S := Real.sqrt_pos.mpr (by positivity)
        positivity
      have h_eq := h_psd_aux p q
      have h_sq : 0 ≤ (a * p - ‖s‖ * q) ^ 2 := sq_nonneg _
      have h_aE_nn : 0 ≤ a * (a * p ^ 2 - 2 * ‖s‖ * p * q + b * q ^ 2) := by rw [h_eq]; exact h_sq
      by_contra h_neg
      have h_neg' : a * p ^ 2 - 2 * ‖s‖ * p * q + b * q ^ 2 < 0 := by linarith
      have h_aE_neg : a * (a * p ^ 2 - 2 * ‖s‖ * p * q + b * q ^ 2) < 0 := mul_neg_of_pos_of_neg ha_pos h_neg'
      linarith
  -- Upper bound
  have h_upper : ∀ x : EuclideanSpace ℂ (Fin 2), ‖f x‖ ≤ σ * ‖x‖ := by
    intro x
    have h_norm_x : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := resolvent_normSq_eq_complex x
    have h_norm_fx : ‖f x‖ ^ 2 = ‖x 0 + s * x 1‖ ^ 2 + ‖x 1‖ ^ 2 := resolvent_normSq_image_CLM_complex s x
    have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
    have hfx_nn : 0 ≤ ‖f x‖ := norm_nonneg _
    -- bound ‖x0 + s x1‖ ≤ ‖x0‖ + ‖s‖‖x1‖
    have h_tri : ‖x 0 + s * x 1‖ ≤ ‖x 0‖ + ‖s‖ * ‖x 1‖ := by
      calc ‖x 0 + s * x 1‖ ≤ ‖x 0‖ + ‖s * x 1‖ := norm_add_le _ _
        _ = ‖x 0‖ + ‖s‖ * ‖x 1‖ := by rw [norm_mul]
    have h_tri_nn : 0 ≤ ‖x 0‖ + ‖s‖ * ‖x 1‖ := by positivity
    have h_le_sq : ‖x 0 + s * x 1‖ ^ 2 ≤ (‖x 0‖ + ‖s‖ * ‖x 1‖) ^ 2 := by
      nlinarith [h_tri, sq_nonneg (‖x 0 + s * x 1‖), sq_nonneg (‖x 0‖ + ‖s‖ * ‖x 1‖), norm_nonneg (x 0 + s * x 1)]
    have h_sq_le : ‖f x‖ ^ 2 ≤ (σ * ‖x‖) ^ 2 := by
      have h1 : ‖f x‖ ^ 2 = ‖x 0 + s * x 1‖ ^ 2 + ‖x 1‖ ^ 2 := h_norm_fx
      have h2 : (σ * ‖x‖) ^ 2 = σ ^ 2 * ‖x‖ ^ 2 := by ring
      rw [h1, h2, h_norm_x]
      have h_expand : σ ^ 2 * (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2) - ((‖x 0‖ + ‖s‖ * ‖x 1‖) ^ 2 + ‖x 1‖ ^ 2) =
        a * ‖x 0‖ ^ 2 - 2 * ‖s‖ * ‖x 0‖ * ‖x 1‖ + b * ‖x 1‖ ^ 2 := by
        simp only [a, b]
        ring
      have h_psd_inst := h_psd ‖x 0‖ ‖x 1‖
      have h_mid : ‖x 0 + s * x 1‖ ^ 2 + ‖x 1‖ ^ 2 ≤ (‖x 0‖ + ‖s‖ * ‖x 1‖) ^ 2 + ‖x 1‖ ^ 2 := by linarith
      linarith
    have h1 : 0 ≤ σ * ‖x‖ := mul_nonneg hσ_nn hx_nn
    nlinarith [sq_nonneg (‖f x‖ - σ * ‖x‖), sq_nonneg (‖f x‖ + σ * ‖x‖)]
  have h_le : ‖f‖ ≤ σ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hσ_nn
    exact h_upper
  -- Lower bound
  have h_ge : σ ≤ ‖f‖ := by
    by_cases hs : s = 0
    · have hnorm_zero : ‖s‖ = 0 := by rw [hs, norm_zero]
      have hσ1 : σ = 1 := by
        simp only [σ, S, hnorm_zero, add_zero]
        have hS_eq : Real.sqrt (4 + (0:ℝ) ^ 2) = 2 := by
          have h4 : (4:ℝ) + (0:ℝ) ^ 2 = 4 := by ring
          rw [h4]
          have h2 : (4:ℝ) = 2 ^ 2 := by ring
          rw [h2, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
        rw [hS_eq]
        ring
      rw [hσ1]
      let x0 : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]
      have hx0_norm : ‖x0‖ = 1 := by
        have hsq : ‖x0‖ ^ 2 = 1 := by
          rw [resolvent_normSq_eq_complex]
          have h0 : x0 0 = 1 := rfl
          have h1 : x0 1 = 0 := rfl
          rw [h0, h1]
          simp
        have h_nn : 0 ≤ ‖x0‖ := norm_nonneg _
        nlinarith
      have hfx0 : ‖f x0‖ = 1 := by
        have hsq : ‖f x0‖ ^ 2 = 1 := by
          rw [resolvent_normSq_image_CLM_complex]
          have h0 : x0 0 = 1 := rfl
          have h1 : x0 1 = 0 := rfl
          rw [h0, h1]
          simp [hs]
        have h_nn : 0 ≤ ‖f x0‖ := norm_nonneg _
        nlinarith
      have h_le_op : ‖f x0‖ ≤ ‖f‖ * ‖x0‖ := f.le_opNorm x0
      rw [hfx0, hx0_norm, mul_one] at h_le_op
      linarith
    · have ha_pos : 0 < a := by
        rw [ha_eq]
        have h_norm_pos : 0 < ‖s‖ := by
          rw [norm_pos_iff]; exact hs
        have hS_pos : 0 < S := Real.sqrt_pos.mpr (by positivity)
        positivity
      have ha_nn' : 0 ≤ a := le_of_lt ha_pos
      -- construct witness x0 = ![s, a]
      let x0 : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![s, (a:ℂ)]
      have hx0_0 : x0 0 = s := rfl
      have hx0_1 : x0 1 = (a:ℂ) := rfl
      have h_norm_a : ‖(a:ℂ)‖ = a := by
        rw [Complex.norm_real]
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg ha_nn']
      have hx0_norm_sq : ‖x0‖ ^ 2 = ‖s‖ ^ 2 + a ^ 2 := by
        rw [resolvent_normSq_eq_complex, hx0_0, hx0_1, h_norm_a]
      have hx0_pos : 0 < ‖x0‖ := by
        have h1 : 0 < ‖x0‖ ^ 2 := by rw [hx0_norm_sq]; positivity
        have h2 : 0 ≤ ‖x0‖ := norm_nonneg _
        nlinarith
      have hfx0_norm_sq : ‖f x0‖ ^ 2 = (σ * ‖x0‖) ^ 2 := by
        have h1 : ‖f x0‖ ^ 2 = ‖x0 0 + s * x0 1‖ ^ 2 + ‖x0 1‖ ^ 2 := resolvent_normSq_image_CLM_complex s x0
        rw [h1, hx0_0, hx0_1, h_norm_a, mul_pow, hx0_norm_sq]
        -- compute ‖ s + s * a ‖ = ‖s‖ * (1+a)
        have h_s_a : s * (a:ℂ) = (a:ℂ) * s := by ring
        have h_norm_s_a : ‖s + s * (a:ℂ)‖ = ‖s‖ * (1 + a) := by
          have h_eq : s + s * (a:ℂ) = (1 + (a:ℂ)) * s := by ring
          rw [h_eq, norm_mul]
          have h_norm_one_add : ‖(1 + (a:ℂ) : ℂ)‖ = 1 + a := by
            have h1 : (1 + (a:ℂ) : ℂ) = ((1 + a : ℝ) : ℂ) := by push_cast; ring
            rw [h1, Complex.norm_real]
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          rw [h_norm_one_add, mul_comm]
        rw [h_norm_s_a]
        have h_psd_zero : a * ‖s‖ ^ 2 - 2 * ‖s‖ * ‖s‖ * a + b * a ^ 2 = 0 := by
          have h : a * b = ‖s‖ ^ 2 := hab
          nlinarith
        have h_expand : σ ^ 2 * (‖s‖ ^ 2 + a ^ 2) - ((‖s‖ * (1 + a)) ^ 2 + a ^ 2) = a * ‖s‖ ^ 2 - 2 * ‖s‖ * ‖s‖ * a + b * a ^ 2 := by
          simp only [a, b]
          ring
        linarith
      have hfx0_nn : 0 ≤ ‖f x0‖ := norm_nonneg _
      have hσx_nn : 0 ≤ σ * ‖x0‖ := mul_nonneg hσ_nn (le_of_lt hx0_pos)
      have h_eq : ‖f x0‖ = σ * ‖x0‖ := by
        nlinarith [sq_nonneg (‖f x0‖ - σ * ‖x0‖), sq_nonneg (‖f x0‖ + σ * ‖x0‖)]
      have h_le_op : ‖f x0‖ ≤ ‖f‖ * ‖x0‖ := f.le_opNorm x0
      rw [h_eq] at h_le_op
      nlinarith
  have h_eq : ‖f‖ = σ := le_antisymm h_le h_ge
  exact h_eq


-- Resolvent scalar identity
lemma resolvent_resNorm_eq (m ρ : ℝ) (hρ : 0 < ρ) :
  (Real.sqrt (4 + (m / ρ) ^ 2) + m / ρ) / 2 / ρ = resNorm m ρ := by
  unfold resNorm
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ
  have hρ2_pos : 0 < ρ ^ 2 := by positivity
  have h_eq1 : 4 + (m / ρ) ^ 2 = (4 * ρ ^ 2 + m ^ 2) / ρ ^ 2 := by
    field_simp
  have h_sqrt : Real.sqrt (4 + (m / ρ) ^ 2) = Real.sqrt (4 * ρ ^ 2 + m ^ 2) / ρ := by
    rw [h_eq1, Real.sqrt_div (by positivity)]
    rw [Real.sqrt_sq (le_of_lt hρ)]
  rw [h_sqrt]
  field_simp

-- Matrix scaling lemma
lemma resolvent_matrix_eq (μ z : ℂ) : !![z⁻¹, μ * z⁻¹ ^ 2; 0, z⁻¹] = z⁻¹ • !![(1:ℂ), μ * z⁻¹; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> ring

lemma resolvent_toEuclideanLin_smul (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
  (c • A).toEuclideanLin = c • A.toEuclideanLin := by
  ext x; simp

lemma resolvent_toContinuousLinearMap_smul (c : ℂ) (f : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)) :
  (c • f).toContinuousLinearMap = c • f.toContinuousLinearMap := by simp

theorem resolvent_opNorm (μ z : ℂ) (hz : z ≠ 0) :
    ‖(Matrix.toEuclideanLin !![z⁻¹, μ * z⁻¹ ^ 2; 0, z⁻¹]).toContinuousLinearMap‖ = resNorm ‖μ‖ ‖z‖ := by
  have hρ_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hρ_ne : (‖z‖ : ℝ) ≠ 0 := ne_of_gt hρ_pos
  have hR : !![z⁻¹, μ * z⁻¹ ^ 2; 0, z⁻¹] = z⁻¹ • !![(1:ℂ), μ * z⁻¹; 0, 1] := resolvent_matrix_eq μ z
  have h_s_eq : ‖μ * z⁻¹‖ = ‖μ‖ / ‖z‖ := by
    rw [norm_mul, norm_inv]
    have h : ‖z‖⁻¹ = 1 / ‖z‖ := by rw [inv_eq_one_div]
    rw [h]
    ring
    -- alternative: field_simp
  have h_norm_smul : ‖(Matrix.toEuclideanLin !![z⁻¹, μ * z⁻¹ ^ 2; 0, z⁻¹]).toContinuousLinearMap‖ =
    ‖z⁻¹‖ * ‖(Matrix.toEuclideanLin !![(1:ℂ), μ * z⁻¹; 0, 1]).toContinuousLinearMap‖ := by
    rw [hR, resolvent_toEuclideanLin_smul, resolvent_toContinuousLinearMap_smul, norm_smul]
  rw [h_norm_smul]
  have h_U : ‖(Matrix.toEuclideanLin !![(1:ℂ), μ * z⁻¹; 0, 1]).toContinuousLinearMap‖ =
    (Real.sqrt (4 + ‖μ * z⁻¹‖ ^ 2) + ‖μ * z⁻¹‖) / 2 := complex_opNorm_unipotent (μ * z⁻¹)
  rw [h_U, h_s_eq]
  have h_norm_inv : ‖z⁻¹‖ = (‖z‖)⁻¹ := norm_inv z
  rw [h_norm_inv]
  have h_inv_eq : (‖z‖ : ℝ)⁻¹ = 1 / ‖z‖ := by rw [inv_eq_one_div]
  rw [h_inv_eq]
  have h_final : 1 / ‖z‖ * ((Real.sqrt (4 + (‖μ‖ / ‖z‖) ^ 2) + ‖μ‖ / ‖z‖) / 2) = resNorm ‖μ‖ ‖z‖ := by
    have h1 : 1 / ‖z‖ * ((Real.sqrt (4 + (‖μ‖ / ‖z‖) ^ 2) + ‖μ‖ / ‖z‖) / 2) =
      (Real.sqrt (4 + (‖μ‖ / ‖z‖) ^ 2) + ‖μ‖ / ‖z‖) / 2 / ‖z‖ := by ring
    rw [h1]
    exact resolvent_resNorm_eq ‖μ‖ ‖z‖ hρ_pos
  exact h_final


end Resolvent

/-! ### Pseudospectrum -/

section Pseudospectrum
open Real Set

private lemma disk_S_nonneg (m ρ : ℝ) : 0 ≤ √(4 * ρ ^ 2 + m ^ 2) := Real.sqrt_nonneg _
private lemma disk_S_sq (m ρ : ℝ) : (√(4 * ρ ^ 2 + m ^ 2)) ^ 2 = 4 * ρ ^ 2 + m ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem resNorm_lt_iff (m ε ρ : ℝ) (_hm : 0 ≤ m) (hε : 0 < ε) (hρ : 0 < ρ) :
    resNorm m ρ < 1 / ε ↔ ε * m + ε ^ 2 < ρ ^ 2 := by
  unfold resNorm
  have h2ρ2 : 0 < 2 * ρ ^ 2 := by positivity
  let S := √(4 * ρ ^ 2 + m ^ 2)
  have hS_nn : 0 ≤ S := disk_S_nonneg m ρ
  have hS_sq : S ^ 2 = 4 * ρ ^ 2 + m ^ 2 := disk_S_sq m ρ
  have h_equiv1 : (S + m) / (2 * ρ ^ 2) < 1 / ε ↔ (S + m) * ε < 2 * ρ ^ 2 := by
    have h : (S + m) / (2 * ρ ^ 2) < 1 / ε ↔ (S + m) * ε < 1 * (2 * ρ ^ 2) := by
      apply div_lt_div_iff₀ h2ρ2 hε
    simp only [one_mul] at h
    exact h
  have h_equiv1' : (S + m) / (2 * ρ ^ 2) < 1 / ε ↔ ε * (S + m) < 2 * ρ ^ 2 := by
    rw [h_equiv1, mul_comm]
  rw [h_equiv1']
  have h_equiv2 : ε * (S + m) < 2 * ρ ^ 2 ↔ ε * S < 2 * ρ ^ 2 - ε * m := by
    constructor <;> intro h <;> nlinarith
  rw [h_equiv2]
  constructor
  · intro h
    have h_pos : 0 < 2 * ρ ^ 2 - ε * m := by linarith [mul_nonneg (le_of_lt hε) hS_nn]
    have h_pos2 : 0 ≤ 2 * ρ ^ 2 - ε * m := le_of_lt h_pos
    have h_sq_lt : (ε * S) ^ 2 < (2 * ρ ^ 2 - ε * m) ^ 2 := by
      apply sq_lt_sq₀ (by positivity) h_pos2 |>.mpr h
    have h_expand_left : (ε * S) ^ 2 = ε ^ 2 * (4 * ρ ^ 2 + m ^ 2) := by
      rw [mul_pow, hS_sq]
    have h_expand_right : (2 * ρ ^ 2 - ε * m) ^ 2 = 4 * ρ ^ 4 - 4 * ε * m * ρ ^ 2 + ε ^ 2 * m ^ 2 := by ring
    rw [h_expand_left] at h_sq_lt
    rw [h_expand_right] at h_sq_lt
    nlinarith
  · intro h
    have h_pos : 0 < 2 * ρ ^ 2 - ε * m := by nlinarith
    have h_pos2 : 0 ≤ 2 * ρ ^ 2 - ε * m := le_of_lt h_pos
    have h_expand_left : (ε * S) ^ 2 = ε ^ 2 * (4 * ρ ^ 2 + m ^ 2) := by
      rw [mul_pow, hS_sq]
    have h_expand_right : (2 * ρ ^ 2 - ε * m) ^ 2 = 4 * ρ ^ 4 - 4 * ε * m * ρ ^ 2 + ε ^ 2 * m ^ 2 := by ring
    have h_sq_lt : (ε * S) ^ 2 < (2 * ρ ^ 2 - ε * m) ^ 2 := by
      rw [h_expand_left, h_expand_right]
      nlinarith
    have h_le : 0 ≤ ε * S := by positivity
    exact (sq_lt_sq₀ h_le h_pos2).mp h_sq_lt

private lemma disk_epsilon_eq (m ρ : ℝ) (hm : 0 ≤ m) (hρ : 0 < ρ) :
    let S := √(m ^ 2 + 4 * ρ ^ 2)
    let ε := (S - m) / 2
    0 < ε ∧ ε * m + ε ^ 2 = ρ ^ 2 := by
  intro S ε
  have h_sum_nn : 0 ≤ m ^ 2 + 4 * ρ ^ 2 := by positivity
  have hS_sq : S ^ 2 = m ^ 2 + 4 * ρ ^ 2 := Real.sq_sqrt h_sum_nn
  have hS_gt_m : m < S := by
    have h_pos : 0 < 4 * ρ ^ 2 := by positivity
    have h1 : m ^ 2 < S ^ 2 := by linarith
    have hS_nn : 0 ≤ S := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (S - m), sq_nonneg (S + m)]
  have hε_pos : 0 < ε := by show 0 < (S - m)/2; linarith
  constructor
  · exact hε_pos
  · show ε * m + ε ^ 2 = ρ ^ 2
    have h_prod : (S - m)/2 * ((S + m)/2) = ρ ^ 2 := by
      have h : (S - m) * (S + m) = S ^ 2 - m ^ 2 := by ring
      have h2 : S ^ 2 - m ^ 2 = 4 * ρ ^ 2 := by linarith
      have h3 : (S - m)/2 * ((S + m)/2) = ((S - m)*(S+m))/4 := by ring
      rw [h3, h, h2]; ring
    have h_eq : ε * m + ε ^ 2 = ε * (m + ε) := by ring
    rw [h_eq]
    have h_mε : m + ε = (S + m)/2 := by show m + (S - m)/2 = (S+m)/2; ring
    rw [h_mε]
    exact h_prod

private lemma disk_resNorm_at_epsilon (m ρ : ℝ) (hm : 0 ≤ m) (hρ : 0 < ρ) :
    let S := √(m ^ 2 + 4 * ρ ^ 2)
    let ε := (S - m) / 2
    resNorm m ρ = 1 / ε := by
  intro S ε
  have hε_pos : 0 < ε := (disk_epsilon_eq m ρ hm hρ).1
  have h_sum_nn : 0 ≤ m ^ 2 + 4 * ρ ^ 2 := by positivity
  have hS_sq : S ^ 2 = m ^ 2 + 4 * ρ ^ 2 := Real.sq_sqrt h_sum_nn
  have hS_eq : S = √(4 * ρ ^ 2 + m ^ 2) := by
    show √(m ^ 2 + 4 * ρ ^ 2) = √(4 * ρ ^ 2 + m ^ 2)
    rw [show m ^ 2 + 4 * ρ ^ 2 = 4 * ρ ^ 2 + m ^ 2 by ring]
  have hρ2_pos : 0 < (2 : ℝ) * ρ ^ 2 := by positivity
  have hρ2_ne : (2 : ℝ) * ρ ^ 2 ≠ 0 := ne_of_gt hρ2_pos
  have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
  have h_key : (S + m) * ε = 2 * ρ ^ 2 := by
    show (S + m) * ((S - m)/2) = 2 * ρ ^ 2
    have h : (S+m)*((S-m)/2) = ((S-m)*(S+m))/2 := by ring
    rw [h]
    have h2 : (S - m)*(S+m) = S ^ 2 - m ^ 2 := by ring
    rw [h2, hS_sq]; ring
  unfold resNorm
  rw [← hS_eq]
  have h_goal : (S + m) / (2 * ρ ^ 2) = 1 / ε := by
    rw [div_eq_div_iff hρ2_ne hε_ne]
    -- gives (S+m)*ε = 2ρ²*1
    have : (S + m) * ε = 1 * (2 * ρ ^ 2) := by linarith
    -- need to rewrite to match exact form: a*d = c*b where c=1
    -- div_eq_div_iff gives a*d = c*b i.e. (S+m)*ε = 1*(2ρ²)
    -- our hypothesis is (S+m)*ε =2ρ², which equals 1*2ρ²
    linarith
  exact h_goal

theorem resNorm_strictAntiOn (m : ℝ) (hm : 0 ≤ m) :
    StrictAntiOn (resNorm m) (Set.Ioi 0) := by
  intro ρ₁ hρ₁ ρ₂ hρ₂ h_lt
  simp only [Set.mem_Ioi] at hρ₁ hρ₂
  have hρ₁_pos : 0 < ρ₁ := hρ₁
  have hρ₂_pos : 0 < ρ₂ := hρ₂
  let S₁ := √(m ^ 2 + 4 * ρ₁ ^ 2)
  let ε₁ := (S₁ - m) / 2
  have hε₁_pos : 0 < ε₁ := (disk_epsilon_eq m ρ₁ hm hρ₁_pos).1
  have hε₁_eq : ε₁ * m + ε₁ ^ 2 = ρ₁ ^ 2 := (disk_epsilon_eq m ρ₁ hm hρ₁_pos).2
  have h_res_eq : resNorm m ρ₁ = 1 / ε₁ := disk_resNorm_at_epsilon m ρ₁ hm hρ₁_pos
  have h_lt_sq : ρ₁ ^ 2 < ρ₂ ^ 2 := by nlinarith [sq_nonneg (ρ₂ - ρ₁), sq_nonneg (ρ₂ + ρ₁)]
  have h_ineq : ε₁ * m + ε₁ ^ 2 < ρ₂ ^ 2 := by linarith
  have h_lt_iff : resNorm m ρ₂ < 1 / ε₁ := (resNorm_lt_iff m ε₁ ρ₂ hm hε₁_pos hρ₂_pos).mpr h_ineq
  calc resNorm m ρ₂ < 1 / ε₁ := h_lt_iff
    _ = resNorm m ρ₁ := h_res_eq.symm


end Pseudospectrum

/-! ### SingularValues -/

section SingularValues
open Real

set_option maxHeartbeats 800000

lemma sigma_J_smul_eq (b m : ℝ) (hb : b ≠ 0) : Jmat b m = b • !![(1:ℝ), m / b; 0, 1] := by
  unfold Jmat
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> field_simp

noncomputable def sigma_JmatInv (b m : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![b⁻¹, -(m / b ^ 2); 0, b⁻¹]

lemma sigma_Jmat_mul_JmatInv (b m : ℝ) (hb : b ≠ 0) : Jmat b m * sigma_JmatInv b m = 1 := by
  unfold Jmat sigma_JmatInv
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; field_simp; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; field_simp

lemma sigma_Jmat_inv_eq (b m : ℝ) (hb : b ≠ 0) : (Jmat b m)⁻¹ = sigma_JmatInv b m := by
  apply Matrix.inv_eq_right_inv
  exact sigma_Jmat_mul_JmatInv b m hb

lemma sigma_JmatInv_smul_eq (b m : ℝ) (hb : b ≠ 0) : sigma_JmatInv b m = b⁻¹ • !![(1:ℝ), -(m / b); 0, 1] := by
  unfold sigma_JmatInv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> field_simp

-- D6 theorems (using Jmat abbreviation; Jmat b m = !![b, m; 0, b] definitionally)

theorem opNorm_J (b m : ℝ) (hb : 0 < b) :
    opNorm (Jmat b m) = (Real.sqrt (m ^ 2 + 4 * b ^ 2) + |m|) / 2 := by
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hb_pos : 0 ≤ b := le_of_lt hb
  have h_eq : Jmat b m = b • !![(1:ℝ), m / b; 0, 1] := sigma_J_smul_eq b m hb_ne
  rw [h_eq, opNorm_smul, abs_of_pos hb, opNorm_unipotent]
  have h_abs_div : |m / b| = |m| / b := by rw [abs_div, abs_of_pos hb]
  rw [h_abs_div]
  have h_sqrt_mul : b * Real.sqrt (4 + (m / b) ^ 2) = Real.sqrt (m ^ 2 + 4 * b ^ 2) := by
    have h_inner : b ^ 2 * (4 + (m / b) ^ 2) = m ^ 2 + 4 * b ^ 2 := by field_simp; ring
    have h_sqrt_b2 : Real.sqrt (b ^ 2 * (4 + (m / b) ^ 2)) = Real.sqrt (m ^ 2 + 4 * b ^ 2) := by rw [h_inner]
    have h_b_sqrt : b * Real.sqrt (4 + (m / b) ^ 2) = Real.sqrt (b ^ 2) * Real.sqrt (4 + (m / b) ^ 2) := by
      rw [Real.sqrt_sq hb_pos]
    rw [h_b_sqrt, ← Real.sqrt_mul (by positivity : 0 ≤ b ^ 2), h_sqrt_b2]
  have h_calc : b * ((Real.sqrt (4 + (m / b) ^ 2) + |m| / b) / 2) = (Real.sqrt (m ^ 2 + 4 * b ^ 2) + |m|) / 2 := by
    have h1 : b * ((Real.sqrt (4 + (m / b) ^ 2) + |m| / b) / 2) = (b * Real.sqrt (4 + (m / b) ^ 2) + b * (|m| / b)) / 2 := by ring
    rw [h1, h_sqrt_mul]
    have h2 : b * (|m| / b) = |m| := by field_simp
    rw [h2]
  exact h_calc

theorem opNorm_J_inv (b m : ℝ) (hb : 0 < b) :
    opNorm (Jmat b m)⁻¹ = 1 / ((Real.sqrt (m ^ 2 + 4 * b ^ 2) - |m|) / 2) := by
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hb_pos : 0 ≤ b := le_of_lt hb
  rw [sigma_Jmat_inv_eq b m hb_ne, sigma_JmatInv_smul_eq b m hb_ne, opNorm_smul]
  have hb_inv_pos : 0 < b⁻¹ := inv_pos.mpr hb
  rw [abs_of_pos hb_inv_pos, opNorm_unipotent]
  have h_abs_div : |(-(m / b))| = |m| / b := by rw [abs_neg, abs_div, abs_of_pos hb]
  rw [h_abs_div]
  have h_neg_sq : (-(m / b)) ^ 2 = (m / b) ^ 2 := by ring
  have h_sqrt_neg : Real.sqrt (4 + (-(m / b)) ^ 2) = Real.sqrt (4 + (m / b) ^ 2) := by rw [h_neg_sq]
  rw [h_sqrt_neg]
  have h_sqrt_mul : b * Real.sqrt (4 + (m / b) ^ 2) = Real.sqrt (m ^ 2 + 4 * b ^ 2) := by
    have h_inner : b ^ 2 * (4 + (m / b) ^ 2) = m ^ 2 + 4 * b ^ 2 := by field_simp; ring
    have h_sqrt_b2 : Real.sqrt (b ^ 2 * (4 + (m / b) ^ 2)) = Real.sqrt (m ^ 2 + 4 * b ^ 2) := by rw [h_inner]
    have h_b_sqrt : b * Real.sqrt (4 + (m / b) ^ 2) = Real.sqrt (b ^ 2) * Real.sqrt (4 + (m / b) ^ 2) := by
      rw [Real.sqrt_sq hb_pos]
    rw [h_b_sqrt, ← Real.sqrt_mul (by positivity : 0 ≤ b ^ 2), h_sqrt_b2]
  have h_sqrt_div : Real.sqrt (4 + (m / b) ^ 2) = Real.sqrt (m ^ 2 + 4 * b ^ 2) / b := by
    have h1 : b * Real.sqrt (4 + (m / b) ^ 2) = Real.sqrt (m ^ 2 + 4 * b ^ 2) := h_sqrt_mul
    have h2 : Real.sqrt (4 + (m / b) ^ 2) = Real.sqrt (m ^ 2 + 4 * b ^ 2) / b := by
      field_simp at h1 ⊢
      linarith
    exact h2
  have h_LHS : b⁻¹ * ((Real.sqrt (4 + (m / b) ^ 2) + |m| / b) / 2) = (Real.sqrt (m ^ 2 + 4 * b ^ 2) + |m|) / (2 * b ^ 2) := by
    rw [h_sqrt_div]
    field_simp
  rw [h_LHS]
  have hS_gt : Real.sqrt (m ^ 2 + 4 * b ^ 2) > |m| := by
    have h1 : m ^ 2 < m ^ 2 + 4 * b ^ 2 := by nlinarith [sq_nonneg b, sq_nonneg m]
    have h2 : 0 ≤ m ^ 2 := sq_nonneg m
    have h_eq : Real.sqrt (m ^ 2) = |m| := Real.sqrt_sq_eq_abs m
    have h_lt : Real.sqrt (m ^ 2) < Real.sqrt (m ^ 2 + 4 * b ^ 2) := Real.sqrt_lt_sqrt h2 h1
    linarith
  have hS_sub_pos : 0 < Real.sqrt (m ^ 2 + 4 * b ^ 2) - |m| := by linarith
  have h_b2_pos : 0 < b ^ 2 := by positivity
  have h_eq : (Real.sqrt (m ^ 2 + 4 * b ^ 2) + |m|) * (Real.sqrt (m ^ 2 + 4 * b ^ 2) - |m|) = 4 * b ^ 2 := by
    have h_sq : Real.sqrt (m ^ 2 + 4 * b ^ 2) ^ 2 = m ^ 2 + 4 * b ^ 2 := Real.sq_sqrt (by positivity)
    nlinarith [sq_abs m]
  have h_final : (Real.sqrt (m ^ 2 + 4 * b ^ 2) + |m|) / (2 * b ^ 2) = 1 / ((Real.sqrt (m ^ 2 + 4 * b ^ 2) - |m|) / 2) := by
    have h_ne1 : (Real.sqrt (m ^ 2 + 4 * b ^ 2) - |m|) / 2 ≠ 0 := by positivity
    have h_ne2 : (2 : ℝ) * b ^ 2 ≠ 0 := by positivity
    field_simp
    linarith
  exact h_final

-- Literal-matrix versions (exact SPEC statement with !![b,m;0,b])
theorem opNorm_J_literal (b m : ℝ) (hb : 0 < b) :
    opNorm !![b, m; 0, b] = (Real.sqrt (m ^ 2 + 4 * b ^ 2) + |m|) / 2 := opNorm_J b m hb

theorem opNorm_J_inv_literal (b m : ℝ) (hb : 0 < b) :
    opNorm (!![b, m; 0, b])⁻¹ = 1 / ((Real.sqrt (m ^ 2 + 4 * b ^ 2) - |m|) / 2) := opNorm_J_inv b m hb


end SingularValues

/-! ### Semigroup -/

section Semigroup
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

def semigroup_Emat : Matrix (Fin 5) (Fin 2) ℝ := !![0, 0; 1, 0; 0, 0; 0, 0; 0, 1]

lemma semigroup_K5_mul_E (a b h c1 c2 μ γ d1 q1 q2 d2 : ℝ) :
    K5 a b h c1 c2 μ γ d1 q1 q2 d2 * semigroup_Emat = semigroup_Emat * Jgam b μ γ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K5, Jgam, semigroup_Emat, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two]

lemma semigroup_K5_pow_mul_E (a b h c1 c2 μ γ d1 q1 q2 d2 : ℝ) (n : ℕ) :
    (K5 a b h c1 c2 μ γ d1 q1 q2 d2) ^ n * semigroup_Emat = semigroup_Emat * (Jgam b μ γ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (K5 a b h c1 c2 μ γ d1 q1 q2 d2) ^ (n + 1) * semigroup_Emat
        = (K5 a b h c1 c2 μ γ d1 q1 q2 d2 ^ n * K5 a b h c1 c2 μ γ d1 q1 q2 d2) * semigroup_Emat := by rw [pow_succ]
      _ = K5 a b h c1 c2 μ γ d1 q1 q2 d2 ^ n * (K5 a b h c1 c2 μ γ d1 q1 q2 d2 * semigroup_Emat) := by rw [Matrix.mul_assoc]
      _ = K5 a b h c1 c2 μ γ d1 q1 q2 d2 ^ n * (semigroup_Emat * Jgam b μ γ) := by rw [semigroup_K5_mul_E]
      _ = (K5 a b h c1 c2 μ γ d1 q1 q2 d2 ^ n * semigroup_Emat) * Jgam b μ γ := by rw [Matrix.mul_assoc]
      _ = (semigroup_Emat * (Jgam b μ γ) ^ n) * Jgam b μ γ := by rw [ih]
      _ = semigroup_Emat * ((Jgam b μ γ) ^ n * Jgam b μ γ) := by rw [Matrix.mul_assoc]
      _ = semigroup_Emat * (Jgam b μ γ) ^ (n+1) := by rw [← pow_succ]

lemma semigroup_smul_K5_pow_mul_E (a b h c1 c2 μ γ d1 q1 q2 d2 t : ℝ) (n : ℕ) :
    ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2) ^ n * semigroup_Emat = semigroup_Emat * ((-t) • Jgam b μ γ) ^ n := by
  have h1 : ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2) ^ n = (-t) ^ n • (K5 a b h c1 c2 μ γ d1 q1 q2 d2) ^ n := smul_pow _ _ _
  have h2 : ((-t) • Jgam b μ γ) ^ n = (-t) ^ n • (Jgam b μ γ) ^ n := smul_pow _ _ _
  rw [h1, h2, Matrix.smul_mul, Matrix.mul_smul, semigroup_K5_pow_mul_E]

def semigroup_R_E_lin : Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] Matrix (Fin 5) (Fin 2) ℝ where
  toFun M := M * semigroup_Emat
  map_add' x y := by simp [Matrix.add_mul]
  map_smul' c x := by simp [Matrix.smul_mul]

def semigroup_L_E_lin : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 5) (Fin 2) ℝ where
  toFun N := semigroup_Emat * N
  map_add' x y := by simp [Matrix.mul_add]
  map_smul' c x := by simp [Matrix.mul_smul]

lemma semigroup_norm_R_E_le (M : Matrix (Fin 5) (Fin 5) ℝ) : ‖semigroup_R_E_lin M‖ ≤ ‖(semigroup_Emat : Matrix (Fin 5) (Fin 2) ℝ)‖ * ‖M‖ := by
  have h : ‖M * semigroup_Emat‖ ≤ ‖M‖ * ‖semigroup_Emat‖ := Matrix.l2_opNorm_mul M semigroup_Emat
  calc ‖semigroup_R_E_lin M‖ = ‖M * semigroup_Emat‖ := rfl
    _ ≤ ‖M‖ * ‖semigroup_Emat‖ := h
    _ = ‖semigroup_Emat‖ * ‖M‖ := by ring

lemma semigroup_norm_L_E_le (N : Matrix (Fin 2) (Fin 2) ℝ) : ‖semigroup_L_E_lin N‖ ≤ ‖(semigroup_Emat : Matrix (Fin 5) (Fin 2) ℝ)‖ * ‖N‖ := by
  have h : ‖semigroup_Emat * N‖ ≤ ‖semigroup_Emat‖ * ‖N‖ := Matrix.l2_opNorm_mul semigroup_Emat N
  calc ‖semigroup_L_E_lin N‖ = ‖semigroup_Emat * N‖ := rfl
    _ ≤ ‖semigroup_Emat‖ * ‖N‖ := h

noncomputable def semigroup_R_E_clm : Matrix (Fin 5) (Fin 5) ℝ →L[ℝ] Matrix (Fin 5) (Fin 2) ℝ :=
  (semigroup_R_E_lin).mkContinuous (‖(semigroup_Emat : Matrix (Fin 5) (Fin 2) ℝ)‖) (fun M => semigroup_norm_R_E_le M)

noncomputable def semigroup_L_E_clm : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 5) (Fin 2) ℝ :=
  (semigroup_L_E_lin).mkContinuous (‖(semigroup_Emat : Matrix (Fin 5) (Fin 2) ℝ)‖) (fun N => semigroup_norm_L_E_le N)

@[simp] lemma R_E_clm_apply (M : Matrix (Fin 5) (Fin 5) ℝ) : semigroup_R_E_clm M = M * semigroup_Emat := rfl
@[simp] lemma L_E_clm_apply (N : Matrix (Fin 2) (Fin 2) ℝ) : semigroup_L_E_clm N = semigroup_Emat * N := rfl

lemma semigroup_exp_K5_mul_E (a b h c1 c2 μ γ d1 q1 q2 d2 t : ℝ) :
    (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2)) * semigroup_Emat = semigroup_Emat * (exp ((-t) • Jgam b μ γ)) := by
  have hK : HasSum (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹ • ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2) ^ n)) (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2)) := by
    have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2); simpa [expSeries_apply_eq] using h
  have hJ : HasSum (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹ • ((-t) • Jgam b μ γ) ^ n)) (exp ((-t) • Jgam b μ γ)) := by
    have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((-t) • Jgam b μ γ); simpa [expSeries_apply_eq] using h
  have hK_map : HasSum (fun n : ℕ => semigroup_R_E_clm (((Nat.factorial n : ℝ)⁻¹ • ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2) ^ n))) (semigroup_R_E_clm (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2))) := semigroup_R_E_clm.hasSum hK
  have hJ_map : HasSum (fun n : ℕ => semigroup_L_E_clm (((Nat.factorial n : ℝ)⁻¹ • ((-t) • Jgam b μ γ) ^ n))) (semigroup_L_E_clm (exp ((-t) • Jgam b μ γ))) := semigroup_L_E_clm.hasSum hJ
  have h_eq : ∀ n : ℕ, semigroup_R_E_clm (((Nat.factorial n : ℝ)⁻¹ • ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2) ^ n)) = semigroup_L_E_clm (((Nat.factorial n : ℝ)⁻¹ • ((-t) • Jgam b μ γ) ^ n)) := by
    intro n; simp only [R_E_clm_apply, L_E_clm_apply, Matrix.smul_mul, Matrix.mul_smul, semigroup_smul_K5_pow_mul_E]
  have h_fun : (fun n : ℕ => semigroup_R_E_clm (((Nat.factorial n : ℝ)⁻¹ • ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2) ^ n))) = (fun n : ℕ => semigroup_L_E_clm (((Nat.factorial n : ℝ)⁻¹ • ((-t) • Jgam b μ γ) ^ n))) := by funext n; exact h_eq n
  have hK_map' : HasSum (fun n : ℕ => semigroup_L_E_clm (((Nat.factorial n : ℝ)⁻¹ • ((-t) • Jgam b μ γ) ^ n))) (semigroup_R_E_clm (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2))) := by rw [h_fun] at hK_map; exact hK_map
  have h_unique := hJ_map.unique hK_map'
  have h_final : semigroup_R_E_clm (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2)) = semigroup_L_E_clm (exp ((-t) • Jgam b μ γ)) := h_unique.symm
  simpa [R_E_clm_apply, L_E_clm_apply] using h_final

lemma semigroup_Emat_mulVec (x : Fin 2 → ℝ) : semigroup_Emat *ᵥ x = ![0, x 0, 0, 0, x 1] := by
  ext i; fin_cases i <;> simp [semigroup_Emat, mulVec, dotProduct, Fin.sum_univ_two]

lemma semigroup_normSq_eq2 (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq x; simp only [Fin.sum_univ_two] at h
  have h1 : ‖x 0‖ = |x 0| := Real.norm_eq_abs _; have h2 : ‖x 1‖ = |x 1| := Real.norm_eq_abs _
  simp only [h1, h2, sq_abs] at h; exact h

lemma semigroup_normSq_eq5 (y : EuclideanSpace ℝ (Fin 5)) : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2 + (y 4) ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq y; simp only [Fin.sum_univ_five] at h
  have h0 : ‖y 0‖ = |y 0| := Real.norm_eq_abs _; have h1 : ‖y 1‖ = |y 1| := Real.norm_eq_abs _
  have h2 : ‖y 2‖ = |y 2| := Real.norm_eq_abs _; have h3 : ‖y 3‖ = |y 3| := Real.norm_eq_abs _
  have h4 : ‖y 4‖ = |y 4| := Real.norm_eq_abs _
  simp only [h0, h1, h2, h3, h4, sq_abs] at h; linarith

lemma semigroup_E_isometry (x : EuclideanSpace ℝ (Fin 2)) : ‖semigroup_Emat.toEuclideanLin x‖ = ‖x‖ := by
  have hE : semigroup_Emat.toEuclideanLin x = WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) := by simp [Matrix.toLpLin_apply]
  rw [hE]
  have h_mul : semigroup_Emat *ᵥ (WithLp.ofLp x) = ![0, x 0, 0, 0, x 1] := by
    have h1 : semigroup_Emat *ᵥ (WithLp.ofLp x) = ![0, (WithLp.ofLp x) 0, 0, 0, (WithLp.ofLp x) 1] := semigroup_Emat_mulVec _
    have h2 : (WithLp.ofLp x) 0 = x 0 := rfl; have h3 : (WithLp.ofLp x) 1 = x 1 := rfl; rw [h1, h2, h3]
  have h_norm_Ex : ‖(WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5))‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    have h5 := semigroup_normSq_eq5 (WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5))
    have c0 : (WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5)) 0 = 0 := by simp [h_mul]
    have c1 : (WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5)) 1 = x 0 := by simp [h_mul]
    have c2 : (WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5)) 2 = 0 := by simp [h_mul]
    have c3 : (WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5)) 3 = 0 := by simp [h_mul]
    have c4 : (WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5)) 4 = x 1 := by simp [h_mul]
    rw [c0, c1, c2, c3, c4] at h5; simp at h5; exact h5
  have h_norm_x := semigroup_normSq_eq2 x
  have h_eq : ‖(WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5))‖ ^ 2 = ‖x‖ ^ 2 := by rw [h_norm_Ex, h_norm_x]
  have h_nn : 0 ≤ ‖x‖ := norm_nonneg _; have hE_nn : 0 ≤ ‖(WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5))‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖x‖ - ‖(WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5))‖), sq_nonneg (‖x‖ + ‖(WithLp.toLp 2 (semigroup_Emat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin 5))‖)]

lemma semigroup_exp_lin_comp_eq (a b h c1 c2 μ γ d1 q1 q2 d2 t : ℝ) :
    (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2)).toEuclideanLin ∘ₗ semigroup_Emat.toEuclideanLin = semigroup_Emat.toEuclideanLin ∘ₗ (exp ((-t) • Jgam b μ γ)).toEuclideanLin := by
  have h_mat := semigroup_exp_K5_mul_E a b h c1 c2 μ γ d1 q1 q2 d2 t
  have h1 : (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2) * semigroup_Emat).toEuclideanLin = (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2)).toEuclideanLin ∘ₗ semigroup_Emat.toEuclideanLin := by
    rw [Matrix.toLpLin_mul 2 2]
  have h2 : (semigroup_Emat * exp ((-t) • Jgam b μ γ)).toEuclideanLin = semigroup_Emat.toEuclideanLin ∘ₗ (exp ((-t) • Jgam b μ γ)).toEuclideanLin := by
    rw [Matrix.toLpLin_mul 2 2]
  have h_eq : (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2) * semigroup_Emat).toEuclideanLin = (semigroup_Emat * exp ((-t) • Jgam b μ γ)).toEuclideanLin := by rw [h_mat]
  rw [h1] at h_eq; rw [h2] at h_eq; exact h_eq

theorem semigroup_bound (a b h c1 c2 μ γ d1 q1 q2 d2 t : ℝ) :
    ‖((exp ((-t) • Jgam b μ γ)).toEuclideanLin.toContinuousLinearMap)‖ ≤
      ‖((exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2)).toEuclideanLin.toContinuousLinearMap)‖ := by
  let Kclm : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 5) := (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2)).toEuclideanLin.toContinuousLinearMap
  let Jclm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) := (exp ((-t) • Jgam b μ γ)).toEuclideanLin.toContinuousLinearMap
  let Eclm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 5) := semigroup_Emat.toEuclideanLin.toContinuousLinearMap
  have h_lin := semigroup_exp_lin_comp_eq a b h c1 c2 μ γ d1 q1 q2 d2 t
  have h_pointwise : ∀ x : EuclideanSpace ℝ (Fin 2), Kclm (Eclm x) = Eclm (Jclm x) := by
    intro x
    have h_lin_x : (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2)).toEuclideanLin (semigroup_Emat.toEuclideanLin x) = semigroup_Emat.toEuclideanLin ((exp ((-t) • Jgam b μ γ)).toEuclideanLin x) := by
      have h := congr_fun (congr_arg DFunLike.coe h_lin) x
      simp only [LinearMap.coe_comp, Function.comp_apply] at h
      exact h
    -- translate to CLM
    have hK : Kclm (Eclm x) = (exp ((-t) • K5 a b h c1 c2 μ γ d1 q1 q2 d2)).toEuclideanLin (semigroup_Emat.toEuclideanLin x) := rfl
    have hE : Eclm (Jclm x) = semigroup_Emat.toEuclideanLin ((exp ((-t) • Jgam b μ γ)).toEuclideanLin x) := rfl
    rw [hK, hE, h_lin_x]
  have h_bound : ∀ x : EuclideanSpace ℝ (Fin 2), ‖Jclm x‖ ≤ ‖Kclm‖ * ‖x‖ := by
    intro x
    have h1 : ‖Jclm x‖ = ‖Eclm (Jclm x)‖ := (semigroup_E_isometry (Jclm x)).symm
    have h2 : Eclm (Jclm x) = Kclm (Eclm x) := (h_pointwise x).symm
    rw [h1, h2]
    have h3 : ‖Kclm (Eclm x)‖ ≤ ‖Kclm‖ * ‖Eclm x‖ := Kclm.le_opNorm (Eclm x)
    have h4 : ‖Eclm x‖ = ‖x‖ := semigroup_E_isometry x
    rw [h4] at h3
    exact h3
  have h_le : ‖Jclm‖ ≤ ‖Kclm‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x; exact h_bound x
  simpa [Kclm, Jclm, Eclm] using h_le


end Semigroup

/-! ### Gain -/

section Gain
open Real

set_option maxHeartbeats 800000

def matexp_Nmat (μ t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -(μ * t); 0, 0]

lemma matexp_Nmat_sq_zero (μ t : ℝ) : matexp_Nmat μ t * matexp_Nmat μ t = 0 := by
  unfold matexp_Nmat; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma matexp_Nmat_pow_two (μ t : ℝ) : (matexp_Nmat μ t) ^ 2 = 0 := by rw [pow_two, matexp_Nmat_sq_zero]

lemma matexp_neg_t_J_eq (b μ t : ℝ) : (-t) • Jmat b μ = (-(b * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + matexp_Nmat μ t := by
  unfold Jmat matexp_Nmat; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> ring

lemma matexp_diag_eq_smul_one (c : ℝ) : c • (1 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal (fun _ : Fin 2 => c) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Matrix.diagonal]

lemma matexp_commute_smul_one_Nmat (b μ t : ℝ) : Commute ((- (b * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (matexp_Nmat μ t) := by
  rw [Commute, SemiconjBy]
  have h1 : ((- (b * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * matexp_Nmat μ t = (- (b * t)) • matexp_Nmat μ t := by rw [smul_mul_assoc, one_mul]
  have h2 : matexp_Nmat μ t * ((- (b * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = (- (b * t)) • matexp_Nmat μ t := by rw [mul_smul_comm, mul_one]
  rw [h1, h2]

lemma matexp_exp_Nmat (μ t : ℝ) : NormedSpace.exp (matexp_Nmat μ t) = 1 + matexp_Nmat μ t := by
  have hpow : (matexp_Nmat μ t) ^ 2 = 0 := matexp_Nmat_pow_two μ t
  have h_norm_exp : NormedSpace.exp (matexp_Nmat μ t) = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • ((matexp_Nmat μ t) ^ n) := by
    have h := NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := Matrix (Fin 2) (Fin 2) ℝ)
    exact congrFun h (matexp_Nmat μ t)
  have h_tsum : (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • ((matexp_Nmat μ t) ^ n)) = (1 : Matrix (Fin 2) (Fin 2) ℝ) + matexp_Nmat μ t := by
    have h_eq_sum : (∑ n ∈ Finset.range 2, ((n.factorial : ℝ)⁻¹) • ((matexp_Nmat μ t) ^ n)) = (1 : Matrix (Fin 2) (Fin 2) ℝ) + matexp_Nmat μ t := by
      simp [Finset.sum_range_succ, pow_zero, pow_one]
    rw [← h_eq_sum]
    apply HasSum.tsum_eq
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    have h_ge : 2 ≤ n := by
      have : n ∉ Finset.range 2 := hn
      simp [Finset.mem_range] at this
      omega
    have h_pow : (matexp_Nmat μ t) ^ n = 0 := pow_eq_zero_of_le h_ge hpow
    rw [h_pow, smul_zero]
  rw [h_norm_exp, h_tsum]

lemma matexp_exp_diag_smul_one (c : ℝ) : NormedSpace.exp (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = (Real.exp c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [matexp_diag_eq_smul_one, Matrix.exp_diagonal]
  have h_exp_real : NormedSpace.exp c = Real.exp c := by
    have h : (NormedSpace.exp : ℝ → ℝ) = Real.exp := Real.exp_eq_exp_ℝ.symm
    rw [h]
  have h2 : Matrix.diagonal (NormedSpace.exp fun _ : Fin 2 => c) = (Real.exp c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hfun : (NormedSpace.exp fun _ : Fin 2 => c) = fun _ : Fin 2 => Real.exp c := by
      funext i
      have hpi : (NormedSpace.exp fun _ : Fin 2 => c) i = NormedSpace.exp c := by
        have hpi2 := Pi.coe_exp (𝔸 := fun _ : Fin 2 => ℝ) (x := fun _ => c) (i := i)
        exact hpi2
      rw [hpi, h_exp_real]
    rw [hfun]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.one_apply]
  exact h2

lemma matexp_matrix_exp_formula (b μ t : ℝ) : NormedSpace.exp ((-t) • Jmat b μ) = !![Real.exp (-(b*t)), -(μ*t) * Real.exp (-(b*t)); 0, Real.exp (-(b*t))] := by
  have h_eq : (-t) • Jmat b μ = (-(b*t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + matexp_Nmat μ t := matexp_neg_t_J_eq b μ t
  rw [h_eq]
  have h_comm := matexp_commute_smul_one_Nmat b μ t
  rw [Matrix.exp_add_of_commute _ _ h_comm]
  rw [matexp_exp_diag_smul_one, matexp_exp_Nmat]
  have h_prod : ((Real.exp (-(b*t))) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (1 + matexp_Nmat μ t) = !![Real.exp (-(b*t)), -(μ*t) * Real.exp (-(b*t)); 0, Real.exp (-(b*t))] := by
    unfold matexp_Nmat
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;> ring
  rw [h_prod]

theorem gain_opNorm (b mu t : ℝ) (ht : 0 ≤ t) :
    opNorm (NormedSpace.exp ((-t) • Jmat b mu)) = gain b (abs mu) t := by
  rw [matexp_matrix_exp_formula]
  have h_factor : (!![Real.exp (-(b*t)), -(mu*t) * Real.exp (-(b*t)); 0, Real.exp (-(b*t))] : Matrix (Fin 2) (Fin 2) ℝ) = (Real.exp (-(b*t))) • !![1, -(mu*t); 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [smul_eq_mul] <;> ring
  rw [h_factor, opNorm_smul]
  have h1 : abs (Real.exp (-(b*t))) = Real.exp (-(b*t)) := abs_of_nonneg (Real.exp_nonneg _)
  rw [h1, opNorm_unipotent]
  have h2 : abs (-(mu * t)) = abs mu * t := by
    have h1 : abs (-(mu * t)) = abs (mu * t) := abs_neg _
    rw [h1, abs_mul, abs_of_nonneg ht]
  have h3 : (-(mu*t)) ^ 2 = (abs mu * t) ^ 2 := by
    calc (-(mu*t)) ^ 2 = (mu*t) ^ 2 := by rw [neg_pow_two]
      _ = mu ^ 2 * t ^ 2 := by rw [mul_pow]
      _ = (abs mu) ^ 2 * t ^ 2 := by rw [sq_abs]
      _ = (abs mu * t) ^ 2 := by rw [mul_pow]
  have h4 : (Real.sqrt (4 + (-(mu*t)) ^ 2) + abs (-(mu*t))) / 2 = (Real.sqrt (4 + (abs mu * t) ^ 2) + abs mu * t) / 2 := by rw [h2, h3]
  rw [h4]
  unfold gain
  rfl


end Gain

/-! ### Peak -/

section Peak
open Real Set

lemma gainpeak_half_sqrt (x : ℝ) : (Real.sqrt (4 + (2 * x) ^ 2) + 2 * x) / 2 = x + Real.sqrt (1 + x ^ 2) := by
  rw [show 4 + (2 * x) ^ 2 = 2 ^ 2 * (1 + x ^ 2) by ring, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  ring

lemma gainpeak_gain_eq (b m t : ℝ) : gain b m t = Real.exp (-(b * t) + Real.arsinh (m * t / 2)) := by
  rw [Real.exp_add, Real.exp_arsinh, gain]
  congr 1
  rw [← gainpeak_half_sqrt (m * t / 2)]
  ring_nf

lemma gainpeak_inv_sqrt_lt {x y : ℝ} (hxy : x < y) (hx : 0 ≤ x) :
    (Real.sqrt (1 + y ^ 2))⁻¹ < (Real.sqrt (1 + x ^ 2))⁻¹ := by
  have h1 : 0 < Real.sqrt (1 + x ^ 2) := by positivity
  have h2 : 0 < Real.sqrt (1 + y ^ 2) := by positivity
  have h3 : Real.sqrt (1 + x ^ 2) < Real.sqrt (1 + y ^ 2) := by
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith
  have h_eq : ((Real.sqrt (1 + y ^ 2))⁻¹ < (Real.sqrt (1 + x ^ 2))⁻¹) ↔ (Real.sqrt (1 + x ^ 2) < Real.sqrt (1 + y ^ 2)) := by
    rw [inv_lt_inv₀ h2 h1]
  rw [h_eq]
  exact h3

lemma gainpeak_ustar_identity (b m : ℝ) (hb : 0 < b) (hm : 2 * b < m) :
    let tstar := Real.sqrt (m ^ 2 - 4 * b ^ 2) / (m * b)
    let ustar := m * tstar / 2
    (Real.sqrt (1 + ustar ^ 2))⁻¹ = 2 * b / m := by
  intro tstar ustar
  have hm_pos : 0 < m := by linarith
  have h_diff_pos : 0 < m ^ 2 - 4 * b ^ 2 := by nlinarith
  have h_diff_nn : 0 ≤ m ^ 2 - 4 * b ^ 2 := le_of_lt h_diff_pos
  have hustar_eq : ustar = Real.sqrt (m ^ 2 - 4 * b ^ 2) / (2 * b) := by
    show m * (Real.sqrt (m ^ 2 - 4 * b ^ 2) / (m * b)) / 2 = Real.sqrt (m ^ 2 - 4 * b ^ 2) / (2 * b)
    field_simp
  have h_ustar_sq : ustar ^ 2 = (m ^ 2 - 4 * b ^ 2) / (4 * b ^ 2) := by
    rw [hustar_eq]
    rw [div_pow, Real.sq_sqrt h_diff_nn]
    rw [show (2 * b) ^ 2 = 4 * b ^ 2 by ring]
  have h_one_add : 1 + ustar ^ 2 = m ^ 2 / (4 * b ^ 2) := by
    rw [h_ustar_sq]
    have hb2 : (4 * b ^ 2) ≠ 0 := by positivity
    field_simp
    linarith
  have h_sqrt_eq : Real.sqrt (m ^ 2 / (4 * b ^ 2)) = m / (2 * b) := by
    rw [Real.sqrt_div (by positivity)]
    rw [Real.sqrt_sq (show (0 : ℝ) ≤ m by linarith)]
    rw [show (4 : ℝ) * b ^ 2 = (2 * b) ^ 2 by ring]
    rw [Real.sqrt_sq (show (0 : ℝ) ≤ 2 * b by linarith)]
  have h_sqrt_ustar : Real.sqrt (1 + ustar ^ 2) = m / (2 * b) := by
    rw [h_one_add, h_sqrt_eq]
  rw [h_sqrt_ustar]
  field_simp

lemma gainpeak_tstar_pos (b m : ℝ) (hb : 0 < b) (hm : 2 * b < m) :
    0 < Real.sqrt (m ^ 2 - 4 * b ^ 2) / (m * b) := by
  have hm_pos : 0 < m := by linarith
  have h_diff_pos : 0 < m ^ 2 - 4 * b ^ 2 := by nlinarith
  positivity

lemma gainpeak_deriv_arsinh_eq (c : ℝ) : deriv Real.arsinh c = (Real.sqrt (1 + c ^ 2))⁻¹ := by
  have h := Real.hasDerivAt_arsinh c
  exact h.deriv

-- Main theorem
set_option maxHeartbeats 800000

theorem gain_peak (b m : ℝ) (hb : 0 < b) (hm : 2 * b < m) :
    IsGreatest {v : ℝ | ∃ t > 0, v = gain b m t} (gain b m (Real.sqrt (m ^ 2 - 4 * b ^ 2) / (m * b))) := by
  have hm_pos : 0 < m := by linarith
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have h_diff_pos : 0 < m ^ 2 - 4 * b ^ 2 := by nlinarith
  let tstar := Real.sqrt (m ^ 2 - 4 * b ^ 2) / (m * b)
  have htstar_pos : 0 < tstar := gainpeak_tstar_pos b m hb hm
  have h_tstar_mem : gain b m tstar ∈ {v : ℝ | ∃ t > 0, v = gain b m t} := by
    simp only [mem_ofPred_eq]
    exact ⟨tstar, htstar_pos, rfl⟩
  let ustar := m * tstar / 2
  have h_ustar_eq : ustar = Real.sqrt (m ^ 2 - 4 * b ^ 2) / (2 * b) := by
    show m * (Real.sqrt (m ^ 2 - 4 * b ^ 2) / (m * b)) / 2 = Real.sqrt (m ^ 2 - 4 * b ^ 2) / (2 * b)
    field_simp
  have h_ustar_pos : 0 < ustar := by
    rw [h_ustar_eq]
    positivity
  have h_ustar_nn : 0 ≤ ustar := le_of_lt h_ustar_pos
  have h_inv_ustar : (Real.sqrt (1 + ustar ^ 2))⁻¹ = 2 * b / m := gainpeak_ustar_identity b m hb hm
  have h_gain_le_iff : ∀ t : ℝ, gain b m t ≤ gain b m tstar ↔ (-(b * t) + Real.arsinh (m * t / 2)) ≤ (-(b * tstar) + Real.arsinh (m * tstar / 2)) := by
    intro t
    rw [gainpeak_gain_eq, gainpeak_gain_eq]
    exact Real.exp_le_exp
  suffices h : ∀ t > 0, gain b m t ≤ gain b m tstar by
    constructor
    · exact h_tstar_mem
    · intro v hv
      simp only [mem_ofPred_eq] at hv
      obtain ⟨t, ht, rfl⟩ := hv
      exact h t ht
  intro t ht
  rw [h_gain_le_iff]
  let u := m * t / 2
  have hu_pos : 0 < u := by positivity
  have hu_nn : 0 ≤ u := le_of_lt hu_pos
  have h_b_t_eq : b * t = 2 * b / m * u := by
    show b * t = 2 * b / m * (m * t / 2)
    field_simp
  have h_b_tstar_eq : b * tstar = 2 * b / m * ustar := by
    show b * tstar = 2 * b / m * (m * tstar / 2)
    field_simp
  by_cases h_eq : u = ustar
  · have h_mt_eq : m * t / 2 = m * tstar / 2 := h_eq
    have h_bt_eq : b * t = b * tstar := by
      have : m * t / 2 = m * tstar / 2 := h_mt_eq
      field_simp at this ⊢
      linarith
    have h_arsinh_eq : Real.arsinh (m * t / 2) = Real.arsinh (m * tstar / 2) := by
      rw [h_mt_eq]
    linarith
  · have h_ne : u ≠ ustar := h_eq
    have h_cases : u < ustar ∨ ustar < u := by
      rcases lt_or_gt_of_ne h_ne with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hcont : ContinuousOn Real.arsinh (Icc (min u ustar) (max u ustar)) := continuous_arsinh.continuousOn
    have hdiff : DifferentiableOn ℝ Real.arsinh (Ioo (min u ustar) (max u ustar)) := differentiable_arsinh.differentiableOn
    have h_min_lt_max : min u ustar < max u ustar := by
      simp only [min_lt_max]
      exact h_ne
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_deriv_eq_slope Real.arsinh h_min_lt_max hcont hdiff
    have hc_deriv : deriv Real.arsinh c = (Real.sqrt (1 + c ^ 2))⁻¹ := gainpeak_deriv_arsinh_eq c
    have h_slope_eq : (Real.arsinh u - Real.arsinh ustar) / (u - ustar) = deriv Real.arsinh c := by
      by_cases h_lt : u < ustar
      · have h_min : min u ustar = u := min_eq_left (le_of_lt h_lt)
        have h_max : max u ustar = ustar := max_eq_right (le_of_lt h_lt)
        rw [h_min, h_max] at hc_eq
        have : (Real.arsinh ustar - Real.arsinh u) / (ustar - u) = (Real.arsinh u - Real.arsinh ustar) / (u - ustar) := by
          rw [show Real.arsinh ustar - Real.arsinh u = -(Real.arsinh u - Real.arsinh ustar) by ring]
          rw [show (ustar - u) = -(u - ustar) by ring]
          rw [neg_div_neg_eq]
        rw [this] at hc_eq
        exact hc_eq.symm
      · have h_not_lt : ¬ (u < ustar) := h_lt
        have h_gt : ustar < u := by
          rcases h_cases with h | h
          · exact absurd h h_not_lt
          · exact h
        have h_min : min u ustar = ustar := min_eq_right (le_of_lt h_gt)
        have h_max : max u ustar = u := max_eq_left (le_of_lt h_gt)
        rw [h_min, h_max] at hc_eq
        exact hc_eq.symm
    have h_c_in : c ∈ Ioo (min u ustar) (max u ustar) := hc_mem
    have h_c_pos_nn : 0 ≤ c := by
      have h_min_nn : 0 ≤ min u ustar := by
        simp only [le_min_iff]
        exact ⟨hu_nn, h_ustar_nn⟩
      have h_c_gt_min : min u ustar < c := h_c_in.1
      linarith
    have h_factor : (Real.arsinh u - Real.arsinh ustar) - 2 * b / m * (u - ustar) = (u - ustar) * ((Real.sqrt (1 + c ^ 2))⁻¹ - 2 * b / m) := by
      have h_slope : Real.arsinh u - Real.arsinh ustar = (u - ustar) * deriv Real.arsinh c := by
        have h1 : deriv Real.arsinh c = (Real.arsinh u - Real.arsinh ustar) / (u - ustar) := h_slope_eq.symm
        have h_ne2 : u - ustar ≠ 0 := sub_ne_zero.mpr h_ne
        calc Real.arsinh u - Real.arsinh ustar = (u - ustar) * ((Real.arsinh u - Real.arsinh ustar) / (u - ustar)) := by
              rw [mul_div_cancel₀ _ h_ne2]
          _ = (u - ustar) * deriv Real.arsinh c := by rw [← h1]
      rw [h_slope, hc_deriv]
      ring
    have h_factor2 : (Real.arsinh u - Real.arsinh ustar) - 2 * b / m * (u - ustar) = (u - ustar) * ((Real.sqrt (1 + c ^ 2))⁻¹ - (Real.sqrt (1 + ustar ^ 2))⁻¹) := by
      rw [h_factor, h_inv_ustar]
    have h_le_zero : (u - ustar) * ((Real.sqrt (1 + c ^ 2))⁻¹ - (Real.sqrt (1 + ustar ^ 2))⁻¹) ≤ 0 := by
      by_cases h_lt2 : u < ustar
      · have h_c_lt_ustar : c < ustar := by
          have h_max : max u ustar = ustar := max_eq_right (le_of_lt h_lt2)
          have : c < max u ustar := h_c_in.2
          rw [h_max] at this
          exact this
        have h_inv_lt : (Real.sqrt (1 + ustar ^ 2))⁻¹ < (Real.sqrt (1 + c ^ 2))⁻¹ := by
          have h1 : c < ustar := h_c_lt_ustar
          have h2 : 0 ≤ c := h_c_pos_nn
          have := gainpeak_inv_sqrt_lt h1 h2
          exact this
        have h_diff_pos : 0 < (Real.sqrt (1 + c ^ 2))⁻¹ - (Real.sqrt (1 + ustar ^ 2))⁻¹ := by linarith
        have h_u_diff_neg : u - ustar < 0 := by linarith
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h_u_diff_neg) (le_of_lt h_diff_pos)
      · have h_not_lt : ¬ (u < ustar) := h_lt2
        have h_gt : ustar < u := by
          rcases h_cases with h | h
          · exact absurd h h_not_lt
          · exact h
        have h_c_gt_ustar : ustar < c := by
          have h_min : min u ustar = ustar := min_eq_right (le_of_lt h_gt)
          have : min u ustar < c := h_c_in.1
          rw [h_min] at this
          exact this
        have h_inv_lt : (Real.sqrt (1 + c ^ 2))⁻¹ < (Real.sqrt (1 + ustar ^ 2))⁻¹ := by
          have := gainpeak_inv_sqrt_lt h_c_gt_ustar h_ustar_nn
          exact this
        have h_diff_neg : (Real.sqrt (1 + c ^ 2))⁻¹ - (Real.sqrt (1 + ustar ^ 2))⁻¹ < 0 := by linarith
        have h_u_diff_pos : 0 < u - ustar := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_u_diff_pos) (le_of_lt h_diff_neg)
    have h_arsinh_diff_le : Real.arsinh u - Real.arsinh ustar ≤ 2 * b / m * (u - ustar) := by
      have h_eq2 := h_factor2
      have h_le := h_le_zero
      linarith
    have h_f_diff : (-(b * t) + Real.arsinh (m * t / 2)) - (-(b * tstar) + Real.arsinh (m * tstar / 2)) ≤ 0 := by
      have h1 : -(b * t) = -(2 * b / m * u) := congrArg Neg.neg h_b_t_eq
      have h2 : -(b * tstar) = -(2 * b / m * ustar) := congrArg Neg.neg h_b_tstar_eq
      have h_arsinh_t : Real.arsinh (m * t / 2) = Real.arsinh u := rfl
      have h_arsinh_star : Real.arsinh (m * tstar / 2) = Real.arsinh ustar := rfl
      rw [h_arsinh_t, h_arsinh_star, h1, h2]
      linarith
    linarith


end Peak

end FilamentFracture
