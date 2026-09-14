/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.Complexification
import Mathlib.Analysis.Convex.Deriv





















noncomputable section

open Topology Matrix LorentzLieGroup ComplexLorentzGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW



/-- The open forward light cone: η₀ > 0 and η·η < 0 (timelike, future-pointing). -/
def InOpenForwardCone (d : ℕ) (η : Fin (d + 1) → ℝ) : Prop :=
  η 0 > 0 ∧ ∑ μ, minkowskiSignature d μ * η μ ^ 2 < 0

/-- Decompose the Minkowski quadratic form into time and spatial parts:
    Q(η) = -(η₀)² + ∑_{i>0} (ηᵢ)². -/
lemma minkowski_sum_decomp (η : Fin (d + 1) → ℝ) :
    ∑ μ, minkowskiSignature d μ * η μ ^ 2 =
    -(η 0) ^ 2 + ∑ i : Fin d, (η (Fin.succ i)) ^ 2 := by
  rw [Fin.sum_univ_succ]; congr 1
  · simp [minkowskiSignature]
  · congr 1; ext i; simp [minkowskiSignature, Fin.succ_ne_zero]

/-- Forward-cone membership in gap form:
`η ∈ V₊` iff `η₀ > 0` and `η₀² - ‖η_spatial‖² > 0`. -/
theorem inOpenForwardCone_iff_timePos_gapPos (η : Fin (d + 1) → ℝ) :
    InOpenForwardCone d η ↔
      η 0 > 0 ∧ 0 < (η 0) ^ 2 - ∑ i : Fin d, (η (Fin.succ i)) ^ 2 := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have hmink :
        ∑ μ, minkowskiSignature d μ * η μ ^ 2 =
          -(η 0) ^ 2 + ∑ i : Fin d, (η (Fin.succ i)) ^ 2 :=
      minkowski_sum_decomp (d := d) (η := η)
    have hquad : ∑ μ, minkowskiSignature d μ * η μ ^ 2 < 0 := h.2
    rw [hmink] at hquad
    linarith
  · rintro ⟨h0, hgap⟩
    refine ⟨h0, ?_⟩
    have hmink :
        ∑ μ, minkowskiSignature d μ * η μ ^ 2 =
          -(η 0) ^ 2 + ∑ i : Fin d, (η (Fin.succ i)) ^ 2 :=
      minkowski_sum_decomp (d := d) (η := η)
    rw [hmink]
    linarith

/-- For η in the forward cone, the spatial norm is less than the time component. -/
lemma spatial_norm_lt_time {η : Fin (d + 1) → ℝ} (h : InOpenForwardCone d η) :
    Real.sqrt (∑ i : Fin d, (η (Fin.succ i)) ^ 2) < η 0 := by
  rw [show η 0 = Real.sqrt ((η 0) ^ 2) from (Real.sqrt_sq (le_of_lt h.1)).symm]
  exact Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (by have := h.2; rw [minkowski_sum_decomp] at this; linarith)

/-- Expand ∑(ax + by)² into a²∑x² + 2ab∑xy + b²∑y². -/
private lemma sum_sq_expand {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) :
    ∑ i : Fin n, (a * x i + b * y i) ^ 2 =
    a ^ 2 * ∑ i : Fin n, x i ^ 2 + 2 * (a * b) * ∑ i : Fin n, x i * y i +
    b ^ 2 * ∑ i : Fin n, y i ^ 2 := by
  trans (∑ i : Fin n, (a ^ 2 * x i ^ 2 + 2 * (a * b) * (x i * y i) + b ^ 2 * y i ^ 2))
  · congr 1; ext i; ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Triangle inequality squared: ∑(ax+by)² ≤ (a‖x‖ + b‖y‖)². Uses Cauchy-Schwarz. -/
private lemma sum_sq_convex_combo_le {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∑ i : Fin n, (a * x i + b * y i) ^ 2 ≤
    (a * Real.sqrt (∑ i, x i ^ 2) + b * Real.sqrt (∑ i, y i ^ 2)) ^ 2 := by
  rw [sum_sq_expand]
  set sx := ∑ i : Fin n, x i ^ 2; set sy := ∑ i : Fin n, y i ^ 2
  have hsx_nn : 0 ≤ sx := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsy_nn : 0 ≤ sy := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hRHS : (a * Real.sqrt sx + b * Real.sqrt sy) ^ 2 =
      a ^ 2 * sx + 2 * (a * b) * (Real.sqrt sx * Real.sqrt sy) + b ^ 2 * sy := by
    nlinarith [Real.sq_sqrt hsx_nn, Real.sq_sqrt hsy_nn]
  rw [hRHS]
  linarith [mul_le_mul_of_nonneg_left
    (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y) (by positivity : 0 ≤ 2 * (a * b))]

/-- **The open forward light cone is convex.** -/
theorem inOpenForwardCone_convex :
    Convex ℝ {η : Fin (d + 1) → ℝ | InOpenForwardCone d η} := by
  intro η₁ hη₁ η₂ hη₂ a b ha hb hab
  simp only [Set.mem_setOf_eq] at hη₁ hη₂ ⊢
  have h_combo : a • η₁ + b • η₂ = fun μ => a * η₁ μ + b * η₂ μ := by
    ext μ; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [InOpenForwardCone, h_combo]
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le ha with rfl | ha'
    · simp at hab; rw [hab]; simp [hη₂.1]
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hη₁.1) (mul_nonneg hb (le_of_lt hη₂.1))
  · rw [minkowski_sum_decomp]
    suffices h : ∑ i : Fin d, (a * η₁ (Fin.succ i) + b * η₂ (Fin.succ i)) ^ 2 <
        (a * η₁ 0 + b * η₂ 0) ^ 2 by linarith
    have h1 := sum_sq_convex_combo_le
      (fun i => η₁ (Fin.succ i)) (fun i => η₂ (Fin.succ i)) a b ha hb
    have hsx := spatial_norm_lt_time hη₁
    have hsy := spatial_norm_lt_time hη₂
    have h_combo_lt : a * Real.sqrt (∑ i, η₁ (Fin.succ i) ^ 2) +
        b * Real.sqrt (∑ i, η₂ (Fin.succ i) ^ 2) < a * η₁ 0 + b * η₂ 0 := by
      rcases eq_or_lt_of_le ha with rfl | ha'
      · simp at hab ⊢; rw [hab]; simp; exact hsy
      · linarith [mul_lt_mul_of_pos_left hsx ha',
                   mul_le_mul_of_nonneg_left (le_of_lt hsy) hb]
    calc ∑ i, (a * η₁ (Fin.succ i) + b * η₂ (Fin.succ i)) ^ 2
        ≤ _ := h1
      _ < (a * η₁ 0 + b * η₂ 0) ^ 2 :=
          pow_lt_pow_left₀ h_combo_lt (by positivity) two_ne_zero

/-- Positive real scaling preserves the open forward cone. -/
theorem inOpenForwardCone_smul_pos {η : Fin (d + 1) → ℝ}
    (hη : InOpenForwardCone d η) {t : ℝ} (ht : 0 < t) :
    InOpenForwardCone d (t • η) := by
  refine ⟨?_, ?_⟩
  · simpa [Pi.smul_apply] using mul_pos ht hη.1
  · have hQ : ∑ μ, minkowskiSignature d μ * (t * η μ) ^ 2 =
      t ^ 2 * (∑ μ, minkowskiSignature d μ * η μ ^ 2) := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
      congr 1
      ext μ
      ring
    rw [show (∑ μ, minkowskiSignature d μ * (t • η) μ ^ 2) =
      (∑ μ, minkowskiSignature d μ * (t * η μ) ^ 2) by
      simp [Pi.smul_apply]]
    rw [hQ]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos ht) hη.2







/-- The Minkowski quadratic form is preserved by Lorentz transformations.
    Q(Λ·v) = Q(v) for any Lorentz matrix Λ.

    Proof: Q(Λv) = ∑ s_μ (Λv)_μ² = ∑_ν ∑_ρ (∑_μ Λ_μν s_μ Λ_μρ) v_ν v_ρ
    = ∑_ν ∑_ρ δ_{νρ} s_ν v_ν v_ρ = ∑_ν s_ν v_ν² = Q(v). -/
theorem lorentz_preserves_quadratic_form
    (Λ : RestrictedLorentzGroup d) (v : Fin (d + 1) → ℝ) :
    ∑ μ, minkowskiSignature d μ * (∑ ν, Λ.val.val μ ν * v ν) ^ 2 =
    ∑ μ, minkowskiSignature d μ * v μ ^ 2 := by
  -- Extract the Lorentz condition entry by entry
  have hL := Λ.val.prop  -- ΛᵀηΛ = η
  have hEntry : ∀ ν ρ : Fin (d + 1),
      ∑ α, Λ.val.val α ν * minkowskiSignature d α * Λ.val.val α ρ =
      if ν = ρ then minkowskiSignature d ν else 0 := by
    intro ν ρ
    have h := congr_fun (congr_fun hL ν) ρ
    simp only [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMatrix,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at h
    convert h using 1
  -- Step 1: Expand (∑_ν R_μν v_ν)² into double sum
  -- Step 2: Swap sums to get ∑_ν ∑_ρ (∑_μ ...) v_ν v_ρ
  -- Step 3: Apply Lorentz condition to inner sum
  -- Step 4: Collapse diagonal sum
  calc ∑ μ, minkowskiSignature d μ * (∑ ν, Λ.val.val μ ν * v ν) ^ 2
      = ∑ μ, ∑ ν, ∑ ρ,
          Λ.val.val μ ν * minkowskiSignature d μ * Λ.val.val μ ρ * (v ν * v ρ) := by
        congr 1; ext μ
        rw [sq]; simp only [Finset.sum_mul, Finset.mul_sum]
        congr 1; ext ν; congr 1; ext ρ; ring
    _ = ∑ ν, ∑ ρ, ∑ μ,
          Λ.val.val μ ν * minkowskiSignature d μ * Λ.val.val μ ρ * (v ν * v ρ) := by
        rw [Finset.sum_comm]; congr 1; ext ν; rw [Finset.sum_comm]
    _ = ∑ ν, ∑ ρ,
          (∑ μ, Λ.val.val μ ν * minkowskiSignature d μ * Λ.val.val μ ρ) * (v ν * v ρ) := by
        congr 1; ext ν; congr 1; ext ρ; rw [Finset.sum_mul]
    _ = ∑ ν, ∑ ρ, (if ν = ρ then minkowskiSignature d ν else 0) * (v ν * v ρ) := by
        simp_rw [hEntry]
    _ = ∑ ν, minkowskiSignature d ν * v ν ^ 2 := by
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        congr 1; ext ν; ring



/-- The imaginary part of a real Lorentz transformation applied to a complex vector
    equals the real Lorentz transformation applied to the imaginary part.
    Since R is real: Im(R·w) = R·Im(w). -/
theorem ofReal_im_action (R : RestrictedLorentzGroup d)
    (w : Fin (d + 1) → ℂ) (μ : Fin (d + 1)) :
    (∑ ν, (ComplexLorentzGroup.ofReal R).val μ ν * w ν).im =
    ∑ ν, R.val.val μ ν * (w ν).im := by
  simp only [ComplexLorentzGroup.ofReal]
  -- Pull .im through ∑ using Complex.imLm (ℂ →ₗ[ℝ] ℝ)
  rw [show (∑ ν, (↑(R.val.val μ ν) : ℂ) * w ν).im =
    ∑ ν, ((↑(R.val.val μ ν) : ℂ) * w ν).im from by
      change ⇑Complex.imLm (∑ ν, _) = _; rw [map_sum]; simp [Complex.imLm_coe]]
  congr 1; ext ν
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- Real restricted Lorentz transformations preserve the open forward light cone.

    Since the Minkowski metric is preserved by the restricted Lorentz group
    and the orthochronous condition preserves the sign of the time component,
    we get η ∈ V₊ → R·η ∈ V₊ for R ∈ SO↑₊(1,d;ℝ). -/
theorem real_lorentz_preserves_forwardCone (R : RestrictedLorentzGroup d)
    (η : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η) :
    InOpenForwardCone d (fun μ => ∑ ν, R.val.val μ ν * η ν) := by
  constructor
  · -- Time component: (R·η)₀ > 0
    -- Uses R₀₀ ≥ 1, Cauchy-Schwarz, and spatial_norm_lt_time
    simp only
    -- Decompose: (R·η)₀ = R₀₀ * η₀ + ∑_{i>0} R_{0,i+1} * η_{i+1}
    rw [Fin.sum_univ_succ]
    -- The main term R₀₀ * η₀ > 0 dominates the spatial correction
    have hR00 : R.val.val 0 0 ≥ 1 := R.prop.2
    have h_spatial_η := spatial_norm_lt_time hη
    have hR_row := row0_sum_sq d R.val.prop
    -- Lower bound on spatial sum: apply CS to (-R, η) to get -spatial ≤ sqrt(∑R²)·sqrt(∑η²)
    have hCS_neg := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i : Fin d => -(R.val.val 0 i.succ)) (fun i => η i.succ)
    simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at hCS_neg
    -- So spatial ≥ -sqrt(∑R²) · sqrt(∑η²)
    -- sqrt(∑ R_{0,k+1}²) ≤ R₀₀ since ∑ R² = R₀₀² - 1 ≤ R₀₀²
    have hR_sq_nn : 0 ≤ ∑ k : Fin d, R.val.val 0 k.succ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hη_sq_nn : 0 ≤ ∑ i : Fin d, η i.succ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    set sqR := ∑ k : Fin d, R.val.val 0 k.succ ^ 2 with sqR_def
    set sqη := ∑ i : Fin d, η i.succ ^ 2 with sqη_def
    have h_sqrt_R_le : Real.sqrt sqR ≤ R.val.val 0 0 := by
      calc Real.sqrt sqR
          ≤ Real.sqrt (R.val.val 0 0 ^ 2) := by
            apply Real.sqrt_le_sqrt; linarith [hR_row]
        _ = |R.val.val 0 0| := Real.sqrt_sq_eq_abs _
        _ = R.val.val 0 0 := abs_of_nonneg (by linarith)
    -- Combine: R₀₀ η₀ + spatial ≥ R₀₀ η₀ - R₀₀ · sqrt(∑η²) = R₀₀(η₀ - sqrt(∑η²)) > 0
    have h_key : -(Real.sqrt sqR * Real.sqrt sqη) ≤
        ∑ i : Fin d, R.val.val 0 i.succ * η i.succ := by
      linarith
    linarith [mul_le_mul_of_nonneg_right h_sqrt_R_le (Real.sqrt_nonneg sqη),
              mul_pos (show (0 : ℝ) < R.val.val 0 0 from by linarith)
                (show (0 : ℝ) < η 0 - Real.sqrt sqη from by linarith)]
  · -- Minkowski norm preserved: Q(R·η) = Q(η) < 0
    rw [lorentz_preserves_quadratic_form]
    exact hη.2







/-- Entrywise complex conjugation of a matrix. -/
abbrev conjMap (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  M.map star

/-- Bridge lemma: conjMap equals (starRingEnd ℂ).mapMatrix. -/
private theorem conjMap_eq_mapMatrix (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap M = (starRingEnd ℂ).mapMatrix M := by
  ext i j; simp [RingHom.mapMatrix_apply]

theorem conjMap_mul (M N : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap (M * N) = conjMap M * conjMap N := by
  rw [conjMap_eq_mapMatrix, conjMap_eq_mapMatrix, conjMap_eq_mapMatrix, map_mul]

theorem conjMap_det (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    (conjMap M).det = star M.det := by
  rw [conjMap_eq_mapMatrix]
  exact ((starRingEnd ℂ).map_det M).symm

/-- The Minkowski metric matrix η is fixed by conjugation (it's real). -/
theorem conjMap_eta : conjMap (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = ηℂ := by
  ext i j
  simp only [Matrix.map_apply, ηℂ, Matrix.diagonal_apply, minkowskiSignature]
  split_ifs <;> simp

/-- Conjugation commutes with transpose. -/
theorem conjMap_transpose (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap M.transpose = (conjMap M).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply]



/-- Entrywise complex conjugation defines a group automorphism of SO⁺(1,d;ℂ). -/
def conjLG (Λ : ComplexLorentzGroup d) : ComplexLorentzGroup d where
  val := conjMap Λ.val
  metric_preserving := by
    -- Apply the ring hom (starRingEnd ℂ) to the matrix equation Λᵀ η Λ = η
    apply of_metric_preserving_matrix
    have hΛ := metric_preserving_matrix Λ
    -- conjMap(Λᵀ η Λ) = conjMap Λᵀ * conjMap η * conjMap Λ = (conjMap Λ)ᵀ * η * conjMap Λ
    have h := congr_arg conjMap hΛ
    rw [conjMap_mul, conjMap_mul, conjMap_eta, conjMap_transpose] at h
    exact h
  proper := by
    show (conjMap Λ.val).det = 1
    rw [conjMap_det, Λ.proper, star_one]

@[simp] theorem conjLG_val (Λ : ComplexLorentzGroup d) :
    (conjLG Λ).val = conjMap Λ.val := rfl



/-
NOTE (2026-02-25): The previous theorem
`geodesic_convexity_forwardCone` has been removed from the working chain.
A numerical d=1 counterexample search indicates the stated endpoint-to-full-interval
implication was too strong as written. Any replacement must use a corrected statement
or additional hypotheses before it can be used safely in connectedness arguments.
-/














end BHW

end
