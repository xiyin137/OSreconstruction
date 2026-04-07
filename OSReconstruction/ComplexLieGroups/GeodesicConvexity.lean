/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.Complexification
import Mathlib.Analysis.Convex.Deriv

/-!
# Geodesic Convexity for the Forward Light Cone

The forward light cone V₊ ⊂ ℝ^{d+1} is "geodesically convex" under the
one-parameter subgroups of the complex Lorentz group: if exp(iY)·w has
imaginary part in V₊ at t=0 and t=1, then it stays in V₊ for all t ∈ [0,1].

This is the key analytical ingredient for proving that the orbit set
O_w = {Λ ∈ SO⁺(1,d;ℂ) : Λ·w ∈ ForwardTube} is path-connected.

## Main results

- `InOpenForwardCone`: Definition of the open forward light cone.
- `inOpenForwardCone_convex`: The forward cone is convex.
- `real_lorentz_preserves_forwardCone`: Real Lorentz transformations preserve V₊.
- `ofReal_im_action`: For real Lorentz R, Im(R·w) = R·Im(w).

Ref: Streater & Wightman, Theorem 2-11; Bros-Epstein-Glaser (1967).
-/

noncomputable section

open Topology Matrix LorentzLieGroup ComplexLorentzGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-! ### Forward light cone definition and properties -/

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

/-! ### Concavity helper on `[0,1]` -/

/-- Concavity on `[0,1]` plus strictly positive endpoint values implies strict
positivity on the whole interval. -/
theorem concave_pos_on_Icc_of_endpoints_pos
    {f : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (h0 : 0 < f 0) (h1 : 0 < f 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < f t := by
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hcomb : t * (1 : ℝ) + (1 - t) * (0 : ℝ) = t := by ring
  have hconc_ineq := hconc.2 (x := (1 : ℝ)) (by simp) (y := (0 : ℝ)) (by simp)
    ht0 (sub_nonneg.mpr ht1) (by ring)
  have hline : t * f 1 + (1 - t) * f 0 ≤ f t := by
    simpa [hcomb] using hconc_ineq
  have hleft_pos : 0 < t * f 1 + (1 - t) * f 0 := by
    by_cases hteq0 : t = 0
    · subst hteq0
      simpa using h0
    · by_cases hteq1 : t = 1
      · subst hteq1
        simp [h1]
      · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hteq0)
        have h1t_pos : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 hteq1)
        have htf1 : 0 < t * f 1 := mul_pos ht_pos h1
        have h1tf0 : 0 < (1 - t) * f 0 := mul_pos h1t_pos h0
        exact add_pos htf1 h1tf0
  exact lt_of_lt_of_le hleft_pos hline

/-- On `[0,1]`, if the time component stays positive and the Minkowski gap
`η₀² - ‖η_spatial‖²` is concave with positive endpoints, then the full vector
stays in the open forward cone. -/
theorem inOpenForwardCone_on_Icc_of_timePos_and_concave_gap
    {η : ℝ → Fin (d + 1) → ℝ}
    (hη0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < η t 0)
    (hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t => (η t 0) ^ 2 - ∑ i : Fin d, (η t (Fin.succ i)) ^ 2))
    (hgap0 : 0 < (η 0 0) ^ 2 - ∑ i : Fin d, (η 0 (Fin.succ i)) ^ 2)
    (hgap1 : 0 < (η 1 0) ^ 2 - ∑ i : Fin d, (η 1 (Fin.succ i)) ^ 2) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, InOpenForwardCone d (η t) := by
  intro t ht
  have hgap_pos :
      0 < (η t 0) ^ 2 - ∑ i : Fin d, (η t (Fin.succ i)) ^ 2 :=
    concave_pos_on_Icc_of_endpoints_pos hconc hgap0 hgap1 t ht
  refine ⟨hη0 t ht, ?_⟩
  have hmink :
      ∑ μ, minkowskiSignature d μ * (η t μ) ^ 2 =
        -((η t 0) ^ 2) + ∑ i : Fin d, (η t (Fin.succ i)) ^ 2 :=
    minkowski_sum_decomp (d := d) (η := η t)
  rw [hmink]
  linarith

/-! ### Hyperbolic helper inequalities -/

/-- For `β ≥ 0` and `t ∈ [0,1]`, one has `sinh (β t) ≤ t * sinh β`.
    This is Jensen on `Icc 0 β` using convexity of `sinh` on `[0,∞)`. -/
theorem sinh_mul_le_mul_sinh {β : ℝ} (hβ : 0 ≤ β) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sinh (β * t) ≤ t * Real.sinh β := by
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) β) Real.sinh := by
    have hderiv : DifferentiableOn ℝ (deriv Real.sinh) (Set.Icc (0 : ℝ) β) := by
      simpa [Real.deriv_sinh] using Real.differentiable_cosh.differentiableOn
    refine convexOn_of_deriv2_nonneg' (D := Set.Icc (0 : ℝ) β) (convex_Icc 0 β)
      Real.differentiable_sinh.differentiableOn hderiv ?_
    intro x hx
    have hiterAux := congrArg (fun g : ℝ → ℝ => g x)
      (iteratedDeriv_eq_iterate (n := 2) (f := Real.sinh)).symm
    have hiter : deriv^[2] Real.sinh x = iteratedDeriv 2 Real.sinh x := hiterAux
    rw [hiter]
    have h2Aux := congrArg (fun g : ℝ → ℝ => g x) (Real.iteratedDeriv_even_sinh 1)
    have h2 : iteratedDeriv 2 Real.sinh x = Real.sinh x := h2Aux
    rw [h2]
    exact (Real.sinh_nonneg_iff).2 hx.1
  rcases hconv with ⟨_, hineq⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) β := ⟨le_rfl, hβ⟩
  have hβmem : β ∈ Set.Icc (0 : ℝ) β := ⟨hβ, le_rfl⟩
  have hmain := hineq h0mem hβmem (sub_nonneg.mpr ht1) ht0 (by linarith : (1 - t) + t = 1)
  simpa [smul_eq_mul, Real.sinh_zero, mul_comm, mul_left_comm, mul_assoc,
    add_comm, add_left_comm, add_assoc] using hmain

/-- Squared form of `sinh_mul_le_mul_sinh` on `[0,1]`. -/
theorem sinh_sq_mul_le_mul_sq_sinh_sq {β : ℝ} (hβ : 0 ≤ β) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sinh (β * t) ^ 2 ≤ t ^ 2 * Real.sinh β ^ 2 := by
  have h1 : Real.sinh (β * t) ≤ t * Real.sinh β :=
    sinh_mul_le_mul_sinh hβ ht0 ht1
  have hlow : -(t * Real.sinh β) ≤ Real.sinh (β * t) := by
    have hs1 : 0 ≤ Real.sinh (β * t) :=
      (Real.sinh_nonneg_iff).2 (mul_nonneg hβ ht0)
    have hs2 : 0 ≤ t * Real.sinh β :=
      mul_nonneg ht0 ((Real.sinh_nonneg_iff).2 hβ)
    linarith
  have hsq : Real.sinh (β * t) ^ 2 ≤ (t * Real.sinh β) ^ 2 := by
    nlinarith [h1, hlow]
  calc
    Real.sinh (β * t) ^ 2 ≤ (t * Real.sinh β) ^ 2 := hsq
    _ = t ^ 2 * Real.sinh β ^ 2 := by ring

/-! ### Lorentz transformation preserves the Minkowski quadratic form -/

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

/-! ### Real Lorentz preserves the forward cone -/

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

/-! ### Lie algebra embedding -/

/-- The Lie algebra of SO(1,d;ℝ) embedded into complex matrices via i·Y.
    If Y ∈ so(1,d;ℝ), then i·(Y.map ofReal) ∈ so(1,d;ℂ). -/
theorem isInLieAlgebra_of_real_times_I
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) :
    IsInLieAlgebra (Complex.I • Y.map Complex.ofReal) := by
  unfold IsInLieAlgebra
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
  suffices h : (Y.map Complex.ofReal).transpose * ηℂ + ηℂ * Y.map Complex.ofReal = 0 by
    rw [h, smul_zero]
  -- Cast the real Lorentz algebra condition to ℂ using RingHom.mapMatrix
  -- hY : Yᵀ * minkowskiMatrix d + minkowskiMatrix d * Y = 0  (over ℝ)
  -- Goal: (Y.map ofReal)ᵀ * ηℂ + ηℂ * Y.map ofReal = 0  (over ℂ)
  -- Key: both sides equal Complex.ofRealHom.mapMatrix applied to hY
  -- Rewrite all terms to Complex.ofRealHom.mapMatrix form, then apply hY
  rw [show (Y.map Complex.ofReal).transpose = Complex.ofRealHom.mapMatrix Y.transpose from by
        ext i j; simp [RingHom.mapMatrix_apply, Matrix.transpose_apply, Matrix.map_apply],
      show ηℂ = Complex.ofRealHom.mapMatrix (minkowskiMatrix d) from by
        ext i j; simp [RingHom.mapMatrix_apply, ηℂ, minkowskiMatrix, Matrix.diagonal_apply]
        split <;> simp,
      show Y.map Complex.ofReal = Complex.ofRealHom.mapMatrix Y from by
        ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply],
      ← map_mul, ← map_mul, ← map_add, hY, map_zero]

/-! ### Geodesic path in the complex Lorentz group -/

/-- For Y ∈ so(1,d;ℝ), the matrix exp(itY) (viewed as a complex Lorentz transformation)
    is a one-parameter subgroup of SO⁺(1,d;ℂ). Using the smul form
    t • (I • Y.map ofReal) which equals (t * I) • Y.map ofReal by smul_smul. -/
def realAlgPath (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) (t : ℝ) : ComplexLorentzGroup d :=
  expLieAlg ((t : ℂ) • (Complex.I • Y.map Complex.ofReal))
    (isInLieAlgebra_smul (↑t) (isInLieAlgebra_of_real_times_I Y hY))

/-- The real algebra path at t=0 is the identity. -/
theorem realAlgPath_zero (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) :
    realAlgPath Y hY 0 = 1 := by
  simp only [realAlgPath, expLieAlg, Complex.ofReal_zero, zero_smul]
  ext i j
  simp [NormedSpace.exp_zero]

/-- The path t ↦ realAlgPath Y hY t is continuous. -/
theorem realAlgPath_continuous (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) :
    Continuous (realAlgPath Y hY) := by
  apply continuous_induced_rng.mpr
  -- val ∘ realAlgPath Y hY = fun t ↦ exp(t • (I • Y.map ofReal))
  exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

/-- The one-parameter subgroup property: exp(isY) * exp(itY) = exp(i(s+t)Y). -/
theorem realAlgPath_mul (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) (s t : ℝ) :
    realAlgPath Y hY s * realAlgPath Y hY t = realAlgPath Y hY (s + t) := by
  apply ComplexLorentzGroup.ext
  show NormedSpace.exp ((s : ℂ) • (Complex.I • Y.map Complex.ofReal)) *
    NormedSpace.exp ((t : ℂ) • (Complex.I • Y.map Complex.ofReal)) =
    NormedSpace.exp (((s + t : ℝ) : ℂ) • (Complex.I • Y.map Complex.ofReal))
  rw [← Matrix.exp_add_of_commute]
  · congr 1
    rw [Complex.ofReal_add, add_smul]
  · exact (Commute.refl _).smul_left _ |>.smul_right _

/-- Scaling Y by c and evaluating at t=1 equals evaluating at t=c. -/
theorem realAlgPath_smul_eq (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) (c : ℝ) :
    realAlgPath (c • Y) (isInLorentzAlgebra_smul d hY c) 1 =
    realAlgPath Y hY c := by
  apply ComplexLorentzGroup.ext
  show NormedSpace.exp ((1 : ℂ) • (Complex.I • (c • Y).map Complex.ofReal)) =
    NormedSpace.exp ((c : ℂ) • (Complex.I • Y.map Complex.ofReal))
  congr 1
  ext i j
  simp [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  ring

/-! ### Entrywise complex conjugation of matrices -/

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

theorem conjMap_involutive (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap (conjMap M) = M := by
  ext i j; simp [Matrix.map_apply]

theorem conjMap_det (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    (conjMap M).det = star M.det := by
  rw [conjMap_eq_mapMatrix]
  exact ((starRingEnd ℂ).map_det M).symm

theorem conjMap_one : conjMap (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = 1 := by
  rw [conjMap_eq_mapMatrix, map_one]

/-- Entrywise conjugation of a matrix exponential equals the exponential of the
    entrywise conjugation: conj(exp X) = exp(conj X).

    Proof chain: M.map star = Mᴴᵀ, then use star_exp and exp_transpose. -/
theorem conjMap_exp (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap (NormedSpace.exp X) = NormedSpace.exp (conjMap X) := by
  -- map star = conjTranspose.transpose
  rw [show conjMap (NormedSpace.exp X) =
      (NormedSpace.exp X).conjTranspose.transpose from
    (Matrix.conjTranspose_transpose _).symm]
  -- star_exp: star(exp X) = exp(star X), i.e., (exp X)ᴴ = exp(Xᴴ)
  rw [show (NormedSpace.exp X).conjTranspose = NormedSpace.exp X.conjTranspose from by
    rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose]
    exact NormedSpace.star_exp X]
  -- exp_transpose: exp(Aᵀ) = (exp A)ᵀ, backwards: (exp B)ᵀ = exp(Bᵀ)
  rw [← Matrix.exp_transpose, Matrix.conjTranspose_transpose]

/-- Conjugation of I • Y.map ofReal gives -(I • Y.map ofReal) for real Y. -/
theorem conjMap_real_I_smul (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    conjMap (Complex.I • Y.map Complex.ofReal) = -(Complex.I • Y.map Complex.ofReal) := by
  ext i j; simp [Matrix.map_apply, Matrix.smul_apply, Complex.conj_I,
    Complex.conj_ofReal, Matrix.neg_apply]

/-- Conjugation fixes real matrices. -/
theorem conjMap_real (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    conjMap (M.map Complex.ofReal) = M.map Complex.ofReal := by
  ext i j; simp [Matrix.map_apply, Complex.conj_ofReal]

/-- The Minkowski metric matrix η is fixed by conjugation (it's real). -/
theorem conjMap_eta : conjMap (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = ηℂ := by
  ext i j
  simp only [Matrix.map_apply, ηℂ, Matrix.diagonal_apply, minkowskiSignature]
  split_ifs <;> simp

/-- Conjugation commutes with transpose. -/
theorem conjMap_transpose (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    conjMap M.transpose = (conjMap M).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply]

/-! ### Conjugation on the complex Lorentz group -/

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

theorem conjLG_involutive (Λ : ComplexLorentzGroup d) :
    conjLG (conjLG Λ) = Λ := by
  apply ComplexLorentzGroup.ext
  exact conjMap_involutive Λ.val

theorem conjLG_mul (Λ₁ Λ₂ : ComplexLorentzGroup d) :
    conjLG (Λ₁ * Λ₂) = conjLG Λ₁ * conjLG Λ₂ := by
  apply ComplexLorentzGroup.ext
  exact conjMap_mul Λ₁.val Λ₂.val

theorem conjLG_one : conjLG (1 : ComplexLorentzGroup d) = 1 := by
  apply ComplexLorentzGroup.ext
  exact conjMap_one

/-- Conjugation fixes the image of the real Lorentz group embedding. -/
theorem conjLG_ofReal (R : RestrictedLorentzGroup d) :
    conjLG (ComplexLorentzGroup.ofReal R) = ComplexLorentzGroup.ofReal R := by
  apply ComplexLorentzGroup.ext
  ext i j
  simp only [conjLG_val, ComplexLorentzGroup.ofReal, Matrix.map_apply]
  exact Complex.conj_ofReal _

/-- For any Λ ∈ SO⁺(1,d;ℂ), the group inverse satisfies Λ⁻¹.val * Λ.val = 1. -/
private theorem group_inv_mul_val (Λ : ComplexLorentzGroup d) :
    Λ⁻¹.val * Λ.val = 1 := by
  have h : Λ⁻¹ * Λ = 1 := inv_mul_cancel Λ
  exact congr_arg ComplexLorentzGroup.val h

/-- For any Λ ∈ SO⁺(1,d;ℂ), group inverse = matrix inverse. -/
private theorem group_inv_eq_matrix_inv (Λ : ComplexLorentzGroup d) :
    Λ⁻¹.val = Λ.val⁻¹ := by
  symm
  exact Matrix.inv_eq_left_inv (group_inv_mul_val Λ)

/-- Conjugation preserves inverses (group homomorphism property). -/
theorem conjLG_inv (Λ : ComplexLorentzGroup d) :
    conjLG Λ⁻¹ = (conjLG Λ)⁻¹ := by
  have h : conjLG Λ * conjLG Λ⁻¹ = 1 := by
    rw [← conjLG_mul, mul_inv_cancel, conjLG_one]
  exact eq_comm.mpr (inv_eq_of_mul_eq_one_right h)

/-- Conjugation sends exp(itY) to exp(-itY) for real Y ∈ so(1,d;ℝ). -/
theorem conjLG_realAlgPath (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) (t : ℝ) :
    conjLG (realAlgPath Y hY t) = (realAlgPath Y hY t)⁻¹ := by
  -- Suffices to show conjLG(B) * B = 1, then conjLG(B) = B⁻¹
  suffices h : conjLG (realAlgPath Y hY t) * realAlgPath Y hY t = 1 by
    exact mul_eq_one_iff_eq_inv.mp h
  apply ComplexLorentzGroup.ext
  -- Goal: (conjLG B * B).val = 1, i.e., conjMap(B.val) * B.val = 1
  show conjMap (realAlgPath Y hY t).val * (realAlgPath Y hY t).val = 1
  -- Unfold: B.val = exp((↑t:ℂ) • (I • Y.map ofReal))
  set X := (↑t : ℂ) • (Complex.I • Y.map Complex.ofReal) with hX_def
  -- conjMap(exp X) = exp(conjMap X)
  rw [show (realAlgPath Y hY t).val = NormedSpace.exp X from rfl]
  rw [conjMap_exp]
  -- conjMap X = -X since conj(t*I*Y) = t*(-I)*Y = -t*I*Y = -X
  rw [show conjMap X = -X from by
    rw [hX_def]
    show ((↑t : ℂ) • (Complex.I • Y.map Complex.ofReal)).map star =
      -((↑t : ℂ) • (Complex.I • Y.map Complex.ofReal))
    ext i j
    show (starRingEnd ℂ) ((t : ℂ) • Complex.I • Y.map Complex.ofReal i j) =
      -((t : ℂ) • Complex.I • Y.map Complex.ofReal i j)
    simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Matrix.map_apply]
    ring]
  -- exp(-X) * exp(X) = 1
  rw [Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp X))

/-- Shorthand: conjLG at t=1. -/
theorem conjLG_realAlgPath_one (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hY : IsInLorentzAlgebra d Y) :
    conjLG (realAlgPath Y hY 1) = (realAlgPath Y hY 1)⁻¹ :=
  conjLG_realAlgPath Y hY 1

/-! ### Geodesic convexity of the forward cone -/

/-
NOTE (2026-02-25): The previous theorem
`geodesic_convexity_forwardCone` has been removed from the working chain.
A numerical d=1 counterexample search indicates the stated endpoint-to-full-interval
implication was too strong as written. Any replacement must use a corrected statement
or additional hypotheses before it can be used safely in connectedness arguments.
-/

/-! ### Deferred Cartan/Polar Infrastructure

The Cartan symmetric-space embedding and the corresponding polar decomposition
for `ComplexLorentzGroup` are mathematically plausible but currently not on the
critical BHW proof path in this repository. The previous draft included two
`sorry`-based placeholders here; they have been removed to keep the dependency
chain axiom-free and warning-free.

If this infrastructure becomes required again, it should be reintroduced with
fully formalized prerequisites (matrix logarithm/symmetric-space machinery) in a
dedicated file.
-/

end BHW

end
