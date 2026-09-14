/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Spacetime.Metric





























noncomputable section

open BigOperators Finset

set_option linter.unusedSectionVars false

variable (d : ℕ) [NeZero d]

namespace MinkowskiSpace



/-- The spatial squared norm: Σᵢ xᵢ² -/
def spatialNormSq (x : MinkowskiSpace d) : ℝ :=
  ∑ i : Fin d, (x (Fin.succ i)) ^ 2

/-- The Minkowski inner product decomposed into time and space parts:
    η(x, y) = -x₀·y₀ + Σᵢ xᵢ·yᵢ -/
theorem minkowskiInner_decomp (x y : MinkowskiSpace d) :
    minkowskiInner d x y = -(x 0 * y 0) + ∑ i : Fin d, x (Fin.succ i) * y (Fin.succ i) := by
  unfold minkowskiInner metricSignature
  rw [Fin.sum_univ_succ]
  simp only [↓reduceIte, Fin.succ_ne_zero, one_mul]
  ring

/-- The Minkowski norm squared decomposed:
    η(x, x) = -x₀² + Σᵢ xᵢ² -/
theorem minkowskiNormSq_decomp (x : MinkowskiSpace d) :
    minkowskiNormSq d x = -(x 0) ^ 2 + spatialNormSq d x := by
  unfold minkowskiNormSq spatialNormSq
  rw [minkowskiInner_decomp]
  congr 1
  · ring
  · congr 1; ext i; ring

/-- For timelike vectors, the time component squared exceeds the spatial norm squared:
    IsTimelike x → x₀² > Σᵢ xᵢ² -/
theorem timelike_time_dominates_space (x : MinkowskiSpace d) (hx : IsTimelike d x) :
    (x 0) ^ 2 > spatialNormSq d x := by
  rw [IsTimelike, minkowskiNormSq_decomp] at hx
  linarith

/-- Spatial norm squared is non-negative -/
theorem spatialNormSq_nonneg (x : MinkowskiSpace d) : spatialNormSq d x ≥ 0 := by
  unfold spatialNormSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- The spatial inner product: Σᵢ xᵢ·yᵢ -/
def spatialInner (x y : MinkowskiSpace d) : ℝ :=
  ∑ i : Fin d, x (Fin.succ i) * y (Fin.succ i)

/-- Cauchy-Schwarz for the spatial inner product:
    (Σᵢ xᵢyᵢ)² ≤ (Σᵢ xᵢ²)(Σᵢ yᵢ²) -/
theorem spatial_cauchy_schwarz (x y : MinkowskiSpace d) :
    (spatialInner d x y) ^ 2 ≤ spatialNormSq d x * spatialNormSq d y := by
  unfold spatialInner spatialNormSq
  -- This is the standard Cauchy-Schwarz inequality for finite sums
  exact Finset.sum_mul_sq_le_sq_mul_sq
    Finset.univ (fun i => x (Fin.succ i)) (fun i => y (Fin.succ i))

/-- The Minkowski inner product in terms of time and spatial components -/
theorem minkowskiInner_eq_time_spatial (x y : MinkowskiSpace d) :
    minkowskiInner d x y = -(x 0 * y 0) + spatialInner d x y := by
  rw [minkowskiInner_decomp]; rfl



/-- **Key lemma**: A nonzero vector Minkowski-orthogonal to a timelike future-directed
    vector is spacelike.

    Proof: Let η be timelike future-directed (η₀ > 0, -η₀² + Σ ηᵢ² < 0) and ξ ⊥_M η.
    Then -ξ₀η₀ + Σ ξᵢηᵢ = 0, so ξ₀η₀ = Σ ξᵢηᵢ.
    By Cauchy-Schwarz: ξ₀²η₀² = (Σ ξᵢηᵢ)² ≤ (Σ ξᵢ²)(Σ ηᵢ²).
    Since η is timelike: Σ ηᵢ² < η₀², so ξ₀²η₀² < (Σ ξᵢ²)η₀².
    Since η₀ > 0: ξ₀² ≤ Σ ξᵢ², hence -ξ₀² + Σ ξᵢ² ≥ 0. -/
theorem minkowskiInner_orthogonal_to_timelike_nonneg
    (ξ η : MinkowskiSpace d)
    (hη_timelike : IsTimelike d η)
    (hη_future : IsFutureDirected d η)
    (horth : minkowskiInner d ξ η = 0) :
    minkowskiNormSq d ξ ≥ 0 := by
  -- Decompose the orthogonality condition
  rw [minkowskiInner_eq_time_spatial] at horth
  -- horth : -(ξ 0 * η 0) + spatialInner d ξ η = 0
  have hsi : ξ 0 * η 0 = spatialInner d ξ η := by linarith
  -- Time dominates space for timelike η
  have hdom := timelike_time_dominates_space d η hη_timelike
  -- η₀ > 0
  have hη0_pos : η 0 > 0 := hη_future
  have hη0_sq_pos : (η 0) ^ 2 > 0 := sq_pos_of_pos hη0_pos
  -- Cauchy-Schwarz on spatial components
  have hcs := spatial_cauchy_schwarz d ξ η
  -- From hsi: (ξ₀ · η₀)² = (spatialInner ξ η)²
  have hsq : (ξ 0) ^ 2 * (η 0) ^ 2 = (spatialInner d ξ η) ^ 2 := by
    have := congr_arg (· ^ 2) hsi; simp [mul_pow] at this ⊢; linarith [this]
  -- Combine: ξ₀²·η₀² ≤ (Σ ξᵢ²)(Σ ηᵢ²) < (Σ ξᵢ²)·η₀²
  -- So ξ₀² ≤ Σ ξᵢ² (when Σ ξᵢ² > 0) or ξ₀ = 0 (when Σ ξᵢ² = 0)
  rw [minkowskiNormSq_decomp]
  -- Goal: -(ξ 0)² + spatialNormSq d ξ ≥ 0, i.e., spatialNormSq d ξ ≥ (ξ 0)²
  -- Case split on whether ξ₀ = 0
  by_cases hξ0 : ξ 0 = 0
  · simp [hξ0, spatialNormSq_nonneg]
  · -- ξ₀ ≠ 0, so spatialInner ≠ 0 (from hsi and η₀ ≠ 0)
    -- From Cauchy-Schwarz: (spatialInner)² ≤ spatialNormSq(ξ) · spatialNormSq(η)
    -- From hdom: spatialNormSq(η) < η₀²
    -- So ξ₀² · η₀² = (spatialInner)² ≤ spatialNormSq(ξ) · spatialNormSq(η)
    --    < spatialNormSq(ξ) · η₀²
    -- Hence ξ₀² < spatialNormSq(ξ) (dividing by η₀² > 0)
    -- But we need ≤ not <. Actually we get strict inequality when spatialNormSq(η) < η₀²
    have hη_spatial_lt : spatialNormSq d η < (η 0) ^ 2 := hdom
    -- Spatial norm of ξ must be positive (otherwise ξ₀η₀ = spatialInner = 0, but ξ₀ ≠ 0, η₀ > 0)
    have hξ_spatial_pos : spatialNormSq d ξ > 0 := by
      by_contra h
      push_neg at h
      have h0 := spatialNormSq_nonneg d ξ
      have heq : spatialNormSq d ξ = 0 := le_antisymm h h0
      -- If spatial norm = 0, then each spatial component = 0
      unfold spatialNormSq at heq
      have : ∀ i : Fin d, ξ (Fin.succ i) = 0 := by
        intro i
        have hle := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (ξ (Fin.succ j)))
        have := Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_ : j ∈ Finset.univ) => sq_nonneg (ξ (Fin.succ j))) |>.mp heq i (mem_univ _)
        exact sq_eq_zero_iff.mp this
      -- So spatialInner d ξ η = 0
      have hsi0 : spatialInner d ξ η = 0 := by
        unfold spatialInner
        exact Finset.sum_eq_zero (fun i _ => by rw [this i, zero_mul])
      -- But ξ₀η₀ = spatialInner = 0, and η₀ > 0, so ξ₀ = 0. Contradiction!
      rw [hsi0] at hsi
      exact hξ0 (mul_right_cancel₀ (ne_of_gt hη0_pos) (hsi.trans (zero_mul _).symm))
    -- Now: ξ₀²·η₀² = (spatialInner)² ≤ spatialNormSq(ξ)·spatialNormSq(η)
    --   < spatialNormSq(ξ)·η₀²
    have step1 : (ξ 0) ^ 2 * (η 0) ^ 2 ≤ spatialNormSq d ξ * spatialNormSq d η := by
      rw [hsq]; exact hcs
    -- Combine: ξ₀²·η₀² ≤ sn(ξ)·sn(η) < sn(ξ)·η₀², hence ξ₀² < sn(ξ)
    nlinarith



/-- The complex Minkowski quadratic form: Q(ζ) = Σ_μ η_μ · ζ_μ²
    This extends the real Minkowski norm squared to complex vectors.
    Note: this uses the COMPLEX BILINEAR form (not sesquilinear). -/
def complexMinkowskiQuadratic (ζ : Fin (d + 1) → ℂ) : ℂ :=
  ∑ μ : Fin (d + 1), (metricSignature d μ : ℂ) * ζ μ ^ 2

/-- Decomposition of the complex quadratic form on ξ + iη:
    Q(ξ + iη) = [minkowskiNormSq(ξ) - minkowskiNormSq(η)] + 2i · minkowskiInner(ξ, η)

    This is the key identity for Jost's lemma: if Λ(ξ + iη) is real, then:
    - Im(Q) = 0, which gives minkowskiInner(ξ, η) = 0 (Minkowski orthogonality)
    - Re(Q) = minkowskiNormSq(ξ) - minkowskiNormSq(η)  -/
theorem complexQuadratic_decomp (ξ η : MinkowskiSpace d) :
    complexMinkowskiQuadratic d (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I) =
    (minkowskiNormSq d ξ - minkowskiNormSq d η : ℝ) +
    (2 * minkowskiInner d ξ η : ℝ) * Complex.I := by
  unfold complexMinkowskiQuadratic minkowskiNormSq minkowskiInner
  -- Expand each summand keeping ℂ casts separate
  have expand : ∀ μ : Fin (d + 1),
      (metricSignature d μ : ℂ) * ((ξ μ : ℂ) + (η μ : ℂ) * Complex.I) ^ 2 =
      ((metricSignature d μ : ℂ) * (ξ μ : ℂ) * (ξ μ : ℂ) -
       (metricSignature d μ : ℂ) * (η μ : ℂ) * (η μ : ℂ)) +
      (2 * (metricSignature d μ : ℂ) * (ξ μ : ℂ) * (η μ : ℂ)) * Complex.I := by
    intro μ
    have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
    linear_combination (metricSignature d μ : ℂ) * (η μ : ℂ) ^ 2 * hI

  simp_rw [expand, Finset.sum_add_distrib, ← Finset.sum_mul]
  -- LHS: (∑ μ, ↑η_μ·↑ξ_μ·↑ξ_μ - ↑η_μ·↑η_μ·↑η_μ) + (∑ μ, 2·↑η_μ·↑ξ_μ·↑η_μ) · I
  -- RHS: ↑(∑ realA - ∑ realB) + ↑(2 * ∑ realC) · I
  congr 1
  · -- Real part: sum of ℂ differences = ↑(real differences)
    rw [Finset.sum_sub_distrib
      (f := fun x => (metricSignature d x : ℂ) * (ξ x : ℂ) * (ξ x : ℂ))
      (g := fun x => (metricSignature d x : ℂ) * (η x : ℂ) * (η x : ℂ))]
    push_cast [map_sum]; rfl
  · -- Imaginary part
    congr 1; push_cast [map_sum, Finset.mul_sum]
    congr 1; ext μ; ring

/-- The real part of the complex quadratic form on ξ + iη:
    Re Q(ξ + iη) = minkowskiNormSq(ξ) - minkowskiNormSq(η) -/
theorem complexQuadratic_re (ξ η : MinkowskiSpace d) :
    (complexMinkowskiQuadratic d (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I)).re =
    minkowskiNormSq d ξ - minkowskiNormSq d η := by
  rw [complexQuadratic_decomp]
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]

/-- The imaginary part of the complex quadratic form on ξ + iη:
    Im Q(ξ + iη) = 2 · minkowskiInner(ξ, η) -/
theorem complexQuadratic_im (ξ η : MinkowskiSpace d) :
    (complexMinkowskiQuadratic d (fun μ => (ξ μ : ℂ) + (η μ : ℂ) * Complex.I)).im =
    2 * minkowskiInner d ξ η := by
  rw [complexQuadratic_decomp]
  simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]



/-- The complex quadratic form is preserved by the complex Lorentz group:
    Q(Λζ) = Q(ζ) for all ζ ∈ ℂ^{d+1} and Λ ∈ L₊(ℂ).

    This follows from Λᵀ η Λ = η applied to the complex bilinear form. -/
theorem complexQuadratic_lorentz_invariant
    (Λ_val : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hΛ : ∀ (μ ν : Fin (d + 1)),
      ∑ α : Fin (d + 1), (metricSignature d α : ℂ) * Λ_val α μ * Λ_val α ν =
      if μ = ν then (metricSignature d μ : ℂ) else 0)
    (ζ : Fin (d + 1) → ℂ) :
    complexMinkowskiQuadratic d (fun μ => ∑ ν, Λ_val μ ν * ζ ν) =
    complexMinkowskiQuadratic d ζ := by
  unfold complexMinkowskiQuadratic
  -- Strategy: expand each μ-term into double sum, swap sums, apply hΛ, collapse
  -- Helper: for each μ, expand η_μ (Σ Λζ)² = Σ_{ν₁,ν₂} η_μ Λ_{ν₁} Λ_{ν₂} ζ_{ν₁} ζ_{ν₂}
  have expand_μ : ∀ μ : Fin (d + 1),
      (metricSignature d μ : ℂ) * (∑ ν, Λ_val μ ν * ζ ν) ^ 2 =
      ∑ ν₁ : Fin (d + 1), ∑ ν₂ : Fin (d + 1),
        (metricSignature d μ : ℂ) * Λ_val μ ν₁ * Λ_val μ ν₂ * (ζ ν₁ * ζ ν₂) := by
    intro μ
    rw [sq, Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    congr 1; ext ν₁; congr 1; ext ν₂; ring
  simp_rw [expand_μ]
  -- Now LHS = Σ_μ Σ_ν₁ Σ_ν₂ η_μ Λ_{μν₁} Λ_{μν₂} (ζ_{ν₁} ζ_{ν₂})
  -- Go through intermediate: Σ_ν₁ Σ_ν₂ (Σ_μ η_μ Λ_{μν₁} Λ_{μν₂}) (ζ_{ν₁} ζ_{ν₂})
  trans (∑ ν₁ : Fin (d + 1), ∑ ν₂ : Fin (d + 1),
    (∑ μ : Fin (d + 1), (metricSignature d μ : ℂ) * Λ_val μ ν₁ * Λ_val μ ν₂) *
    (ζ ν₁ * ζ ν₂))
  · -- Swap sums and factor out ζ
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext ν₁; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext ν₁; arg 2; ext ν₂; rw [← Finset.sum_mul]
  · -- Apply hΛ (Kronecker delta) and collapse inner sum
    conv_lhs => arg 2; ext ν₁; arg 2; ext ν₂; rw [show
      (∑ μ : Fin (d + 1), (metricSignature d μ : ℂ) * Λ_val μ ν₁ * Λ_val μ ν₂) =
      if ν₁ = ν₂ then (metricSignature d ν₁ : ℂ) else 0 from hΛ ν₁ ν₂]
    simp only [ite_mul, zero_mul]
    congr 1; ext ν
    rw [Finset.sum_ite_eq]
    simp [sq]



end MinkowskiSpace

end
