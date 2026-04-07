/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import OSReconstruction.Wightman.Spacetime.Metric

/-!
# The Full and Connected Lorentz Groups

This file defines both the full Lorentz group `O(1,d)` and its connected
proper-orthochronous subgroup `SO⁺(1,d)` as groups of linear transformations
preserving the Minkowski metric.

## Main Definitions

* `FullLorentzGroup d` - The indefinite orthogonal group O(1,d) ⊂ GL(d+1, ℝ)
* `LorentzGroup d` - The connected proper orthochronous group SO⁺(1,d)
* `FullLorentzGroup.IsProper` - Proper Lorentz transformations (det = 1)
* `FullLorentzGroup.IsOrthochronous` - Orthochronous transformations (Λ₀₀ ≥ 1)

## Mathematical Background

The full Lorentz group O(1,d) consists of all real (d+1)×(d+1) matrices Λ satisfying:
  Λᵀ η Λ = η
where η = diag(-1, +1, ..., +1) is the Minkowski metric.

The group has four connected components, characterized by:
- det(Λ) = ±1 (proper vs improper)
- Λ₀₀ ≥ 1 or Λ₀₀ ≤ -1 (orthochronous vs non-orthochronous)

The proper orthochronous Lorentz group SO⁺(1,d) is the identity component.
This file now uses `LorentzGroup d` for that connected component, while
`FullLorentzGroup d` denotes the full disconnected group.

## References

* Weinberg, "The Quantum Theory of Fields", Vol. I, Chapter 2
* Streater-Wightman, "PCT, Spin and Statistics, and All That"
-/

noncomputable section

open Matrix BigOperators

set_option linter.unusedSectionVars false

variable (d : ℕ) [NeZero d]

/-! ### The Lorentz Group -/

/-- A matrix Λ is a Lorentz transformation if it preserves the Minkowski metric:
    Λᵀ η Λ = η -/
def IsLorentzMatrix (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Prop :=
  Λᵀ * minkowskiMatrix d * Λ = minkowskiMatrix d

namespace IsLorentzMatrix

variable {d : ℕ} [NeZero d]

/-- The identity matrix is a Lorentz transformation -/
theorem one : IsLorentzMatrix d (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
  simp only [IsLorentzMatrix, transpose_one, one_mul, mul_one]

/-- The product of two Lorentz transformations is a Lorentz transformation -/
theorem mul {Λ₁ Λ₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h₁ : IsLorentzMatrix d Λ₁) (h₂ : IsLorentzMatrix d Λ₂) :
    IsLorentzMatrix d (Λ₁ * Λ₂) := by
  unfold IsLorentzMatrix at *
  simp only [transpose_mul]
  calc Λ₂ᵀ * Λ₁ᵀ * minkowskiMatrix d * (Λ₁ * Λ₂)
      = Λ₂ᵀ * (Λ₁ᵀ * minkowskiMatrix d * Λ₁) * Λ₂ := by noncomm_ring
    _ = Λ₂ᵀ * minkowskiMatrix d * Λ₂ := by rw [h₁]
    _ = minkowskiMatrix d := h₂

/-- A Lorentz transformation is invertible -/
theorem isUnit (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : IsLorentzMatrix d Λ) :
    IsUnit Λ := by
  rw [Matrix.isUnit_iff_isUnit_det]
  -- From Λᵀ η Λ = η, taking determinants: det(Λ)² det(η) = det(η)
  -- Since det(η) ≠ 0, we get det(Λ)² = 1, so det(Λ) = ±1
  have h_det_sq : Λ.det ^ 2 = 1 := by
    have h_eq := congr_arg Matrix.det h
    simp only [det_mul, det_transpose] at h_eq
    have h_eta_ne : (minkowskiMatrix d).det ≠ 0 := by
      rw [MinkowskiMatrix.det_eq]
      norm_num
    field_simp at h_eq
    linarith [sq_nonneg Λ.det]
  rcases sq_eq_one_iff.mp h_det_sq with hd | hd <;> simp [hd]

/-- The inverse of a Lorentz transformation is also a Lorentz transformation.
    The inverse is given by Λ⁻¹ = η Λᵀ η. -/
theorem inv_eq (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : IsLorentzMatrix d Λ) :
    Λ⁻¹ = minkowskiMatrix d * Λᵀ * minkowskiMatrix d := by
  -- η Λᵀ η is a left inverse, so it equals the matrix inverse
  have hleft : (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * Λ = 1 := by
    unfold IsLorentzMatrix at h
    calc (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * Λ
        = minkowskiMatrix d * Λᵀ * (minkowskiMatrix d * Λ) := by noncomm_ring
      _ = minkowskiMatrix d * (Λᵀ * minkowskiMatrix d * Λ) := by noncomm_ring
      _ = minkowskiMatrix d * minkowskiMatrix d := by rw [h]
      _ = 1 := MinkowskiMatrix.mul_self d
  exact Matrix.inv_eq_left_inv hleft

/-- The determinant of a Lorentz transformation is ±1 -/
theorem det_eq_pm_one (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : IsLorentzMatrix d Λ) :
    Λ.det = 1 ∨ Λ.det = -1 := by
  -- From Λᵀ η Λ = η, taking determinants:
  -- det(Λᵀ) det(η) det(Λ) = det(η)
  -- det(Λ)² det(η) = det(η)
  -- Since det(η) = -1 ≠ 0, we get det(Λ)² = 1
  have h_det : Λ.det ^ 2 = 1 := by
    have h_eq := congr_arg Matrix.det h
    simp only [det_mul, det_transpose] at h_eq
    have h_eta_ne : (minkowskiMatrix d).det ≠ 0 := by
      rw [MinkowskiMatrix.det_eq]
      norm_num
    field_simp at h_eq
    linarith [sq_nonneg Λ.det]
  rcases sq_eq_one_iff.mp h_det with h1 | h1
  · left; exact h1
  · right; exact h1

/-- The first column of a Lorentz matrix satisfies the "unit timelike" condition:
    Λ₀₀² - Σⱼ>₀ Λⱼ₀² = 1
    This comes from (Λᵀ η Λ)₀₀ = η₀₀ = -1. -/
theorem first_column_timelike (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : IsLorentzMatrix d Λ) :
    Λ 0 0 ^ 2 = 1 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ j 0 ^ 2 := by
  unfold IsLorentzMatrix at h
  have h00 : (Λᵀ * minkowskiMatrix d * Λ) 0 0 = (minkowskiMatrix d) 0 0 := by rw [h]
  simp only [mul_apply, minkowskiMatrix, diagonal_apply, transpose_apply,
    MinkowskiSpace.metricSignature, ite_true] at h00
  have hinner : ∀ j : Fin (d + 1),
      (∑ k : Fin (d + 1), Λ k 0 * (if k = j then (if k = 0 then (-1:ℝ) else 1) else 0)) =
      (if j = 0 then -1 else 1) * Λ j 0 := by
    intro j
    rw [Finset.sum_eq_single j]
    · by_cases hj : j = 0 <;> simp [hj]
    · intro k _ hkj; simp [hkj]
    · simp
  have h00' : (∑ j : Fin (d + 1), (if j = 0 then (-1:ℝ) else 1) * Λ j 0 * Λ j 0) = -1 := by
    trans (∑ j, (∑ k, Λ k 0 * (if k = j then if k = 0 then (-1:ℝ) else 1 else 0)) * Λ j 0)
    · apply Finset.sum_congr rfl; intro j _; rw [hinner j]
    · exact h00
  have hsplit : (∑ j : Fin (d + 1), (if j = 0 then (-1:ℝ) else 1) * Λ j 0 * Λ j 0) =
      -Λ 0 0 ^ 2 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ j 0 ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (0 : Fin (d+1)))]
    simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton,
      neg_mul, one_mul, sq]
    ring_nf
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hj, sq]
  rw [hsplit] at h00'
  linarith

/-- The first row of a Lorentz matrix satisfies the "unit timelike" condition:
    Λ₀₀² - Σⱼ>₀ Λ₀ⱼ² = 1
    This comes from (Λ η Λᵀ)₀₀ = η₀₀ = -1, using Λ η Λᵀ = η (from Λᵀ η Λ = η). -/
theorem first_row_timelike (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : IsLorentzMatrix d Λ) :
    Λ 0 0 ^ 2 = 1 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ 0 j ^ 2 := by
  -- From Λᵀ η Λ = η, we derive Λ η Λᵀ = η:
  -- Multiply on left by η Λ and right by Λᵀ η, using η² = 1 and Λᵀ η Λ = η:
  -- η Λ (Λᵀ η Λ) Λᵀ η = η Λ η Λᵀ η
  -- η Λ η Λᵀ η = η Λ η Λᵀ η (trivially)
  -- But η (Λ Λᵀ η Λ Λᵀ) η = η η η = η by associativity games
  -- The key insight: (η Λᵀ η) is the left inverse of Λ, so Λ (η Λᵀ η) = 1
  have h' : Λ * minkowskiMatrix d * Λᵀ = minkowskiMatrix d := by
    -- First show (η Λᵀ η) Λ = 1
    have hleft : (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * Λ = 1 := by
      unfold IsLorentzMatrix at h
      calc (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * Λ
          = minkowskiMatrix d * Λᵀ * (minkowskiMatrix d * Λ) := by noncomm_ring
        _ = minkowskiMatrix d * (Λᵀ * minkowskiMatrix d * Λ) := by noncomm_ring
        _ = minkowskiMatrix d * minkowskiMatrix d := by rw [h]
        _ = 1 := MinkowskiMatrix.mul_self d
    -- By Matrix.mul_eq_one_comm, also Λ (η Λᵀ η) = 1
    have hright : Λ * (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) = 1 :=
      mul_eq_one_comm.mp hleft
    -- Now: Λ η Λᵀ = Λ η Λᵀ (η η) = (Λ η Λᵀ η) η = (Λ (η Λᵀ η)) η = 1 · η = η
    calc Λ * minkowskiMatrix d * Λᵀ
        = Λ * minkowskiMatrix d * Λᵀ * (minkowskiMatrix d * minkowskiMatrix d) := by
          rw [MinkowskiMatrix.mul_self]; simp
      _ = Λ * (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * minkowskiMatrix d := by
          noncomm_ring
      _ = 1 * minkowskiMatrix d := by rw [hright]
      _ = minkowskiMatrix d := one_mul _
  -- Now extract the (0,0) entry of Λ η Λᵀ = η
  have h00 : (Λ * minkowskiMatrix d * Λᵀ) 0 0 = (minkowskiMatrix d) 0 0 := by rw [h']
  simp only [mul_apply, minkowskiMatrix, diagonal_apply, transpose_apply,
    MinkowskiSpace.metricSignature, ite_true] at h00
  have hinner : ∀ j : Fin (d + 1),
      (∑ k : Fin (d + 1), Λ 0 k * (if k = j then (if k = 0 then (-1:ℝ) else 1) else 0)) =
      (if j = 0 then -1 else 1) * Λ 0 j := by
    intro j
    rw [Finset.sum_eq_single j]
    · by_cases hj : j = 0 <;> simp [hj]
    · intro k _ hkj; simp [hkj]
    · simp
  have h00' : (∑ j : Fin (d + 1), (if j = 0 then (-1:ℝ) else 1) * Λ 0 j * Λ 0 j) = -1 := by
    trans (∑ j, (∑ k, Λ 0 k * (if k = j then if k = 0 then (-1:ℝ) else 1 else 0)) * Λ 0 j)
    · apply Finset.sum_congr rfl; intro j _; rw [hinner j]
    · exact h00
  have hsplit : (∑ j : Fin (d + 1), (if j = 0 then (-1:ℝ) else 1) * Λ 0 j * Λ 0 j) =
      -Λ 0 0 ^ 2 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ 0 j ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (0 : Fin (d+1)))]
    simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton,
      neg_mul, one_mul, sq]
    ring_nf
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hj, sq]
  rw [hsplit] at h00'
  linarith

/-- The (0,0) component of a Lorentz transformation satisfies |Λ₀₀| ≥ 1 -/
theorem abs_zero_zero_ge_one (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : IsLorentzMatrix d Λ) :
    |Λ 0 0| ≥ 1 := by
  -- From (Λᵀ η Λ)₀₀ = η₀₀ = -1, we have:
  -- -Λ₀₀² + Σᵢ>₀ Λᵢ₀² = -1
  -- So Λ₀₀² = 1 + Σᵢ>₀ Λᵢ₀² ≥ 1
  unfold IsLorentzMatrix at h
  -- Extract the (0,0) entry of the equation Λᵀ η Λ = η
  have h00 : (Λᵀ * minkowskiMatrix d * Λ) 0 0 = (minkowskiMatrix d) 0 0 := by
    rw [h]
  simp only [mul_apply, minkowskiMatrix, diagonal_apply, transpose_apply,
    MinkowskiSpace.metricSignature, ite_true] at h00
  -- The inner sum simplifies: only k=j contributes (η is diagonal)
  -- h00 has form: Σⱼ (Σₖ Λₖ₀ · ηₖⱼ) · Λⱼ₀ = -1
  have hinner : ∀ j : Fin (d + 1),
      (∑ k : Fin (d + 1), Λ k 0 * (if k = j then (if k = 0 then (-1:ℝ) else 1) else 0)) =
      (if j = 0 then -1 else 1) * Λ j 0 := by
    intro j
    rw [Finset.sum_eq_single j]
    · by_cases hj : j = 0 <;> simp [hj]
    · intro k _ hkj; simp [hkj]
    · simp
  have h00' : (∑ j : Fin (d + 1), (if j = 0 then (-1:ℝ) else 1) * Λ j 0 * Λ j 0) = -1 := by
    trans (∑ j, (∑ k, Λ k 0 * (if k = j then if k = 0 then (-1:ℝ) else 1 else 0)) * Λ j 0)
    · apply Finset.sum_congr rfl; intro j _; rw [hinner j]
    · exact h00
  -- h00': Σⱼ (if j = 0 then -1 else 1) · Λⱼ₀² = -1
  -- Now h00: Σⱼ (if j = 0 then -1 else 1) · Λⱼ₀ · Λⱼ₀ = -1
  -- i.e., -Λ₀₀² + Σⱼ>₀ Λⱼ₀² = -1, so Λ₀₀² = 1 + Σⱼ>₀ Λⱼ₀²
  have hsplit : (∑ j : Fin (d + 1), (if j = 0 then (-1:ℝ) else 1) * Λ j 0 * Λ j 0) =
      -Λ 0 0 ^ 2 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ j 0 ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (0 : Fin (d+1)))]
    simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton,
      neg_mul, one_mul, sq]
    ring_nf
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hj, sq]
  rw [hsplit] at h00'
  -- h00': -Λ₀₀² + Σⱼ≠₀ Λⱼ₀² = -1
  have hsum_nonneg : (∑ j ∈ Finset.univ.filter (· ≠ 0), Λ j 0 ^ 2) ≥ 0 := by
    apply Finset.sum_nonneg
    intro j _; exact sq_nonneg _
  have hsq : Λ 0 0 ^ 2 ≥ 1 := by linarith
  -- From x² ≥ 1, we get |x| ≥ 1 using x² = |x|² and sqrt monotonicity
  have hsq_abs : |Λ 0 0| ^ 2 ≥ 1 := by rwa [sq_abs]
  nlinarith [sq_nonneg (|Λ 0 0| - 1), sq_nonneg (|Λ 0 0| + 1), abs_nonneg (Λ 0 0)]

end IsLorentzMatrix

/-- The full Lorentz group O(1,d) as matrices preserving the Minkowski metric.
    This is the indefinite orthogonal group. -/
def FullLorentzGroup (d : ℕ) [NeZero d] :=
  { Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ // IsLorentzMatrix d Λ }

namespace FullLorentzGroup

local notation "LorentzGroup" => FullLorentzGroup

variable {d : ℕ} [NeZero d]

instance : Coe (LorentzGroup d) (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := ⟨Subtype.val⟩

@[ext]
theorem ext {Λ₁ Λ₂ : LorentzGroup d} (h : Λ₁.val = Λ₂.val) : Λ₁ = Λ₂ :=
  Subtype.ext h

/-- Coercion to matrix -/
theorem toMatrix (Λ : LorentzGroup d) : (Λ : Matrix _ _ ℝ) = Λ.val := rfl

/-- Extensionality for matrix entries -/
theorem ext_entries {Λ₁ Λ₂ : LorentzGroup d} :
    Λ₁ = Λ₂ ↔ ∀ i j, Λ₁.val i j = Λ₂.val i j :=
  ⟨fun h _ _ => by rw [h], fun h => ext (Matrix.ext fun i j => h i j)⟩

/-- Key lemma: (η Λᵀ η) Λ = 1 for Lorentz matrices.
    This follows from Λᵀ η Λ = η by left multiplication by η. -/
theorem lorentz_inv_mul {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (h : IsLorentzMatrix d Λ) :
    (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * Λ = 1 := by
  unfold IsLorentzMatrix at h
  calc (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * Λ
      = minkowskiMatrix d * Λᵀ * (minkowskiMatrix d * Λ) := by noncomm_ring
    _ = minkowskiMatrix d * (Λᵀ * minkowskiMatrix d * Λ) := by noncomm_ring
    _ = minkowskiMatrix d * minkowskiMatrix d := by rw [h]
    _ = 1 := MinkowskiMatrix.mul_self d

/-- Key lemma: Λ (η Λᵀ η) = 1 for Lorentz matrices.
    This follows from the left inverse property and invertibility. -/
theorem lorentz_mul_inv {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (h : IsLorentzMatrix d Λ) :
    Λ * (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) = 1 := by
  have hleft := lorentz_inv_mul h
  -- Use Matrix.mul_eq_one_comm: if M * N = 1 then N * M = 1
  exact mul_eq_one_comm.mp hleft

/-- The inverse formula η Λᵀ η satisfies the Lorentz condition.
    From Λᵀ η Λ = η, we derive (Λ⁻¹)ᵀ η Λ⁻¹ = η. -/
theorem lorentz_inv_isLorentz {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (h : IsLorentzMatrix d Λ) :
    IsLorentzMatrix d (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) := by
  unfold IsLorentzMatrix
  -- Compute the transpose: (η Λᵀ η)ᵀ = η Λ η
  have htrans : (minkowskiMatrix d * Λᵀ * minkowskiMatrix d)ᵀ =
      minkowskiMatrix d * Λ * minkowskiMatrix d := by
    simp only [transpose_mul, MinkowskiMatrix.transpose_eq, transpose_transpose]
    noncomm_ring
  rw [htrans]
  -- We need to show (η Λ η) η (η Λᵀ η) = η
  have hmul := lorentz_mul_inv h
  calc minkowskiMatrix d * Λ * minkowskiMatrix d * minkowskiMatrix d *
         (minkowskiMatrix d * Λᵀ * minkowskiMatrix d)
      = minkowskiMatrix d * Λ * (minkowskiMatrix d * minkowskiMatrix d) *
         (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) := by noncomm_ring
    _ = minkowskiMatrix d * Λ * 1 *
         (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) := by rw [MinkowskiMatrix.mul_self]
    _ = minkowskiMatrix d * Λ *
         (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) := by noncomm_ring
    _ = minkowskiMatrix d * (Λ * (minkowskiMatrix d * Λᵀ * minkowskiMatrix d)) := by noncomm_ring
    _ = minkowskiMatrix d * 1 := by rw [hmul]
    _ = minkowskiMatrix d := by noncomm_ring

/-- The Lorentz group forms a group under matrix multiplication -/
instance : Group (LorentzGroup d) where
  mul Λ₁ Λ₂ := ⟨Λ₁.val * Λ₂.val, IsLorentzMatrix.mul Λ₁.2 Λ₂.2⟩
  one := ⟨1, IsLorentzMatrix.one⟩
  inv Λ := ⟨minkowskiMatrix d * Λ.valᵀ * minkowskiMatrix d, lorentz_inv_isLorentz Λ.2⟩
  mul_assoc a b c := ext (Matrix.mul_assoc _ _ _)
  one_mul a := ext (Matrix.one_mul _)
  mul_one a := ext (Matrix.mul_one _)
  inv_mul_cancel a := ext (lorentz_inv_mul a.2)

/-- The determinant of a Lorentz transformation is ±1 -/
theorem det_eq_pm_one (Λ : LorentzGroup d) : Λ.val.det = 1 ∨ Λ.val.det = -1 :=
  IsLorentzMatrix.det_eq_pm_one _ Λ.2

/-! ### Proper and Orthochronous Lorentz Transformations -/

/-- A Lorentz transformation is proper if det(Λ) = 1 -/
def IsProper (Λ : LorentzGroup d) : Prop :=
  Λ.val.det = 1

/-- A Lorentz transformation is orthochronous if Λ₀₀ ≥ 1 -/
def IsOrthochronous (Λ : LorentzGroup d) : Prop :=
  Λ.val 0 0 ≥ 1

/-! ### Properties of Proper Transformations -/

namespace IsProper

/-- The identity is proper: det(I) = 1 -/
theorem one : IsProper (1 : LorentzGroup d) := by
  simp only [IsProper]
  have h : (1 : LorentzGroup d).val = 1 := rfl
  simp [h]

/-- The product of proper transformations is proper: det(ΛΛ') = det(Λ)det(Λ') = 1 -/
theorem mul {Λ₁ Λ₂ : LorentzGroup d} (h₁ : IsProper Λ₁) (h₂ : IsProper Λ₂) :
    IsProper (Λ₁ * Λ₂) := by
  simp only [IsProper] at *
  have h : (Λ₁ * Λ₂).val = Λ₁.val * Λ₂.val := rfl
  simp only [h, det_mul, h₁, h₂, mul_one]

/-- The inverse of a proper transformation is proper: det(Λ⁻¹) = 1/det(Λ) = 1 -/
theorem inv {Λ : LorentzGroup d} (h : IsProper Λ) : IsProper Λ⁻¹ := by
  simp only [IsProper] at *
  -- Λ⁻¹ = η Λᵀ η, so det(Λ⁻¹) = det(η)² det(Λᵀ) = det(Λ) = 1
  have hval : Λ⁻¹.val = minkowskiMatrix d * Λ.valᵀ * minkowskiMatrix d := rfl
  simp only [hval, det_mul, det_transpose]
  rw [MinkowskiMatrix.det_eq]
  ring_nf
  exact h

end IsProper

/-! ### Properties of Orthochronous Transformations -/

/-- The hyperbolic bound: for a, b ≥ 1, we have a*b - √(a²-1)*√(b²-1) ≥ 1.
    Equality holds when a = b = 1, or viewing a = cosh(α), b = cosh(β),
    the expression equals cosh(α - β) ≥ 1. -/
theorem hyperbolic_bound {a b : ℝ} (ha : a ≥ 1) (hb : b ≥ 1) :
    a * b - Real.sqrt (a ^ 2 - 1) * Real.sqrt (b ^ 2 - 1) ≥ 1 := by
  -- We prove (ab - 1)² ≥ (√(a²-1) √(b²-1))² = (a²-1)(b²-1)
  -- Expanding: a²b² - 2ab + 1 ≥ a²b² - a² - b² + 1
  -- Simplifying: -2ab ≥ -a² - b², i.e., a² + b² - 2ab ≥ 0, i.e., (a-b)² ≥ 0 ✓
  have ha_sq : a ^ 2 - 1 ≥ 0 := by nlinarith [sq_nonneg a]
  have hb_sq : b ^ 2 - 1 ≥ 0 := by nlinarith [sq_nonneg b]
  have hab : a * b ≥ 1 := by nlinarith
  have hsqrt_nonneg : Real.sqrt (a ^ 2 - 1) * Real.sqrt (b ^ 2 - 1) ≥ 0 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- Key inequality: (ab - 1)² ≥ (a² - 1)(b² - 1)
  have hkey : (a * b - 1) ^ 2 ≥ (a ^ 2 - 1) * (b ^ 2 - 1) := by
    have h : (a * b - 1) ^ 2 - (a ^ 2 - 1) * (b ^ 2 - 1) = (a - b) ^ 2 := by ring
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    nlinarith [sq_nonneg (a - b)]
  -- Since ab ≥ 1, we have ab - 1 ≥ 0
  have hab1 : a * b - 1 ≥ 0 := by linarith
  -- From (ab - 1)² ≥ (a² - 1)(b² - 1) and ab - 1 ≥ 0:
  -- ab - 1 ≥ √((a² - 1)(b² - 1)) = √(a² - 1) · √(b² - 1)
  have hsqrt_prod : Real.sqrt ((a ^ 2 - 1) * (b ^ 2 - 1)) =
      Real.sqrt (a ^ 2 - 1) * Real.sqrt (b ^ 2 - 1) :=
    Real.sqrt_mul ha_sq _
  rw [← hsqrt_prod]
  have hsqrt_ineq : a * b - 1 ≥ Real.sqrt ((a ^ 2 - 1) * (b ^ 2 - 1)) := by
    rw [← Real.sqrt_sq hab1]
    exact Real.sqrt_le_sqrt hkey
  linarith

namespace IsOrthochronous

/-- The identity is orthochronous: I₀₀ = 1 ≥ 1 -/
theorem one : IsOrthochronous (1 : LorentzGroup d) := by
  simp only [IsOrthochronous]
  have h : (1 : LorentzGroup d).val = 1 := rfl
  simp [h]

/-- The product of orthochronous Lorentz transformations is orthochronous.

    This is a fundamental fact about the Lorentz group following from the constraint
    Λᵀ η Λ = η. The (0,0) entry of the product satisfies:
    (Λ₁Λ₂)₀₀ = Σⱼ (Λ₁)₀ⱼ (Λ₂)ⱼ₀

    Using the Lorentz condition and properties of timelike vectors, one shows
    that if (Λ₁)₀₀ ≥ 1 and (Λ₂)₀₀ ≥ 1, then (Λ₁Λ₂)₀₀ ≥ 1.

    The proof uses that the (0,0) entry squared exceeds 1 + sum of spatial entries squared. -/
theorem mul {Λ₁ Λ₂ : LorentzGroup d} (h₁ : IsOrthochronous Λ₁) (h₂ : IsOrthochronous Λ₂) :
    IsOrthochronous (Λ₁ * Λ₂) := by
  simp only [IsOrthochronous] at *
  -- Step 1: Express (Λ₁ * Λ₂)₀₀ as a sum
  have hprod : (Λ₁ * Λ₂).val 0 0 = ∑ j : Fin (d + 1), Λ₁.val 0 j * Λ₂.val j 0 := rfl
  -- Step 2: Split into j=0 term and j≠0 sum
  have hsplit : ∑ j : Fin (d + 1), Λ₁.val 0 j * Λ₂.val j 0 =
      Λ₁.val 0 0 * Λ₂.val 0 0 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ₁.val 0 j * Λ₂.val j 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (0 : Fin (d+1)))]
    simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton]
  rw [hprod, hsplit]
  -- Step 3: Get the "unit timelike" conditions from Lorentz constraint
  have hrow := IsLorentzMatrix.first_row_timelike Λ₁.val Λ₁.2
  have hcol := IsLorentzMatrix.first_column_timelike Λ₂.val Λ₂.2
  -- Step 4: Define the spatial sums
  let S₁ := ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ₁.val 0 j ^ 2
  let S₂ := ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ₂.val j 0 ^ 2
  have hS₁_eq : S₁ = Λ₁.val 0 0 ^ 2 - 1 := by simp only [S₁]; linarith [hrow]
  have hS₂_eq : S₂ = Λ₂.val 0 0 ^ 2 - 1 := by simp only [S₂]; linarith [hcol]
  have hS₁_nonneg : S₁ ≥ 0 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hS₂_nonneg : S₂ ≥ 0 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  -- Step 5: Apply Cauchy-Schwarz: (Σaᵢbᵢ)² ≤ (Σaᵢ²)(Σbᵢ²)
  -- So |Σaᵢbᵢ| ≤ √(Σaᵢ²) * √(Σbᵢ²)
  have hCS_sq : (∑ j ∈ Finset.univ.filter (· ≠ 0), Λ₁.val 0 j * Λ₂.val j 0) ^ 2 ≤ S₁ * S₂ := by
    -- Use Mathlib's Cauchy-Schwarz: sum_mul_sq_le_sq_mul_sq
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hCS : |∑ j ∈ Finset.univ.filter (· ≠ 0), Λ₁.val 0 j * Λ₂.val j 0| ≤
      Real.sqrt S₁ * Real.sqrt S₂ := by
    rw [← Real.sqrt_mul hS₁_nonneg S₂]
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hCS_sq
  -- The spatial sum is bounded by √S₁ * √S₂
  have hbound : -(Real.sqrt S₁ * Real.sqrt S₂) ≤
      ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ₁.val 0 j * Λ₂.val j 0 := by
    have := neg_abs_le (∑ j ∈ Finset.univ.filter (· ≠ 0), Λ₁.val 0 j * Λ₂.val j 0)
    linarith [hCS]
  -- Step 6: Apply the hyperbolic bound
  have hS₁_eq' : Real.sqrt S₁ = Real.sqrt (Λ₁.val 0 0 ^ 2 - 1) := by rw [hS₁_eq]
  have hS₂_eq' : Real.sqrt S₂ = Real.sqrt (Λ₂.val 0 0 ^ 2 - 1) := by rw [hS₂_eq]
  have hhyp := hyperbolic_bound h₁ h₂
  calc Λ₁.val 0 0 * Λ₂.val 0 0 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ₁.val 0 j * Λ₂.val j 0
      ≥ Λ₁.val 0 0 * Λ₂.val 0 0 - Real.sqrt S₁ * Real.sqrt S₂ := by linarith [hbound]
    _ = Λ₁.val 0 0 * Λ₂.val 0 0 - Real.sqrt (Λ₁.val 0 0 ^ 2 - 1) * Real.sqrt (Λ₂.val 0 0 ^ 2 - 1) := by
        rw [hS₁_eq', hS₂_eq']
    _ ≥ 1 := hhyp

/-- The inverse of an orthochronous transformation is orthochronous.

    Since Λ⁻¹ = η Λᵀ η for Lorentz transformations, and the (0,0) entry of
    a transpose equals the original (0,0) entry, we have (Λ⁻¹)₀₀ = (Λ)₀₀ ≥ 1.

    Proof sketch: For diagonal η with η₀₀ = -1 and ηᵢᵢ = 1 for i > 0,
    (η Λᵀ η)₀₀ = Σⱼ η₀ⱼ (Σₖ Λₖⱼ ηₖ₀) = η₀₀ · Λ₀₀ · η₀₀ = (-1)·Λ₀₀·(-1) = Λ₀₀ ≥ 1. -/
theorem inv {Λ : LorentzGroup d} (h : IsOrthochronous Λ) : IsOrthochronous Λ⁻¹ := by
  simp only [IsOrthochronous] at *
  have hval : Λ⁻¹.val = minkowskiMatrix d * Λ.valᵀ * minkowskiMatrix d := rfl
  -- The (0,0) entry of η Λᵀ η equals Λ₀₀ due to diagonal structure of η
  have hentry : (minkowskiMatrix d * Λ.valᵀ * minkowskiMatrix d) 0 0 = Λ.val 0 0 := by
    -- For diagonal η, (η Aᵀ η)₀₀ = η₀₀ · A₀₀ · η₀₀ = (-1)·A₀₀·(-1) = A₀₀
    simp only [mul_apply, minkowskiMatrix, diagonal_apply, transpose_apply,
      MinkowskiSpace.metricSignature]
    simp only [ite_true]
    -- The inner sum: only k=0 contributes (diagonal η)
    have hinner : ∀ x : Fin (d + 1),
        (∑ k : Fin (d + 1), (if (0 : Fin (d+1)) = k then (-1 : ℝ) else 0) * Λ.val x k) =
        -Λ.val x 0 := by
      intro x
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk; simp [hk.symm]
      · simp
    -- Rewrite using hinner
    have hsum : ∀ x : Fin (d + 1),
        (∑ k, (if (0 : Fin (d+1)) = k then (-1 : ℝ) else 0) * Λ.val x k) *
        (if x = 0 then if x = 0 then (-1 : ℝ) else 1 else 0) =
        (if x = 0 then Λ.val 0 0 else 0) := by
      intro x
      rw [hinner x]
      by_cases hx : x = 0
      · simp [hx]
      · simp [hx]
    trans (∑ x : Fin (d + 1), if x = 0 then Λ.val 0 0 else 0)
    · exact Finset.sum_congr rfl (fun x _ => hsum x)
    · simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hval, hentry]
  exact h

end IsOrthochronous

/-! ### Special Elements -/

/-- Space inversion (parity): P = diag(+1, -1, -1, ..., -1)
    Action: (t, x) ↦ (t, -x). Keeps time, flips spatial coordinates.
    Note: P = -η in the mostly positive convention. -/
def parity : LorentzGroup d := ⟨
  diagonal (fun i => if i = 0 then 1 else -1),
  by
    -- Pᵀ η P = P η P (since P diagonal) = η because Pᵢᵢ² ηᵢᵢ = ηᵢᵢ
    -- Key: P = -η, so Pᵀ η P = (-η) η (-η) = η η η = η
    show (diagonal (fun i => if i = 0 then (1 : ℝ) else -1))ᵀ *
        minkowskiMatrix d * diagonal (fun i => if i = 0 then 1 else -1) = minkowskiMatrix d
    ext i j
    simp only [minkowskiMatrix, diagonal_transpose, diagonal_mul_diagonal, Matrix.mul_apply,
      diagonal_apply, MinkowskiSpace.metricSignature]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]
      by_cases h0 : i = 0 <;> simp [h0]
    · simp only [hij, ↓reduceIte]
      apply Finset.sum_eq_zero; intro k _
      by_cases hik : i = k
      · subst hik; simp [hij]
      · simp [hik]⟩

/-- Time reversal: T = diag(-1, +1, +1, ..., +1)
    Action: (t, x) ↦ (-t, x). Flips time, keeps spatial coordinates.
    Note: T = η in the mostly positive convention. -/
def timeReversal : LorentzGroup d := ⟨
  diagonal (fun i => if i = 0 then -1 else 1),
  by
    -- T = η, so Tᵀ η T = η η η = η (since η² = 1)
    show (diagonal (fun i => if i = 0 then (-1 : ℝ) else 1))ᵀ *
        minkowskiMatrix d * diagonal (fun i => if i = 0 then -1 else 1) = minkowskiMatrix d
    ext i j
    simp only [minkowskiMatrix, diagonal_transpose, diagonal_mul_diagonal, Matrix.mul_apply,
      diagonal_apply, MinkowskiSpace.metricSignature]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]
      by_cases h0 : i = 0 <;> simp [h0]
    · simp only [hij, ↓reduceIte]
      apply Finset.sum_eq_zero; intro k _
      by_cases hik : i = k
      · subst hik; simp [hij]
      · simp [hik]⟩

@[simp] theorem timeReversal_mul_timeReversal :
    timeReversal (d := d) * timeReversal (d := d) = 1 := by
  ext i j
  change ((diagonal (fun i : Fin (d + 1) => if i = 0 then (-1 : ℝ) else 1) *
      diagonal (fun i : Fin (d + 1) => if i = 0 then (-1 : ℝ) else 1)) i j) =
    ((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i j)
  rw [diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst hij
    by_cases h0 : i = 0 <;> simp [h0]
  · simp [hij]

@[simp] theorem inv_timeReversal :
    (timeReversal (d := d))⁻¹ = timeReversal (d := d) := by
  apply inv_eq_of_mul_eq_one_left
  simpa using timeReversal_mul_timeReversal (d := d)

/-- The time component of any Lorentz transformation has absolute value at least 1. -/
theorem time_zero_zero_sq_ge_one (Λ : LorentzGroup d) :
    (Λ.val 0 0) ^ 2 ≥ 1 := by
  let S := ∑ j ∈ Finset.univ.filter (· ≠ (0 : Fin (d + 1))), Λ.val 0 j ^ 2
  have hrow := IsLorentzMatrix.first_row_timelike Λ.val Λ.2
  have hS_nonneg : S ≥ 0 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hS_eq : S = Λ.val 0 0 ^ 2 - 1 := by
    simp only [S]
    linarith
  nlinarith [hS_nonneg, hS_eq]

/-- Every Lorentz transformation is either orthochronous already, or becomes
orthochronous after composing with time reversal. This isolates the genuinely
non-orthochronous component to the single discrete generator `T`. -/
theorem orthochronous_or_timeReversal_mul_orthochronous (Λ : LorentzGroup d) :
    IsOrthochronous Λ ∨ IsOrthochronous (timeReversal (d := d) * Λ) := by
  by_cases hΛ : IsOrthochronous Λ
  · exact Or.inl hΛ
  · right
    have hnot_ge : ¬ Λ.val 0 0 ≥ 1 := by
      simpa [IsOrthochronous] using hΛ
    have hlt1 : Λ.val 0 0 < 1 := lt_of_not_ge hnot_ge
    have hsq : (Λ.val 0 0) ^ 2 ≥ 1 := time_zero_zero_sq_ge_one (d := d) Λ
    have hle_neg : Λ.val 0 0 ≤ -1 := by
      nlinarith
    show (timeReversal (d := d) * Λ).val 0 0 ≥ 1
    have hentry : (timeReversal (d := d) * Λ).val 0 0 = -Λ.val 0 0 := by
      change
        (((timeReversal (d := d)).val * Λ.val) 0 0) = -Λ.val 0 0
      rw [show (timeReversal (d := d)).val =
          diagonal (fun i => if i = 0 then (-1 : ℝ) else 1) from rfl]
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk
        have h0k : (0 : Fin (d + 1)) ≠ k := by simpa using hk.symm
        simp [Matrix.diagonal, h0k]
      · simp [timeReversal]
    rw [hentry]
    linarith

/-- PT = diag(-1, -1, ..., -1) = -I, the total inversion.
    Action: (t, x) ↦ (-t, -x). -/
theorem parity_mul_timeReversal : parity (d := d) * timeReversal = ⟨-1, by
    -- (-I)ᵀ η (-I) = I η I = η
    show (-1)ᵀ * minkowskiMatrix d * (-1) = minkowskiMatrix d
    simp only [transpose_neg, transpose_one, neg_mul, one_mul, mul_neg, mul_one]
    exact neg_neg (minkowskiMatrix d)⟩ := by
  ext i j
  -- Unfold and compute the matrix product
  unfold parity timeReversal
  change ((diagonal (fun i : Fin (d+1) => if i = 0 then (1:ℝ) else -1)) *
          (diagonal (fun i : Fin (d+1) => if i = 0 then (-1:ℝ) else 1))) i j =
         ((-1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ)) i j
  rw [diagonal_mul_diagonal]
  simp only [diagonal_apply, neg_apply, one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    by_cases h0 : i = 0 <;> simp [h0]
  · simp [hij]

end FullLorentzGroup

/-- The connected proper orthochronous Lorentz group SO⁺(1,d).

This is the default physics-facing Lorentz group in the Wightman/OS layers. -/
def LorentzGroup (d : ℕ) [NeZero d] :=
  { Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ //
      IsLorentzMatrix d Λ ∧ Λ.det = 1 ∧ Λ 0 0 ≥ 1 }

namespace LorentzGroup

variable {d : ℕ} [NeZero d]

instance : Coe (LorentzGroup d) (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := ⟨Subtype.val⟩

/-- Forget the connectedness conditions and view a connected Lorentz element as
an element of the full Lorentz group. -/
def toFull (Λ : LorentzGroup d) : FullLorentzGroup d := ⟨Λ.val, Λ.prop.1⟩

instance : Coe (LorentzGroup d) (FullLorentzGroup d) := ⟨toFull⟩

@[ext]
theorem ext {Λ₁ Λ₂ : LorentzGroup d} (h : Λ₁.val = Λ₂.val) : Λ₁ = Λ₂ :=
  Subtype.ext h

/-- Coercion to matrix -/
theorem toMatrix (Λ : LorentzGroup d) : (Λ : Matrix _ _ ℝ) = Λ.val := rfl

/-- Extensionality for matrix entries -/
theorem ext_entries {Λ₁ Λ₂ : LorentzGroup d} :
    Λ₁ = Λ₂ ↔ ∀ i j, Λ₁.val i j = Λ₂.val i j :=
  ⟨fun h _ _ => by rw [h], fun h => ext (Matrix.ext fun i j => h i j)⟩

instance : Group (LorentzGroup d) where
  mul Λ₁ Λ₂ := ⟨Λ₁.val * Λ₂.val, by
    refine ⟨IsLorentzMatrix.mul Λ₁.2.1 Λ₂.2.1, ?_, ?_⟩
    · simp [Matrix.det_mul, Λ₁.2.2.1, Λ₂.2.2.1]
    · simpa [FullLorentzGroup.IsOrthochronous] using
        (FullLorentzGroup.IsOrthochronous.mul (d := d)
          (Λ₁ := toFull Λ₁) (Λ₂ := toFull Λ₂) Λ₁.2.2.2 Λ₂.2.2.2)⟩
  one := ⟨1, ⟨IsLorentzMatrix.one, by simp, by simp⟩⟩
  inv Λ := ⟨(toFull Λ)⁻¹.val, by
    refine ⟨(toFull Λ)⁻¹.2, ?_, ?_⟩
    · exact FullLorentzGroup.IsProper.inv (d := d) (Λ := toFull Λ) Λ.2.2.1
    · exact FullLorentzGroup.IsOrthochronous.inv (d := d) (Λ := toFull Λ) Λ.2.2.2⟩
  mul_assoc a b c := ext (Matrix.mul_assoc _ _ _)
  one_mul a := ext (Matrix.one_mul _)
  mul_one a := ext (Matrix.mul_one _)
  inv_mul_cancel a := by
    apply ext
    exact FullLorentzGroup.lorentz_inv_mul (d := d) a.2.1

/-- A connected Lorentz transformation is automatically proper. -/
def IsProper (Λ : LorentzGroup d) : Prop := Λ.val.det = 1

/-- A connected Lorentz transformation is automatically orthochronous. -/
def IsOrthochronous (Λ : LorentzGroup d) : Prop := Λ.val 0 0 ≥ 1

theorem det_eq_one (Λ : LorentzGroup d) : Λ.val.det = 1 := Λ.2.2.1

theorem zero_zero_ge_one (Λ : LorentzGroup d) : Λ.val 0 0 ≥ 1 := Λ.2.2.2

theorem det_eq_pm_one (Λ : LorentzGroup d) : Λ.val.det = 1 ∨ Λ.val.det = -1 := by
  left
  exact det_eq_one Λ

namespace IsProper

theorem one : IsProper (1 : LorentzGroup d) := det_eq_one 1

theorem mul {Λ₁ Λ₂ : LorentzGroup d} (h₁ : IsProper Λ₁) (h₂ : IsProper Λ₂) :
    IsProper (Λ₁ * Λ₂) := by
  exact det_eq_one (Λ₁ * Λ₂)

theorem inv {Λ : LorentzGroup d} (h : IsProper Λ) : IsProper Λ⁻¹ := by
  simpa [IsProper] using (FullLorentzGroup.IsProper.inv (d := d) (Λ := Λ.toFull) h)

end IsProper

namespace IsOrthochronous

theorem one : IsOrthochronous (1 : LorentzGroup d) := zero_zero_ge_one 1

theorem mul {Λ₁ Λ₂ : LorentzGroup d} (h₁ : IsOrthochronous Λ₁) (h₂ : IsOrthochronous Λ₂) :
    IsOrthochronous (Λ₁ * Λ₂) := by
  exact zero_zero_ge_one (Λ₁ * Λ₂)

theorem inv {Λ : LorentzGroup d} (h : IsOrthochronous Λ) : IsOrthochronous Λ⁻¹ := by
  exact zero_zero_ge_one (Λ⁻¹)

end IsOrthochronous

/-- Compatibility alias for the full parity element. -/
abbrev parity (d : ℕ) [NeZero d] : FullLorentzGroup d := FullLorentzGroup.parity (d := d)

/-- Compatibility alias for the full time-reversal element. -/
abbrev timeReversal (d : ℕ) [NeZero d] : FullLorentzGroup d := FullLorentzGroup.timeReversal (d := d)

/-- Compatibility alias for the full time-reversal involution theorem. -/
theorem timeReversal_mul_timeReversal (d : ℕ) [NeZero d] :
    timeReversal (d := d) * timeReversal (d := d) = 1 :=
  FullLorentzGroup.timeReversal_mul_timeReversal (d := d)

/-- Compatibility alias for the full-group orthochronous/time-reversal split. -/
theorem orthochronous_or_timeReversal_mul_orthochronous (Λ : FullLorentzGroup d) :
    FullLorentzGroup.IsOrthochronous Λ ∨
      FullLorentzGroup.IsOrthochronous (timeReversal (d := d) * Λ) :=
  FullLorentzGroup.orthochronous_or_timeReversal_mul_orthochronous (d := d) Λ

end LorentzGroup

/-! ### Notation -/

/-- Standard notation for the 3+1 dimensional full Lorentz group -/
abbrev FullLorentz4 := FullLorentzGroup 3

/-- Standard notation for the 3+1 dimensional connected Lorentz group -/
abbrev Lorentz4 := LorentzGroup 3

end
