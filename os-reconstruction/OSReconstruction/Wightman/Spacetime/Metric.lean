/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Matrix.Reflection

































noncomputable section

open BigOperators Matrix

set_option linter.unusedSectionVars false

variable (d : ℕ) [NeZero d]



/-- Minkowski space ℝ^{1,d} as a (d+1)-dimensional real vector space.
    The parameter d is the number of spatial dimensions. -/
abbrev MinkowskiSpace := Fin (d + 1) → ℝ

namespace MinkowskiSpace



/-- The Minkowski metric signature: η = diag(-1, +1, +1, ..., +1)
    This is the "mostly positive" or "particle physics" convention. -/
def metricSignature : Fin (d + 1) → ℝ :=
  fun i => if i = 0 then -1 else 1

/-- The metric signature at index 0 is -1 (timelike direction) -/
@[simp]
theorem metricSignature_zero : metricSignature d 0 = -1 := by
  simp [metricSignature]

/-- The metric signature at non-zero indices is +1 (spacelike directions) -/
theorem metricSignature_succ (i : Fin d) : metricSignature d (Fin.succ i) = 1 := by
  simp [metricSignature, Fin.succ_ne_zero]

/-- The metric signature squared is always 1 -/
@[simp]
theorem metricSignature_sq (i : Fin (d + 1)) : metricSignature d i ^ 2 = 1 := by
  simp only [metricSignature]
  split_ifs <;> ring

/-- The product of metric signatures at the same index gives 1 -/
@[simp]
theorem metricSignature_mul_self (i : Fin (d + 1)) :
    metricSignature d i * metricSignature d i = 1 := by
  rw [← sq]
  exact metricSignature_sq d i



/-- The Minkowski inner product (not positive definite).
    η(x, y) = -x₀y₀ + x₁y₁ + x₂y₂ + ... + x_d y_d -/
def minkowskiInner (x y : MinkowskiSpace d) : ℝ :=
  ∑ i : Fin (d + 1), metricSignature d i * x i * y i

/-- The Minkowski quadratic form (norm squared): η(x, x) -/
def minkowskiNormSq (x : MinkowskiSpace d) : ℝ :=
  minkowskiInner d x x



/-- The Minkowski inner product is symmetric -/
theorem minkowskiInner_comm (x y : MinkowskiSpace d) :
    minkowskiInner d x y = minkowskiInner d y x := by
  unfold minkowskiInner
  congr 1
  ext i
  ring

/-- The Minkowski inner product is bilinear: left addition -/
theorem minkowskiInner_add_left (x y z : MinkowskiSpace d) :
    minkowskiInner d (x + y) z = minkowskiInner d x z + minkowskiInner d y z := by
  unfold minkowskiInner
  simp only [Pi.add_apply, ← Finset.sum_add_distrib]
  congr 1
  ext i
  ring

/-- The Minkowski inner product is bilinear: right addition -/
theorem minkowskiInner_add_right (x y z : MinkowskiSpace d) :
    minkowskiInner d x (y + z) = minkowskiInner d x y + minkowskiInner d x z := by
  rw [minkowskiInner_comm, minkowskiInner_add_left, minkowskiInner_comm, minkowskiInner_comm d x z]

/-- The Minkowski inner product is bilinear: left scalar multiplication -/
theorem minkowskiInner_smul_left (c : ℝ) (x y : MinkowskiSpace d) :
    minkowskiInner d (c • x) y = c * minkowskiInner d x y := by
  unfold minkowskiInner
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  ext i
  ring

/-- The Minkowski inner product is bilinear: right scalar multiplication -/
theorem minkowskiInner_smul_right (c : ℝ) (x y : MinkowskiSpace d) :
    minkowskiInner d x (c • y) = c * minkowskiInner d x y := by
  rw [minkowskiInner_comm, minkowskiInner_smul_left, minkowskiInner_comm]

/-- Negation in the Minkowski inner product -/
theorem minkowskiInner_neg_left (x y : MinkowskiSpace d) :
    minkowskiInner d (-x) y = -minkowskiInner d x y := by
  have h : -x = (-1 : ℝ) • x := by ext i; simp
  rw [h, minkowskiInner_smul_left]
  ring

theorem minkowskiInner_neg_right (x y : MinkowskiSpace d) :
    minkowskiInner d x (-y) = -minkowskiInner d x y := by
  rw [minkowskiInner_comm, minkowskiInner_neg_left, minkowskiInner_comm]



/-- The time component x⁰ -/
def timeComponent (x : MinkowskiSpace d) : ℝ := x 0

/-- The spatial components (x¹, x², ..., xᵈ) -/
def spatialComponents (x : MinkowskiSpace d) : Fin d → ℝ := fun i => x (Fin.succ i)

/-- The Minkowski norm squared in terms of time and space components:
    η(x,x) = -t² + |x|² -/
theorem minkowskiNormSq_eq (x : MinkowskiSpace d) :
    minkowskiNormSq d x = -(timeComponent d x)^2 + ∑ i : Fin d, (spatialComponents d x i)^2 := by
  unfold minkowskiNormSq minkowskiInner timeComponent spatialComponents metricSignature
  -- Split the sum at index 0
  rw [Fin.sum_univ_succ]
  simp only [↓reduceIte, Fin.succ_ne_zero, one_mul, sq]
  linarith [sq_nonneg (x 0)]



/-- A vector is timelike if η(x,x) < 0 (with mostly positive signature) -/
def IsTimelike (x : MinkowskiSpace d) : Prop :=
  minkowskiNormSq d x < 0

/-- A vector is spacelike if η(x,x) > 0 (with mostly positive signature) -/
def IsSpacelike (x : MinkowskiSpace d) : Prop :=
  minkowskiNormSq d x > 0

/-- A vector is causal (timelike or lightlike) -/
def IsCausal (x : MinkowskiSpace d) : Prop :=
  minkowskiNormSq d x ≤ 0

/-- Two points are spacelike separated if their difference is spacelike -/
def AreSpacelikeSeparated (x y : MinkowskiSpace d) : Prop :=
  IsSpacelike d (x - y)

/-- A vector is future-directed if x⁰ > 0 -/
def IsFutureDirected (x : MinkowskiSpace d) : Prop :=
  timeComponent d x > 0

/-- The forward light cone: causal vectors with x⁰ ≥ 0 -/
def ForwardLightCone : Set (MinkowskiSpace d) :=
  { x | IsCausal d x ∧ timeComponent d x ≥ 0 }

/-- The closed forward light cone (same as ForwardLightCone) -/
def ClosedForwardLightCone : Set (MinkowskiSpace d) :=
  ForwardLightCone d



end MinkowskiSpace



/-- The Minkowski metric as a diagonal matrix η = diag(-1, +1, +1, ..., +1) -/
def minkowskiMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal (MinkowskiSpace.metricSignature d)

namespace MinkowskiMatrix

/-- The Minkowski matrix is symmetric -/
theorem transpose_eq : (minkowskiMatrix d)ᵀ = minkowskiMatrix d := by
  ext i j
  simp only [minkowskiMatrix, transpose_apply, diagonal_apply]
  by_cases h : i = j <;> simp [h, eq_comm]

/-- The Minkowski matrix is its own inverse: η² = I -/
theorem mul_self : minkowskiMatrix d * minkowskiMatrix d = 1 := by
  ext i j
  simp only [minkowskiMatrix, mul_apply, diagonal_apply, one_apply]
  by_cases hij : i = j
  · subst hij
    simp [MinkowskiSpace.metricSignature_mul_self]
  · simp only [ite_mul, zero_mul]
    rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro k _
      split_ifs with hik hkj
      · subst hik; exact (hij hkj).elim
      · simp
      · rfl

/-- The determinant of the Minkowski matrix -/
theorem det_eq : (minkowskiMatrix d).det = -1 := by
  simp only [minkowskiMatrix, det_diagonal]
  rw [Fin.prod_univ_succ]
  simp only [MinkowskiSpace.metricSignature_zero]
  have : ∏ i : Fin d, MinkowskiSpace.metricSignature d (Fin.succ i) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    exact MinkowskiSpace.metricSignature_succ d i
  simp [this]

end MinkowskiMatrix

end


-- Realize the metric equations eagerly for reproducible elaboration.
run_cmd Lean.Elab.Command.liftTermElabM do
  let _ ← Lean.Meta.getEqnsFor? ``MinkowskiSpace.minkowskiInner
  let _ ← Lean.Meta.getEqnsFor? ``MinkowskiSpace.minkowskiNormSq
  pure ()
