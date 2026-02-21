/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# Lorentz Group as a Topological Group

This file defines the Lorentz group independently and establishes its
topological group structure. The definitions here are self-contained —
they do not depend on the Wightman physics module.

## Main definitions

* `LorentzLieGroup.minkowskiSignature` — the metric signature (-1, +1, ..., +1)
* `LorentzLieGroup.minkowskiMatrix` — the Minkowski metric η = diag(-1, +1, ..., +1)
* `LorentzLieGroup.IsLorentzMatrix` — predicate: Λᵀ η Λ = η
* `LorentzLieGroup.LorentzGroup` — O(1,d) as a subtype of matrices
* `LorentzLieGroup.RestrictedLorentzGroup` — SO⁺(1,d) (proper orthochronous)

## Main results

* `LorentzGroup.instGroup` — group structure
* `LorentzGroup.instTopologicalSpace` — subspace topology
* `LorentzGroup.instIsTopologicalGroup` — topological group
* `RestrictedLorentzGroup.isPathConnected` — SO⁺(1,d) is path-connected (sorry)

## References

* Hall, B.C. (2015). *Lie Groups, Lie Algebras, and Representations*. Springer, Ch. 1.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Manifold
open Topology NormedSpace

namespace LorentzLieGroup

variable (d : ℕ)

/-! ### Minkowski metric -/

/-- The Minkowski metric signature: (-1, +1, +1, ..., +1). -/
def minkowskiSignature : Fin (d + 1) → ℝ :=
  fun i => if i = 0 then -1 else 1

/-- The Minkowski metric matrix η = diag(-1, +1, ..., +1). -/
def minkowskiMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal (minkowskiSignature d)

/-- η is symmetric: ηᵀ = η. -/
theorem minkowskiMatrix_transpose :
    (minkowskiMatrix d).transpose = minkowskiMatrix d := by
  simp [minkowskiMatrix, Matrix.diagonal_transpose]

/-- η is self-inverse: η² = 1. -/
theorem minkowskiMatrix_sq :
    minkowskiMatrix d * minkowskiMatrix d = 1 := by
  simp only [minkowskiMatrix, Matrix.diagonal_mul_diagonal, minkowskiSignature]
  ext i j
  simp [Matrix.diagonal, Matrix.one_apply]
  split_ifs <;> ring

/-! ### Lorentz group definition -/

/-- A matrix is Lorentz if it preserves the Minkowski metric: Λᵀ η Λ = η. -/
def IsLorentzMatrix (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Prop :=
  Λ.transpose * minkowskiMatrix d * Λ = minkowskiMatrix d

/-- The identity matrix is Lorentz. -/
theorem IsLorentzMatrix.one : IsLorentzMatrix d (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
  simp [IsLorentzMatrix]

/-- The product of Lorentz matrices is Lorentz. -/
theorem IsLorentzMatrix.mul {Λ₁ Λ₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h₁ : IsLorentzMatrix d Λ₁) (h₂ : IsLorentzMatrix d Λ₂) :
    IsLorentzMatrix d (Λ₁ * Λ₂) := by
  unfold IsLorentzMatrix at *
  -- (Λ₁Λ₂)ᵀ η (Λ₁Λ₂) = Λ₂ᵀ (Λ₁ᵀ η Λ₁) Λ₂ = Λ₂ᵀ η Λ₂ = η
  rw [Matrix.transpose_mul]
  have : Λ₂.transpose * Λ₁.transpose * minkowskiMatrix d * (Λ₁ * Λ₂)
      = Λ₂.transpose * (Λ₁.transpose * minkowskiMatrix d * Λ₁) * Λ₂ := by
    simp only [Matrix.mul_assoc]
  rw [this, h₁, h₂]

/-- The Lorentz group O(1,d) as a subtype of matrices. -/
def LorentzGroup := { Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ // IsLorentzMatrix d Λ }

instance : Coe (LorentzGroup d) (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := ⟨Subtype.val⟩

/-- Lorentz matrices have det = ±1. -/
theorem IsLorentzMatrix.det_sq_eq_one {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : Λ.det ^ 2 = 1 := by
  have hdet : Λ.det * (minkowskiMatrix d).det * Λ.det = (minkowskiMatrix d).det := by
    have := congr_arg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
    exact this
  have hη_ne : (minkowskiMatrix d).det ≠ 0 := by
    have := congr_arg Matrix.det (minkowskiMatrix_sq d)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [h0, mul_zero] at this; exact zero_ne_one this
  have key : Λ.det ^ 2 * (minkowskiMatrix d).det = (minkowskiMatrix d).det := by
    calc Λ.det ^ 2 * (minkowskiMatrix d).det
        = Λ.det * (minkowskiMatrix d).det * Λ.det := by ring
      _ = (minkowskiMatrix d).det := hdet
  exact mul_right_cancel₀ hη_ne (key.trans (one_mul _).symm)

/-- Lorentz matrices are invertible. -/
theorem IsLorentzMatrix.det_ne_zero {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : Λ.det ≠ 0 := by
  intro hzero
  have := h.det_sq_eq_one
  rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at this
  exact zero_ne_one this

/-! ### Group structure -/

/-- The inverse of a Lorentz matrix via η Λᵀ η. -/
def lorentzInv (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  minkowskiMatrix d * Λ.transpose * minkowskiMatrix d

/-- η Λᵀ η is a left inverse of a Lorentz matrix Λ. -/
theorem lorentzInv_mul {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : lorentzInv d Λ * Λ = 1 := by
  unfold lorentzInv
  calc minkowskiMatrix d * Λ.transpose * minkowskiMatrix d * Λ
      = minkowskiMatrix d * (Λ.transpose * minkowskiMatrix d * Λ) := by
        simp only [Matrix.mul_assoc]
    _ = minkowskiMatrix d * minkowskiMatrix d := by rw [h]
    _ = 1 := minkowskiMatrix_sq d

/-- η Λᵀ η is also a right inverse of a Lorentz matrix Λ. -/
theorem mul_lorentzInv {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : Λ * lorentzInv d Λ = 1 :=
  mul_eq_one_comm.mpr (lorentzInv_mul d h)

theorem lorentzInv_isLorentz {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : IsLorentzMatrix d (lorentzInv d Λ) := by
  have hη := minkowskiMatrix_sq d
  have hηt := minkowskiMatrix_transpose d
  -- From Λ * lorentzInv Λ = 1, derive Λ * η * Λᵀ = η
  have hΛηΛt : Λ * minkowskiMatrix d * Λ.transpose = minkowskiMatrix d := by
    have h1 : Λ * minkowskiMatrix d * Λ.transpose * minkowskiMatrix d = 1 := by
      have := mul_lorentzInv d h
      unfold lorentzInv at this
      calc Λ * minkowskiMatrix d * Λ.transpose * minkowskiMatrix d
          = Λ * (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := this
    calc Λ * minkowskiMatrix d * Λ.transpose
        = Λ * minkowskiMatrix d * Λ.transpose * 1 := by rw [Matrix.mul_one]
      _ = Λ * minkowskiMatrix d * Λ.transpose *
          (minkowskiMatrix d * minkowskiMatrix d) := by rw [hη]
      _ = (Λ * minkowskiMatrix d * Λ.transpose * minkowskiMatrix d) *
          minkowskiMatrix d := by simp only [Matrix.mul_assoc]
      _ = 1 * minkowskiMatrix d := by rw [h1]
      _ = minkowskiMatrix d := Matrix.one_mul _
  -- Now prove (lorentzInv Λ)ᵀ * η * (lorentzInv Λ) = η
  unfold IsLorentzMatrix lorentzInv
  -- (η * Λᵀ * η)ᵀ = η * Λ * η
  have htrans : (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d).transpose =
      minkowskiMatrix d * Λ * minkowskiMatrix d := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hηt, Matrix.mul_assoc]
  rw [htrans]
  calc minkowskiMatrix d * Λ * minkowskiMatrix d * minkowskiMatrix d *
      (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d)
      = minkowskiMatrix d * Λ * (minkowskiMatrix d * minkowskiMatrix d) *
        (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d) := by
          simp only [Matrix.mul_assoc]
    _ = minkowskiMatrix d * Λ *
        (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d) := by
          rw [hη, Matrix.mul_one]
    _ = minkowskiMatrix d * (Λ * minkowskiMatrix d * Λ.transpose) *
        minkowskiMatrix d := by simp only [Matrix.mul_assoc]
    _ = minkowskiMatrix d * minkowskiMatrix d * minkowskiMatrix d := by rw [hΛηΛt]
    _ = 1 * minkowskiMatrix d := by rw [hη]
    _ = minkowskiMatrix d := Matrix.one_mul _

instance : Group (LorentzGroup d) where
  mul Λ₁ Λ₂ := ⟨Λ₁.val * Λ₂.val, IsLorentzMatrix.mul d Λ₁.prop Λ₂.prop⟩
  one := ⟨1, IsLorentzMatrix.one d⟩
  inv Λ := ⟨lorentzInv d Λ.val, lorentzInv_isLorentz d Λ.prop⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc _ _ _)
  one_mul a := Subtype.ext (Matrix.one_mul _)
  mul_one a := Subtype.ext (Matrix.mul_one _)
  inv_mul_cancel a := by
    apply Subtype.ext
    show lorentzInv d a.val * a.val = 1
    exact lorentzInv_mul d a.prop

/-! ### Proper and orthochronous conditions -/

/-- A Lorentz matrix is proper if det(Λ) = 1. -/
def IsProperLorentz (Λ : LorentzGroup d) : Prop :=
  (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).det = 1

/-- A Lorentz matrix is orthochronous if Λ₀₀ ≥ 1. -/
def IsOrthochronous (Λ : LorentzGroup d) : Prop :=
  (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 0 ≥ 1

/-- The restricted Lorentz group SO⁺(1,d) = proper orthochronous. -/
def RestrictedLorentzGroup :=
  { Λ : LorentzGroup d // IsProperLorentz d Λ ∧ IsOrthochronous d Λ }

/-! ### Topology -/

instance instTopologicalSpace : TopologicalSpace (LorentzGroup d) :=
  instTopologicalSpaceSubtype

/-- The embedding into matrices is continuous. -/
theorem continuous_val :
    Continuous (Subtype.val : LorentzGroup d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :=
  continuous_subtype_val

/-- Multiplication is continuous. -/
theorem continuous_mul :
    Continuous (fun p : LorentzGroup d × LorentzGroup d => p.1 * p.2) := by
  apply continuous_induced_rng.mpr
  show Continuous (fun p : LorentzGroup d × LorentzGroup d => (p.1 * p.2).val)
  have : (fun p : LorentzGroup d × LorentzGroup d => (p.1 * p.2).val) =
      (fun p : LorentzGroup d × LorentzGroup d => p.1.val * p.2.val) := by
    ext p; rfl
  rw [this]
  exact (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

/-- Inversion is continuous. -/
theorem continuous_inv :
    Continuous (fun Λ : LorentzGroup d => Λ⁻¹) := by
  apply continuous_induced_rng.mpr
  show Continuous (fun Λ : LorentzGroup d => (Λ⁻¹).val)
  -- Λ⁻¹ = η Λᵀ η, which is continuous (transpose and const multiplication are continuous)
  have : (fun Λ : LorentzGroup d => (Λ⁻¹).val) =
      (fun Λ : LorentzGroup d => minkowskiMatrix d * Λ.val.transpose * minkowskiMatrix d) := by
    ext Λ; rfl
  rw [this]
  exact (continuous_const.matrix_mul
    (continuous_subtype_val.matrix_transpose)).matrix_mul continuous_const

instance instIsTopologicalGroup : IsTopologicalGroup (LorentzGroup d) where
  continuous_mul := continuous_mul d
  continuous_inv := continuous_inv d

instance RestrictedLorentzGroup.instTopologicalSpace :
    TopologicalSpace (RestrictedLorentzGroup d) :=
  instTopologicalSpaceSubtype

/-! ### Connectedness -/

/-- The Lorentz group is a closed subset of matrices. -/
theorem isClosed_lorentzGroup :
    IsClosed {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ | IsLorentzMatrix d Λ} := by
  have : {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ | IsLorentzMatrix d Λ} =
      (fun Λ => Λ.transpose * minkowskiMatrix d * Λ) ⁻¹' {minkowskiMatrix d} := by
    ext Λ; simp [IsLorentzMatrix, Set.mem_preimage]
  rw [this]
  exact IsClosed.preimage
    ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id)
    isClosed_singleton

/-! ### Lie algebra and exponential map -/

/-- The Minkowski matrix η as a unit (η² = 1). -/
def ηUnit : (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)ˣ where
  val := minkowskiMatrix d
  inv := minkowskiMatrix d
  val_inv := minkowskiMatrix_sq d
  inv_val := minkowskiMatrix_sq d

/-- The Lie algebra condition: X^T η + η X = 0. -/
def IsInLorentzAlgebra (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Prop :=
  X.transpose * minkowskiMatrix d + minkowskiMatrix d * X = 0

/-- Scalar multiples of Lie algebra elements remain in the Lie algebra. -/
theorem isInLorentzAlgebra_smul {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hX : IsInLorentzAlgebra d X) (t : ℝ) : IsInLorentzAlgebra d (t • X) := by
  unfold IsInLorentzAlgebra at *
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

/-- The matrix exponential of a Lie algebra element preserves the Minkowski metric. -/
theorem exp_isLorentz {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hX : IsInLorentzAlgebra d X) : IsLorentzMatrix d (exp X) := by
  -- Xᵀ = η(-X)η
  have lie : X.transpose = minkowskiMatrix d * (-X) * minkowskiMatrix d := by
    have h1 : X.transpose + minkowskiMatrix d * X * minkowskiMatrix d = 0 := by
      have := congr_arg (· * minkowskiMatrix d) hX
      simp only [add_mul, Matrix.mul_assoc, minkowskiMatrix_sq, Matrix.mul_one,
        Matrix.zero_mul] at this
      rwa [← Matrix.mul_assoc] at this
    rw [eq_neg_of_add_eq_zero_left h1]; noncomm_ring
  -- (exp X)ᵀ = exp(Xᵀ) = exp(η(-X)η) = η exp(-X) η
  have h_expT : (exp X : Matrix _ _ ℝ).transpose =
      minkowskiMatrix d * exp (-X) * minkowskiMatrix d := by
    rw [← Matrix.exp_transpose, lie]
    exact Matrix.exp_units_conj' (ηUnit d) (-X)
  -- exp(-X) * exp(X) = 1
  have h_cancel : exp (-X) * exp X = (1 : Matrix _ _ ℝ) :=
    (Matrix.exp_add_of_commute (-X) X (Commute.neg_left (Commute.refl X))).symm.trans
      (by rw [neg_add_cancel, exp_zero])
  -- (exp X)ᵀ * η * exp X = η exp(-X) η * η * exp X = η exp(-X) exp X = η
  unfold IsLorentzMatrix; rw [h_expT]
  calc minkowskiMatrix d * exp (-X) * minkowskiMatrix d * minkowskiMatrix d * exp X
      = minkowskiMatrix d * exp (-X) * (minkowskiMatrix d * minkowskiMatrix d) * exp X := by
        simp only [Matrix.mul_assoc]
    _ = minkowskiMatrix d * (exp (-X) * exp X) := by
        rw [minkowskiMatrix_sq]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = minkowskiMatrix d := by rw [h_cancel, Matrix.mul_one]

/-- det(exp X) = 1 for X in the Lorentz Lie algebra, via clopen argument. -/
theorem exp_det_one {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hX : IsInLorentzAlgebra d X) :
    (exp X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).det = 1 := by
  -- det(exp(tX))^2 = 1 for all t (Lorentz condition)
  have hdet_sq : ∀ t : ℝ, ((exp (t • X) : Matrix _ _ ℝ).det) ^ 2 = 1 := by
    intro t
    have hL := exp_isLorentz d (isInLorentzAlgebra_smul d hX t)
    have hΛ := congr_arg Matrix.det hL
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hΛ
    have hη_ne : (minkowskiMatrix d).det ≠ 0 := by
      have := congr_arg Matrix.det (minkowskiMatrix_sq d)
      rw [Matrix.det_mul, Matrix.det_one] at this
      intro h0; rw [h0, mul_zero] at this; exact zero_ne_one this
    exact mul_right_cancel₀ hη_ne
      ((by ring : _ ^ 2 * _ = _ * _ * _).trans hΛ |>.trans (one_mul _).symm)
  -- det(exp(tX)) is continuous, takes values ±1, equals 1 at t=0
  have hdet_cont : Continuous (fun t : ℝ => (exp (t • X) : Matrix _ _ ℝ).det) :=
    Continuous.matrix_det (exp_continuous.comp (by fun_prop))
  have hcover : ∀ t : ℝ, (exp (t • X) : Matrix _ _ ℝ).det = 1 ∨
      (exp (t • X) : Matrix _ _ ℝ).det = -1 := by
    intro t
    rcases mul_eq_zero.mp (by linear_combination hdet_sq t :
      ((exp (t • X) : Matrix _ _ ℝ).det - 1) *
      ((exp (t • X) : Matrix _ _ ℝ).det + 1) = 0) with h1 | h2
    · left; exact sub_eq_zero.mp h1
    · right; exact eq_neg_of_add_eq_zero_left h2
  -- Clopen argument: {det = 1} is clopen, contains 0, hence = ℝ
  have h1_closed : IsClosed {t : ℝ | (exp (t • X) : Matrix _ _ ℝ).det = 1} :=
    (isClosed_singleton (x := (1 : ℝ))).preimage hdet_cont
  have hm1_closed : IsClosed {t : ℝ | (exp (t • X) : Matrix _ _ ℝ).det = -1} :=
    (isClosed_singleton (x := (-1 : ℝ))).preimage hdet_cont
  have h1_open : IsOpen {t : ℝ | (exp (t • X) : Matrix _ _ ℝ).det = 1} := by
    rw [show {t : ℝ | (exp (t • X) : Matrix _ _ ℝ).det = 1} =
        {t : ℝ | (exp (t • X) : Matrix _ _ ℝ).det = -1}ᶜ from by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact ⟨fun h1 hm1 => by rw [h1] at hm1; norm_num at hm1,
             fun hne => (hcover t).resolve_right hne⟩]
    exact hm1_closed.isOpen_compl
  have h1_univ := IsClopen.eq_univ ⟨h1_closed, h1_open⟩ ⟨0, by simp [exp_zero]⟩
  have h1_mem : (1 : ℝ) ∈ {t : ℝ | (exp (t • X) : Matrix _ _ ℝ).det = 1} :=
    h1_univ ▸ Set.mem_univ _
  simp only [Set.mem_setOf_eq, one_smul] at h1_mem; exact h1_mem

/-- For a Lorentz matrix, (Λ₀₀)² ≥ 1. -/
theorem IsLorentzMatrix.entry00_sq_ge_one {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : Λ 0 0 ^ 2 ≥ 1 := by
  have h00 := congr_fun (congr_fun h 0) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at h00
  simp only [minkowskiMatrix, Matrix.diagonal_apply, minkowskiSignature, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h00
  rw [Fin.sum_univ_succ] at h00
  simp only [↓reduceIte, Fin.succ_ne_zero] at h00
  nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    mul_self_nonneg (Λ (Fin.succ i) 0)), sq (Λ 0 0)]

/-- exp(X)₀₀ ≥ 1 for X in the Lorentz Lie algebra, via clopen argument. -/
theorem exp_orthochronous {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hX : IsInLorentzAlgebra d X) :
    (exp X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 0 ≥ 1 := by
  suffices h : ∀ t : ℝ, (exp (t • X) : Matrix _ _ ℝ) 0 0 ≥ 1 by
    simpa [one_smul] using h 1
  intro t
  have h_sq : ∀ s : ℝ, (exp (s • X) : Matrix _ _ ℝ) 0 0 ^ 2 ≥ 1 :=
    fun s => (exp_isLorentz d (isInLorentzAlgebra_smul d hX s)).entry00_sq_ge_one
  have hcont : Continuous (fun s : ℝ => (exp (s • X) : Matrix _ _ ℝ) 0 0) :=
    (exp_continuous.comp (by fun_prop : Continuous (fun s : ℝ => s • X))).matrix_elem 0 0
  -- Clopen: {s | f(s) ≥ 1} = {s | f(s) ≤ -1}ᶜ
  set S := {s : ℝ | (exp (s • X) : Matrix _ _ ℝ) 0 0 ≥ 1}
  set T := {s : ℝ | (exp (s • X) : Matrix _ _ ℝ) 0 0 ≤ -1}
  have hS_closed : IsClosed S := isClosed_le continuous_const hcont
  have hT_closed : IsClosed T := isClosed_le hcont continuous_const
  have hS_eq_Tc : S = Tᶜ := by
    ext s; simp only [S, T, Set.mem_setOf_eq, Set.mem_compl_iff, not_le, ge_iff_le]
    constructor
    · intro h; linarith
    · intro h
      nlinarith [h_sq s, sq_nonneg ((exp (s • X) : Matrix _ _ ℝ) 0 0 + 1),
                 sq_nonneg ((exp (s • X) : Matrix _ _ ℝ) 0 0 - 1)]
  have hS_open : IsOpen S := hS_eq_Tc ▸ hT_closed.isOpen_compl
  have hS_univ : S = Set.univ := IsClopen.eq_univ ⟨hS_closed, hS_open⟩
    ⟨0, show (exp ((0 : ℝ) • X) : Matrix _ _ ℝ) 0 0 ≥ 1 by simp [exp_zero]⟩
  show t ∈ S; rw [hS_univ]; exact Set.mem_univ t

/-- exp(X) is in SO⁺(1,d) for X in the Lorentz Lie algebra. -/
def expLorentz (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hX : IsInLorentzAlgebra d X) :
    RestrictedLorentzGroup d :=
  ⟨⟨exp X, exp_isLorentz d hX⟩,
   ⟨exp_det_one d hX, exp_orthochronous d hX⟩⟩

/-- The identity as an element of SO⁺(1,d). -/
def RestrictedLorentzGroup.one : RestrictedLorentzGroup d :=
  ⟨⟨1, IsLorentzMatrix.one d⟩, by
    constructor
    · show (1 : Matrix _ _ ℝ).det = 1; exact Matrix.det_one
    · show (1 : Matrix _ _ ℝ) 0 0 ≥ 1; simp⟩

/-- The path t ↦ exp(tX) connects 1 to exp(X) in SO⁺(1,d). -/
theorem joined_one_expLorentz (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hX : IsInLorentzAlgebra d X) :
    Joined (RestrictedLorentzGroup.one d) (expLorentz d X hX) := by
  have hcont : Continuous (fun t : ℝ => exp (t • X) : ℝ → Matrix _ _ ℝ) :=
    exp_continuous.comp (by fun_prop)
  -- Build the function I → RestrictedLorentzGroup
  set f : unitInterval → RestrictedLorentzGroup d :=
    fun t => ⟨⟨exp (t.val • X), exp_isLorentz d (isInLorentzAlgebra_smul d hX t.val)⟩,
      ⟨exp_det_one d (isInLorentzAlgebra_smul d hX t.val),
       exp_orthochronous d (isInLorentzAlgebra_smul d hX t.val)⟩⟩
  have hf_cont : Continuous f :=
    Continuous.subtype_mk (Continuous.subtype_mk
      (hcont.comp continuous_subtype_val) _) _
  have hf_source : f ⟨0, unitInterval.zero_mem⟩ = RestrictedLorentzGroup.one d :=
    Subtype.ext (Subtype.ext (by simp [f, exp_zero, RestrictedLorentzGroup.one]))
  have hf_target : f ⟨1, unitInterval.one_mem⟩ = expLorentz d X hX :=
    Subtype.ext (Subtype.ext (by simp [f, expLorentz]))
  exact ⟨⟨⟨f, hf_cont⟩, hf_source, hf_target⟩⟩

/-! ### Symmetric Lorentz condition and sum identities -/

/-- ΛηΛᵀ = η follows from ΛᵀηΛ = η (Lorentz matrices preserve metric both ways). -/
theorem IsLorentzMatrix.symm {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : Λ * minkowskiMatrix d * Λ.transpose = minkowskiMatrix d := by
  have h_left_inv : minkowskiMatrix d * Λ.transpose * minkowskiMatrix d * Λ = 1 := by
    calc minkowskiMatrix d * Λ.transpose * minkowskiMatrix d * Λ
        = minkowskiMatrix d * (Λ.transpose * minkowskiMatrix d * Λ) := by
          simp only [Matrix.mul_assoc]
      _ = minkowskiMatrix d * minkowskiMatrix d := by rw [h]
      _ = 1 := minkowskiMatrix_sq d
  have h_right_inv : Λ * (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d) = 1 :=
    mul_eq_one_comm.mpr h_left_inv
  calc Λ * minkowskiMatrix d * Λ.transpose
      = Λ * minkowskiMatrix d * Λ.transpose * 1 := by rw [Matrix.mul_one]
    _ = Λ * minkowskiMatrix d * Λ.transpose * (minkowskiMatrix d * minkowskiMatrix d) := by
        rw [minkowskiMatrix_sq]
    _ = (Λ * (minkowskiMatrix d * Λ.transpose * minkowskiMatrix d)) * minkowskiMatrix d := by
        simp only [Matrix.mul_assoc]
    _ = 1 * minkowskiMatrix d := by rw [h_right_inv]
    _ = minkowskiMatrix d := Matrix.one_mul _

/-- Column 0 identity: Λ₀₀² = 1 + Σ_{k≥1} Λ_{k,0}². -/
theorem col0_sum_sq {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : Λ 0 0 ^ 2 = 1 + ∑ k : Fin d, Λ k.succ 0 ^ 2 := by
  have h00 := congr_fun (congr_fun h 0) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMatrix, Matrix.diagonal_apply,
    minkowskiSignature, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h00
  rw [Fin.sum_univ_succ] at h00
  simp only [↓reduceIte, Fin.succ_ne_zero] at h00
  have hsq : ∀ i : Fin d, Λ i.succ 0 * Λ i.succ 0 = Λ i.succ 0 ^ 2 :=
    fun i => (sq (Λ i.succ 0)).symm
  simp_rw [hsq] at h00
  linarith

/-- Row 0 identity: Λ₀₀² = 1 + Σ_{k≥1} Λ₀ₖ² (from symmetric Lorentz condition). -/
theorem row0_sum_sq {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : IsLorentzMatrix d Λ) : Λ 0 0 ^ 2 = 1 + ∑ k : Fin d, Λ 0 k.succ ^ 2 := by
  have h00 := congr_fun (congr_fun (h.symm) 0) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMatrix, Matrix.diagonal_apply,
    minkowskiSignature, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h00
  rw [Fin.sum_univ_succ] at h00
  simp only [↓reduceIte, Fin.succ_ne_zero] at h00
  have hsq : ∀ i : Fin d, Λ 0 i.succ * Λ 0 i.succ = Λ 0 i.succ ^ 2 :=
    fun i => (sq (Λ 0 i.succ)).symm
  simp_rw [hsq] at h00
  linarith

/-! ### Orthochronous closure under products and inverses -/

private theorem ab_sqrt_ge_one (a b : ℝ) (ha : a ≥ 1) (hb : b ≥ 1) :
    a * b - Real.sqrt ((a ^ 2 - 1) * (b ^ 2 - 1)) ≥ 1 := by
  have h1 : a * b - 1 ≥ 0 := by nlinarith
  rw [ge_iff_le, ← sub_nonneg,
    show a * b - Real.sqrt _ - 1 = (a * b - 1) - Real.sqrt _ from by ring, sub_nonneg,
    ← Real.sqrt_sq h1.le]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a - b)])

/-- Product of orthochronous Lorentz matrices is orthochronous (Cauchy-Schwarz). -/
theorem orthochronous_mul {Λ₁ Λ₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h1 : IsLorentzMatrix d Λ₁) (h2 : IsLorentzMatrix d Λ₂)
    (ho1 : Λ₁ 0 0 ≥ 1) (ho2 : Λ₂ 0 0 ≥ 1) : (Λ₁ * Λ₂) 0 0 ≥ 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  set S := ∑ x : Fin d, Λ₁ 0 x.succ * Λ₂ x.succ 0
  have hCS : S ^ 2 ≤ (∑ k : Fin d, Λ₁ 0 k.succ ^ 2) * (∑ k : Fin d, Λ₂ k.succ 0 ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hA : ∑ k : Fin d, Λ₁ 0 k.succ ^ 2 = Λ₁ 0 0 ^ 2 - 1 := by
    linarith [row0_sum_sq (d := d) h1]
  have hB : ∑ k : Fin d, Λ₂ k.succ 0 ^ 2 = Λ₂ 0 0 ^ 2 - 1 := by
    linarith [col0_sum_sq (d := d) h2]
  rw [hA, hB] at hCS
  have hS_bound : S ≥ -Real.sqrt ((Λ₁ 0 0 ^ 2 - 1) * (Λ₂ 0 0 ^ 2 - 1)) := by
    rw [ge_iff_le, neg_le_iff_add_nonneg]
    by_cases hS : S ≥ 0
    · linarith [Real.sqrt_nonneg ((Λ₁ 0 0 ^ 2 - 1) * (Λ₂ 0 0 ^ 2 - 1))]
    · push_neg at hS
      have hSneg : 0 ≤ -S := le_of_lt (neg_pos.mpr hS)
      have h1 : -S ≤ Real.sqrt ((Λ₁ 0 0 ^ 2 - 1) * (Λ₂ 0 0 ^ 2 - 1)) := by
        calc -S = Real.sqrt ((-S) ^ 2) := (Real.sqrt_sq hSneg).symm
          _ = Real.sqrt (S ^ 2) := by rw [show (-S) ^ 2 = S ^ 2 from by ring]
          _ ≤ Real.sqrt ((Λ₁ 0 0 ^ 2 - 1) * (Λ₂ 0 0 ^ 2 - 1)) := Real.sqrt_le_sqrt hCS
      linarith
  linarith [ab_sqrt_ge_one _ _ ho1 ho2]

/-- The inverse of an orthochronous Lorentz matrix is orthochronous.
    Since (Λ⁻¹)₀₀ = (ηΛᵀη)₀₀ = Λ₀₀. -/
theorem orthochronous_inv {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (_ : IsLorentzMatrix d Λ) (ho : Λ 0 0 ≥ 1) : (lorentzInv d Λ) 0 0 ≥ 1 := by
  simp [lorentzInv, minkowskiMatrix, minkowskiSignature, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.transpose_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ]
  linarith

/-! ### Restricted Lorentz group operations -/

instance : Group (RestrictedLorentzGroup d) where
  mul a b := ⟨⟨a.val.val * b.val.val, IsLorentzMatrix.mul d a.val.prop b.val.prop⟩,
    ⟨by show (a.val.val * b.val.val).det = 1
        rw [Matrix.det_mul, a.prop.1, b.prop.1, one_mul],
     orthochronous_mul (d := d) a.val.prop b.val.prop a.prop.2 b.prop.2⟩⟩
  one := RestrictedLorentzGroup.one d
  inv a := ⟨⟨lorentzInv d a.val.val, lorentzInv_isLorentz d a.val.prop⟩,
    ⟨by show (lorentzInv d a.val.val).det = 1
        -- det(ηΛᵀη) = det(η)² · det(Λ) = 1 · 1 = 1
        have hdet : a.val.val.det = 1 := a.prop.1
        simp only [lorentzInv, Matrix.det_mul, Matrix.det_transpose, hdet, mul_one]
        have hη := congr_arg Matrix.det (minkowskiMatrix_sq d)
        rw [Matrix.det_mul, Matrix.det_one] at hη
        linarith,
     orthochronous_inv (d := d) a.val.prop a.prop.2⟩⟩
  mul_assoc a b c := Subtype.ext (Subtype.ext (Matrix.mul_assoc _ _ _))
  one_mul a := Subtype.ext (Subtype.ext (Matrix.one_mul _))
  mul_one a := Subtype.ext (Subtype.ext (Matrix.mul_one _))
  inv_mul_cancel a := Subtype.ext (Subtype.ext (lorentzInv_mul d a.val.prop))

instance : IsTopologicalGroup (RestrictedLorentzGroup d) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    show Continuous fun p : RestrictedLorentzGroup d × RestrictedLorentzGroup d =>
      p.1.val.val * p.2.val.val
    exact ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))
  continuous_inv := by
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    show Continuous fun a : RestrictedLorentzGroup d => lorentzInv d a.val.val
    exact (continuous_const.matrix_mul
      ((continuous_subtype_val.comp continuous_subtype_val).matrix_transpose)).matrix_mul
      continuous_const

/-- Joined 1 a → Joined 1 b → Joined 1 (a * b) in any topological group. -/
private theorem joined_one_mul_general {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {a b : G} (ha : Joined 1 a) (hb : Joined 1 b) :
    Joined 1 (a * b) := by
  obtain ⟨γa⟩ := ha
  obtain ⟨γb⟩ := hb
  have h1 : Joined 1 b := ⟨γb⟩
  have h2 : Joined b (a * b) := by
    refine ⟨⟨⟨fun t => γa t * b, ?_⟩, ?_, ?_⟩⟩
    · exact γa.continuous.mul continuous_const
    · simp [γa.source]
    · simp [γa.target]
  exact h1.trans h2

/-! ### Planar boost -/

/-- Planar boost in the (0, k+1) plane with rapidity parameter β. -/
def planarBoost (k : Fin d) (β : ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  1 + Real.sinh β • (Matrix.single 0 k.succ 1 + Matrix.single k.succ 0 (1 : ℝ)) +
  (Real.cosh β - 1) • (Matrix.single 0 0 1 + Matrix.single k.succ k.succ (1 : ℝ))

/-! Row-level entry lemmas that bypass the `True ∧ False` issue with `Matrix.single_apply`. -/

@[simp] theorem pb0 (k : Fin d) (β : ℝ) (j : Fin (d + 1)) :
    planarBoost d k β 0 j =
    if j = 0 then Real.cosh β else if j = k.succ then Real.sinh β else 0 := by
  simp only [planarBoost, Matrix.single_apply, Matrix.one_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hj0 : j = 0 <;> by_cases hjk : j = k.succ <;>
  simp_all [Fin.succ_ne_zero, eq_comm]

@[simp] theorem pbK (k : Fin d) (β : ℝ) (j : Fin (d + 1)) :
    planarBoost d k β k.succ j =
    if j = 0 then Real.sinh β else if j = k.succ then Real.cosh β else 0 := by
  simp only [planarBoost, Matrix.single_apply, Matrix.one_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hj0 : j = 0 <;> by_cases hjk : j = k.succ <;>
  simp_all [Fin.succ_ne_zero, eq_comm]

@[simp] theorem pbO (k : Fin d) (β : ℝ) (i : Fin (d + 1))
    (hi0 : i ≠ 0) (hik : i ≠ k.succ) (j : Fin (d + 1)) :
    planarBoost d k β i j = if i = j then 1 else 0 := by
  simp only [planarBoost, Matrix.single_apply, Matrix.one_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]; simp [Ne.symm hi0, Ne.symm hik]

theorem planarBoost_transpose (k : Fin d) (β : ℝ) :
    (planarBoost d k β).transpose = planarBoost d k β := by
  ext i j; simp only [Matrix.transpose_apply]
  by_cases hi0 : i = 0 <;> by_cases hik : i = k.succ <;>
  by_cases hj0 : j = 0 <;> by_cases hjk : j = k.succ
  all_goals (first | subst hi0 | subst hik | skip)
  all_goals (first | subst hj0 | subst hjk | skip)
  all_goals simp_all (config := { decide := true }) [pb0, pbK, pbO,
    Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero _), eq_comm]

/-- The planar boost preserves the Minkowski metric. -/
theorem planarBoost_isLorentz (k : Fin d) (β : ℝ) :
    IsLorentzMatrix d (planarBoost d k β) := by
  unfold IsLorentzMatrix
  rw [planarBoost_transpose]
  ext i j
  simp only [Matrix.mul_apply, minkowskiMatrix, Matrix.diagonal_apply]
  simp_rw [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Goal: ∑ l, pb(i,l) * η(l) * pb(l,j) = (if i = j then η(i) else 0)
  by_cases hi0 : i = 0
  · subst hi0
    rw [Fin.sum_univ_succ]
    simp only [pb0 d, minkowskiSignature, Fin.succ_ne_zero, ↓reduceIte]
    simp_rw [Fin.succ_inj, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, pbK d]
    by_cases hj0 : j = 0
    · subst hj0; simp; nlinarith [Real.cosh_sq β]
    · by_cases hjk : j = k.succ
      · subst hjk; simp [Ne.symm (Fin.succ_ne_zero k)]; ring
      · simp [hj0, hjk, Ne.symm hj0]
  · by_cases hik : i = k.succ
    · subst hik
      rw [Fin.sum_univ_succ]
      simp only [pbK d, minkowskiSignature, Fin.succ_ne_zero, ↓reduceIte]
      simp_rw [Fin.succ_inj, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, pb0 d, pbK d]
      by_cases hj0 : j = 0
      · subst hj0; simp [Fin.succ_ne_zero]; ring
      · by_cases hjk : j = k.succ
        · subst hjk; simp [Fin.succ_ne_zero]; nlinarith [Real.cosh_sq β]
        · simp only [hj0, hjk, ↓reduceIte, mul_zero, add_zero]
          simp [show k.succ ≠ j from fun h => hjk h.symm]
    · simp_rw [show ∀ j, planarBoost d k β i j = if i = j then 1 else 0 from
        fun j => pbO d k β i hi0 hik j]
      simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [show planarBoost d k β i j = if i = j then 1 else 0 from
        pbO d k β i hi0 hik j]
      simp only [minkowskiSignature, hi0, ↓reduceIte]
      split_ifs <;> ring

theorem planarBoost_zero (k : Fin d) : planarBoost d k 0 = 1 := by
  simp only [planarBoost, Real.sinh_zero, Real.cosh_zero]; simp

theorem planarBoost_entry00 (k : Fin d) (β : ℝ) :
    planarBoost d k β 0 0 = Real.cosh β := by
  simp [pb0 d]

theorem planarBoost_orthochronous (k : Fin d) (β : ℝ) :
    planarBoost d k β 0 0 ≥ 1 := by
  rw [planarBoost_entry00]
  exact_mod_cast Real.one_le_cosh β

/-- det(planarBoost) = 1 via clopen argument. -/
theorem planarBoost_det_one (k : Fin d) (β : ℝ) :
    (planarBoost d k β).det = 1 := by
  have hdet_sq : ∀ t : ℝ, (planarBoost d k t).det ^ 2 = 1 :=
    fun t => (planarBoost_isLorentz d k t).det_sq_eq_one
  have hcont : Continuous (fun t : ℝ => (planarBoost d k t).det) := by
    apply Continuous.matrix_det
    apply continuous_pi; intro i; apply continuous_pi; intro j
    simp only [planarBoost, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.single_apply, smul_eq_mul]
    fun_prop
  have hcover : ∀ t : ℝ, (planarBoost d k t).det = 1 ∨ (planarBoost d k t).det = -1 := by
    intro t
    rcases mul_eq_zero.mp (by linear_combination hdet_sq t :
      ((planarBoost d k t).det - 1) * ((planarBoost d k t).det + 1) = 0) with h | h
    · left; linarith
    · right; linarith
  have h1_closed : IsClosed {t : ℝ | (planarBoost d k t).det = 1} :=
    (isClosed_singleton (x := (1 : ℝ))).preimage hcont
  have hm1_closed : IsClosed {t : ℝ | (planarBoost d k t).det = -1} :=
    (isClosed_singleton (x := (-1 : ℝ))).preimage hcont
  have h1_open : IsOpen {t : ℝ | (planarBoost d k t).det = 1} := by
    rw [show {t : ℝ | (planarBoost d k t).det = 1} =
        {t : ℝ | (planarBoost d k t).det = -1}ᶜ from by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact ⟨fun h1 hm1 => by rw [h1] at hm1; norm_num at hm1,
             fun hne => (hcover t).resolve_right hne⟩]
    exact hm1_closed.isOpen_compl
  have h1_univ := IsClopen.eq_univ ⟨h1_closed, h1_open⟩
    ⟨0, by simp [planarBoost_zero d k, Matrix.det_one]⟩
  have h1_mem : β ∈ {t : ℝ | (planarBoost d k t).det = 1} := h1_univ ▸ Set.mem_univ β
  exact h1_mem

/-- The planar boost as an element of SO⁺(1,d). -/
def boostElement (k : Fin d) (β : ℝ) : RestrictedLorentzGroup d :=
  ⟨⟨planarBoost d k β, planarBoost_isLorentz d k β⟩,
   ⟨planarBoost_det_one d k β, planarBoost_orthochronous d k β⟩⟩

/-- The path t ↦ planarBoost(k, tβ) connects 1 to boostElement(k, β). -/
theorem joined_one_boostElement (k : Fin d) (β : ℝ) :
    Joined (1 : RestrictedLorentzGroup d) (boostElement d k β) := by
  set f : unitInterval → RestrictedLorentzGroup d :=
    fun t => boostElement d k (t.val * β)
  have hf_cont : Continuous f := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi; intro i; apply continuous_pi; intro j
    simp only [planarBoost, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.single_apply, smul_eq_mul]
    fun_prop
  have hf0 : f ⟨0, unitInterval.zero_mem⟩ = 1 :=
    Subtype.ext (Subtype.ext (by
      simp only [f, boostElement, planarBoost_zero, zero_mul]; rfl))
  have hf1 : f ⟨1, unitInterval.one_mem⟩ = boostElement d k β :=
    Subtype.ext (Subtype.ext (by simp [f, boostElement]))
  exact ⟨⟨⟨f, hf_cont⟩, hf0, hf1⟩⟩

/-! ### Column action formulas -/

theorem planarBoost_mul_entry0 (k : Fin d) (β : ℝ)
    (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    (planarBoost d k β * Λ) 0 0 = Real.cosh β * Λ 0 0 + Real.sinh β * Λ k.succ 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, pb0 d]
  simp only [↓reduceIte, Fin.succ_ne_zero, ite_mul, zero_mul, Fin.succ_inj]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

theorem planarBoost_mul_entryK (k : Fin d) (β : ℝ)
    (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    (planarBoost d k β * Λ) k.succ 0 = Real.sinh β * Λ 0 0 + Real.cosh β * Λ k.succ 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, pbK d]
  simp only [↓reduceIte, Fin.succ_ne_zero, ite_mul, zero_mul, Fin.succ_inj]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

theorem planarBoost_mul_other (k : Fin d) (β : ℝ)
    (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (i : Fin (d + 1))
    (hi0 : i ≠ 0) (hik : i ≠ k.succ) :
    (planarBoost d k β * Λ) i 0 = Λ i 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ,
    show ∀ j, planarBoost d k β i j = if i = j then 1 else 0 from
      fun j => pbO d k β i hi0 hik j]
  simp only [hi0, ↓reduceIte, ite_mul, one_mul, zero_mul, zero_add]
  obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi0
  simp_rw [Fin.succ_inj]
  simp [Finset.mem_univ]

/-! ### Column reduction via boosts -/

/-- The Lorentz condition implies Λ₀₀² ≥ 1 + Λ_{k+1,0}². -/
theorem lorentz_entry00_sq (hL : IsLorentzMatrix d Λ) (k : Fin d) :
    Λ 0 0 ^ 2 ≥ 1 + Λ k.succ 0 ^ 2 := by
  -- From (Λᵀ η Λ)₀₀ = η₀₀: -Λ₀₀² + ∑_{l≥1} Λ_{l,0}² = -1
  have h := congr_fun (congr_fun hL 0) 0
  simp only [minkowskiMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, minkowskiSignature] at h
  -- Simplify the inner sum: ∑ x₁, Λ(x₁,0) * (if x₁ = x then η(x₁) else 0) = Λ(x,0) * η(x)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  -- Now h : ∑ x, (Λ x 0 * if x = 0 then -1 else 1) * Λ x 0 = -1
  -- Split off the l=0 term
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.succ_ne_zero, ↓reduceIte] at h
  -- h : (-1) * Λ 0 0 * Λ 0 0 + ∑ l, Λ l.succ 0 * 1 * Λ l.succ 0 = -1
  -- i.e., -Λ₀₀² + ∑_{l≥1} Λ_{l+1,0}² = -1
  -- So Λ₀₀² = 1 + ∑_{l≥1} Λ_{l+1,0}²
  have hge : ∑ l : Fin d, Λ l.succ 0 * 1 * Λ l.succ 0 ≥ Λ k.succ 0 * 1 * Λ k.succ 0 := by
    apply Finset.single_le_sum (fun i _ => by nlinarith [mul_self_nonneg (Λ i.succ 0)])
      (Finset.mem_univ k)
  nlinarith [mul_self_nonneg (Λ 0 0), mul_self_nonneg (Λ k.succ 0)]

/-- For any Lorentz matrix with Λ₀₀ ≥ 1, there exists a boost zeroing out entry (k+1,0).
    Uses the intermediate value theorem. -/
theorem boost_zero_entry (k : Fin d) {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (_hL : IsLorentzMatrix d Λ) (ho : Λ 0 0 ≥ 1)
    (hab : Λ 0 0 ^ 2 ≥ 1 + Λ k.succ 0 ^ 2) :
    ∃ β : ℝ, (planarBoost d k β * Λ) k.succ 0 = 0 := by
  simp only [planarBoost_mul_entryK]
  set a := Λ 0 0; set b := Λ k.succ 0
  have ha : a ≥ 1 := ho
  have hab' : a ^ 2 - 1 ≥ b ^ 2 := by linarith
  set f := fun β : ℝ => Real.sinh β * a + Real.cosh β * b
  have hf_cont : Continuous f :=
    (Real.continuous_sinh.mul continuous_const).add (Real.continuous_cosh.mul continuous_const)
  have hf0 : f 0 = b := by simp [f, Real.sinh_zero, Real.cosh_zero]
  have hsqrt_ge : Real.sqrt (a ^ 2 - 1) ≥ |b| := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hab'
  have hb_le : b ≤ √(a ^ 2 - 1) := le_trans (le_abs_self b) hsqrt_ge
  have hb_ge : -√(a ^ 2 - 1) ≤ b := le_trans (neg_le_neg hsqrt_ge) (neg_abs_le b)
  have ha_pos : (0 : ℝ) ≤ a := by linarith
  have hfp : f (Real.arcosh a) ≥ 0 := by
    simp only [f, Real.sinh_arcosh ha, Real.cosh_arcosh ha]
    nlinarith [mul_nonneg ha_pos (show (0 : ℝ) ≤ √(a ^ 2 - 1) + b by linarith)]
  have hfn : f (-Real.arcosh a) ≤ 0 := by
    simp only [f, Real.sinh_neg, Real.cosh_neg, Real.sinh_arcosh ha, Real.cosh_arcosh ha]
    nlinarith [mul_nonneg ha_pos (show (0 : ℝ) ≤ √(a ^ 2 - 1) - b by linarith)]
  by_cases hb : b ≤ 0
  · obtain ⟨c, _, hfc⟩ := intermediate_value_Icc (Real.arcosh_nonneg ha) hf_cont.continuousOn
      ⟨hf0 ▸ hb, hfp⟩
    exact ⟨c, hfc⟩
  · push_neg at hb
    obtain ⟨c, _, hfc⟩ := intermediate_value_Icc (neg_nonpos.mpr (Real.arcosh_nonneg ha))
      hf_cont.continuousOn ⟨hfn, hf0 ▸ hb.le⟩
    exact ⟨c, hfc⟩

/-! ### Spatial rotations -/

/-- Spatial rotation in the (i+1, j+1) plane by angle θ. Leaves time coordinate unchanged. -/
def spatialRot (i j : Fin d) (θ : ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun a b =>
    if a = i.succ then
      if b = i.succ then Real.cos θ else if b = j.succ then Real.sin θ else 0
    else if a = j.succ then
      if b = i.succ then -Real.sin θ else if b = j.succ then Real.cos θ else 0
    else if a = b then 1 else 0

@[simp] theorem sr_i (i j : Fin d) (θ : ℝ) (b : Fin (d + 1)) :
    spatialRot d i j θ i.succ b =
    if b = i.succ then Real.cos θ else if b = j.succ then Real.sin θ else 0 := by
  simp [spatialRot, Matrix.of_apply]

@[simp] theorem sr_j (i j : Fin d) (hij : i ≠ j) (θ : ℝ) (b : Fin (d + 1)) :
    spatialRot d i j θ j.succ b =
    if b = i.succ then -Real.sin θ else if b = j.succ then Real.cos θ else 0 := by
  simp [spatialRot, Matrix.of_apply,
    show j.succ ≠ i.succ from Fin.succ_injective _ |>.ne hij.symm]

@[simp] theorem sr_other (i j : Fin d) (θ : ℝ) (a : Fin (d + 1))
    (ha_i : a ≠ i.succ) (ha_j : a ≠ j.succ) (b : Fin (d + 1)) :
    spatialRot d i j θ a b = if a = b then 1 else 0 := by
  simp [spatialRot, Matrix.of_apply, ha_i, ha_j]

private theorem nested_ite_sum {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (f g : Fin n → ℝ) :
    ∑ x, (if x = i then f x else if x = j then g x else 0) = f i + g j := by
  have : ∀ x, (if x = i then f x else if x = j then g x else (0:ℝ)) =
      (if x = i then f x else 0) + (if x = j then g x else 0) := by
    intro x; split_ifs with h1 h2 <;> simp_all
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem spatialRot_mul_row_i (i j : Fin d) (hij : i ≠ j) (θ : ℝ)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (l : Fin (d + 1)) :
    (spatialRot d i j θ * A) i.succ l =
    Real.cos θ * A i.succ l + Real.sin θ * A j.succ l := by
  simp only [Matrix.mul_apply]; simp_rw [sr_i d, ite_mul, zero_mul]
  exact nested_ite_sum (Fin.succ_injective _ |>.ne hij) _ _

theorem spatialRot_mul_row_j (i j : Fin d) (hij : i ≠ j) (θ : ℝ)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (l : Fin (d + 1)) :
    (spatialRot d i j θ * A) j.succ l =
    -Real.sin θ * A i.succ l + Real.cos θ * A j.succ l := by
  simp only [Matrix.mul_apply]; simp_rw [sr_j d _ _ hij, ite_mul, zero_mul]
  exact nested_ite_sum (Fin.succ_injective _ |>.ne hij) _ _

theorem spatialRot_mul_row_other (i j : Fin d) (θ : ℝ)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (l k : Fin (d + 1))
    (hk_i : k ≠ i.succ) (hk_j : k ≠ j.succ) :
    (spatialRot d i j θ * A) k l = A k l := by
  simp only [Matrix.mul_apply, sr_other d _ _ _ _ hk_i hk_j, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem spatialRot_zero (i j : Fin d) (hij : i ≠ j) :
    spatialRot d i j 0 = 1 := by
  ext a b; simp only [Matrix.one_apply]
  by_cases ha_i : a = i.succ
  · subst ha_i; rw [sr_i]; simp only [Real.cos_zero, Real.sin_zero]
    by_cases hb : b = i.succ
    · simp [hb]
    · simp [hb, show ¬(i.succ = b) from fun h => hb h.symm]
  · by_cases ha_j : a = j.succ
    · subst ha_j; rw [sr_j d _ _ hij]; simp only [Real.sin_zero, neg_zero, Real.cos_zero]
      by_cases hb : b = j.succ
      · simp [hb, hij.symm]
      · simp [hb, show ¬(j.succ = b) from fun h => hb h.symm]
    · rw [sr_other d _ _ _ _ ha_i ha_j]

/-- Universal entry lemma for x.succ row: works under binders (∑ x, ...). -/
theorem spatialRot_succ_apply (i j : Fin d) (hij : i ≠ j) (θ : ℝ)
    (x : Fin d) (a : Fin (d + 1)) :
    spatialRot d i j θ x.succ a =
    if x = i then (if a = i.succ then Real.cos θ else if a = j.succ then Real.sin θ else 0)
    else if x = j then
      (if a = i.succ then -(Real.sin θ) else if a = j.succ then Real.cos θ else 0)
    else (if x.succ = a then 1 else 0) := by
  by_cases hxi : x = i
  · subst hxi; simp [spatialRot, Matrix.of_apply]
  · by_cases hxj : x = j
    · subst hxj; simp only [hxi, ↓reduceIte, spatialRot, Matrix.of_apply,
        show x.succ ≠ i.succ from Fin.succ_injective _ |>.ne hxi]
    · simp only [hxi, hxj, ↓reduceIte, spatialRot, Matrix.of_apply,
        show x.succ ≠ i.succ from Fin.succ_injective _ |>.ne hxi,
        show x.succ ≠ j.succ from Fin.succ_injective _ |>.ne hxj]

private theorem ite_mul_ite' {p q : Prop} [Decidable p] [Decidable q]
    (a b c d' e f : ℝ) :
    (if p then a else if q then b else c) * (if p then d' else if q then e else f) =
    if p then a * d' else if q then b * e else c * f := by split_ifs <;> ring

private theorem nested_ite_sum_gen {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (A B : ℝ) (f : Fin n → ℝ) :
    ∑ x : Fin n, (if x = i then A else if x = j then B else f x) =
    A - f i + (B - f j) + ∑ x : Fin n, f x := by
  have : ∀ x : Fin n, (if x = i then A else if x = j then B else f x) =
      (if x = i then A - f x else 0) + (if x = j then B - f x else 0) + f x := by
    intro x; by_cases h1 : x = i
    · subst h1; simp [hij]
    · by_cases h2 : x = j
      · subst h2; simp [h1]
      · simp only [h1, h2, ↓reduceIte]; ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem succ_indicator_sum (a b : Fin (d + 1)) :
    ∑ x : Fin d, (if x.succ = a then (1:ℝ) else 0) * (if x.succ = b then 1 else 0) =
    if a = b then (if a = 0 then 0 else 1) else 0 := by
  by_cases hab : a = b
  · subst hab; simp only [ite_mul, one_mul, zero_mul, ite_true]
    by_cases ha0 : a = 0
    · simp [ha0, Fin.succ_ne_zero]
    · obtain ⟨a', rfl⟩ := Fin.exists_succ_eq.mpr ha0
      simp only [ha0, ↓reduceIte]; rw [Finset.sum_eq_single a']
      · simp
      · intro b' _ hb'; simp [Fin.succ_injective _ |>.ne hb']
      · intro h; exact absurd (Finset.mem_univ a') h
  · simp only [hab, ↓reduceIte]; apply Finset.sum_eq_zero
    intro x _; by_cases h1 : x.succ = a <;> by_cases h2 : x.succ = b <;> simp_all

theorem spatialRot_isLorentz (i j : Fin d) (hij : i ≠ j) (θ : ℝ) :
    IsLorentzMatrix d (spatialRot d i j θ) := by
  unfold IsLorentzMatrix; ext a b
  simp only [Matrix.mul_apply, minkowskiMatrix, Matrix.diagonal_apply, minkowskiSignature]
  simp_rw [Matrix.transpose_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Fin.sum_univ_succ]
  simp_rw [spatialRot_succ_apply d i j hij]
  simp only [spatialRot, Matrix.of_apply, Fin.succ_ne_zero, ↓reduceIte,
    show (0 : Fin (d+1)) ≠ i.succ from Ne.symm (Fin.succ_ne_zero i),
    show (0 : Fin (d+1)) ≠ j.succ from Ne.symm (Fin.succ_ne_zero j), mul_one]
  simp_rw [ite_mul_ite']
  rw [nested_ite_sum_gen hij, succ_indicator_sum]
  -- Pure ite arithmetic — case split on a, b being 0 or succ
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
  · simp [Ne.symm (Fin.succ_ne_zero i), Ne.symm (Fin.succ_ne_zero j), Fin.succ_ne_zero]
  · simp only [Ne.symm (Fin.succ_ne_zero a'), ↓reduceIte, Fin.succ_inj]
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
    · simp [Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero i), Ne.symm (Fin.succ_ne_zero j)]
    · simp only [Ne.symm (Fin.succ_ne_zero b'), ↓reduceIte, Fin.succ_inj]
      by_cases ha_i : a' = i <;> by_cases ha_j : a' = j <;>
        by_cases hb_i : b' = i <;> by_cases hb_j : b' = j
      all_goals first
        | (exfalso; subst_vars; exact hij rfl)
        | (subst_vars; split_ifs <;> simp_all <;> nlinarith [Real.sin_sq_add_cos_sq θ])

theorem spatialRot_orthochronous (i j : Fin d) (θ : ℝ) :
    spatialRot d i j θ 0 0 ≥ 1 := by
  rw [sr_other d _ _ _ _ (Ne.symm (Fin.succ_ne_zero i)) (Ne.symm (Fin.succ_ne_zero j))]
  simp

theorem spatialRot_det_one (i j : Fin d) (hij : i ≠ j) (θ : ℝ) :
    (spatialRot d i j θ).det = 1 := by
  -- Same clopen argument as planarBoost_det_one
  have hcont : Continuous (fun t : ℝ => (spatialRot d i j t).det) := by
    apply Continuous.matrix_det
    apply continuous_matrix; intro a b
    simp only [spatialRot, Matrix.of_apply]
    split_ifs <;> fun_prop
  have hdet_sq : ∀ t : ℝ, (spatialRot d i j t).det ^ 2 = 1 := by
    intro t
    have hL := spatialRot_isLorentz d i j hij t
    have := congr_arg Matrix.det hL
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
    have hη_ne : (minkowskiMatrix d).det ≠ 0 := by
      have := congr_arg Matrix.det (minkowskiMatrix_sq d)
      rw [Matrix.det_mul, Matrix.det_one] at this
      intro h0; rw [h0, mul_zero] at this; exact zero_ne_one this
    exact mul_right_cancel₀ hη_ne
      ((by ring : _ ^ 2 * _ = _ * _ * _).trans this |>.trans (one_mul _).symm)
  have hcover : ∀ t, (spatialRot d i j t).det = 1 ∨ (spatialRot d i j t).det = -1 := by
    intro t
    rcases mul_eq_zero.mp (by linear_combination hdet_sq t :
      ((spatialRot d i j t).det - 1) * ((spatialRot d i j t).det + 1) = 0) with h1 | h2
    · left; exact sub_eq_zero.mp h1
    · right; exact eq_neg_of_add_eq_zero_left h2
  have h1_closed : IsClosed {t : ℝ | (spatialRot d i j t).det = 1} :=
    (isClosed_singleton (x := (1 : ℝ))).preimage hcont
  have hm1_closed : IsClosed {t : ℝ | (spatialRot d i j t).det = -1} :=
    (isClosed_singleton (x := (-1 : ℝ))).preimage hcont
  have h1_open : IsOpen {t : ℝ | (spatialRot d i j t).det = 1} := by
    rw [show {t : ℝ | (spatialRot d i j t).det = 1} =
        {t : ℝ | (spatialRot d i j t).det = -1}ᶜ from by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact ⟨fun h1 hm1 => by rw [h1] at hm1; norm_num at hm1,
             fun hne => (hcover t).resolve_right hne⟩]
    exact hm1_closed.isOpen_compl
  have h1_univ := IsClopen.eq_univ ⟨h1_closed, h1_open⟩
    ⟨0, by simp [spatialRot_zero d i j hij, Matrix.det_one]⟩
  have h1_mem : θ ∈ {t : ℝ | (spatialRot d i j t).det = 1} := h1_univ ▸ Set.mem_univ θ
  exact h1_mem

/-- The spatial rotation as an element of SO⁺(1,d). -/
def spatialRotElement (i j : Fin d) (hij : i ≠ j) (θ : ℝ) : RestrictedLorentzGroup d :=
  ⟨⟨spatialRot d i j θ, spatialRot_isLorentz d i j hij θ⟩,
   ⟨spatialRot_det_one d i j hij θ, spatialRot_orthochronous d i j θ⟩⟩

/-- The path t ↦ spatialRot(tθ) connects 1 to spatialRotElement. -/
theorem joined_one_spatialRotElement (i j : Fin d) (hij : i ≠ j) (θ : ℝ) :
    Joined (1 : RestrictedLorentzGroup d) (spatialRotElement d i j hij θ) := by
  set f : unitInterval → RestrictedLorentzGroup d :=
    fun t => spatialRotElement d i j hij (t.val * θ)
  have hf_cont : Continuous f := by
    apply Continuous.subtype_mk; apply Continuous.subtype_mk
    apply continuous_matrix; intro a b
    simp only [spatialRot, Matrix.of_apply]
    split_ifs <;> fun_prop
  have hf0 : f ⟨0, unitInterval.zero_mem⟩ = 1 :=
    Subtype.ext (Subtype.ext (by
      simp only [f, spatialRotElement, spatialRot_zero d i j hij, zero_mul]; rfl))
  have hf1 : f ⟨1, unitInterval.one_mem⟩ = spatialRotElement d i j hij θ :=
    Subtype.ext (Subtype.ext (by simp [f, spatialRotElement]))
  exact ⟨⟨⟨f, hf_cont⟩, hf0, hf1⟩⟩

/-! ### Path-connectedness proof -/

/-- SO⁺(1,d) is path-connected. Every element is connected to the identity
    via boost-rotation decomposition. -/
theorem RestrictedLorentzGroup.isPathConnected :
    IsPathConnected (Set.univ : Set (RestrictedLorentzGroup d)) := by
  sorry

/-! ### Embedding into GL -/

/-- Every Lorentz matrix is invertible, so we get an embedding into GL(d+1, ℝ). -/
def toGL (Λ : LorentzGroup d) : GL (Fin (d + 1)) ℝ where
  val := Λ.val
  inv := lorentzInv d Λ.val
  val_inv := mul_lorentzInv d Λ.prop
  inv_val := lorentzInv_mul d Λ.prop

end LorentzLieGroup
