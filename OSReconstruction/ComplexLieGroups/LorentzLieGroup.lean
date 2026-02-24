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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

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

/-- For any a, b : ℝ, there exists θ such that -sin(θ) * a + cos(θ) * b = 0.
    This is the spatial rotation analogue of `boost_zero_entry`. -/
theorem rotation_zero_entry (a b : ℝ) : ∃ θ : ℝ, -Real.sin θ * a + Real.cos θ * b = 0 := by
  by_cases ha : a = 0
  · exact ⟨Real.pi / 2, by simp [ha, Real.sin_pi_div_two, Real.cos_pi_div_two]⟩
  · refine ⟨Real.arctan (b / a), ?_⟩
    set θ := Real.arctan (b / a)
    have hcos_ne : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_arctan_pos (b / a))
    have h := Real.tan_arctan (b / a)
    rw [Real.tan_eq_sin_div_cos, div_eq_div_iff hcos_ne ha] at h
    linarith

/-- Joined 1 a implies Joined 1 a⁻¹ in any topological group. -/
private theorem joined_one_inv' {a : RestrictedLorentzGroup d}
    (h : Joined 1 a) : Joined 1 a⁻¹ := by
  obtain ⟨γ⟩ := h
  exact ⟨⟨⟨fun t => (γ t)⁻¹, γ.continuous.inv⟩, by simp [γ.source], by simp [γ.target]⟩⟩

/-- Boost column zeroing: there exists B (product of boosts, Joined 1) such that
    (B * Λ).val.val k.succ 0 = 0 for all k : Fin d. -/
private theorem boost_column_zeroing (Λ : RestrictedLorentzGroup d) :
    ∃ B : RestrictedLorentzGroup d, Joined 1 B ∧
    ∀ k : Fin d, (B * Λ).val.val k.succ 0 = 0 := by
  suffices h : ∀ n : ℕ, n ≤ d → ∃ B : RestrictedLorentzGroup d, Joined 1 B ∧
    ∀ k : Fin d, k.val < n → (B * Λ).val.val k.succ 0 = 0 from by
    obtain ⟨B, hJ, hz⟩ := h d le_rfl
    exact ⟨B, hJ, fun k => hz k k.isLt⟩
  intro n hn
  induction n with
  | zero => exact ⟨1, Joined.refl 1, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨B', hJB', hzero⟩ := ih (by omega)
    set C := B' * Λ
    have hCL : IsLorentzMatrix d C.val.val := C.val.prop
    have hCo : C.val.val 0 0 ≥ 1 := C.prop.2
    have hab := lorentz_entry00_sq d hCL ⟨m, by omega⟩
    obtain ⟨β, hβ⟩ := boost_zero_entry d ⟨m, by omega⟩ hCL hCo hab
    refine ⟨boostElement d ⟨m, by omega⟩ β * B',
      joined_one_mul_general (joined_one_boostElement _ _ _) hJB', ?_⟩
    intro k hk
    rw [mul_assoc]
    show (planarBoost d ⟨m, by omega⟩ β * C.val.val) k.succ 0 = 0
    by_cases hkm : k.val = m
    · convert hβ using 2; exact congrArg Fin.succ (Fin.ext hkm)
    · rw [planarBoost_mul_other d ⟨m, by omega⟩ β C.val.val k.succ
        (Fin.succ_ne_zero k)
        (fun h => hkm (congrArg Fin.val (Fin.succ_injective _ h)))]
      exact hzero k (by omega)

/-- If Λ is Lorentz with Λ_{k+1, 0} = 0 for all k and Λ₀₀ ≥ 1, then Λ₀₀ = 1. -/
private theorem col0_zero_entry00_one {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hL : IsLorentzMatrix d Λ) (ho : Λ 0 0 ≥ 1)
    (hcol : ∀ k : Fin d, Λ k.succ 0 = 0) : Λ 0 0 = 1 := by
  have h := col0_sum_sq d hL
  have hsum : ∑ k : Fin d, Λ k.succ 0 ^ 2 = 0 :=
    Finset.sum_eq_zero (fun k _ => by rw [hcol k]; ring)
  rw [hsum, add_zero] at h
  nlinarith [sq_nonneg (Λ 0 0 - 1)]

/-- If Λ is Lorentz with column 0 = e₀, then row 0 = e₀ᵀ. -/
private theorem col0_e0_implies_row0 {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hL : IsLorentzMatrix d Λ) (h00 : Λ 0 0 = 1)
    (hcol : ∀ k : Fin d, Λ k.succ 0 = 0) :
    ∀ k : Fin d, Λ 0 k.succ = 0 := by
  intro k
  have h := congr_fun (congr_fun hL 0) k.succ
  simp only [minkowskiMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, minkowskiSignature, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [Fin.sum_univ_succ] at h
  simp only [↓reduceIte, Fin.succ_ne_zero] at h
  simp only [hcol, zero_mul, Finset.sum_const_zero, add_zero,
    show (0 : Fin (d + 1)) ≠ k.succ from (Fin.succ_ne_zero k).symm, ↓reduceIte] at h
  rw [h00] at h; linarith

/-- The spatial rotation in plane (i, j) applied to a matrix with column 0 = e₀
    preserves column 0 = e₀. -/
private theorem spatialRot_preserves_col0 (i j : Fin d) (hij : i ≠ j) (θ : ℝ)
    {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h00 : Λ 0 0 = 1) (hcol : ∀ k : Fin d, Λ k.succ 0 = 0) :
    (∀ k : Fin d, (spatialRot d i j θ * Λ) k.succ 0 = 0) ∧
    (spatialRot d i j θ * Λ) 0 0 = 1 := by
  constructor
  · intro k
    by_cases hki : k = i
    · rw [hki, spatialRot_mul_row_i d i j hij θ Λ 0, hcol i, hcol j]; ring
    · by_cases hkj : k = j
      · rw [hkj, spatialRot_mul_row_j d i j hij θ Λ 0, hcol i, hcol j]; ring
      · rw [spatialRot_mul_row_other d i j θ Λ 0 k.succ
            (fun h => hki (Fin.succ_injective _ h))
            (fun h => hkj (Fin.succ_injective _ h))]
        exact hcol k
  · rw [spatialRot_mul_row_other d i j θ Λ 0 0
        (Ne.symm (Fin.succ_ne_zero i))
        (Ne.symm (Fin.succ_ne_zero j))]
    exact h00

/-- Spatial row zeroing: for any entry Λ (i+1) (j+1) in the spatial block,
    there exists a spatial rotation S in the (i, m) plane that zeros out
    Λ's (m+1, j+1) entry while preserving all entries in rows not involving
    the i and m indices, and preserving col 0 = e₀.

    Concretely: for the spatial block row m and column j, we can find θ such that
    spatialRot(i, m, θ) * Λ has zero (m+1, j+1) entry, using `rotation_zero_entry`.

    This is the spatial analogue of `boost_zero_entry`. -/
private theorem spatial_zero_entry (i m : Fin d) (him : i ≠ m) (j : Fin d)
    {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h00 : Λ 0 0 = 1) (hcol : ∀ k : Fin d, Λ k.succ 0 = 0)
    (hrow : ∀ k : Fin d, Λ 0 k.succ = 0) :
    ∃ θ : ℝ, (spatialRot d i m θ * Λ) m.succ j.succ = 0 ∧
    (∀ k : Fin d, (spatialRot d i m θ * Λ) k.succ 0 = 0) ∧
    (spatialRot d i m θ * Λ) 0 0 = 1 ∧
    (∀ k : Fin d, (spatialRot d i m θ * Λ) 0 k.succ = 0) := by
  obtain ⟨θ, hθ⟩ := rotation_zero_entry (Λ i.succ j.succ) (Λ m.succ j.succ)
  refine ⟨θ, ?_, (spatialRot_preserves_col0 d i m him θ h00 hcol).1,
    (spatialRot_preserves_col0 d i m him θ h00 hcol).2, ?_⟩
  · rw [spatialRot_mul_row_j d i m him θ Λ j.succ]; linarith
  · intro k
    rw [spatialRot_mul_row_other d i m θ Λ k.succ 0
      (Ne.symm (Fin.succ_ne_zero i)) (Ne.symm (Fin.succ_ne_zero m))]
    exact hrow k

/-- If Λ is Lorentz with col 0 = e₀ and row 0 = e₀ᵀ, and the spatial block is the
    identity (Λ (i+1) (j+1) = δ_{ij} for all i j), then Λ = 1. -/
private theorem spatial_identity_implies_one
    {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h00 : Λ 0 0 = 1) (hcol : ∀ k : Fin d, Λ k.succ 0 = 0)
    (hrow : ∀ k : Fin d, Λ 0 k.succ = 0)
    (hspatial : ∀ i j : Fin d, Λ i.succ j.succ = if i = j then 1 else 0) :
    Λ = 1 := by
  ext a b
  simp only [Matrix.one_apply]
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
  · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
    · simp [h00]
    · simp [hrow b', Ne.symm (Fin.succ_ne_zero b')]
  · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
    · simp [hcol a']
    · rw [hspatial a' b']
      simp [Fin.succ_inj]

/-- Lorentz orthogonality for spatial columns: if Λ is Lorentz with col 0 = e₀ and
    row 0 = e₀ᵀ, then the spatial columns are orthonormal:
    ∑_k Λ_{k+1, i+1} * Λ_{k+1, j+1} = δ_{ij}. -/
private theorem lorentz_spatial_col_orthonormal
    {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hL : IsLorentzMatrix d Λ) (_h00 : Λ 0 0 = 1)
    (_hcol : ∀ k : Fin d, Λ k.succ 0 = 0)
    (hrow : ∀ k : Fin d, Λ 0 k.succ = 0) (i j : Fin d) :
    ∑ k : Fin d, Λ k.succ i.succ * Λ k.succ j.succ =
    if i = j then 1 else 0 := by
  -- From Λᵀ η Λ = η, extract the (i+1, j+1) entry
  have h := congr_fun (congr_fun hL i.succ) j.succ
  simp only [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMatrix, Matrix.diagonal_apply,
    minkowskiSignature, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.succ_ne_zero, ↓reduceIte, hrow i, zero_mul, zero_add] at h
  -- h : ∑ x, Λ x.succ i.succ * Λ x.succ j.succ = if i.succ = j.succ then 1 else 0
  -- goal: same but with i = j
  convert h using 1
  simp [Fin.succ_inj]

/-- When R = 1, (↑↑R * Λ) = Λ for matrices. -/
private theorem one_val_val_eq :
    (1 : RestrictedLorentzGroup d).val.val = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := rfl

/-- Subdiagonal entry zeroing: for a single column j, zero out entries below the
    diagonal, preserving col 0 = e₀, row 0 = e₀ᵀ, and any previously zeroed columns. -/
private theorem spatial_subdiag_zeroing (j : Fin d)
    {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hL : IsLorentzMatrix d Λ) (h00 : Λ 0 0 = 1)
    (hcol : ∀ k : Fin d, Λ k.succ 0 = 0)
    (hrow : ∀ k : Fin d, Λ 0 k.succ = 0)
    (hprev_cols : ∀ c : Fin d, c.val < j.val → ∀ i : Fin d, c.val < i.val →
      Λ i.succ c.succ = 0) :
    ∀ n : ℕ, n ≤ d →
    ∃ R : RestrictedLorentzGroup d, Joined 1 R ∧
      (∀ k : Fin d, (R.val.val * Λ) k.succ 0 = 0) ∧
      (∀ k : Fin d, (R.val.val * Λ) 0 k.succ = 0) ∧
      (R.val.val * Λ) 0 0 = 1 ∧
      IsLorentzMatrix d (R.val.val * Λ) ∧
      (∀ i : Fin d, j.val < i.val → i.val < j.val + 1 + n →
        (R.val.val * Λ) i.succ j.succ = 0) ∧
      (∀ c : Fin d, c.val < j.val → ∀ i : Fin d, c.val < i.val →
        (R.val.val * Λ) i.succ c.succ = 0) := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨1, Joined.refl 1, ?_, ?_, ?_, ?_, fun _ _ h => absurd h (by omega), ?_⟩
    all_goals (rw [show (1 : RestrictedLorentzGroup d).val.val = 1 from rfl, Matrix.one_mul])
    · exact hcol
    · exact hrow
    · exact h00
    · exact hL
    · exact hprev_cols
  | succ m ih =>
    obtain ⟨R', hJR', hcol', hrow', h00', hL', hzero', hprev'⟩ := ih (by omega)
    -- Check if the next entry to zero is within range
    by_cases hrange : j.val + 1 + m < d
    · -- We need to zero out entry (j + 1 + m, j) in the spatial block
      set target_row : Fin d := ⟨j.val + 1 + m, hrange⟩
      have hjt : j ≠ target_row := by
        intro h; exact absurd (congr_arg Fin.val h) (by simp [target_row]; omega)
      obtain ⟨θ, hθzero, hθcol, hθ00, hθrow⟩ :=
        spatial_zero_entry d j target_row hjt j h00' hcol' hrow'
      set S := spatialRotElement d j target_row hjt θ
      have hSmul : (S * R').val.val = S.val.val * R'.val.val := rfl
      have hSval : S.val.val = spatialRot d j target_row θ := rfl
      refine ⟨S * R', joined_one_mul_general (joined_one_spatialRotElement d j target_row hjt θ) hJR',
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- col 0 preservation
      · intro k; rw [hSmul, Matrix.mul_assoc, hSval]; exact hθcol k
      -- row 0 preservation
      · intro k; rw [hSmul, Matrix.mul_assoc, hSval]; exact hθrow k
      -- (0,0) entry
      · rw [hSmul, Matrix.mul_assoc, hSval]; exact hθ00
      -- Lorentz property
      · rw [hSmul, Matrix.mul_assoc]; exact IsLorentzMatrix.mul d S.val.prop hL'
      -- Zeroed entries in column j (including the new one)
      · intro i hij hi_bound
        rw [hSmul, Matrix.mul_assoc, hSval]
        by_cases hi_target : i = target_row
        · rw [hi_target]; exact hθzero
        · have hi_ne_j : i.succ ≠ j.succ := by
            intro h; exact absurd (Fin.succ_injective _ h |>.symm |> congr_arg Fin.val) (by omega)
          have hi_ne_t : i.succ ≠ target_row.succ :=
            fun h => hi_target (Fin.succ_injective _ h)
          rw [spatialRot_mul_row_other d j target_row θ (R'.val.val * Λ) j.succ i.succ
            hi_ne_j hi_ne_t]
          have hi_val_ne : i.val ≠ j.val + 1 + m := fun h => hi_target (Fin.ext h)
          exact hzero' i hij (by omega)
      -- Previously zeroed columns c < j are preserved
      · intro c hcj i hci
        rw [hSmul, Matrix.mul_assoc, hSval]
        -- Rotation in (j, target_row) plane: rows j+1 and target_row+1 are modified.
        -- For column c+1 with c < j: both j > c and target_row.val > j > c,
        -- so entries at rows j+1 and target_row+1 in column c+1 were zero (from hprev').
        -- The rotation's linear combination of zeros is zero.
        -- For other rows: unchanged.
        by_cases hi_j : i.succ = j.succ
        · -- Row j+1: cos(θ) * old + sin(θ) * old_target
          rw [show i = j from Fin.succ_injective _ hi_j,
            spatialRot_mul_row_i d j target_row hjt θ (R'.val.val * Λ) c.succ]
          have h1 := hprev' c hcj j (by omega)
          have h2 := hprev' c hcj target_row (by simp [target_row]; omega)
          rw [h1, h2]; ring
        · by_cases hi_t : i.succ = target_row.succ
          · -- Row target_row+1: -sin(θ) * old_j + cos(θ) * old_target
            rw [show i = target_row from Fin.succ_injective _ hi_t,
              spatialRot_mul_row_j d j target_row hjt θ (R'.val.val * Λ) c.succ]
            have h1 := hprev' c hcj j (by omega)
            have h2 := hprev' c hcj target_row (by simp [target_row]; omega)
            rw [h1, h2]; ring
          · -- Other rows: unchanged
            rw [spatialRot_mul_row_other d j target_row θ (R'.val.val * Λ) c.succ i.succ
              hi_j hi_t]
            exact hprev' c hcj i hci
    · -- Beyond range
      refine ⟨R', hJR', hcol', hrow', h00', hL', ?_, hprev'⟩
      intro i hij hi_bound
      exact hzero' i hij (by omega)

/-- Givens QR reduction of the spatial block: there exists R (product of spatial rotations,
    Joined to 1) such that R * Λ has all sub-diagonal spatial entries zero.
    This is the spatial analogue of boost_column_zeroing, extended to all columns.

    Uses spatial_subdiag_zeroing iteratively for each column j = 0, ..., d-1.
    Key invariant: the rotation for column j acts in rows > j, so it preserves
    zeros created in columns < j (since those zeros are at positions (i, k) with
    i > k and i ≤ j, and the rotation only affects rows > j). -/
private theorem spatial_givens_reduction
    {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hL : IsLorentzMatrix d Λ) (h00 : Λ 0 0 = 1)
    (hcol : ∀ k : Fin d, Λ k.succ 0 = 0)
    (hrow : ∀ k : Fin d, Λ 0 k.succ = 0) :
    ∃ R : RestrictedLorentzGroup d, Joined 1 R ∧
      (∀ k : Fin d, (R.val.val * Λ) k.succ 0 = 0) ∧
      (∀ k : Fin d, (R.val.val * Λ) 0 k.succ = 0) ∧
      (R.val.val * Λ) 0 0 = 1 ∧
      IsLorentzMatrix d (R.val.val * Λ) ∧
      (∀ i j : Fin d, j.val < i.val → (R.val.val * Λ) i.succ j.succ = 0) := by
  -- Outer induction on column index c
  suffices h : ∀ c : ℕ, c ≤ d →
      ∃ R : RestrictedLorentzGroup d, Joined 1 R ∧
        (∀ k : Fin d, (R.val.val * Λ) k.succ 0 = 0) ∧
        (∀ k : Fin d, (R.val.val * Λ) 0 k.succ = 0) ∧
        (R.val.val * Λ) 0 0 = 1 ∧
        IsLorentzMatrix d (R.val.val * Λ) ∧
        (∀ i j : Fin d, j.val < c → j.val < i.val → (R.val.val * Λ) i.succ j.succ = 0) from by
    obtain ⟨R, hJ, hc, hr, h0, hL', hsub⟩ := h d le_rfl
    exact ⟨R, hJ, hc, hr, h0, hL', fun i j hjlt => hsub i j j.isLt hjlt⟩
  intro c hc
  induction c with
  | zero =>
    refine ⟨1, Joined.refl 1, ?_, ?_, ?_, ?_, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    all_goals (rw [show (1 : RestrictedLorentzGroup d).val.val = 1 from rfl, Matrix.one_mul])
    · exact hcol
    · exact hrow
    · exact h00
    · exact hL
  | succ m ihm =>
    obtain ⟨R', hJR', hcol', hrow', h00', hL', hprev⟩ := ihm (by omega)
    -- Process column m (if m < d)
    by_cases hmd : m < d
    · -- Use spatial_subdiag_zeroing on column ⟨m, hmd⟩
      -- Need to provide the previously zeroed columns to spatial_subdiag_zeroing
      have hprev_for_m : ∀ c : Fin d, c.val < (⟨m, hmd⟩ : Fin d).val →
          ∀ i : Fin d, c.val < i.val → (R'.val.val * Λ) i.succ c.succ = 0 := by
        intro c hcm i hci
        exact hprev i c hcm hci
      obtain ⟨S, hJS, hcol'', hrow'', h00'', hL'', hzero, hprev_cols'⟩ :=
        spatial_subdiag_zeroing d ⟨m, hmd⟩ hL' h00' hcol' hrow' hprev_for_m d le_rfl
      have hSR : (S * R').val.val = S.val.val * R'.val.val := rfl
      have hSR_assoc : (S * R').val.val * Λ = S.val.val * (R'.val.val * Λ) := by
        rw [hSR, Matrix.mul_assoc]
      refine ⟨S * R', joined_one_mul_general hJS hJR', ?_, ?_, ?_, ?_, ?_⟩
      · intro k; rw [hSR_assoc]; exact hcol'' k
      · intro k; rw [hSR_assoc]; exact hrow'' k
      · rw [hSR_assoc]; exact h00''
      · rw [hSR_assoc]; exact IsLorentzMatrix.mul d S.val.prop hL'
      · intro i j hjm hjlt
        rw [hSR_assoc]
        by_cases hjm' : j.val < m
        · -- Column j was already processed. Use hprev_cols' from spatial_subdiag_zeroing.
          exact hprev_cols' j hjm' i hjlt
        · -- j.val = m (since j.val < m + 1 and j.val ≥ m)
          push_neg at hjm'
          have hjm_eq : j = ⟨m, hmd⟩ :=
            Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp hjm) hjm')
          subst hjm_eq
          exact hzero i hjlt (by omega)
    · -- m ≥ d, no more columns
      exact ⟨R', hJR', hcol', hrow', h00', hL', fun i j hjm hjlt =>
        hprev i j (by omega) hjlt⟩

/-- From upper-triangular + column orthonormality, the above-diagonal entries in
    the spatial block are also zero (by strong induction), and diagonal entries are ±1. -/
private theorem upper_triangular_orthogonal_to_diagonal
    {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hL : IsLorentzMatrix d Λ) (h00 : Λ 0 0 = 1)
    (hcol : ∀ k : Fin d, Λ k.succ 0 = 0)
    (hrow : ∀ k : Fin d, Λ 0 k.succ = 0)
    (hsubdiag : ∀ i j : Fin d, j.val < i.val → Λ i.succ j.succ = 0) :
    (∀ i j : Fin d, Λ i.succ j.succ = if i = j then Λ i.succ i.succ else 0) ∧
    (∀ j : Fin d, Λ j.succ j.succ = 1 ∨ Λ j.succ j.succ = -1) := by
  have horth := lorentz_spatial_col_orthonormal d hL h00 hcol hrow
  -- Step 1: Prove all off-diagonal entries are 0, by strong induction on column index.
  -- The above-diagonal zeros use the IH (columns k < j have only diagonal entry ≠ 0).
  -- First, we prove the off-diagonal property:
  have hoff : ∀ i j : Fin d, i ≠ j → Λ i.succ j.succ = 0 := by
    -- Suffices: for each j, ∀ i < j, Λ_{i+1,j+1} = 0.
    -- (The i > j case follows from hsubdiag.)
    suffices above : ∀ n : ℕ, n ≤ d →
        (∀ j : Fin d, j.val < n → ∀ i : Fin d, i.val < j.val → Λ i.succ j.succ = 0) by
      intro i j hij
      by_cases h : j.val < i.val
      · exact hsubdiag i j h
      · push_neg at h
        have : i.val < j.val := lt_of_le_of_ne h (fun h' => hij (Fin.ext h'))
        exact above d le_rfl j j.isLt i this
    intro n hn
    induction n with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ m ihm =>
      intro j hj i hi
      -- If j.val < m, use the IH directly
      by_cases hjm : j.val < m
      · exact ihm (by omega) j hjm i hi
      · -- j.val = m. Need to show Λ_{i+1,j+1} = 0 for i < j.
        push_neg at hjm
        have hjm_eq : j.val = m := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) hjm
        -- Use orthonormality: ∑_k Λ_{k+1,i+1} * Λ_{k+1,j+1} = 0 (since i ≠ j)
        have hij : i ≠ j := Fin.ne_of_val_ne (by omega)
        have hsum := horth i j
        simp only [hij, ite_false] at hsum
        -- In the sum, only k = i contributes:
        -- k > j: Λ_{k+1,j+1} = 0 (sub-diagonal)
        -- i < k ≤ j: Λ_{k+1,i+1} = 0 (sub-diagonal in col i)
        -- k < i: Λ_{k+1,i+1} = 0 (above-diagonal in col i, by IH since i < j = m)
        have honly_i : ∀ k : Fin d, k ≠ i → Λ k.succ i.succ * Λ k.succ j.succ = 0 := by
          intro k hki
          by_cases hk_gt_j : j.val < k.val
          · rw [hsubdiag k j hk_gt_j]; ring
          · push_neg at hk_gt_j
            by_cases hk_gt_i : i.val < k.val
            · rw [hsubdiag k i hk_gt_i]; ring
            · push_neg at hk_gt_i
              have hk_lt_i : k.val < i.val :=
                lt_of_le_of_ne hk_gt_i (fun h => hki (Fin.ext h))
              -- k < i < m, so above-diagonal in col i which was processed by IH
              rw [ihm (by omega) i (by omega) k hk_lt_i]; ring
        -- Sum reduces to Λ_{i+1,i+1} * Λ_{i+1,j+1}
        have hsum_eq : ∑ k : Fin d, Λ k.succ i.succ * Λ k.succ j.succ =
            Λ i.succ i.succ * Λ i.succ j.succ := by
          have h1 := Finset.add_sum_erase Finset.univ
            (fun k : Fin d => Λ k.succ i.succ * Λ k.succ j.succ) (Finset.mem_univ i)
          have h2 : ∑ k ∈ Finset.univ.erase i, Λ k.succ i.succ * Λ k.succ j.succ = 0 :=
            Finset.sum_eq_zero (fun k hk => honly_i k (Finset.ne_of_mem_erase hk))
          linarith
        rw [hsum_eq] at hsum
        -- hsum : Λ_{i+1,i+1} * Λ_{i+1,j+1} = 0
        -- Λ_{i+1,i+1}^2 = 1, so Λ_{i+1,i+1} ≠ 0
        have hii_sq : Λ i.succ i.succ ^ 2 = 1 := by
          have honly_ii : ∀ k : Fin d, k ≠ i → Λ k.succ i.succ ^ 2 = 0 := by
            intro k hki
            by_cases hk_gt : i.val < k.val
            · rw [hsubdiag k i hk_gt]; ring
            · push_neg at hk_gt
              have : k.val < i.val := lt_of_le_of_ne hk_gt (fun h => hki (Fin.ext h))
              rw [ihm (by omega) i (by omega) k this]; ring
          have hii_sum := horth i i
          simp only [ite_true] at hii_sum
          have h1 := Finset.add_sum_erase Finset.univ
            (fun k : Fin d => Λ k.succ i.succ ^ 2) (Finset.mem_univ i)
          have h2 : ∑ k ∈ Finset.univ.erase i, Λ k.succ i.succ ^ 2 = 0 :=
            Finset.sum_eq_zero (fun k hk => honly_ii k (Finset.ne_of_mem_erase hk))
          have h3 : ∑ k : Fin d, Λ k.succ i.succ ^ 2 = 1 := by
            convert hii_sum using 1; congr 1; ext k; ring
          linarith
        have hii_ne : Λ i.succ i.succ ≠ 0 := by
          intro h; rw [h] at hii_sq; simp at hii_sq
        -- hsum is now: Λ i.succ i.succ * Λ i.succ j.succ = 0 (from rw [hsum_eq] above)
        exact (mul_eq_zero.mp hsum).resolve_left hii_ne
  -- Step 2: Derive diagonal = ±1 from off-diagonal = 0 and column orthonormality.
  constructor
  · -- Off-diagonal = 0 (with specific shape)
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]; exact hoff i j hij
  · -- Diagonal = ±1
    intro j
    have hsum := horth j j
    simp only [ite_true] at hsum
    -- All off-diagonal terms vanish, so Λ_{j+1,j+1}^2 = 1
    have : ∑ k : Fin d, Λ k.succ j.succ ^ 2 = 1 := by
      convert hsum using 1; congr 1; ext k; ring
    have honly_jj : ∀ k : Fin d, k ≠ j → Λ k.succ j.succ ^ 2 = 0 := by
      intro k hkj; rw [hoff k j hkj]; ring
    have : Λ j.succ j.succ ^ 2 = 1 := by
      have hsplit := (Finset.add_sum_erase Finset.univ
        (fun k : Fin d => Λ k.succ j.succ ^ 2) (Finset.mem_univ j)).symm
      have hrest : ∑ k ∈ Finset.univ.erase j, Λ k.succ j.succ ^ 2 = 0 :=
        Finset.sum_eq_zero (fun k hk => honly_jj k (Finset.ne_of_mem_erase hk))
      linarith
    rcases mul_eq_zero.mp (show (Λ j.succ j.succ - 1) * (Λ j.succ j.succ + 1) = 0 by nlinarith) with h | h
    · left; linarith
    · right; linarith

/-- A π-rotation in the (i,j)-plane applied to a diagonal spatial matrix
    flips the signs of the i-th and j-th diagonal entries. -/
private theorem pi_rotation_diag_flip (i j : Fin d) (hij : i ≠ j)
    {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h00 : Λ 0 0 = 1)
    (hcol : ∀ k : Fin d, Λ k.succ 0 = 0)
    (hrow : ∀ k : Fin d, Λ 0 k.succ = 0)
    (hdiag : ∀ a b : Fin d, Λ a.succ b.succ = if a = b then Λ a.succ a.succ else 0) :
    let S := spatialRot d i j Real.pi
    (S * Λ) 0 0 = 1 ∧
    (∀ k : Fin d, (S * Λ) k.succ 0 = 0) ∧
    (∀ k : Fin d, (S * Λ) 0 k.succ = 0) ∧
    (∀ a b : Fin d, (S * Λ) a.succ b.succ =
      if a = b then (if a = i ∨ a = j then -Λ a.succ a.succ else Λ a.succ a.succ) else 0) := by
  intro S
  have hcos : Real.cos Real.pi = -1 := Real.cos_pi
  have hsin : Real.sin Real.pi = 0 := Real.sin_pi
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (S * Λ) 0 0 = 1: row 0 is unchanged
    rw [spatialRot_mul_row_other d i j Real.pi Λ 0 0
      (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]; exact h00
  · -- col 0 preserved
    intro k
    by_cases hk_i : k = i
    · rw [hk_i, spatialRot_mul_row_i d i j hij Real.pi Λ 0, hcol i, hcol j]; ring
    · by_cases hk_j : k = j
      · rw [hk_j, spatialRot_mul_row_j d i j hij Real.pi Λ 0, hcol i, hcol j]; ring
      · rw [spatialRot_mul_row_other d i j Real.pi Λ 0 k.succ
          (fun h => hk_i (Fin.succ_injective _ h)) (fun h => hk_j (Fin.succ_injective _ h))]
        exact hcol k
  · -- row 0 preserved
    intro k
    rw [spatialRot_mul_row_other d i j Real.pi Λ k.succ 0
      (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]; exact hrow k
  · -- spatial entries
    intro a b
    by_cases hab : a = b
    · -- diagonal case
      rw [hab]; simp only [ite_true]
      by_cases hb_i : b = i
      · rw [hb_i]; simp only [true_or, ite_true]
        rw [spatialRot_mul_row_i d i j hij Real.pi Λ i.succ, hdiag i i, hdiag j i]
        simp only [ite_true, hij.symm, ite_false]; rw [hcos, hsin]; ring
      · by_cases hb_j : b = j
        · rw [hb_j, if_pos (Or.inr rfl : j = i ∨ j = j)]
          rw [spatialRot_mul_row_j d i j hij Real.pi Λ j.succ, hdiag i j, hdiag j j]
          simp only [hij, ite_false, ite_true]; rw [hcos, hsin]; ring
        · have : ¬(b = i ∨ b = j) := fun h => h.elim hb_i hb_j
          simp only [this, ite_false]
          rw [spatialRot_mul_row_other d i j Real.pi Λ b.succ b.succ
            (fun h => hb_i (Fin.succ_injective _ h)) (fun h => hb_j (Fin.succ_injective _ h))]
    · -- off-diagonal case
      simp only [hab, ite_false]
      by_cases ha_i : a = i
      · rw [ha_i, spatialRot_mul_row_i d i j hij Real.pi Λ b.succ]
        have hib : i ≠ b := fun h => hab (ha_i ▸ h)
        rw [hdiag i b]; simp only [hib, ite_false]
        rw [hcos, hsin]; ring
      · by_cases ha_j : a = j
        · rw [ha_j, spatialRot_mul_row_j d i j hij Real.pi Λ b.succ]
          have hjb : j ≠ b := fun h => hab (ha_j ▸ h)
          rw [hdiag j b]; simp only [hjb, ite_false]
          rw [hcos, hsin]; ring
        · rw [spatialRot_mul_row_other d i j Real.pi Λ b.succ a.succ
            (fun h => ha_i (Fin.succ_injective _ h)) (fun h => ha_j (Fin.succ_injective _ h))]
          rw [hdiag a b]; simp [hab]

/-- Given a diagonal ±1 Lorentz matrix where all spatial diagonal entries are 1,
    the matrix is the identity. -/
private theorem diagonal_all_one_is_identity
    {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h00 : Λ 0 0 = 1)
    (hcol : ∀ k : Fin d, Λ k.succ 0 = 0)
    (hrow : ∀ k : Fin d, Λ 0 k.succ = 0)
    (hdiag : ∀ i j : Fin d, Λ i.succ j.succ = if i = j then Λ i.succ i.succ else 0)
    (hall : ∀ j : Fin d, Λ j.succ j.succ = 1) :
    Λ = 1 := by
  have hid : ∀ i j : Fin d, Λ i.succ j.succ = if i = j then 1 else 0 := by
    intro i j; rw [hdiag i j]; split_ifs with h <;> [exact h ▸ hall i; rfl]
  exact spatial_identity_implies_one d h00 hcol hrow hid

/-- Given a diagonal ±1 Lorentz matrix with det = 1, products of π-rotations turn all
    spatial diagonal entries to 1. Uses well-founded induction on negative-index count. -/
private theorem diagonal_sign_fixing
    {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hL : IsLorentzMatrix d Λ) (h00 : Λ 0 0 = 1)
    (hcol : ∀ k : Fin d, Λ k.succ 0 = 0)
    (hrow : ∀ k : Fin d, Λ 0 k.succ = 0)
    (hdiag : ∀ i j : Fin d, Λ i.succ j.succ = if i = j then Λ i.succ i.succ else 0)
    (hpm : ∀ j : Fin d, Λ j.succ j.succ = 1 ∨ Λ j.succ j.succ = -1)
    (hdet : Matrix.det Λ = 1) :
    ∃ R : RestrictedLorentzGroup d, Joined 1 R ∧ R.val.val * Λ = 1 := by
  -- Strong induction on the number of negative indices
  set negCount := (Finset.univ.filter (fun j : Fin d => Λ j.succ j.succ = -1)).card
  suffices key : ∀ (m : ℕ) {Λ' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
      IsLorentzMatrix d Λ' → Λ' 0 0 = 1 →
      (∀ k : Fin d, Λ' k.succ 0 = 0) →
      (∀ k : Fin d, Λ' 0 k.succ = 0) →
      (∀ i j : Fin d, Λ' i.succ j.succ = if i = j then Λ' i.succ i.succ else 0) →
      (∀ j : Fin d, Λ' j.succ j.succ = 1 ∨ Λ' j.succ j.succ = -1) →
      Matrix.det Λ' = 1 →
      (Finset.univ.filter (fun j : Fin d => Λ' j.succ j.succ = -1)).card ≤ 2 * m →
      ∃ R : RestrictedLorentzGroup d, Joined 1 R ∧ R.val.val * Λ' = 1 by
    have hle : (Finset.univ.filter (fun j : Fin d => Λ j.succ j.succ = -1)).card ≤ d :=
      (Finset.card_filter_le _ _).trans (by simp)
    exact key (d / 2 + 1) hL h00 hcol hrow hdiag hpm hdet (by omega)
  intro m
  induction m with
  | zero =>
    intro Λ' hL' h00' hcol' hrow' hdiag' hpm' hdet' hcard'
    have hcard0 : (Finset.univ.filter (fun j : Fin d => Λ' j.succ j.succ = -1)).card = 0 :=
      by omega
    have hall : ∀ j : Fin d, Λ' j.succ j.succ = 1 := by
      intro j; rcases hpm' j with h | h
      · exact h
      · exfalso
        have : j ∈ Finset.univ.filter (fun j : Fin d => Λ' j.succ j.succ = -1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        rw [Finset.card_eq_zero.mp hcard0] at this; exact absurd this (Finset.notMem_empty _)
    exact ⟨1, Joined.refl _, by
      rw [show (1 : RestrictedLorentzGroup d).val.val = 1 from rfl, Matrix.one_mul]
      exact diagonal_all_one_is_identity d h00' hcol' hrow' hdiag' hall⟩
  | succ m ihm =>
    intro Λ' hL' h00' hcol' hrow' hdiag' hpm' hdet' hcard'
    -- If already no negatives, done
    by_cases hcard0 : (Finset.univ.filter (fun j : Fin d => Λ' j.succ j.succ = -1)).card = 0
    · have hall : ∀ j : Fin d, Λ' j.succ j.succ = 1 := by
        intro j; rcases hpm' j with h | h
        · exact h
        · exfalso
          have : j ∈ Finset.univ.filter (fun j : Fin d => Λ' j.succ j.succ = -1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          rw [Finset.card_eq_zero.mp hcard0] at this; exact absurd this (Finset.notMem_empty _)
      exact ⟨1, Joined.refl _, by
        rw [show (1 : RestrictedLorentzGroup d).val.val = 1 from rfl, Matrix.one_mul]
        exact diagonal_all_one_is_identity d h00' hcol' hrow' hdiag' hall⟩
    · -- There exist negative indices. Need at least 2 (by even parity from det = 1).
      -- Step 1: The number of -1 entries is even (from det = 1)
      have hneg_even : Even (Finset.univ.filter (fun j : Fin d => Λ' j.succ j.succ = -1)).card := by
        -- First derive: product of spatial diagonal = 1
        have hΛ'_diag_eq : Λ' = Matrix.diagonal (fun i => Λ' i i) := by
          ext i j; rw [Matrix.diagonal_apply]
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
            · simp
            · rw [if_neg (Fin.succ_ne_zero j').symm]; exact hrow' j'
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
            · rw [if_neg (Fin.succ_ne_zero i')]; exact hcol' i'
            · rw [hdiag' i' j']
              split_ifs with h₁ h₂ h₂
              · rfl
              · exact absurd (congrArg Fin.succ h₁) h₂
              · exact absurd (Fin.succ_injective _ h₂) h₁
              · rfl
        have hsprod : ∏ j : Fin d, Λ' j.succ j.succ = 1 := by
          have hdet_prod := hdet'
          rw [hΛ'_diag_eq, Matrix.det_diagonal, Fin.prod_univ_succ] at hdet_prod
          rw [h00', one_mul] at hdet_prod; exact hdet_prod
        -- Each diagonal entry is ±1 = (-1)^(0 or 1)
        have heach : ∀ j : Fin d, Λ' j.succ j.succ =
            (-1 : ℝ) ^ (if Λ' j.succ j.succ = -1 then 1 else 0) := by
          intro j; rcases hpm' j with h | h <;> simp [h]
        -- Product = (-1)^(card of neg set)
        have hprod_pow : ∏ j : Fin d, Λ' j.succ j.succ =
            (-1 : ℝ) ^ (Finset.univ.filter (fun j : Fin d => Λ' j.succ j.succ = -1)).card := by
          rw [show ∏ j : Fin d, Λ' j.succ j.succ =
            ∏ j : Fin d, (-1 : ℝ) ^ (if Λ' j.succ j.succ = -1 then 1 else 0) from
            Finset.prod_congr rfl (fun j _ => heach j)]
          rw [Finset.prod_pow_eq_pow_sum, Finset.card_filter]
        rw [hsprod] at hprod_pow
        exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hprod_pow.symm
      -- Step 2: Since card ≥ 1 and even, card ≥ 2
      have hcard_ge2 : 2 ≤ (Finset.univ.filter (fun j : Fin d => Λ' j.succ j.succ = -1)).card := by
        rcases hneg_even with ⟨k, hk⟩; omega
      -- Step 3: Pick two distinct negative indices
      set negS := Finset.univ.filter (fun j : Fin d => Λ' j.succ j.succ = -1) with negS_def
      obtain ⟨i₀, hi₀_mem⟩ := Finset.card_pos.mp (by omega : 0 < negS.card)
      have hi₀_neg : Λ' i₀.succ i₀.succ = -1 := (Finset.mem_filter.mp hi₀_mem).2
      have hne2 : 0 < (negS.erase i₀).card := by
        rw [Finset.card_erase_of_mem hi₀_mem]; omega
      obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp hne2
      have hj₀_neg : Λ' j₀.succ j₀.succ = -1 :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj₀)).2
      have hij₀ : i₀ ≠ j₀ := (Finset.ne_of_mem_erase hj₀).symm
      -- Step 4: Apply π-rotation to flip both signs
      set S := spatialRotElement d i₀ j₀ hij₀ Real.pi
      have hSval : S.val.val = spatialRot d i₀ j₀ Real.pi := rfl
      obtain ⟨h00S, hcolS, hrowS, hdiagS⟩ :=
        pi_rotation_diag_flip d i₀ j₀ hij₀ h00' hcol' hrow' hdiag'
      -- Transfer from spatialRot to S.val.val
      rw [← hSval] at h00S hcolS hrowS hdiagS
      -- Step 5: S * Λ' preserves the ±1 diagonal structure
      have hSΛ_pm : ∀ j : Fin d, (S.val.val * Λ') j.succ j.succ = 1 ∨
          (S.val.val * Λ') j.succ j.succ = -1 := by
        intro j; have hd := hdiagS j j; simp only [ite_true] at hd; rw [hd]
        rcases hpm' j with h | h <;> by_cases hj_ij : j = i₀ ∨ j = j₀ <;> simp [hj_ij, h]
      have hSΛ_diag : ∀ i j : Fin d, (S.val.val * Λ') i.succ j.succ =
          if i = j then (S.val.val * Λ') i.succ i.succ else 0 := by
        intro i j; have hd := hdiagS i j
        by_cases h : i = j
        · subst h; simp
        · simp only [h, ite_false] at hd ⊢; exact hd
      -- Step 6: The neg count drops by 2
      have hcard_new : (Finset.univ.filter (fun j : Fin d =>
          (S.val.val * Λ') j.succ j.succ = -1)).card ≤ 2 * m := by
        -- The diagonal entry of S * Λ' at j: if j ∈ {i₀, j₀} then -Λ' else Λ'
        have hSΛ_diag_val : ∀ j : Fin d, (S.val.val * Λ') j.succ j.succ =
            if j = i₀ ∨ j = j₀ then -Λ' j.succ j.succ else Λ' j.succ j.succ := by
          intro j; have := hdiagS j j; simp only [ite_true] at this; exact this
        -- i₀ flips to 1, j₀ flips to 1
        have hi₀_pos : (S.val.val * Λ') i₀.succ i₀.succ = 1 := by
          rw [hSΛ_diag_val, if_pos (Or.inl rfl), hi₀_neg]; ring
        have hj₀_pos : (S.val.val * Λ') j₀.succ j₀.succ = 1 := by
          rw [hSΛ_diag_val, if_pos (Or.inr rfl), hj₀_neg]; ring
        -- For j ∉ {i₀, j₀}, the entry is unchanged
        have hother : ∀ j : Fin d, j ≠ i₀ → j ≠ j₀ →
            (S.val.val * Λ') j.succ j.succ = Λ' j.succ j.succ := by
          intro j hni hnj; rw [hSΛ_diag_val, if_neg (by push_neg; exact ⟨hni, hnj⟩)]
        -- The new negative set is a subset of (negS.erase i₀).erase j₀
        have hsub : Finset.univ.filter (fun j : Fin d => (S.val.val * Λ') j.succ j.succ = -1) ⊆
            (negS.erase i₀).erase j₀ := by
          intro j hj
          rw [Finset.mem_filter] at hj
          have hj_neg := hj.2
          rw [Finset.mem_erase, Finset.mem_erase]
          refine ⟨fun hjj₀ => by rw [hjj₀, hj₀_pos] at hj_neg; norm_num at hj_neg,
                  fun hji₀ => by rw [hji₀, hi₀_pos] at hj_neg; norm_num at hj_neg, ?_⟩
          rw [negS_def, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hji : j ≠ i₀ := fun h => by rw [h, hi₀_pos] at hj_neg; norm_num at hj_neg
          have hjj : j ≠ j₀ := fun h => by rw [h, hj₀_pos] at hj_neg; norm_num at hj_neg
          rw [hother j hji hjj] at hj_neg; exact hj_neg
        have hcard_sub : ((negS.erase i₀).erase j₀).card = negS.card - 2 := by
          have hj₀_mem_erase : j₀ ∈ negS.erase i₀ := hj₀
          rw [Finset.card_erase_of_mem hj₀_mem_erase, Finset.card_erase_of_mem hi₀_mem]; omega
        calc (Finset.univ.filter (fun j : Fin d => (S.val.val * Λ') j.succ j.succ = -1)).card
            ≤ ((negS.erase i₀).erase j₀).card := Finset.card_le_card hsub
          _ = negS.card - 2 := hcard_sub
          _ ≤ 2 * m := by omega
      -- Step 7: S * Λ' is Lorentz with det 1
      have hL_new : IsLorentzMatrix d (S.val.val * Λ') :=
        IsLorentzMatrix.mul d S.val.prop hL'
      have hdet_new : (S.val.val * Λ').det = 1 := by
        rw [Matrix.det_mul, S.prop.1, hdet', one_mul]
      -- Step 8: Apply IH
      obtain ⟨R', hJR', hR'eq⟩ := ihm hL_new h00S hcolS hrowS hSΛ_diag hSΛ_pm hdet_new hcard_new
      -- Step 9: Compose
      exact ⟨R' * S, joined_one_mul_general hJR' (joined_one_spatialRotElement d i₀ j₀ hij₀ Real.pi),
        by rw [show (R' * S).val.val = R'.val.val * S.val.val from rfl, Matrix.mul_assoc, hR'eq]⟩

/-- Full spatial reduction: there exists R (product of spatial rotations, Joined to 1)
    such that R * Λ = 1. -/
private theorem spatial_full_reduction (Λ : RestrictedLorentzGroup d)
    (hcol : ∀ k : Fin d, Λ.val.val k.succ 0 = 0) :
    ∃ R : RestrictedLorentzGroup d, Joined 1 R ∧ R * Λ = 1 := by
  -- Step 1: Extract key properties
  have hL : IsLorentzMatrix d Λ.val.val := Λ.val.prop
  have ho : Λ.val.val 0 0 ≥ 1 := Λ.prop.2
  have h00 : Λ.val.val 0 0 = 1 := col0_zero_entry00_one d hL ho hcol
  have hrow : ∀ k : Fin d, Λ.val.val 0 k.succ = 0 := col0_e0_implies_row0 d hL h00 hcol
  -- Step 2: Apply Givens reduction to get upper triangular
  obtain ⟨R₁, hJR₁, hcol₁, hrow₁, h00₁, hL₁, hsubdiag₁⟩ :=
    spatial_givens_reduction d hL h00 hcol hrow
  -- Step 3: Upper triangular + orthogonal → diagonal with ±1 entries
  obtain ⟨hdiag₁, hpm₁⟩ := upper_triangular_orthogonal_to_diagonal d hL₁ h00₁ hcol₁ hrow₁ hsubdiag₁
  -- Step 4: Fix diagonal signs using π-rotations via diagonal_sign_fixing
  have hdet₁ : Matrix.det (R₁.val.val * Λ.val.val) = 1 := by
    rw [Matrix.det_mul, R₁.prop.1, Λ.prop.1, one_mul]
  obtain ⟨R₂, hJR₂, hR₂eq⟩ := diagonal_sign_fixing d hL₁ h00₁ hcol₁ hrow₁ hdiag₁ hpm₁ hdet₁
  -- Now R₂.val.val * (R₁.val.val * Λ.val.val) = 1
  -- So (R₂ * R₁) * Λ = 1
  refine ⟨R₂ * R₁, joined_one_mul_general hJR₂ hJR₁, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  show (R₂ * R₁).val.val * Λ.val.val = 1
  rw [show (R₂ * R₁).val.val = R₂.val.val * R₁.val.val from rfl, Matrix.mul_assoc, hR₂eq]

/-- Spatial column zeroing: Given Λ ∈ SO⁺(1,d) with col 0 = e₀, there exists S
    (product of spatial rotations, Joined 1) such that S * Λ = 1. -/
private theorem spatial_reduction (Λ : RestrictedLorentzGroup d)
    (hcol : ∀ k : Fin d, Λ.val.val k.succ 0 = 0) :
    Joined 1 Λ := by
  obtain ⟨R, hJR, heq⟩ := spatial_full_reduction d Λ hcol
  have : Λ = R⁻¹ * 1 := by rw [← heq]; group
  rw [this, mul_one]
  exact joined_one_inv' d hJR

/-- Every element of SO⁺(1,d) is Joined to 1. -/
private theorem joined_one (Λ : RestrictedLorentzGroup d) : Joined 1 Λ := by
  obtain ⟨B, hJB, hcol⟩ := boost_column_zeroing d Λ
  have h1 : Joined 1 (B * Λ) := spatial_reduction d (B * Λ) hcol
  have h2 : Λ = B⁻¹ * (B * Λ) := by group
  rw [h2]
  exact joined_one_mul_general (joined_one_inv' d hJB) h1

/-- SO⁺(1,d) is path-connected. Every element is connected to the identity
    via boost-rotation decomposition. -/
theorem RestrictedLorentzGroup.isPathConnected :
    IsPathConnected (Set.univ : Set (RestrictedLorentzGroup d)) := by
  refine ⟨1, Set.mem_univ _, ?_⟩
  intro _ _
  exact joinedIn_univ.mpr (joined_one d _)

/-! ### Embedding into GL -/

/-- Every Lorentz matrix is invertible, so we get an embedding into GL(d+1, ℝ). -/
def toGL (Λ : LorentzGroup d) : GL (Fin (d + 1)) ℝ where
  val := Λ.val
  inv := lorentzInv d Λ.val
  val_inv := mul_lorentzInv d Λ.prop
  inv_val := lorentzInv_mul d Λ.prop

end LorentzLieGroup
