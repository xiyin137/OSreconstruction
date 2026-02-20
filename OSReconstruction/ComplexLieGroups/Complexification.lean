/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import OSReconstruction.ComplexLieGroups.LorentzLieGroup

/-!
# Complexification of the Lorentz Group

This file defines the complex Lorentz group SO⁺(1,d;ℂ) and establishes its
topological and group-theoretic properties. The crucial result is that
SO⁺(1,d;ℂ) is **connected**, which is the key input to the
Bargmann-Hall-Wightman theorem.

## Main definitions

* `ComplexLorentzGroup` — SO⁺(1,d;ℂ) as a structure (complex matrices preserving η with det = 1)
* `ComplexLorentzGroup.ofReal` — embedding SO⁺(1,d;ℝ) ↪ SO⁺(1,d;ℂ)
* `ComplexLorentzGroup.ofEuclidean` — embedding SO(d+1;ℝ) ↪ SO⁺(1,d;ℂ) via Wick rotation

## Main results

* `ComplexLorentzGroup.instGroup` — group structure
* `ComplexLorentzGroup.instTopologicalSpace` — induced topology from matrices
* `ComplexLorentzGroup.isPathConnected` — SO⁺(1,d;ℂ) is path-connected

## Strategy for connectedness

Over ℂ, the proper complex orthogonal group SO(n;ℂ) is connected. This follows
because every element can be written as a product of complex rotations in 2-planes,
and each such rotation group is isomorphic to ℂ* (hence connected).
Since SO⁺(1,d;ℂ) ≅ SO(d+1;ℂ) via Wick rotation, SO⁺(1,d;ℂ) is connected.

## References

* Hall, B.C. (2015). *Lie Groups, Lie Algebras, and Representations*. Springer, Ch. 1.
* Bargmann, V. (1947). *Irreducible unitary representations of the Lorentz group*.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup

variable {d : ℕ}

/-! ### Complex Lorentz group definition -/

/-- The complex Lorentz group SO⁺(1,d;ℂ): complex matrices preserving the
    Minkowski metric with determinant 1.

    Over ℂ, this group is already connected (unlike the real Lorentz group
    which has 4 connected components). No separate orthochronous condition
    is needed. -/
structure ComplexLorentzGroup (d : ℕ) where
  /-- The matrix Λ ∈ M_{(d+1)×(d+1)}(ℂ) -/
  val : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  /-- Preserves Minkowski metric: ΛᵀηΛ = η, componentwise.
      Σ_α η(α) · Λ(α,μ) · Λ(α,ν) = η(μ) · δ_{μν} -/
  metric_preserving : ∀ (μ ν : Fin (d + 1)),
    ∑ α : Fin (d + 1),
      (minkowskiSignature d α : ℂ) * val α μ * val α ν =
    if μ = ν then (minkowskiSignature d μ : ℂ) else 0
  /-- Proper: det(Λ) = 1 -/
  proper : val.det = 1

namespace ComplexLorentzGroup

/-! ### Topology -/

/-- Topology from the embedding into complex matrices. -/
instance instTopologicalSpace : TopologicalSpace (ComplexLorentzGroup d) :=
  TopologicalSpace.induced ComplexLorentzGroup.val inferInstance

/-- The `val` projection is continuous. -/
theorem continuous_val :
    Continuous (ComplexLorentzGroup.val : ComplexLorentzGroup d →
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  continuous_induced_dom

/-- Matrix entries are continuous. -/
theorem continuous_entry (μ ν : Fin (d + 1)) :
    Continuous (fun Λ : ComplexLorentzGroup d => Λ.val μ ν) :=
  (continuous_apply_apply μ ν).comp continuous_val

/-! ### Complex Minkowski matrix helpers -/

/-- The complex Minkowski metric matrix η_ℂ = diag(-1, +1, ..., +1). -/
private def ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ))

private theorem ηℂ_sq : (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * ηℂ = 1 := by
  simp only [ηℂ, Matrix.diagonal_mul_diagonal]
  ext i j; simp [Matrix.diagonal, Matrix.one_apply, minkowskiSignature]
  split_ifs <;> push_cast <;> ring

private theorem ηℂ_transpose :
    (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose = ηℂ := by
  simp [ηℂ, Matrix.diagonal_transpose]

/-- The componentwise metric condition is equivalent to the matrix equation Λᵀ η Λ = η. -/
theorem metric_preserving_matrix (Λ : ComplexLorentzGroup d) :
    Λ.val.transpose * ηℂ * Λ.val = ηℂ := by
  ext μ ν
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ηℂ, Matrix.diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  convert Λ.metric_preserving μ ν using 1
  apply Finset.sum_congr rfl; intro α _; ring

/-- Recover the componentwise condition from the matrix equation. -/
private theorem of_metric_preserving_matrix {M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (h : M.transpose * ηℂ * M = ηℂ) :
    ∀ (μ ν : Fin (d + 1)),
    ∑ α : Fin (d + 1),
      (minkowskiSignature d α : ℂ) * M α μ * M α ν =
    if μ = ν then (minkowskiSignature d μ : ℂ) else 0 := by
  intro μ ν
  have := congr_fun (congr_fun h μ) ν
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ηℂ, Matrix.diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
  convert this using 1
  apply Finset.sum_congr rfl; intro α _; ring

/-! ### Group structure -/

/-- The identity matrix is in SO⁺(1,d;ℂ). -/
def one : ComplexLorentzGroup d where
  val := 1
  metric_preserving := by
    intro μ ν
    simp only [Matrix.one_apply]
    split_ifs with h
    · subst h
      simp [Finset.sum_ite_eq', minkowskiSignature]
    · apply Finset.sum_eq_zero; intro α _
      by_cases hα : α = μ <;> simp [hα, h, Matrix.one_apply]
  proper := by simp

/-- The product of two elements of SO⁺(1,d;ℂ) is in SO⁺(1,d;ℂ). -/
def mul (Λ₁ Λ₂ : ComplexLorentzGroup d) : ComplexLorentzGroup d where
  val := Λ₁.val * Λ₂.val
  metric_preserving := by
    -- (Λ₁Λ₂)ᵀ η (Λ₁Λ₂) = Λ₂ᵀ (Λ₁ᵀ η Λ₁) Λ₂ = Λ₂ᵀ η Λ₂ = η
    apply of_metric_preserving_matrix
    rw [Matrix.transpose_mul]
    calc Λ₂.val.transpose * Λ₁.val.transpose * ηℂ * (Λ₁.val * Λ₂.val)
        = Λ₂.val.transpose * (Λ₁.val.transpose * ηℂ * Λ₁.val) * Λ₂.val := by
          simp only [Matrix.mul_assoc]
      _ = Λ₂.val.transpose * ηℂ * Λ₂.val := by rw [metric_preserving_matrix Λ₁]
      _ = ηℂ := metric_preserving_matrix Λ₂
  proper := by
    show (Λ₁.val * Λ₂.val).det = 1
    rw [Matrix.det_mul, Λ₁.proper, Λ₂.proper, mul_one]

instance instGroup : Group (ComplexLorentzGroup d) where
  mul := mul
  one := one
  inv Λ := {
    val := ηℂ * Λ.val.transpose * ηℂ
    metric_preserving := by
      apply of_metric_preserving_matrix
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ηℂ_transpose]
      have hη := ηℂ_sq (d := d)
      have hΛ := metric_preserving_matrix Λ
      -- Need: Λ * η * Λᵀ = η (from Λ * (η Λᵀ η) = 1 and η² = 1)
      have inv_mul : (ηℂ * Λ.val.transpose * ηℂ) * Λ.val = 1 := by
        calc ηℂ * Λ.val.transpose * ηℂ * Λ.val
            = ηℂ * (Λ.val.transpose * ηℂ * Λ.val) := by simp only [Matrix.mul_assoc]
          _ = ηℂ * ηℂ := by rw [hΛ]
          _ = 1 := hη
      have mul_inv : Λ.val * (ηℂ * Λ.val.transpose * ηℂ) = 1 :=
        mul_eq_one_comm.mpr inv_mul
      have hΛηΛt : Λ.val * ηℂ * Λ.val.transpose = ηℂ := by
        have h1 : Λ.val * ηℂ * Λ.val.transpose * ηℂ = 1 := by
          calc Λ.val * ηℂ * Λ.val.transpose * ηℂ
              = Λ.val * (ηℂ * Λ.val.transpose * ηℂ) := by simp only [Matrix.mul_assoc]
            _ = 1 := mul_inv
        calc Λ.val * ηℂ * Λ.val.transpose
            = Λ.val * ηℂ * Λ.val.transpose * 1 := by rw [Matrix.mul_one]
          _ = Λ.val * ηℂ * Λ.val.transpose * (ηℂ * ηℂ) := by rw [hη]
          _ = (Λ.val * ηℂ * Λ.val.transpose * ηℂ) * ηℂ := by simp only [Matrix.mul_assoc]
          _ = 1 * ηℂ := by rw [h1]
          _ = ηℂ := Matrix.one_mul _
      calc ηℂ * (Λ.val * ηℂ) * ηℂ * (ηℂ * Λ.val.transpose * ηℂ)
          = ηℂ * Λ.val * (ηℂ * ηℂ) * (ηℂ * Λ.val.transpose * ηℂ) := by
            simp only [Matrix.mul_assoc]
        _ = ηℂ * Λ.val * (ηℂ * Λ.val.transpose * ηℂ) := by rw [hη, Matrix.mul_one]
        _ = ηℂ * (Λ.val * ηℂ * Λ.val.transpose) * ηℂ := by simp only [Matrix.mul_assoc]
        _ = ηℂ * ηℂ * ηℂ := by rw [hΛηΛt]
        _ = 1 * ηℂ := by rw [hη]
        _ = ηℂ := Matrix.one_mul _
    proper := by
      show (ηℂ * Λ.val.transpose * ηℂ).det = 1
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Λ.proper, mul_one]
      have : (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).det *
          (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).det = 1 := by
        have := congr_arg Matrix.det (ηℂ_sq (d := d))
        rwa [Matrix.det_mul, Matrix.det_one] at this
      exact this
  }
  mul_assoc a b c := by
    show mul (mul a b) c = mul a (mul b c)
    cases a; cases b; cases c
    simp only [mul, Matrix.mul_assoc]
  one_mul a := by
    show mul one a = a
    cases a; simp only [mul, one, Matrix.one_mul]
  mul_one a := by
    show mul a one = a
    cases a; simp only [mul, one, Matrix.mul_one]
  inv_mul_cancel := by
    intro a
    show mul ⟨ηℂ * a.val.transpose * ηℂ, _, _⟩ a = one
    cases a with | mk v mp pr =>
    simp only [mul, one]
    congr 1
    calc ηℂ * v.transpose * ηℂ * v
        = ηℂ * (v.transpose * ηℂ * v) := by simp only [Matrix.mul_assoc]
      _ = ηℂ * ηℂ := by
          congr 1
          have : (ComplexLorentzGroup.mk v mp pr).val.transpose * ηℂ *
              (ComplexLorentzGroup.mk v mp pr).val = ηℂ :=
            metric_preserving_matrix ⟨v, mp, pr⟩
          simpa using this
      _ = 1 := ηℂ_sq

/-! ### Embedding of the real restricted Lorentz group -/

/-- The real restricted Lorentz group embeds into SO⁺(1,d;ℂ)
    by viewing real matrices as complex matrices. -/
def ofReal (Λ : RestrictedLorentzGroup d) : ComplexLorentzGroup d where
  val := fun i j => (Λ.val.val i j : ℂ)
  metric_preserving := by
    intro μ ν
    -- Extract the componentwise real Lorentz condition (with full simplification)
    have h := Λ.val.prop
    have hμν := congr_fun (congr_fun h μ) ν
    simp only [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMatrix,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at hμν
    -- hμν : ∑ x, Λ x μ * η x * Λ x ν = if μ = ν then η μ else 0 (over ℝ)
    -- Rewrite each summand to a single ℝ→ℂ cast
    have cast_eq : ∀ α, (minkowskiSignature d α : ℂ) * (↑(Λ.val.val α μ) : ℂ) *
        (↑(Λ.val.val α ν) : ℂ) =
        ((Λ.val.val α μ * minkowskiSignature d α * Λ.val.val α ν : ℝ) : ℂ) := by
      intro α; push_cast; ring
    simp_rw [cast_eq]
    norm_cast
    rw [hμν]
    split_ifs <;> simp
  proper := by
    change (Complex.ofRealHom.mapMatrix Λ.val.val).det = 1
    rw [← RingHom.map_det]
    have hdet : Λ.val.val.det = 1 := Λ.prop.1
    rw [hdet, map_one]

/-- SO(d+1;ℝ) embeds into SO⁺(1,d;ℂ) via Wick rotation conjugation.
    R ↦ W R W⁻¹ where W = diag(i, 1, ..., 1). -/
def ofEuclidean (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.det = 1) (horth : R.transpose * R = 1) :
    ComplexLorentzGroup d where
  val := fun μ ν =>
    let wμ : ℂ := if μ = (0 : Fin (d + 1)) then I else 1
    let wν_inv : ℂ := if ν = (0 : Fin (d + 1)) then -I else 1
    wμ * (R μ ν : ℂ) * wν_inv
  metric_preserving := by
    intro μ ν
    -- Key identity: η(α) · w(α)² = 1 for all α
    -- (For α=0: (-1)·I² = (-1)·(-1) = 1; for α≠0: 1·1² = 1)
    have hw_sq : ∀ α : Fin (d + 1),
        (minkowskiSignature d α : ℂ) *
        (if α = (0 : Fin (d + 1)) then I else 1) ^ 2 = 1 := by
      intro α; simp only [minkowskiSignature]
      split_ifs <;> push_cast <;> simp [Complex.I_sq]
    -- From horth: (Rᵀ R)(μ,ν) = δ(μ,ν), cast to ℂ
    have hRR : ∑ α : Fin (d + 1), (R α μ : ℂ) * (R α ν : ℂ) =
        if μ = ν then 1 else 0 := by
      have h := congr_fun (congr_fun horth μ) ν
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
      have h' : (↑(∑ x : Fin (d + 1), R x μ * R x ν) : ℂ) =
          (if μ = ν then (1 : ℂ) else 0) := by rw [h]; split_ifs <;> simp
      push_cast at h'; exact h'
    -- Transform each summand: factor out w_inv(μ) · w_inv(ν) using hw_sq
    have key : ∀ α : Fin (d + 1),
        (minkowskiSignature d α : ℂ) *
          ((if α = (0 : Fin (d + 1)) then I else 1) * (↑(R α μ) : ℂ) *
            (if μ = (0 : Fin (d + 1)) then -I else 1)) *
          ((if α = (0 : Fin (d + 1)) then I else 1) * (↑(R α ν) : ℂ) *
            (if ν = (0 : Fin (d + 1)) then -I else 1)) =
        (if μ = (0 : Fin (d + 1)) then -I else 1) *
          (if ν = (0 : Fin (d + 1)) then -I else 1) *
          ((↑(R α μ) : ℂ) * (↑(R α ν) : ℂ)) := by
      intro α
      by_cases hα : α = (0 : Fin (d + 1))
      · subst hα
        simp only [minkowskiSignature, ↓reduceIte]; push_cast
        set wμ := (if μ = (0 : Fin (d + 1)) then (-I : ℂ) else 1)
        set wν := (if ν = (0 : Fin (d + 1)) then (-I : ℂ) else 1)
        have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
        linear_combination -(↑(R 0 μ) * ↑(R 0 ν) * wμ * wν) * hI
      · simp only [minkowskiSignature, hα, ↓reduceIte]; push_cast; ring
    simp_rw [key, ← Finset.mul_sum, hRR]
    -- Goal: w_inv(μ) · w_inv(ν) · δ(μ,ν) = if μ = ν then η(μ) else 0
    by_cases h : μ = ν
    · subst h
      simp only [if_true, mul_one, minkowskiSignature]
      split_ifs with h0 <;> push_cast <;> simp [Complex.I_mul_I]
    · simp [if_neg h]
  proper := by
    -- Express val as W · R_ℂ · W⁻¹ where W = diag(I,1,...,1), W⁻¹ = diag(-I,1,...,1)
    -- det(W · R_ℂ · W⁻¹) = det(W) · det(R_ℂ) · det(W⁻¹) = I · 1 · (-I) = 1
    suffices h : Matrix.det (
        Matrix.diagonal (fun i : Fin (d + 1) => if i = (0 : Fin (d + 1)) then I else (1 : ℂ)) *
        Complex.ofRealHom.mapMatrix R *
        Matrix.diagonal (fun i : Fin (d + 1) =>
          if i = (0 : Fin (d + 1)) then -I else (1 : ℂ))) = 1 by
      convert h using 2
      ext μ ν
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal,
        RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [show (Complex.ofRealHom.mapMatrix R).det = (R.det : ℂ) from by
      rw [← RingHom.map_det]; rfl]
    rw [hR]; push_cast; simp only [mul_one, mul_neg, Complex.I_mul_I, neg_neg]

/-- The identity is in SO⁺(1,d;ℂ). -/
theorem one_val : (one (d := d)).val = 1 := rfl

/-! ### Exponential map infrastructure -/

/-- Two elements of `ComplexLorentzGroup` with the same matrix are equal. -/
@[ext]
theorem ext {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : Λ₁.val = Λ₂.val) : Λ₁ = Λ₂ := by
  cases Λ₁; cases Λ₂; cases h; rfl

open NormedSpace in
/-- ηℂ as a matrix unit (since ηℂ² = 1). -/
private def ηℂ_unit : (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)ˣ where
  val := ηℂ
  inv := ηℂ
  val_inv := ηℂ_sq
  inv_val := ηℂ_sq

/-- The Lie algebra condition: X^T η + η X = 0. -/
def IsInLieAlgebra (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : Prop :=
  X.transpose * ηℂ + ηℂ * X = 0

/-- If X is in the Lie algebra, so is t • X for any t : ℂ. -/
theorem isInLieAlgebra_smul {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (t : ℂ)
    (hX : IsInLieAlgebra X) : IsInLieAlgebra (t • X) := by
  unfold IsInLieAlgebra at *
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
  rw [hX, smul_zero]

/-- From the Lie algebra condition, X^T = -(η X η). -/
private theorem lie_algebra_transpose {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX : IsInLieAlgebra X) :
    X.transpose = -(ηℂ (d := d) * X * ηℂ) := by
  have h := hX
  unfold IsInLieAlgebra at h
  have h1 : X.transpose * ηℂ = -(ηℂ * X) := eq_neg_of_add_eq_zero_left h
  calc X.transpose
      = X.transpose * 1 := (Matrix.mul_one _).symm
    _ = X.transpose * (ηℂ * ηℂ) := by rw [ηℂ_sq]
    _ = X.transpose * ηℂ * ηℂ := (Matrix.mul_assoc _ _ _).symm
    _ = -(ηℂ * X) * ηℂ := by rw [h1]
    _ = -(ηℂ * X * ηℂ) := neg_mul _ _

open NormedSpace in
/-- If X is in the Lie algebra, then exp(X) preserves the Minkowski metric:
    exp(X)^T η exp(X) = η. -/
private theorem exp_metric_preserving {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX : IsInLieAlgebra X) :
    (exp X).transpose * ηℂ * exp X = ηℂ := by
  have hηU : IsUnit (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    IsUnit.of_mul_eq_one _ ηℂ_sq
  have hηInv : (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)⁻¹ = ηℂ :=
    Matrix.inv_eq_right_inv ηℂ_sq
  -- (exp X)^T = exp(X^T) = exp(-(ηℂ X ηℂ))
  rw [← Matrix.exp_transpose, lie_algebra_transpose hX]
  -- exp(-(ηℂ X ηℂ)) = exp(ηℂ (-X) ηℂ) = exp(ηℂ (-X) ηℂ⁻¹) = ηℂ exp(-X) ηℂ⁻¹ = ηℂ exp(-X) ηℂ
  rw [show -(ηℂ * X * ηℂ) = ηℂ * (-X) * (ηℂ : Matrix _ _ ℂ)⁻¹ from by
    rw [hηInv]; simp [mul_neg, neg_mul]]
  rw [Matrix.exp_conj ηℂ (-X) hηU, hηInv]
  -- Goal: ηℂ * exp(-X) * ηℂ * ηℂ * exp X = ηℂ
  calc ηℂ * exp (-X) * ηℂ * ηℂ * exp X
      = ηℂ * exp (-X) * (ηℂ * ηℂ) * exp X := by simp only [Matrix.mul_assoc]
    _ = ηℂ * exp (-X) * 1 * exp X := by rw [ηℂ_sq]
    _ = ηℂ * (exp (-X) * exp X) := by simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = ηℂ * 1 := by
        congr 1
        open scoped Matrix.Norms.Operator in
        rw [Matrix.exp_neg]
        open scoped Matrix.Norms.Operator in
        exact Matrix.nonsing_inv_mul _
          ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp X))
    _ = ηℂ := Matrix.mul_one _

open NormedSpace in
/-- If X is in the Lie algebra, then det(exp(X)) = 1.

    Proof: det(exp(tX))² = 1 for all t (from metric preservation), and
    det(exp(0)) = 1. Since t ↦ det(exp(tX)) is continuous and {1,-1} is
    discrete, it must be constant. -/
private theorem exp_det_one {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hX : IsInLieAlgebra X) :
    (exp X).det = 1 := by
  -- det(exp(tX))² = 1 for all t
  have hdet_sq : ∀ t : ℝ, ((exp ((t : ℂ) • X)).det) ^ 2 = 1 := by
    intro t
    have hmet := exp_metric_preserving (isInLieAlgebra_smul (t : ℂ) hX)
    have h1 := congr_arg Matrix.det hmet
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
    have hη_ne : (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).det ≠ 0 := by
      have := congr_arg Matrix.det (ηℂ_sq (d := d))
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact left_ne_zero_of_mul_eq_one this
    have h2 : (exp ((t : ℂ) • X)).det ^ 2 * (ηℂ (d := d)).det = 1 * (ηℂ (d := d)).det := by
      rw [one_mul, sq]; linear_combination h1
    exact mul_right_cancel₀ hη_ne h2
  -- det(exp(0·X)) = 1
  have hdet_0 : (exp (((0 : ℝ) : ℂ) • X)).det = 1 := by
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.det_one]
  -- t ↦ det(exp(tX)) is continuous
  have hdet_cont : Continuous (fun t : ℝ => (exp ((t : ℂ) • X)).det) := by
    open scoped Matrix.Norms.Operator in
    exact Continuous.matrix_det
      (NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const))
  -- det ∈ {1, -1} for all t
  have hcover : ∀ t : ℝ, (exp ((t : ℂ) • X)).det = 1 ∨
      (exp ((t : ℂ) • X)).det = -1 := by
    intro t
    have h0 : ((exp ((t : ℂ) • X)).det - 1) * ((exp ((t : ℂ) • X)).det + 1) = 0 := by
      linear_combination hdet_sq t
    rcases mul_eq_zero.mp h0 with h1 | h2
    · left; exact sub_eq_zero.mp h1
    · right; exact eq_neg_of_add_eq_zero_left h2
  -- {det = 1} is clopen
  have h1_closed : IsClosed {t : ℝ | (exp ((t : ℂ) • X)).det = 1} :=
    (isClosed_singleton (x := (1 : ℂ))).preimage hdet_cont
  have hm1_closed : IsClosed {t : ℝ | (exp ((t : ℂ) • X)).det = -1} :=
    (isClosed_singleton (x := (-1 : ℂ))).preimage hdet_cont
  have h1_open : IsOpen {t : ℝ | (exp ((t : ℂ) • X)).det = 1} := by
    rw [show {t : ℝ | (exp ((t : ℂ) • X)).det = 1} =
        {t : ℝ | (exp ((t : ℂ) • X)).det = -1}ᶜ from by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact ⟨fun h1 hm1 => by rw [h1] at hm1; norm_num at hm1,
             fun hne => (hcover t).resolve_right hne⟩]
    exact hm1_closed.isOpen_compl
  -- {det = 1} is clopen, nonempty, in connected ℝ → equals univ
  have h1_univ := IsClopen.eq_univ ⟨h1_closed, h1_open⟩ ⟨0, hdet_0⟩
  -- t = 1: det(exp(X)) = 1
  have h1_mem : (1 : ℝ) ∈ {t : ℝ | (exp ((t : ℂ) • X)).det = 1} :=
    h1_univ ▸ Set.mem_univ _
  simp only [Set.mem_setOf_eq, Complex.ofReal_one, one_smul] at h1_mem
  exact h1_mem

open NormedSpace in
/-- If X is in the Lie algebra, then exp(X) ∈ ComplexLorentzGroup. -/
def expLieAlg (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX : IsInLieAlgebra X) : ComplexLorentzGroup d where
  val := exp X
  metric_preserving := of_metric_preserving_matrix (exp_metric_preserving hX)
  proper := exp_det_one hX

open NormedSpace in
/-- The path t ↦ exp(tX) connects one to expLieAlg X. -/
theorem joined_one_expLieAlg (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hX : IsInLieAlgebra X) :
    Joined (one : ComplexLorentzGroup d) (expLieAlg X hX) := by
  rw [Joined]
  refine ⟨{
    toFun := fun t => expLieAlg ((t : ℂ) • X) (isInLieAlgebra_smul _ hX)
    continuous_toFun := by
      have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
      rw [hind.continuous_iff]
      show Continuous (fun t : ↥unitInterval => exp ((↑↑t : ℂ) • X))
      open scoped Matrix.Norms.Operator in
      exact NormedSpace.exp_continuous.comp
        ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)
    source' := by
      show expLieAlg _ _ = one
      ext; simp [expLieAlg, one, NormedSpace.exp_zero]
    target' := by
      show expLieAlg _ _ = expLieAlg X hX
      ext; simp [expLieAlg]
  }⟩

/-! ### Connectedness -/

/-- Left multiplication in ComplexLorentzGroup is continuous. -/
private theorem continuous_mul_left (a : ComplexLorentzGroup d) :
    Continuous (a * · : ComplexLorentzGroup d → ComplexLorentzGroup d) := by
  have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
  rw [hind.continuous_iff]
  change Continuous (fun x : ComplexLorentzGroup d => a.val * x.val)
  exact continuous_const.mul continuous_val

/-- If a and b are each joined to the identity, so is their product. -/
private theorem joined_one_mul {a b : ComplexLorentzGroup d}
    (ha : Joined one a) (hb : Joined one b) :
    Joined one (a * b) := by
  -- Left multiply path for b by a: t ↦ a * γ_b(t) gives path from a*1 to a*b
  -- then cast a*1 = a using mul_one
  have h : Joined a (a * b) :=
    ⟨(hb.somePath.map (continuous_mul_left a)).cast (mul_one a).symm rfl⟩
  exact ha.trans h

/-- Every element of SO⁺(1,d;ℂ) is joined to the identity.

    The proof uses the fact that SO⁺(1,d;ℂ) ≅ SO(d+1;ℂ) via Wick rotation,
    and SO(d+1;ℂ) is connected because every element can be written as a product
    of complex 2-plane rotations, each of which is exp of a Lie algebra element
    and hence continuously connected to the identity. -/
private theorem joined_one_all (Λ : ComplexLorentzGroup d) :
    Joined (one : ComplexLorentzGroup d) Λ := by
  sorry

/-- **SO⁺(1,d;ℂ) is path-connected.**

    This is the crucial fact for the Bargmann-Hall-Wightman theorem. -/
theorem isPathConnected :
    IsPathConnected (Set.univ : Set (ComplexLorentzGroup d)) := by
  rw [← pathConnectedSpace_iff_univ]
  exact PathConnectedSpace.mk ⟨one⟩ fun x y =>
    (joined_one_all x).symm.trans (joined_one_all y)

end ComplexLorentzGroup
