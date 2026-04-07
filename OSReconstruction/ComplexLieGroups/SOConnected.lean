/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Topology.Connected.PathConnected
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# SO(n;ℂ) is Path-Connected

This file defines the special orthogonal group SO(n;ℂ) over the complex numbers and
proves it is path-connected. The proof uses algebraic rotation matrices with path-
connectedness proved by column reduction and induction on dimension.

## Main definitions

* `SOComplex n` — the special orthogonal group SO(n;ℂ)

## Main results

* `SOComplex.isPathConnected` — SO(n;ℂ) is path-connected for all n

## Proof strategy

1. Define SO(n;ℂ) = {A ∈ M_n(ℂ) : A^T A = 1, det A = 1}
2. Define rotation matrices R_{i,j}(c,s) algebraically via projections P and skew generators Q
3. Prove R is in SO(n;ℂ) and joined to identity (via complex angle parametrization)
4. Column-reduce any A ∈ SO(n;ℂ) to have first column e₀ using rotations
5. Extract block structure and apply induction

## References

* Hall, B.C. (2015). *Lie Groups, Lie Algebras, and Representations*. Springer, Ch. 1.
-/

noncomputable section

open Complex Topology Matrix Finset
open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-! ### SO(n;ℂ) definition -/

/-- The special orthogonal group SO(n;ℂ): complex matrices with A^T A = I and det A = 1. -/
structure SOComplex (n : ℕ) where
  /-- The underlying matrix -/
  val : Matrix (Fin n) (Fin n) ℂ
  /-- Orthogonality: A^T A = I -/
  orthogonal : val.transpose * val = 1
  /-- Proper: det A = 1 -/
  proper : val.det = 1

namespace SOComplex

/-- Two elements with the same matrix are equal. -/
@[ext]
theorem ext {A B : SOComplex n} (h : A.val = B.val) : A = B := by
  cases A; cases B; cases h; rfl

/-- The identity matrix. -/
def one : SOComplex n where
  val := 1
  orthogonal := by simp
  proper := by simp

/-- The product of two elements. -/
def mul (A B : SOComplex n) : SOComplex n where
  val := A.val * B.val
  orthogonal := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc A.val.transpose, A.orthogonal, Matrix.one_mul, B.orthogonal]
  proper := by
    rw [Matrix.det_mul, A.proper, B.proper, mul_one]

/-- The inverse (= transpose, since A^T A = I). -/
def inv (A : SOComplex n) : SOComplex n where
  val := A.val.transpose
  orthogonal := by
    rw [Matrix.transpose_transpose]
    have hdet : A.val.det ≠ 0 := by rw [A.proper]; exact one_ne_zero
    exact mul_eq_one_comm.mpr A.orthogonal
  proper := by rw [Matrix.det_transpose, A.proper]

instance instGroup : Group (SOComplex n) where
  mul := mul
  one := one
  inv := inv
  mul_assoc a b c := ext (Matrix.mul_assoc _ _ _)
  one_mul a := ext (Matrix.one_mul _)
  mul_one a := ext (Matrix.mul_one _)
  inv_mul_cancel a := by
    show mul (inv a) a = one
    exact ext a.orthogonal

/-! ### Topology -/

instance instTopologicalSpace : TopologicalSpace (SOComplex n) :=
  TopologicalSpace.induced SOComplex.val inferInstance

theorem continuous_val : Continuous (SOComplex.val : SOComplex n → Matrix (Fin n) (Fin n) ℂ) :=
  continuous_induced_dom

instance instContinuousMul : ContinuousMul (SOComplex n) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    change Continuous (fun p : SOComplex n × SOComplex n => p.1.val * p.2.val)
    exact (continuous_val.comp continuous_fst).mul
      (continuous_val.comp continuous_snd)

instance instContinuousInv : ContinuousInv (SOComplex n) where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun a : SOComplex n => a.val.transpose)
    exact continuous_val.matrix_transpose

instance instIsTopologicalGroup : IsTopologicalGroup (SOComplex n) :=
  { instContinuousMul, instContinuousInv with }

/-! ### Exponential map -/

/-- A matrix is skew-symmetric if X^T = -X. -/
def IsSkewSymm (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  X.transpose = -X

/-- Skew-symmetric matrices are closed under scalar multiplication. -/
theorem isSkewSymm_smul (t : ℂ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : IsSkewSymm X) : IsSkewSymm (t • X) := by
  unfold IsSkewSymm at *
  rw [Matrix.transpose_smul, hX, smul_neg]

/-- exp(X)^T * exp(X) = I when X^T = -X. -/
theorem exp_orthogonal {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : IsSkewSymm X) : (NormedSpace.exp X).transpose * NormedSpace.exp X = 1 := by
  rw [← Matrix.exp_transpose, hX, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp X))

/-- det(exp(X)) = 1 when X^T = -X, via the clopen argument. -/
theorem exp_det_one_skew {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : IsSkewSymm X) : (NormedSpace.exp X).det = 1 := by
  have hdet_sq : ∀ t : ℝ, ((NormedSpace.exp ((t : ℂ) • X)).det) ^ 2 = 1 := by
    intro t
    have horth := exp_orthogonal (isSkewSymm_smul (t : ℂ) hX)
    have h := congr_arg Matrix.det horth
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    calc (NormedSpace.exp ((t : ℂ) • X)).det ^ 2
        = (NormedSpace.exp ((t : ℂ) • X)).det *
          (NormedSpace.exp ((t : ℂ) • X)).det := sq _
      _ = 1 := h
  have hdet_0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • X)).det = 1 := by
    simp [NormedSpace.exp_zero]
  have hdet_cont : Continuous (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).det) := by
    apply Continuous.matrix_det
    exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)
  have hcover : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X)).det = 1 ∨
      (NormedSpace.exp ((t : ℂ) • X)).det = -1 := by
    intro t
    have h0 : ((NormedSpace.exp ((t : ℂ) • X)).det - 1) *
        ((NormedSpace.exp ((t : ℂ) • X)).det + 1) = 0 := by
      linear_combination hdet_sq t
    rcases mul_eq_zero.mp h0 with h1 | h2
    · left; exact sub_eq_zero.mp h1
    · right; exact eq_neg_of_add_eq_zero_left h2
  have h1_closed : IsClosed {t : ℝ | (NormedSpace.exp ((t : ℂ) • X)).det = 1} :=
    (isClosed_singleton (x := (1 : ℂ))).preimage hdet_cont
  have hm1_closed : IsClosed {t : ℝ | (NormedSpace.exp ((t : ℂ) • X)).det = -1} :=
    (isClosed_singleton (x := (-1 : ℂ))).preimage hdet_cont
  have h1_open : IsOpen {t : ℝ | (NormedSpace.exp ((t : ℂ) • X)).det = 1} := by
    rw [show {t : ℝ | (NormedSpace.exp ((t : ℂ) • X)).det = 1} =
        {t : ℝ | (NormedSpace.exp ((t : ℂ) • X)).det = -1}ᶜ from by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact ⟨fun h1 hm1 => by rw [h1] at hm1; norm_num at hm1,
             fun hne => (hcover t).resolve_right hne⟩]
    exact hm1_closed.isOpen_compl
  have h1_univ := IsClopen.eq_univ ⟨h1_closed, h1_open⟩ ⟨0, hdet_0⟩
  have h1_mem : (1 : ℝ) ∈ {t : ℝ | (NormedSpace.exp ((t : ℂ) • X)).det = 1} :=
    h1_univ ▸ Set.mem_univ _
  simp only [Set.mem_setOf_eq, Complex.ofReal_one, one_smul] at h1_mem
  exact h1_mem

/-- Constructor: exp of a skew-symmetric matrix gives an element of SO(n;ℂ). -/
def expSkew (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsSkewSymm X) : SOComplex n where
  val := NormedSpace.exp X
  orthogonal := exp_orthogonal hX
  proper := exp_det_one_skew hX

/-- The path t ↦ exp(tX) connects one to expSkew X. -/
theorem joined_one_expSkew (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsSkewSymm X) :
    Joined (one : SOComplex n) (expSkew X hX) := by
  rw [Joined]
  refine ⟨{
    toFun := fun t => expSkew ((t : ℂ) • X) (isSkewSymm_smul _ hX)
    continuous_toFun := by
      have hind : IsInducing (SOComplex.val : SOComplex n → _) := ⟨rfl⟩
      rw [hind.continuous_iff]
      show Continuous (fun t : ↥unitInterval => NormedSpace.exp ((↑↑t : ℂ) • X))
      exact NormedSpace.exp_continuous.comp
        ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)
    source' := by
      show expSkew _ _ = one
      ext; simp [expSkew, one, NormedSpace.exp_zero]
    target' := by
      show expSkew _ _ = expSkew X hX
      ext; simp [expSkew]
  }⟩

/-- Left multiplication is continuous. -/
private theorem continuous_mul_left (a : SOComplex n) :
    Continuous (a * · : SOComplex n → SOComplex n) := by
  have hind : IsInducing (SOComplex.val : SOComplex n → _) := ⟨rfl⟩
  rw [hind.continuous_iff]
  change Continuous (fun x : SOComplex n => a.val * x.val)
  exact continuous_const.mul continuous_val

/-- If a and b are each joined to the identity, so is their product. -/
theorem joined_one_mul {a b : SOComplex n}
    (ha : Joined one a) (hb : Joined one b) :
    Joined one (a * b) := by
  have h : Joined a (a * b) :=
    ⟨(hb.somePath.map (continuous_mul_left a)).cast (mul_one a).symm rfl⟩
  exact ha.trans h

/-- If a is joined to the identity, so is its inverse. -/
private theorem joined_one_inv {a : SOComplex n} (ha : Joined one a) :
    Joined one (inv a) := by
  have hinv_cont : Continuous (inv : SOComplex n → SOComplex n) := by
    have hind : IsInducing (SOComplex.val : SOComplex n → _) := ⟨rfl⟩
    rw [hind.continuous_iff]
    show Continuous (fun x : SOComplex n => x.val.transpose)
    exact continuous_val.matrix_transpose
  have hinv_one : inv one = (one : SOComplex n) := ext (Matrix.transpose_one)
  exact hinv_one ▸ ⟨ha.somePath.map hinv_cont⟩

/-! ### Projections P and skew generators Q for algebraic proofs -/

/-- The projection onto the 2D subspace spanned by e_i and e_j:
    P = E_{ii} + E_{jj}. -/
private def P (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single i i 1 + Matrix.single j j 1

/-- The skew generator for rotation in the (i,j)-plane:
    Q = E_{ij} - E_{ji}. -/
private def Q (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single i j 1 - Matrix.single j i 1

/-! #### Algebraic identities for P and Q -/

private theorem P_sq (i j : Fin n) (hij : i ≠ j) : P i j * P i j = P i j := by
  unfold P
  simp only [add_mul, mul_add, Matrix.single_mul_single_same, mul_one,
    Matrix.single_mul_single_of_ne (1 : ℂ) i i j hij (1 : ℂ),
    Matrix.single_mul_single_of_ne (1 : ℂ) j j i hij.symm (1 : ℂ)]; abel

private theorem Q_sq (i j : Fin n) (hij : i ≠ j) : Q i j * Q i j = -P i j := by
  unfold Q P
  simp only [sub_mul, mul_sub, Matrix.single_mul_single_same, mul_one,
    Matrix.single_mul_single_of_ne (1 : ℂ) i j i hij.symm (1 : ℂ),
    Matrix.single_mul_single_of_ne (1 : ℂ) j i j hij (1 : ℂ)]; abel

private theorem PQ_eq (i j : Fin n) (hij : i ≠ j) : P i j * Q i j = Q i j := by
  unfold P Q
  simp only [add_mul, mul_sub, Matrix.single_mul_single_same, mul_one,
    Matrix.single_mul_single_of_ne (1 : ℂ) i i j hij (1 : ℂ),
    Matrix.single_mul_single_of_ne (1 : ℂ) j j i hij.symm (1 : ℂ)]; abel

private theorem QP_eq (i j : Fin n) (hij : i ≠ j) : Q i j * P i j = Q i j := by
  unfold Q P
  simp only [sub_mul, mul_add, Matrix.single_mul_single_same, mul_one,
    Matrix.single_mul_single_of_ne (1 : ℂ) i j i hij.symm (1 : ℂ),
    Matrix.single_mul_single_of_ne (1 : ℂ) j i j hij (1 : ℂ)]; abel

private theorem P_transpose (i j : Fin n) : (P i j).transpose = P i j := by
  unfold P; simp [Matrix.transpose_add, Matrix.transpose_single]

private theorem Q_transpose (i j : Fin n) : (Q i j).transpose = -Q i j := by
  unfold Q; simp [Matrix.transpose_sub, Matrix.transpose_single]

/-! ### Rotation matrices -/

/-- The rotation matrix in the (i,j)-plane with parameters (c,s):
    R = I + (c-1)P + sQ. When c²+s²=1, this gives the standard Givens rotation. -/
def rotMatrix (i j : Fin n) (c s : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + (c - 1) • P i j + s • Q i j

/-- The identity rotation. -/
theorem rotMatrix_one_zero (i j : Fin n) : rotMatrix i j 1 0 = 1 := by
  simp [rotMatrix, P, Q]

/-! #### Orthogonality: R^T R = I when c²+s²=1, proved algebraically -/

/-- **Orthogonality** of rotation matrices, proved via P/Q algebra. -/
theorem rotMatrix_orthogonal (i j : Fin n) (hij : i ≠ j) (c s : ℂ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (rotMatrix i j c s).transpose * rotMatrix i j c s = 1 := by
  -- R^T = I + (c-1)P - sQ
  have hRT : (rotMatrix i j c s).transpose = 1 + (c - 1) • P i j - s • Q i j := by
    unfold rotMatrix
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      P_transpose, Q_transpose, smul_neg, sub_eq_add_neg]
  rw [hRT]; unfold rotMatrix
  -- Expand using P²=P, Q²=-P, PQ=Q, QP=Q
  simp only [add_mul, mul_add, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
    P_sq i j hij, Q_sq i j hij, PQ_eq i j hij, QP_eq i j hij, sub_mul]
  simp only [smul_neg]
  -- Go to entries and use linear_combination with c²+s²=1
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.neg_apply, smul_eq_mul]
  ring_nf
  linear_combination (P i j a b) * hcs

/-! #### det(rotMatrix) = 1 via complex angle and clopen argument -/

/-- Helper: c + Is ≠ 0 when c²+s²=1. -/
private theorem csI_ne_zero (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1) :
    c + I * s ≠ 0 := by
  intro h
  have h1 : (c + I * s) * (c - I * s) = c ^ 2 + s ^ 2 := by
    have : (c + I * s) * (c - I * s) = c ^ 2 - (I * s) ^ 2 := by ring
    rw [this, mul_pow, I_sq]; ring
  rw [hcs, h, zero_mul] at h1
  exact zero_ne_one h1

/-- Helper: θ*I = log(c+Is) where θ = -I·log(c+Is). -/
private theorem thetaI_eq_log (c s : ℂ) (_hw_ne : c + I * s ≠ 0) :
    (-I * Complex.log (c + I * s)) * I = Complex.log (c + I * s) := by
  have : -I * Complex.log (c + I * s) * I = -(I * I) * Complex.log (c + I * s) := by ring
  rw [this, show I * I = I ^ 2 from (sq I).symm, I_sq]; ring

/-- Helper: (c+Is)⁻¹ = c - Is when c²+s²=1. -/
private theorem csI_inv (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (c + I * s)⁻¹ = c - I * s := by
  rw [eq_comm, inv_eq_of_mul_eq_one_left]
  have : (c - I * s) * (c + I * s) = c ^ 2 - (I * s) ^ 2 := by ring
  rw [this, mul_pow, I_sq]; linear_combination hcs

/-- cos θ = c where θ = -I·log(c+Is). -/
private theorem cos_complex_angle (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1)
    (hw_ne : c + I * s ≠ 0) :
    Complex.cos (-I * Complex.log (c + I * s)) = c := by
  set θ := -I * Complex.log (c + I * s)
  have hexp : Complex.exp (θ * I) = c + I * s := by
    rw [thetaI_eq_log c s hw_ne, Complex.exp_log hw_ne]
  have hexp_neg : Complex.exp (-θ * I) = (c + I * s)⁻¹ := by
    rw [show -θ * I = -(θ * I) from neg_mul θ I, Complex.exp_neg, hexp]
  rw [Complex.cos.eq_1, hexp, hexp_neg, csI_inv c s hcs]
  field_simp; ring

/-- sin θ = s where θ = -I·log(c+Is). -/
private theorem sin_complex_angle (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1)
    (hw_ne : c + I * s ≠ 0) :
    Complex.sin (-I * Complex.log (c + I * s)) = s := by
  set θ := -I * Complex.log (c + I * s)
  have hexp : Complex.exp (θ * I) = c + I * s := by
    rw [thetaI_eq_log c s hw_ne, Complex.exp_log hw_ne]
  have hexp_neg : Complex.exp (-θ * I) = (c + I * s)⁻¹ := by
    rw [show -θ * I = -(θ * I) from neg_mul θ I, Complex.exp_neg, hexp]
  rw [Complex.sin.eq_1, hexp, hexp_neg, csI_inv c s hcs]
  field_simp; ring_nf; rw [I_sq]; ring

/-- **det = 1** for rotation matrices, via clopen argument on the complex angle path. -/
theorem rotMatrix_det_one (i j : Fin n) (hij : i ≠ j) (c s : ℂ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (rotMatrix i j c s).det = 1 := by
  -- Find θ ∈ ℂ with cos θ = c, sin θ = s
  have hw_ne := csI_ne_zero c s hcs
  set θ := -I * Complex.log (c + I * s) with hθ_def
  have hcosθ : Complex.cos θ = c := cos_complex_angle c s hcs hw_ne
  have hsinθ : Complex.sin θ = s := sin_complex_angle c s hcs hw_ne
  -- The path t ∈ ℝ ↦ rotMatrix(cos(tθ), sin(tθ)) is continuous and det ∈ {1,-1}
  have hdet_path : ∀ t : ℝ,
      (rotMatrix i j (Complex.cos ((t : ℂ) * θ)) (Complex.sin ((t : ℂ) * θ))).det ^ 2 = 1 := by
    intro t
    have hcs_t := Complex.cos_sq_add_sin_sq ((t : ℂ) * θ)
    have horth := rotMatrix_orthogonal i j hij _ _ hcs_t
    have h := congr_arg Matrix.det horth
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact_mod_cast show _ ^ 2 = _ from calc
      _ = _ * _ := sq _
      _ = 1 := h
  have hcont : Continuous (fun t : ℝ =>
      (rotMatrix i j (Complex.cos ((t : ℂ) * θ)) (Complex.sin ((t : ℂ) * θ))).det) := by
    apply Continuous.matrix_det
    apply continuous_pi; intro a; apply continuous_pi; intro b
    simp only [rotMatrix, P, Q, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sub_apply, smul_eq_mul, Matrix.single_apply]
    apply Continuous.add
    · apply Continuous.add
      · exact continuous_const
      · exact ((Complex.continuous_cos.comp
          (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).mul
          continuous_const
    · exact (Complex.continuous_sin.comp
        (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const
  have hdet_0 : (rotMatrix i j (Complex.cos (((0 : ℝ) : ℂ) * θ))
      (Complex.sin (((0 : ℝ) : ℂ) * θ))).det = 1 := by
    simp [Complex.cos_zero, Complex.sin_zero, rotMatrix_one_zero]
  have hcover : ∀ t : ℝ,
      (rotMatrix i j (Complex.cos ((t : ℂ) * θ)) (Complex.sin ((t : ℂ) * θ))).det = 1 ∨
      (rotMatrix i j (Complex.cos ((t : ℂ) * θ)) (Complex.sin ((t : ℂ) * θ))).det = -1 := by
    intro t
    set d := (rotMatrix i j (Complex.cos ((t : ℂ) * θ)) (Complex.sin ((t : ℂ) * θ))).det
    have h0 := hdet_path t
    have : (d - 1) * (d + 1) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h1 | h2
    · left; exact sub_eq_zero.mp h1
    · right; exact eq_neg_of_add_eq_zero_left h2
  have h1_closed : IsClosed {t : ℝ |
      (rotMatrix i j (Complex.cos (↑t * θ)) (Complex.sin (↑t * θ))).det = 1} :=
    (isClosed_singleton (x := (1 : ℂ))).preimage hcont
  have hm1_closed : IsClosed {t : ℝ |
      (rotMatrix i j (Complex.cos (↑t * θ)) (Complex.sin (↑t * θ))).det = -1} :=
    (isClosed_singleton (x := (-1 : ℂ))).preimage hcont
  have h1_open : IsOpen {t : ℝ |
      (rotMatrix i j (Complex.cos (↑t * θ)) (Complex.sin (↑t * θ))).det = 1} := by
    rw [show {t : ℝ | (rotMatrix i j (Complex.cos (↑t * θ)) (Complex.sin (↑t * θ))).det = 1} =
        {t : ℝ | (rotMatrix i j (Complex.cos (↑t * θ)) (Complex.sin (↑t * θ))).det = -1}ᶜ from by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact ⟨fun h1 hm1 => by rw [h1] at hm1; norm_num at hm1,
             fun hne => (hcover t).resolve_right hne⟩]
    exact hm1_closed.isOpen_compl
  have h1_univ := IsClopen.eq_univ ⟨h1_closed, h1_open⟩ ⟨0, hdet_0⟩
  -- At t = 1: cos(1·θ) = cos θ = c, sin(1·θ) = sin θ = s
  have h1_mem : (1 : ℝ) ∈ {t : ℝ |
      (rotMatrix i j (Complex.cos (↑t * θ)) (Complex.sin (↑t * θ))).det = 1} :=
    h1_univ ▸ Set.mem_univ _
  simp only [Set.mem_setOf_eq, Complex.ofReal_one, one_mul] at h1_mem
  rw [hcosθ, hsinθ] at h1_mem
  exact h1_mem

/-! ### rotElement and path to identity -/

/-- Rotation in the (i,j)-plane as an element of SO(n;ℂ). -/
def rotElement (i j : Fin n) (hij : i ≠ j) (c s : ℂ)
    (hcs : c ^ 2 + s ^ 2 = 1) : SOComplex n where
  val := rotMatrix i j c s
  orthogonal := rotMatrix_orthogonal i j hij c s hcs
  proper := rotMatrix_det_one i j hij c s hcs

/-- Every rotation element is joined to the identity via the complex angle path. -/
theorem joined_one_rotElement (i j : Fin n) (hij : i ≠ j) (c s : ℂ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    Joined (one : SOComplex n) (rotElement i j hij c s hcs) := by
  have hw_ne := csI_ne_zero c s hcs
  set θ := -I * Complex.log (c + I * s)
  have hcosθ : Complex.cos θ = c := cos_complex_angle c s hcs hw_ne
  have hsinθ : Complex.sin θ = s := sin_complex_angle c s hcs hw_ne
  -- Path: t ↦ rotElement(cos(tθ), sin(tθ)) for t ∈ [0,1]
  rw [Joined]
  refine ⟨{
    toFun := fun t =>
      rotElement i j hij (Complex.cos ((t : ℂ) * θ)) (Complex.sin ((t : ℂ) * θ))
        (Complex.cos_sq_add_sin_sq _)
    continuous_toFun := by
      have hind : IsInducing (SOComplex.val : SOComplex n → _) := ⟨rfl⟩
      rw [hind.continuous_iff]
      show Continuous (fun t : ↥unitInterval =>
        rotMatrix i j (Complex.cos ((↑↑t : ℂ) * θ)) (Complex.sin ((↑↑t : ℂ) * θ)))
      apply continuous_pi; intro a; apply continuous_pi; intro b
      simp only [rotMatrix, P, Q, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.sub_apply, smul_eq_mul, Matrix.single_apply]
      apply Continuous.add
      · apply Continuous.add
        · exact continuous_const
        · exact ((Complex.continuous_cos.comp
            ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)).sub
            continuous_const).mul continuous_const
      · exact (Complex.continuous_sin.comp
          ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)).mul
          continuous_const
    source' := by
      show rotElement _ _ _ _ _ _ = one
      apply ext; simp [rotElement, rotMatrix_one_zero, one]
    target' := by
      show rotElement _ _ _ _ _ _ = rotElement i j hij c s hcs
      congr 1 <;> simp [hcosθ, hsinθ]
  }⟩

/-! ### Row action formulas -/

/-- Left-multiplying by rotMatrix transforms row i of A. -/
theorem rotMatrix_mul_row_i (i j : Fin n) (hij : i ≠ j) (c s : ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (l : Fin n) :
    (rotMatrix i j c s * A) i l = c * A i l + s * A j l := by
  simp only [rotMatrix, add_mul, one_mul, smul_mul_assoc, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  have hPA : (P i j * A) i l = A i l := by
    simp only [P, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply]
    simp only [show (j = i) = False from propext ⟨fun h => hij (h ▸ rfl), False.elim⟩,
      false_and, ite_false, add_zero]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  have hQA : (Q i j * A) i l = A j l := by
    simp only [Q, Matrix.mul_apply, Matrix.sub_apply, Matrix.single_apply]
    simp only [show (j = i) = False from propext ⟨fun h => hij (h ▸ rfl), False.elim⟩,
      false_and, ite_false, sub_zero]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  rw [hPA, hQA]; ring

/-- Left-multiplying by rotMatrix transforms row j of A. -/
theorem rotMatrix_mul_row_j (i j : Fin n) (hij : i ≠ j) (c s : ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (l : Fin n) :
    (rotMatrix i j c s * A) j l = -s * A i l + c * A j l := by
  simp only [rotMatrix, add_mul, one_mul, smul_mul_assoc, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  have hPA : (P i j * A) j l = A j l := by
    simp only [P, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply]
    simp only [show (i = j) = False from propext ⟨fun h => hij h, False.elim⟩,
      false_and, ite_false, zero_add]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  have hQA : (Q i j * A) j l = -A i l := by
    simp only [Q, Matrix.mul_apply, Matrix.sub_apply, Matrix.single_apply]
    simp only [show (i = j) = False from propext ⟨fun h => hij h, False.elim⟩,
      false_and, ite_false, zero_sub]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  rw [hPA, hQA]; ring

/-- Left-multiplying by rotMatrix doesn't change other rows. -/
theorem rotMatrix_mul_row_other (i j : Fin n) (_hij : i ≠ j) (c s : ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (l : Fin n) (k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (rotMatrix i j c s * A) k l = A k l := by
  simp only [rotMatrix, add_mul, one_mul, smul_mul_assoc, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  have hPA : (P i j * A) k l = 0 := by
    simp only [P, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply]
    simp only [show (i = k) = False from propext ⟨fun h => hki (h ▸ rfl), False.elim⟩,
      show (j = k) = False from propext ⟨fun h => hkj (h ▸ rfl), False.elim⟩,
      false_and, ite_false, add_zero]
    simp
  have hQA : (Q i j * A) k l = 0 := by
    simp only [Q, Matrix.mul_apply, Matrix.sub_apply, Matrix.single_apply]
    simp only [show (i = k) = False from propext ⟨fun h => hki (h ▸ rfl), False.elim⟩,
      show (j = k) = False from propext ⟨fun h => hkj (h ▸ rfl), False.elim⟩,
      false_and, ite_false, sub_zero]
    simp
  rw [hPA, hQA]; ring

/-! ### Column-related infrastructure -/

/-- Sum of squares in the first column equals `(Mᵀ M)₀₀`. -/
theorem firstColSqSum_eq_entry00 {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (∑ k : Fin (n + 1), M k 0 ^ 2) = (M.transpose * M) 0 0 := by
  simp [Matrix.mul_apply, sq]

/-- Left multiplication by an element of `SOComplex` preserves first-column
sum-of-squares. -/
theorem firstColSqSum_mul_left_SO {n : ℕ}
    (R : SOComplex (n + 1))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (∑ k : Fin (n + 1), (R.val * M) k 0 ^ 2) =
      (∑ k : Fin (n + 1), M k 0 ^ 2) := by
  calc
    (∑ k : Fin (n + 1), (R.val * M) k 0 ^ 2)
        = (((R.val * M).transpose * (R.val * M)) 0 0) := by
            exact firstColSqSum_eq_entry00 (R.val * M)
    _ = ((M.transpose * (R.val.transpose * R.val) * M) 0 0) := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ((M.transpose * M) 0 0) := by
          simp [R.orthogonal]
    _ = (∑ k : Fin (n + 1), M k 0 ^ 2) := by
          exact (firstColSqSum_eq_entry00 M).symm

/-- Matrix with first column `v` and all other columns zero. -/
def colMatrix {n : ℕ} (v : Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if j = 0 then v i else 0

@[simp] theorem colMatrix_apply_zero {n : ℕ} (v : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    colMatrix v i 0 = v i := by
  simp [colMatrix]

@[simp] theorem colMatrix_apply_succ {n : ℕ} (v : Fin (n + 1) → ℂ)
    (i : Fin (n + 1)) (j : Fin n) :
    colMatrix v i j.succ = 0 := by
  simp [colMatrix]

/-- First column of `A * colMatrix v` equals `A *ᵥ v`. -/
theorem mul_colMatrix_col0_eq_mulVec {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (v : Fin (n + 1) → ℂ) :
    (fun i => (A * colMatrix v) i 0) = (A *ᵥ v) := by
  ext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMatrix]

/-- First-column sum-of-squares for `colMatrix v` is exactly `∑ vᵢ²`. -/
theorem firstColSqSum_colMatrix {n : ℕ} (v : Fin (n + 1) → ℂ) :
    (∑ k : Fin (n + 1), (colMatrix v) k 0 ^ 2) = (∑ k : Fin (n + 1), v k ^ 2) := by
  simp [colMatrix]

/-- Vector action formula for the `i`-row of `rotMatrix`. -/
theorem rotMatrix_mulVec_i {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≠ j) (c s : ℂ)
    (v : Fin (n + 1) → ℂ) :
    (rotMatrix i j c s *ᵥ v) i = c * v i + s * v j := by
  have hrow :=
    rotMatrix_mul_row_i i j hij c s (colMatrix v) (0 : Fin (n + 1))
  have hcol : (rotMatrix i j c s * colMatrix v) i 0 = c * v i + s * v j := by
    simpa [colMatrix] using hrow
  have hmul := congrArg (fun f => f i) (mul_colMatrix_col0_eq_mulVec (rotMatrix i j c s) v)
  simpa [hcol] using hmul.symm

/-- Vector action formula for the `j`-row of `rotMatrix`. -/
theorem rotMatrix_mulVec_j {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≠ j) (c s : ℂ)
    (v : Fin (n + 1) → ℂ) :
    (rotMatrix i j c s *ᵥ v) j = -s * v i + c * v j := by
  have hrow :=
    rotMatrix_mul_row_j i j hij c s (colMatrix v) (0 : Fin (n + 1))
  have hcol : (rotMatrix i j c s * colMatrix v) j 0 = -s * v i + c * v j := by
    simpa [colMatrix] using hrow
  have hmul := congrArg (fun f => f j) (mul_colMatrix_col0_eq_mulVec (rotMatrix i j c s) v)
  simpa [hcol] using hmul.symm

/-- Vector action formula for rows other than `i` and `j`. -/
theorem rotMatrix_mulVec_other {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≠ j) (c s : ℂ)
    (v : Fin (n + 1) → ℂ) (k : Fin (n + 1))
    (hki : k ≠ i) (hkj : k ≠ j) :
    (rotMatrix i j c s *ᵥ v) k = v k := by
  have hrow :=
    rotMatrix_mul_row_other i j hij c s (colMatrix v) (0 : Fin (n + 1)) k hki hkj
  have hcol : (rotMatrix i j c s * colMatrix v) k 0 = v k := by
    simpa [colMatrix] using hrow
  have hmul := congrArg (fun f => f k) (mul_colMatrix_col0_eq_mulVec (rotMatrix i j c s) v)
  simpa [hcol] using hmul.symm

/-- `rotMatrix` preserves the quadratic sum `∑ vᵢ²` on vectors. -/
theorem sumSq_rotMatrix_mulVec_eq {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≠ j) (c s : ℂ)
    (hcs : c ^ 2 + s ^ 2 = 1)
    (v : Fin (n + 1) → ℂ) :
    (∑ k : Fin (n + 1), (rotMatrix i j c s *ᵥ v) k ^ 2) =
      (∑ k : Fin (n + 1), v k ^ 2) := by
  let R : SOComplex (n + 1) := rotElement i j hij c s hcs
  have hcolfun : (fun k : Fin (n + 1) => (R.val * colMatrix v) k 0) = R.val *ᵥ v := by
    simpa [R] using (mul_colMatrix_col0_eq_mulVec (rotMatrix i j c s) v)
  have hsumfun :
      (∑ k : Fin (n + 1), (R.val *ᵥ v) k ^ 2) =
        (∑ k : Fin (n + 1), (R.val * colMatrix v) k 0 ^ 2) := by
    exact congrArg (fun f : Fin (n + 1) → ℂ => ∑ k : Fin (n + 1), f k ^ 2) hcolfun.symm
  calc
    (∑ k : Fin (n + 1), (rotMatrix i j c s *ᵥ v) k ^ 2)
        = (∑ k : Fin (n + 1), (R.val * colMatrix v) k 0 ^ 2) := by
            simpa [R] using hsumfun
    _ = (∑ k : Fin (n + 1), (colMatrix v) k 0 ^ 2) := firstColSqSum_mul_left_SO R (colMatrix v)
    _ = (∑ k : Fin (n + 1), v k ^ 2) := firstColSqSum_colMatrix v

/-- Number of nonzero entries below index `0` in a vector. -/
def nonzeroBelowCount {m : ℕ} (v : Fin (m + 2) → ℂ) : ℕ :=
  (Finset.univ.filter (fun k : Fin (m + 2) => k ≠ 0 ∧ v k ≠ 0)).card

/-- Base case of vector column-reduction: if all entries below `0` vanish and
`∑ vᵢ² = 1`, then a rotation joined to identity sends `v` to `e₀`. -/
theorem reduceVector_count_zero {m : ℕ}
    (v : Fin (m + 2) → ℂ)
    (hcnt : nonzeroBelowCount v = 0)
    (hsum : ∑ k : Fin (m + 2), v k ^ 2 = 1) :
    ∃ R : SOComplex (m + 2), Joined SOComplex.one R ∧
      (∀ k : Fin (m + 2), (R.val *ᵥ v) k = if k = 0 then 1 else 0) := by
  have hzero : ∀ k : Fin (m + 2), k ≠ 0 → v k = 0 := by
    intro k hk
    by_contra hvk
    have hmem : k ∈ Finset.univ.filter (fun x : Fin (m + 2) => x ≠ 0 ∧ v x ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hvk⟩
    have hpos : 0 < nonzeroBelowCount v := by
      unfold nonzeroBelowCount
      exact Finset.card_pos.mpr ⟨k, hmem⟩
    have hnot : ¬ 0 < nonzeroBelowCount v := by simp [hcnt]
    exact hnot hpos
  have hv0_sq : v 0 ^ 2 = 1 := by
    rw [Fin.sum_univ_succ] at hsum
    have hrest : ∑ x : Fin (m + 1), v x.succ ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [hzero x.succ (Fin.succ_ne_zero _), zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    simpa [hrest] using hsum
  have hv0_pm : v 0 = 1 ∨ v 0 = -1 := by
    have hsplit : (v 0 - 1) * (v 0 + 1) = 0 := by
      linear_combination hv0_sq
    rcases mul_eq_zero.mp hsplit with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h2)
  rcases hv0_pm with hv0_one | hv0_neg_one
  · refine ⟨SOComplex.one, Joined.refl SOComplex.one, ?_⟩
    intro k
    simpa [SOComplex.one] using (show v k = if k = 0 then 1 else 0 from by
      by_cases hk : k = 0
      · simp [hk, hv0_one]
      · simp [hk, hzero k hk])
  · have h01 : (0 : Fin (m + 2)) ≠ 1 := Fin.zero_ne_one
    have hcs : (-1 : ℂ) ^ 2 + (0 : ℂ) ^ 2 = 1 := by norm_num
    refine ⟨SOComplex.rotElement 0 1 h01 (-1) 0 hcs,
      SOComplex.joined_one_rotElement 0 1 h01 (-1) 0 hcs, ?_⟩
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · have h0 :=
        rotMatrix_mulVec_i (i := 0) (j := 1) h01 (-1) 0 v
      have h10idx : (1 : Fin (m + 2)) ≠ 0 := by
        intro h
        have hval : (1 : ℕ) = 0 := by exact congrArg Fin.val h
        omega
      have h10 : v 1 = 0 := hzero 1 h10idx
      simpa [hv0_neg_one, h10] using h0
    ·
      by_cases hi : i = 0
      · subst hi
        have h1 :=
          rotMatrix_mulVec_j (i := 0) (j := 1) h01 (-1) 0 v
        have h10idx : (1 : Fin (m + 2)) ≠ 0 := by
          intro h
          have hval : (1 : ℕ) = 0 := by exact congrArg Fin.val h
          omega
        have h10 : v 1 = 0 := hzero 1 h10idx
        simpa [h10] using h1
      · have hs : i.succ ≠ 1 := by
          intro his
          have hi0 : i = 0 := by
            apply Fin.ext
            have hval : i.val + 1 = 1 := by
              exact congrArg Fin.val his
            have hval0 : i.val = 0 := by
              exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hval)
            exact hval0
          exact hi hi0
        have hother :=
          rotMatrix_mulVec_other (i := 0) (j := 1) h01 (-1) 0 v i.succ
            (Fin.succ_ne_zero i) hs
        have hz : v i.succ = 0 := hzero i.succ (Fin.succ_ne_zero i)
        simpa [hz, Fin.succ_ne_zero i] using hother

/-- Full vector reduction: if `∑ vᵢ² = 1`, there is `R ∈ SO(m+2;ℂ)` joined to
the identity with `R *ᵥ v = e₀`. -/
theorem reduceVector_full {m : ℕ}
    (v : Fin (m + 2) → ℂ)
    (hv : ∑ k : Fin (m + 2), v k ^ 2 = 1) :
    ∃ R : SOComplex (m + 2), Joined SOComplex.one R ∧
      (∀ k : Fin (m + 2), (R.val *ᵥ v) k = if k = 0 then 1 else 0) := by
  suffices h : ∀ N (B : Fin (m + 2) → ℂ), nonzeroBelowCount B ≤ N →
      (∑ k : Fin (m + 2), B k ^ 2 = 1) →
      ∃ R : SOComplex (m + 2), Joined SOComplex.one R ∧
        (∀ k : Fin (m + 2), (R.val *ᵥ B) k = if k = 0 then 1 else 0) by
    exact h (nonzeroBelowCount v) v le_rfl hv
  intro N
  induction N with
  | zero =>
      intro B hB hsumB
      have hcnt0 : nonzeroBelowCount B = 0 := by
        exact Nat.eq_zero_of_le_zero hB
      exact reduceVector_count_zero B hcnt0 hsumB
  | succ n ih =>
      intro B hB hsumB
      by_cases hle : nonzeroBelowCount B ≤ n
      · exact ih B hle hsumB
      · have hgt : n < nonzeroBelowCount B := Nat.lt_of_not_ge hle
        have hcnt_pos : 0 < nonzeroBelowCount B := lt_of_le_of_lt (Nat.zero_le n) hgt
        obtain ⟨k₁, hk₁_mem⟩ := Finset.card_pos.mp (by
          simpa [nonzeroBelowCount] using hcnt_pos)
        rw [Finset.mem_filter] at hk₁_mem
        obtain ⟨_, hk₁0, hvk₁⟩ := hk₁_mem
        suffices
            ∃ (a b : Fin (m + 2)), a ≠ b ∧ b ≠ 0 ∧ B b ≠ 0 ∧
              B a ^ 2 + B b ^ 2 ≠ 0 ∧ (a = 0 ∨ B a ≠ 0) by
          obtain ⟨a, b, hab, hb0, hvb, hsum, ha_good⟩ := this
          obtain ⟨w, hw'⟩ := IsAlgClosed.exists_eq_mul_self (B a ^ 2 + B b ^ 2)
          have hw : w ^ 2 = B a ^ 2 + B b ^ 2 := by
            simpa [sq] using hw'.symm
          have hw_ne : w ≠ 0 := by
            intro h0
            rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hw
            exact hsum hw.symm
          have hcs : (B a / w) ^ 2 + (B b / w) ^ 2 = 1 := by
            rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hw_ne)]
            exact hw.symm
          let R : SOComplex (m + 2) := SOComplex.rotElement a b hab (B a / w) (B b / w) hcs
          let B' : Fin (m + 2) → ℂ :=
            SOComplex.rotMatrix a b (B a / w) (B b / w) *ᵥ B
          have hzero_b : B' b = 0 := by
            have hbj : B' b = -(B b / w) * B a + (B a / w) * B b := by
              simpa [B'] using
                SOComplex.rotMatrix_mulVec_j (i := a) (j := b) hab (B a / w) (B b / w) B
            calc
              B' b = -(B b / w) * B a + (B a / w) * B b := hbj
              _ = 0 := by
                    field_simp [hw_ne]
                    ring
          have hunchanged : ∀ l : Fin (m + 2), l ≠ a → l ≠ b → B' l = B l := by
            intro l hla hlb
            dsimp [B']
            exact SOComplex.rotMatrix_mulVec_other (i := a) (j := b) hab
              (B a / w) (B b / w) B l hla hlb
          have hsub :
              Finset.univ.filter (fun k : Fin (m + 2) => k ≠ 0 ∧ B' k ≠ 0) ⊆
                (Finset.univ.filter (fun k : Fin (m + 2) => k ≠ 0 ∧ B k ≠ 0)).erase b := by
            intro l hl
            rw [Finset.mem_erase, Finset.mem_filter]
            rw [Finset.mem_filter] at hl
            obtain ⟨_, hl0, hlne⟩ := hl
            have hlb : l ≠ b := by
              intro hlb'
              exact hlne (hlb' ▸ hzero_b)
            refine ⟨hlb, Finset.mem_univ _, hl0, ?_⟩
            by_cases hla : l = a
            · subst hla
              rcases ha_good with hA0 | hAne
              · exact False.elim (hl0 hA0)
              · exact hAne
            · have hsame : B' l = B l := hunchanged l hla hlb
              exact by
                simpa [hsame] using hlne
          have hb_in : b ∈ Finset.univ.filter (fun k : Fin (m + 2) => k ≠ 0 ∧ B k ≠ 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0, hvb⟩
          have hcnt_eq : nonzeroBelowCount B = n + 1 :=
            Nat.le_antisymm hB (Nat.succ_le_of_lt hgt)
          have hcnt_dec : nonzeroBelowCount B' ≤ n := by
            calc
              nonzeroBelowCount B' = (Finset.univ.filter (fun k : Fin (m + 2) => k ≠ 0 ∧ B' k ≠ 0)).card := rfl
              _ ≤ ((Finset.univ.filter (fun k : Fin (m + 2) => k ≠ 0 ∧ B k ≠ 0)).erase b).card :=
                Finset.card_le_card hsub
              _ = (Finset.univ.filter (fun k : Fin (m + 2) => k ≠ 0 ∧ B k ≠ 0)).card - 1 :=
                Finset.card_erase_of_mem hb_in
              _ = nonzeroBelowCount B - 1 := rfl
              _ = n := by simp [hcnt_eq]
          have hsumB' : ∑ k : Fin (m + 2), B' k ^ 2 = 1 := by
            dsimp [B']
            calc
              ∑ k : Fin (m + 2), (SOComplex.rotMatrix a b (B a / w) (B b / w) *ᵥ B) k ^ 2
                  = ∑ k : Fin (m + 2), B k ^ 2 :=
                    SOComplex.sumSq_rotMatrix_mulVec_eq (i := a) (j := b) hab
                      (B a / w) (B b / w) hcs B
              _ = 1 := hsumB
          obtain ⟨R₂, hR₂_join, hR₂_col⟩ := ih B' hcnt_dec hsumB'
          refine ⟨R₂ * R, SOComplex.joined_one_mul hR₂_join
            (SOComplex.joined_one_rotElement a b hab (B a / w) (B b / w) hcs), ?_⟩
          intro k
          have hassoc :
              ((R₂ * R).val *ᵥ B) k = (R₂.val *ᵥ B') k := by
            change (((R₂.val * R.val) *ᵥ B) k = (R₂.val *ᵥ B') k)
            simp [R, SOComplex.rotElement, B', Matrix.mulVec_mulVec]
          simpa [hassoc] using hR₂_col k
        by_cases h0k₁ : B 0 ^ 2 + B k₁ ^ 2 ≠ 0
        · exact ⟨0, k₁, fun h => hk₁0 h.symm, hk₁0, hvk₁, h0k₁, Or.inl rfl⟩
        · push_neg at h0k₁
          have hcnt2 : 1 < nonzeroBelowCount B := by
            by_contra hlt
            push_neg at hlt
            have hcnt1 : nonzeroBelowCount B = 1 := by
              omega
            have huniq : ∀ l : Fin (m + 2), l ≠ 0 → l ≠ k₁ → B l = 0 := by
              intro l hl0 hlk
              by_contra hvl
              have : 1 < nonzeroBelowCount B := by
                unfold nonzeroBelowCount
                exact Finset.one_lt_card.mpr
                  ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl0, hvl⟩,
                   k₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₁0, hvk₁⟩, hlk⟩
              exact (not_lt_of_ge hlt) this
            have hrest : ∀ l : Fin (m + 1), l.succ ≠ k₁ → B l.succ ^ 2 = 0 := by
              intro l hlk
              rw [huniq l.succ (Fin.succ_ne_zero _) hlk, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
            have hsumbelow : ∑ l : Fin (m + 1), B l.succ ^ 2 = B k₁ ^ 2 := by
              have hk₁_pos : 0 < k₁.val := Fin.pos_of_ne_zero hk₁0
              set k₁' : Fin (m + 1) := ⟨k₁.val - 1, by omega⟩
              have hk₁_eq : k₁ = k₁'.succ := Fin.ext (by simp [k₁']; omega)
              rw [Finset.sum_eq_single k₁'
                (fun l _ hlk => hrest l (fun h =>
                  hlk (Fin.succ_injective _ (h.trans hk₁_eq))))]
              · rw [hk₁_eq]
              · simp [Finset.mem_univ]
            rw [Fin.sum_univ_succ, hsumbelow] at hsumB
            exact (one_ne_zero (h0k₁ ▸ hsumB).symm).elim
          have hk₁_in : k₁ ∈ Finset.univ.filter (fun k : Fin (m + 2) => k ≠ 0 ∧ B k ≠ 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₁0, hvk₁⟩
          have hcard_erase :
              0 < ((Finset.univ.filter (fun k : Fin (m + 2) => k ≠ 0 ∧ B k ≠ 0)).erase k₁).card := by
            rw [Finset.card_erase_of_mem hk₁_in]
            simpa [nonzeroBelowCount] using Nat.sub_pos_of_lt hcnt2
          obtain ⟨k₂, hk₂_erase⟩ := Finset.card_pos.mp hcard_erase
          rw [Finset.mem_erase] at hk₂_erase
          obtain ⟨hk₂_ne_k₁, hk₂_in⟩ := hk₂_erase
          rw [Finset.mem_filter] at hk₂_in
          obtain ⟨_, hk₂0, hvk₂⟩ := hk₂_in
          by_cases h0k₂ : B 0 ^ 2 + B k₂ ^ 2 ≠ 0
          · exact ⟨0, k₂, fun h => hk₂0 h.symm, hk₂0, hvk₂, h0k₂, Or.inl rfl⟩
          · push_neg at h0k₂
            have hk₁k₂ : B k₁ ^ 2 + B k₂ ^ 2 ≠ 0 := by
              have hv0_ne : B 0 ^ 2 ≠ 0 := by
                intro h0
                rw [sq, mul_self_eq_zero] at h0
                rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at h0k₁
                rw [sq, mul_self_eq_zero] at h0k₁
                exact hvk₁ h0k₁
              intro h
              have : B k₁ ^ 2 + B k₂ ^ 2 = -(2 * B 0 ^ 2) := by
                linear_combination h0k₁ + h0k₂
              rw [this] at h
              rw [neg_eq_zero] at h
              rcases mul_eq_zero.mp h with h2 | h0
              · norm_num at h2
              · exact hv0_ne h0
            exact ⟨k₁, k₂, hk₂_ne_k₁.symm, hk₂0, hvk₂, hk₁k₂, Or.inr hvk₁⟩

/-- Existence of an orthogonal matrix with prescribed first column on the unit quadric. -/
theorem exists_so_with_firstCol {m : ℕ}
    (v : Fin (m + 2) → ℂ)
    (hv : ∑ k : Fin (m + 2), v k ^ 2 = 1) :
    ∃ A : SOComplex (m + 2), ∀ k : Fin (m + 2), A.val k 0 = v k := by
  obtain ⟨R, _hR_join, hRcol⟩ := reduceVector_full (m := m) v hv
  let e0 : Fin (m + 2) → ℂ := Pi.single 0 (1 : ℂ)
  have hRv : R.val *ᵥ v = e0 := by
    funext k
    simpa [e0, Pi.single_apply] using hRcol k
  refine ⟨R⁻¹, ?_⟩
  intro k
  have hinv_mul : (R⁻¹).val * R.val = (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) := by
    ext i j
    change ((R⁻¹ * R).val i j = (1 : SOComplex (m + 2)).val i j)
    exact congrArg (fun M : SOComplex (m + 2) => M.val i j) (inv_mul_cancel R)
  have hv_eq : v = (R⁻¹).val *ᵥ e0 := by
    calc
      v = (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) *ᵥ v := by simp
      _ = ((R⁻¹).val * R.val) *ᵥ v := by simp [hinv_mul]
      _ = (R⁻¹).val *ᵥ (R.val *ᵥ v) := by
            simp [Matrix.mulVec_mulVec]
      _ = (R⁻¹).val *ᵥ e0 := by simp [hRv]
  have hcol : ((R⁻¹).val *ᵥ e0) k = (R⁻¹).val k 0 := by
    have hcol_fun :
        (R⁻¹).val *ᵥ e0 = (R⁻¹).val.col (0 : Fin (m + 2)) := by
      ext i
      simp [e0]
    exact congrFun hcol_fun k
  have hv_eq_k : v k = ((R⁻¹).val *ᵥ e0) k := congrArg (fun f => f k) hv_eq
  calc
    (R⁻¹).val k 0 = ((R⁻¹).val *ᵥ e0) k := hcol.symm
    _ = v k := hv_eq_k.symm

/-- The first column of A ∈ SO(n+1;ℂ) satisfies ∑ᵢ (A i 0)² = 1. -/
theorem first_col_sq_sum (A : SOComplex (n + 1)) :
    ∑ k : Fin (n + 1), A.val k 0 ^ 2 = 1 := by
  have h := A.orthogonal
  have h00 := congr_fun (congr_fun h 0) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, ↓reduceIte] at h00
  convert h00 using 1
  apply Finset.sum_congr rfl; intro k _; ring

/-- For m ≥ 2 and ∑ vᵢ² = 1, there exist distinct i, j with vᵢ² + vⱼ² ≠ 0. -/
theorem nonzero_pair_exists {m : ℕ} (hm : 2 ≤ m) (v : Fin m → ℂ)
    (hv : ∑ i : Fin m, v i ^ 2 = 1) :
    ∃ (i j : Fin m), i ≠ j ∧ v i ^ 2 + v j ^ 2 ≠ 0 := by
  by_contra h
  push_neg at h
  -- All pairs have vᵢ² + vⱼ² = 0, so vⱼ² = -vᵢ² for all i ≠ j
  have hpair : ∀ i j : Fin m, i ≠ j → v j ^ 2 = -(v i ^ 2) := by
    intro i j hij; linear_combination h i j hij
  -- Pick two distinct elements
  have ⟨i₀, i₁, hi₀₁⟩ : ∃ i₀ i₁ : Fin m, i₀ ≠ i₁ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  -- For all k ≠ i₀: v k² = -(v i₀²)
  have hrel : ∀ k : Fin m, k ≠ i₀ → v k ^ 2 = -(v i₀ ^ 2) :=
    fun k hk => hpair i₀ k hk.symm
  -- Compute the sum: split off the i₀ term
  have hsum : ∑ i : Fin m, v i ^ 2 = v i₀ ^ 2 + ∑ k ∈ univ.erase i₀, v k ^ 2 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have hrest : ∑ k ∈ univ.erase i₀, v k ^ 2 = ∑ k ∈ univ.erase i₀, (-(v i₀ ^ 2)) := by
    apply Finset.sum_congr rfl
    intro k hk; exact hrel k (Finset.ne_of_mem_erase hk)
  rw [hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _)] at hsum
  rw [hv] at hsum
  simp only [Finset.card_fin, nsmul_eq_mul] at hsum
  -- hsum: 1 = v i₀² + (m-1) · (-(v i₀²))
  by_cases hm2 : m = 2
  · -- m = 2: 1 = v i₀² - v i₀² = 0, contradiction
    subst hm2; norm_num at hsum
  · -- m ≥ 3: find k, ℓ both ≠ i₀ with k ≠ ℓ
    have hm3 : 3 ≤ m := by omega
    have ⟨k, ℓ, hk, hℓ, hkℓ⟩ : ∃ k ℓ : Fin m, k ≠ i₀ ∧ ℓ ≠ i₀ ∧ k ≠ ℓ := by
      have : 2 ≤ (univ.erase i₀ : Finset (Fin m)).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]; omega
      obtain ⟨k, hk, ℓ, hℓ, hkℓ⟩ := Finset.one_lt_card.mp this
      exact ⟨k, ℓ, Finset.ne_of_mem_erase hk, Finset.ne_of_mem_erase hℓ, hkℓ⟩
    have hkval := hrel k hk
    have hℓval := hrel ℓ hℓ
    have hpairval := h k ℓ hkℓ
    -- v k² + v ℓ² = 0 and both = -(v i₀²), so v i₀² = 0
    have hvi0 : v i₀ ^ 2 = 0 := by
      have : -(v i₀ ^ 2) + -(v i₀ ^ 2) = 0 := by
        linear_combination hpairval - hkval - hℓval
      linear_combination (-1/2 : ℂ) * this
    -- Then all v k² = 0, contradicting ∑ v k² = 1
    have hall : ∀ k : Fin m, v k ^ 2 = 0 := by
      intro k
      by_cases hki : k = i₀
      · rw [hki]; exact hvi0
      · rw [hrel k hki, hvi0, neg_zero]
    have : ∑ i : Fin m, v i ^ 2 = 0 := Finset.sum_eq_zero (fun i _ => hall i)
    rw [hv] at this; exact one_ne_zero this

/-! ### Block embedding -/

/-- The block diagonal matrix diag(1, B) for embedding SO(m) into SO(m+1). -/
private def embedVal {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Fin.cons (Fin.cons 1 (fun _ => 0)) (fun i => Fin.cons 0 (fun j => B i j))

@[simp] private theorem embedVal_zero_zero {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) :
    embedVal B 0 0 = 1 := by simp [embedVal]

@[simp] private theorem embedVal_zero_succ {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    embedVal B 0 j.succ = 0 := by simp [embedVal]

@[simp] private theorem embedVal_succ_zero {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) :
    embedVal B i.succ 0 = 0 := by simp [embedVal]

@[simp] private theorem embedVal_succ_succ {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    embedVal B i.succ j.succ = B i j := by simp [embedVal]

private theorem embedVal_transpose {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) :
    (embedVal B).transpose = embedVal B.transpose := by
  ext a b; simp only [Matrix.transpose_apply, embedVal]
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;> simp

private theorem embedVal_orthogonal {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ)
    (hB : B.transpose * B = 1) :
    (embedVal B).transpose * embedVal B = 1 := by
  rw [embedVal_transpose]
  ext a b
  simp only [Matrix.mul_apply, embedVal, Matrix.one_apply]
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  · simp [Fin.sum_univ_succ]
  · simp [Fin.sum_univ_succ, (Fin.succ_ne_zero j).symm]
  · simp [Fin.sum_univ_succ]
  · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add]
    have h := congr_fun (congr_fun hB i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    simp_rw [Fin.succ_inj]
    exact h

private theorem embedVal_submatrix {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) :
    (embedVal B).submatrix (Fin.succAbove 0) (Fin.succAbove 0) = B := by
  ext i j; simp [Matrix.submatrix, Fin.succAbove, embedVal]

private theorem embedVal_det {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) (hB : B.det = 1) :
    (embedVal B).det = 1 := by
  rw [Matrix.det_succ_row (embedVal B) 0, Fin.sum_univ_succ]
  simp only [embedVal_zero_zero, embedVal_zero_succ, Fin.val_zero,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, embedVal_submatrix]
  simp [hB]

/-- Embed SO(m) into SO(m+1) via block diagonal: B ↦ diag(1, B). -/
def embed {m : ℕ} (B : SOComplex m) : SOComplex (m + 1) where
  val := embedVal B.val
  orthogonal := embedVal_orthogonal B.val B.orthogonal
  proper := embedVal_det B.val B.proper

/-- The embedding is continuous. -/
theorem embed_continuous {m : ℕ} : Continuous (embed : SOComplex m → SOComplex (m + 1)) := by
  have hind : IsInducing (SOComplex.val : SOComplex (m + 1) → _) := ⟨rfl⟩
  rw [hind.continuous_iff]
  show Continuous (fun B : SOComplex m => embedVal B.val)
  apply continuous_pi; intro a; apply continuous_pi; intro b
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_apply_apply i j).comp continuous_val

/-- The embedding preserves one. -/
theorem embed_one {m : ℕ} : embed (one : SOComplex m) = (one : SOComplex (m + 1)) := by
  apply ext; ext a b
  simp only [embed, one]
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  · simp [embedVal]
  · simp [embedVal, Matrix.one_apply, (Fin.succ_ne_zero j).symm]
  · simp [embedVal, Matrix.one_apply, Fin.succ_ne_zero]
  · simp only [embedVal_succ_succ, Matrix.one_apply]
    simp_rw [Fin.succ_inj]

/-- Joined lifts through the embedding. -/
theorem embed_joined {m : ℕ} {A : SOComplex m}
    (h : Joined one A) : Joined (one : SOComplex (m + 1)) (embed A) := by
  rw [← embed_one]
  exact ⟨h.somePath.map embed_continuous⟩

/-! ### Path-connectedness of SO(n;ℂ) -/

/-- Every element of ℂ is a square (from algebraic closure). -/
private theorem exists_sq_root (z : ℂ) : ∃ w : ℂ, w ^ 2 = z := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_eq_mul_self z; exact ⟨w, by rw [sq, hw]⟩

/-- Column reduction: given A ∈ SO(n;ℂ) with n ≥ 2, there is a product of rotation elements
    R (joined to identity) such that (R * A) has first column e₀ = (1, 0, ..., 0). -/
private theorem column_reduce {m : ℕ} (A : SOComplex (m + 2)) :
    ∃ R : SOComplex (m + 2), Joined one R ∧
      (∀ k : Fin (m + 2), (R.val * A.val) k 0 = if k = 0 then 1 else 0) := by
  -- Strong induction on the count of nonzero entries below position 0
  let cnt (B : SOComplex (m + 2)) :=
    (Finset.univ.filter (fun k : Fin (m + 2) => k ≠ 0 ∧ B.val k 0 ≠ 0)).card
  suffices h : ∀ (N : ℕ) (B : SOComplex (m + 2)), cnt B ≤ N →
      ∃ R : SOComplex (m + 2), Joined one R ∧
        (∀ k : Fin (m + 2), (R.val * B.val) k 0 = if k = 0 then 1 else 0) by
    exact h _ A le_rfl
  intro N; induction N with
  | zero =>
    intro B hB
    -- All entries below 0 are zero
    have hzero : ∀ k : Fin (m + 2), k ≠ 0 → B.val k 0 = 0 := by
      intro k hk; by_contra hvk
      exact Nat.not_lt_zero _ (lt_of_lt_of_le
        (Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hvk⟩⟩) hB)
    -- v₀² = 1
    have hv0_sq : B.val 0 0 ^ 2 = 1 := by
      have := first_col_sq_sum B; rw [Fin.sum_univ_succ] at this
      simp_rw [hzero _ (Fin.succ_ne_zero _), zero_pow (by norm_num : 2 ≠ 0),
        Finset.sum_const_zero, add_zero] at this; exact this
    -- v₀ = ±1
    have hv0_pm : B.val 0 0 = 1 ∨ B.val 0 0 = -1 := by
      have : (B.val 0 0 - 1) * (B.val 0 0 + 1) = 0 := by linear_combination hv0_sq
      rcases mul_eq_zero.mp this with h | h
      · left; exact sub_eq_zero.mp h
      · right; exact eq_neg_of_add_eq_zero_left h
    rcases hv0_pm with h1 | hm1
    · -- v₀ = 1: take R = one
      exact ⟨one, Joined.refl one, fun k => by
        have : (one : SOComplex (m + 2)).val = 1 := rfl
        rw [this, Matrix.one_mul]; split_ifs with hk
        · exact hk ▸ h1
        · exact hzero k hk⟩
    · -- v₀ = -1: take R = rotElement 0 1 (-1) 0
      have h01 : (0 : Fin (m + 2)) ≠ 1 := Fin.zero_ne_one
      have hcs : (-1 : ℂ) ^ 2 + (0 : ℂ) ^ 2 = 1 := by norm_num
      refine ⟨rotElement 0 1 h01 (-1) 0 hcs,
        joined_one_rotElement 0 1 h01 (-1) 0 hcs, fun k => ?_⟩
      have hRval : (rotElement 0 1 h01 (-1) 0 hcs).val = rotMatrix 0 1 (-1) 0 := rfl
      rw [hRval]; split_ifs with hk
      · subst hk; rw [rotMatrix_mul_row_i 0 1 h01 (-1) 0 B.val 0]
        simp [hm1, hzero 1 h01.symm]
      · by_cases hk1 : k = 1
        · subst hk1; rw [rotMatrix_mul_row_j 0 1 h01 (-1) 0 B.val 0]
          simp [hm1, hzero 1 h01.symm]
        · rw [rotMatrix_mul_row_other 0 1 h01 (-1) 0 B.val 0 k hk hk1]
          exact hzero k hk
  | succ n ih =>
    intro B hB
    -- If count ≤ n, apply IH directly
    by_cases hle : cnt B ≤ n
    · exact ih B hle
    push_neg at hle
    -- count = n + 1; find k₁ ≠ 0 with B.val k₁ 0 ≠ 0
    obtain ⟨k₁, hk₁_mem⟩ := Finset.card_pos.mp (show 0 < cnt B by omega)
    rw [Finset.mem_filter] at hk₁_mem
    obtain ⟨_, hk₁0, hvk₁⟩ := hk₁_mem
    -- Helper: construct rotation R(a,b) that zeros entry b, show count decreases, apply IH
    suffices ∃ (a b : Fin (m + 2)), a ≠ b ∧ b ≠ 0 ∧ B.val b 0 ≠ 0 ∧
        B.val a 0 ^ 2 + B.val b 0 ^ 2 ≠ 0 ∧ (a = 0 ∨ B.val a 0 ≠ 0) by
      obtain ⟨a, b, hab, hb0, hvb, hsum, ha_good⟩ := this
      -- Construct the rotation
      obtain ⟨w, hw⟩ := exists_sq_root (B.val a 0 ^ 2 + B.val b 0 ^ 2)
      have hw_ne : w ≠ 0 := by
        intro h0; rw [h0, zero_pow (by norm_num : 2 ≠ 0)] at hw; exact hsum hw.symm
      have hcs : (B.val a 0 / w) ^ 2 + (B.val b 0 / w) ^ 2 = 1 := by
        rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hw_ne)]; exact hw.symm
      set R := rotElement a b hab (B.val a 0 / w) (B.val b 0 / w) hcs
      -- Entry b is zeroed
      have hzero_b : (R.val * B.val) b 0 = 0 := by
        show (rotMatrix a b _ _ * B.val) b 0 = 0
        rw [rotMatrix_mul_row_j a b hab _ _ B.val 0]; field_simp; ring
      -- Other entries unchanged
      have hunchanged : ∀ l, l ≠ a → l ≠ b → (R.val * B.val) l 0 = B.val l 0 := by
        intro l hla hlb
        show (rotMatrix a b _ _ * B.val) l 0 = B.val l 0
        exact rotMatrix_mul_row_other a b hab _ _ B.val 0 l hla hlb
      -- Count decreases: S' ⊆ S.erase b
      have hcnt_dec : cnt (mul R B) ≤ n := by
        have hsub : Finset.univ.filter (fun k : Fin (m+2) => k ≠ 0 ∧ (R.val * B.val) k 0 ≠ 0) ⊆
            (Finset.univ.filter (fun k : Fin (m+2) => k ≠ 0 ∧ B.val k 0 ≠ 0)).erase b := by
          intro l hl
          rw [Finset.mem_erase, Finset.mem_filter]
          rw [Finset.mem_filter] at hl; obtain ⟨_, hl0, hlne⟩ := hl
          have hlb : l ≠ b := fun h => hlne (h ▸ hzero_b)
          refine ⟨hlb, Finset.mem_univ _, hl0, ?_⟩
          by_cases hla : l = a
          · subst hla; rcases ha_good with rfl | ha
            · exact absurd rfl hl0
            · exact ha
          · rw [← hunchanged l hla hlb]; exact hlne
        have hb_in : b ∈ Finset.univ.filter (fun k : Fin (m+2) => k ≠ 0 ∧ B.val k 0 ≠ 0) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0, hvb⟩
        calc cnt (mul R B) ≤ _ := Finset.card_le_card hsub
          _ = cnt B - 1 := Finset.card_erase_of_mem hb_in
          _ ≤ n := by omega
      -- Apply IH
      obtain ⟨R₂, hR₂_join, hR₂_col⟩ := ih (mul R B) hcnt_dec
      exact ⟨mul R₂ R, joined_one_mul hR₂_join (joined_one_rotElement a b hab _ _ hcs),
        fun k => by
          have : (mul R₂ R).val = R₂.val * R.val := rfl
          rw [this, Matrix.mul_assoc]; exact hR₂_col k⟩
    -- Now find the good pair (a, b)
    by_cases h0k₁ : B.val 0 0 ^ 2 + B.val k₁ 0 ^ 2 ≠ 0
    · -- Non-isotropic: (a, b) = (0, k₁)
      exact ⟨0, k₁, fun h => hk₁0 h.symm, hk₁0, hvk₁, h0k₁, Or.inl rfl⟩
    · -- Isotropic: v₀² + v_{k₁}² = 0
      push_neg at h0k₁
      -- Count ≥ 2 (if count = 1, ∑ v² = v₀² + v_{k₁}² = 0 ≠ 1)
      have hcnt2 : 1 < cnt B := by
        by_contra hlt; push_neg at hlt
        have hcnt1 : cnt B = 1 := by omega
        -- Only k₁ is nonzero below 0
        have huniq : ∀ l : Fin (m + 2), l ≠ 0 → l ≠ k₁ → B.val l 0 = 0 := by
          intro l hl0 hlk; by_contra hvl
          have : 1 < cnt B := Finset.one_lt_card.mpr
            ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl0, hvl⟩,
             k₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₁0, hvk₁⟩, hlk⟩
          omega
        -- ∑ v² = v₀² + v_{k₁}² + 0 = 0 ≠ 1
        have hsum := first_col_sq_sum B
        have hrest : ∀ l : Fin (m + 1), l.succ ≠ k₁ → B.val l.succ 0 ^ 2 = 0 := by
          intro l hlk; rw [huniq l.succ (Fin.succ_ne_zero _) hlk,
            zero_pow (by norm_num : 2 ≠ 0)]
        -- Rearrange: the sum equals v₀² + v_{k₁}²
        have : ∑ l : Fin (m + 1), B.val l.succ 0 ^ 2 = B.val k₁ 0 ^ 2 := by
          have hk₁_pos : 0 < k₁.val := Fin.pos_of_ne_zero hk₁0
          set k₁' : Fin (m + 1) := ⟨k₁.val - 1, by omega⟩
          have hk₁_eq : k₁ = k₁'.succ := Fin.ext (by simp [k₁']; omega)
          rw [Finset.sum_eq_single k₁' (fun l _ hlk => hrest l (fun h =>
            hlk (Fin.succ_injective _ (h.trans hk₁_eq))))]
          · rw [hk₁_eq]
          · simp [Finset.mem_univ]
        rw [Fin.sum_univ_succ, this] at hsum
        exact one_ne_zero (h0k₁ ▸ hsum).symm
      -- Find k₂ ≠ k₁ from the filter set using erase
      have hk₁_in : k₁ ∈ Finset.univ.filter
          (fun k : Fin (m + 2) => k ≠ 0 ∧ B.val k 0 ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₁0, hvk₁⟩
      have hcard_erase : 0 < ((Finset.univ.filter
          (fun k : Fin (m + 2) => k ≠ 0 ∧ B.val k 0 ≠ 0)).erase k₁).card := by
        rw [Finset.card_erase_of_mem hk₁_in]; show 0 < cnt B - 1; omega
      obtain ⟨k₂, hk₂_erase⟩ := Finset.card_pos.mp hcard_erase
      rw [Finset.mem_erase] at hk₂_erase
      obtain ⟨hk₂_ne_k₁, hk₂_in⟩ := hk₂_erase
      rw [Finset.mem_filter] at hk₂_in
      obtain ⟨_, hk₂0, hvk₂⟩ := hk₂_in
      by_cases h0k₂ : B.val 0 0 ^ 2 + B.val k₂ 0 ^ 2 ≠ 0
      · -- (a, b) = (0, k₂)
        exact ⟨0, k₂, fun h => hk₂0 h.symm, hk₂0, hvk₂, h0k₂, Or.inl rfl⟩
      · -- Both isotropic: v_{k₁}² + v_{k₂}² ≠ 0
        push_neg at h0k₂
        have hk₁k₂ : B.val k₁ 0 ^ 2 + B.val k₂ 0 ^ 2 ≠ 0 := by
          have hv0_ne : B.val 0 0 ^ 2 ≠ 0 := by
            intro h0; rw [sq, mul_self_eq_zero] at h0
            rw [h0, zero_pow (by norm_num : 2 ≠ 0), zero_add] at h0k₁
            rw [sq, mul_self_eq_zero] at h0k₁; exact hvk₁ h0k₁
          intro h
          have : B.val k₁ 0 ^ 2 + B.val k₂ 0 ^ 2 = -(2 * B.val 0 0 ^ 2) := by
            linear_combination h0k₁ + h0k₂
          rw [this] at h; rw [neg_eq_zero] at h
          rcases mul_eq_zero.mp h with h2 | h0
          · norm_num at h2
          · exact hv0_ne h0
        exact ⟨k₁, k₂, hk₂_ne_k₁.symm, hk₂0, hvk₂, hk₁k₂, Or.inr hvk₁⟩

/-- If A ∈ SO(m+2;ℂ) has first column e₀, then A = embed(B) for some B ∈ SO(m+1;ℂ). -/
private theorem of_first_col_e0 {m : ℕ} (A : SOComplex (m + 2))
    (h : ∀ k : Fin (m + 2), A.val k 0 = if k = 0 then 1 else 0) :
    ∃ B : SOComplex (m + 1), A = embed B := by
  -- First row is also e₀ (from A^T A = 1)
  have hrow : ∀ j : Fin (m + 2), A.val 0 j = if j = 0 then 1 else 0 := by
    intro j
    have h0j := congr_fun (congr_fun A.orthogonal 0) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h0j
    have hsum : ∑ k : Fin (m + 2), A.val k 0 * A.val k j = A.val 0 j := by
      rw [Fin.sum_univ_succ]; simp only [h 0, ↓reduceIte, one_mul]
      have : ∑ x : Fin (m + 1), A.val x.succ 0 * A.val x.succ j = 0 :=
        Finset.sum_eq_zero fun k _ => by simp [h k.succ, Fin.succ_ne_zero]
      rw [this, add_zero]
    rw [hsum] at h0j
    simp_rw [eq_comm (a := (0 : Fin (m + 2)))] at h0j
    exact h0j
  -- Define B as the lower-right submatrix
  refine ⟨{
    val := A.val.submatrix Fin.succ Fin.succ
    orthogonal := by
      ext i j
      have hij := congr_fun (congr_fun A.orthogonal i.succ) j.succ
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
        Fin.succ_inj, Matrix.submatrix] at hij ⊢
      rw [Fin.sum_univ_succ] at hij
      simp only [hrow, Fin.succ_ne_zero, ↓reduceIte, mul_zero, zero_add] at hij
      exact hij
    proper := by
      have hdet' : A.val.det = (A.val.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det := by
        rw [Matrix.det_succ_column A.val 0, Fin.sum_univ_succ]
        simp only [h, ↓reduceIte, Fin.val_zero, pow_zero, one_mul, Fin.succ_ne_zero,
          mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      rw [show A.val.submatrix (Fin.succAbove 0) (Fin.succAbove 0) =
          A.val.submatrix Fin.succ Fin.succ from by
        ext i j; simp [Matrix.submatrix, Fin.succAbove]] at hdet'
      rw [A.proper] at hdet'; exact hdet'.symm
  }, by
    apply ext; ext a b
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · simp [embed, embedVal, h 0]
    · simp [embed, embedVal, hrow j.succ, Fin.succ_ne_zero]
    · simp [embed, embedVal, h i.succ, Fin.succ_ne_zero]
    · simp [embed, embedVal, Matrix.submatrix]
  ⟩

/-- In `SO(m+2;ℂ)`, the first column equals `e₀`. -/
def firstColEqE0 {m : ℕ} (A : SOComplex (m + 2)) : Prop :=
  ∀ k : Fin (m + 2), A.val k 0 = if k = 0 then 1 else 0

/-- In `SO(m+2;ℂ)`, the first column equals a prescribed vector `v`. -/
def firstColEqVec {m : ℕ} (v : Fin (m + 2) → ℂ) (A : SOComplex (m + 2)) : Prop :=
  ∀ k : Fin (m + 2), A.val k 0 = v k

/-- Basepoint-join criterion for preconnectedness. -/
private theorem isPreconnected_of_joinedIn_base
    {X : Type*} [TopologicalSpace X]
    {S : Set X} {x0 : X}
    (hx0 : x0 ∈ S)
    (hjoined : ∀ y ∈ S, JoinedIn S x0 y) :
    IsPreconnected S := by
  let x0S : S := ⟨x0, hx0⟩
  have h_joined_subtype : ∀ y : S, Joined x0S y := by
    intro y
    exact (joinedIn_iff_joined (x_in := hx0) (y_in := y.2)).mp (hjoined y y.2)
  haveI : PathConnectedSpace S := by
    refine PathConnectedSpace.mk ?_ ?_
    · exact ⟨x0S⟩
    · intro x y
      exact (h_joined_subtype x).symm.trans (h_joined_subtype y)
  exact (isPreconnected_iff_preconnectedSpace).2 (inferInstance : PreconnectedSpace S)

/-- **SO(n;ℂ) is path-connected.** -/
theorem isPathConnected (m : ℕ) :
    IsPathConnected (Set.univ : Set (SOComplex m)) := by
  rw [← pathConnectedSpace_iff_univ]
  apply PathConnectedSpace.mk ⟨one⟩
  intro x y
  suffices h : ∀ A : SOComplex m, Joined one A from
    (h x).symm.trans (h y)
  intro A
  -- Induction on m
  induction m with
  | zero =>
    -- SO(0;ℂ) is trivial: only element is the empty matrix
    have : A = one := by apply ext; ext i; exact Fin.elim0 i
    rw [this]
  | succ m ih =>
    -- For SO(m+1;ℂ)
    induction m with
    | zero =>
      -- SO(1;ℂ) is trivial: only the 1×1 identity matrix
      have hdet : A.val = 1 := by
        ext i j; fin_cases i; fin_cases j
        have h := A.proper; rw [Matrix.det_fin_one] at h
        simpa [Matrix.one_apply] using h
      have : A = one := ext hdet
      rw [this]
    | succ m _ =>
      -- SO(m+2;ℂ): column reduction + induction
      obtain ⟨R, hR_joined, hR_col⟩ := column_reduce A
      have hRA := of_first_col_e0 ⟨R.val * A.val, by
        rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc R.val.transpose,
          R.orthogonal, Matrix.one_mul, A.orthogonal], by
        rw [Matrix.det_mul, R.proper, A.proper, mul_one]⟩ hR_col
      obtain ⟨B, hB⟩ := hRA
      -- R * A = embed(B), so A = R⁻¹ * embed(B)
      have hRA_embed : mul R A = embed B := by
        apply ext; exact congr_arg SOComplex.val hB
      have hB_joined : Joined one B := ih B B B
      have hEmbed_joined : Joined one (embed B) := embed_joined hB_joined
      -- A = R⁻¹ * (R * A) = R⁻¹ * embed(B)
      have hA_eq : A = mul (inv R) (embed B) := by
        apply ext
        show A.val = R.val.transpose * (embed B).val
        rw [← congr_arg SOComplex.val hRA_embed]
        show A.val = R.val.transpose * (R.val * A.val)
        rw [← Matrix.mul_assoc, R.orthogonal, Matrix.one_mul]
      rw [hA_eq]
      exact joined_one_mul (joined_one_inv hR_joined) hEmbed_joined

/-- The complex unit quadric `∑ᵢ vᵢ² = 1` is connected. -/
theorem isConnected_unitQuadric {m : ℕ} :
    IsConnected {v : Fin (m + 2) → ℂ | ∑ k : Fin (m + 2), v k ^ 2 = (1 : ℂ)} := by
  let f : SOComplex (m + 2) → (Fin (m + 2) → ℂ) :=
    fun A k => A.val k 0
  have hf_cont : Continuous f := by
    apply continuous_pi
    intro k
    exact (continuous_apply 0).comp ((continuous_apply k).comp SOComplex.continuous_val)
  have hIm_conn : IsConnected (Set.range f) := by
    haveI : PathConnectedSpace (SOComplex (m + 2)) :=
      pathConnectedSpace_iff_univ.mpr (SOComplex.isPathConnected (m + 2))
    simpa [f] using (isConnected_univ.image f hf_cont.continuousOn)
  have hIm_eq : Set.range f = {v : Fin (m + 2) → ℂ | ∑ k : Fin (m + 2), v k ^ 2 = (1 : ℂ)} := by
    ext v
    constructor
    · rintro ⟨A, rfl⟩
      change ∑ k : Fin (m + 2), A.val k 0 ^ 2 = (1 : ℂ)
      calc
        ∑ k : Fin (m + 2), A.val k 0 ^ 2
            = (A.val.transpose * A.val) 0 0 := SOComplex.firstColSqSum_eq_entry00 A.val
        _ = (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) 0 0 := by simp [A.orthogonal]
        _ = (1 : ℂ) := by simp
    · intro hv
      rcases SOComplex.exists_so_with_firstCol (m := m) v hv with ⟨A, hAcol⟩
      exact ⟨A, funext hAcol⟩
  simpa [hIm_eq] using hIm_conn

/-- The subset of `SO(m+2;ℂ)` fixing the first column to `e₀` is connected. -/
theorem isConnected_firstColEqE0_set {m : ℕ} :
    IsConnected {A : SOComplex (m + 2) | firstColEqE0 A} := by
  refine ⟨⟨(one : SOComplex (m + 2)), ?_⟩, ?_⟩
  · intro k
    simp [one, Matrix.one_apply]
  · refine isPreconnected_of_joinedIn_base
      (S := {A : SOComplex (m + 2) | firstColEqE0 A})
      (x0 := (one : SOComplex (m + 2))) ?_ ?_
    · intro k
      simp [one, Matrix.one_apply]
    · intro A hA
      rcases of_first_col_e0 A hA with ⟨B, rfl⟩
      have hB_joinedIn :
          JoinedIn (Set.univ : Set (SOComplex (m + 1))) one B :=
        (isPathConnected (m + 1)).joinedIn one (Set.mem_univ _) B (Set.mem_univ _)
      rcases joinedIn_univ.mp hB_joinedIn with ⟨γ⟩
      refine ⟨
        { toFun := fun t => embed (γ t)
          continuous_toFun := embed_continuous.comp γ.continuous_toFun
          source' := by
            rw [γ.source]
            simpa using (embed_one (m := m + 1))
          target' := by
            rw [γ.target] },
        ?_⟩
      intro t k
      refine Fin.cases ?_ ?_ k
      · show (embed (γ t)).val 0 0 = _
        simp [embed, embedVal]
      · intro i
        show (embed (γ t)).val (Fin.succ i) 0 = _
        simp [embed, embedVal, Fin.succ_ne_zero]

/-- Connectedness of the first-column fiber over any unit-quadric point. -/
theorem isConnected_firstColEqVec_set {m : ℕ}
    (v : Fin (m + 2) → ℂ)
    (hv : ∑ k : Fin (m + 2), v k ^ 2 = (1 : ℂ)) :
    IsConnected {A : SOComplex (m + 2) | firstColEqVec v A} := by
  rcases SOComplex.exists_so_with_firstCol (m := m) v hv with ⟨B, hBcol⟩
  let S0 : Set (SOComplex (m + 2)) := {A | SOComplex.firstColEqE0 A}
  let Sv : Set (SOComplex (m + 2)) := {A | firstColEqVec v A}
  have hS0_conn : IsConnected S0 := by
    simpa [S0] using (SOComplex.isConnected_firstColEqE0_set (m := m))
  let φ : SOComplex (m + 2) → SOComplex (m + 2) := fun A => B * A
  have hφ_cont : Continuous φ := continuous_const.mul continuous_id
  have hφ_map : φ '' S0 = Sv := by
    ext A
    constructor
    · rintro ⟨A0, hA0, rfl⟩
      intro k
      have hA0col : ∀ t : Fin (m + 2), A0.val t 0 = if t = 0 then 1 else 0 := hA0
      calc
        (B * A0).val k 0 = ∑ j : Fin (m + 2), B.val k j * A0.val j 0 := by
            change ((B.val * A0.val) k 0) = _
            rw [Matrix.mul_apply]
        _ = B.val k 0 := by
            rw [Finset.sum_eq_single 0]
            · simp [hA0col]
            · intro j _ hj
              simp [hA0col, hj]
            · simp [hA0col]
        _ = v k := hBcol k
    · intro hA
      refine ⟨B⁻¹ * A, ?_, ?_⟩
      · intro k
        have hmulkM : (B⁻¹ * B).val = (1 : SOComplex (m + 2)).val := by
          exact congrArg SOComplex.val (inv_mul_cancel B)
        have hmulk : ((B⁻¹).val * B.val) k 0 = ((1 : SOComplex (m + 2)).val) k 0 := by
          exact congrArg (fun M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ => M k 0) hmulkM
        calc
          (B⁻¹ * A).val k 0 = ∑ j : Fin (m + 2), (B⁻¹).val k j * A.val j 0 := by
              change (((B⁻¹).val * A.val) k 0) = _
              rw [Matrix.mul_apply]
          _ = ∑ j : Fin (m + 2), (B⁻¹).val k j * B.val j 0 := by
              apply Finset.sum_congr rfl
              intro j _
              simp [hA j, hBcol j]
          _ = ((B⁻¹).val * B.val) k 0 := by
              rw [Matrix.mul_apply]
          _ = ((1 : SOComplex (m + 2)).val) k 0 := hmulk
          _ = if k = 0 then 1 else 0 := by
              change ((1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) k 0) = _
              simp [Matrix.one_apply]
      · calc
          B * (B⁻¹ * A) = (B * B⁻¹) * A := by exact (mul_assoc B B⁻¹ A).symm
          _ = A := by simp
  have hSv_conn : IsConnected Sv := by
    have hIm_conn : IsConnected (φ '' S0) := hS0_conn.image φ hφ_cont.continuousOn
    simpa [hφ_map] using hIm_conn
  simpa [Sv] using hSv_conn

end SOComplex

end
