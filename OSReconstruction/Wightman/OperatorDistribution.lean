/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import OSReconstruction.Wightman.Basic
import OSReconstruction.vNA.Unbounded.StoneTheorem

/-!
# Operator-Valued Distributions

This file provides a rigorous mathematical foundation for operator-valued distributions
(OVDs), which are essential for the Wightman formulation of quantum field theory.

## Main Definitions

* `OperatorValuedDistribution` - A map from Schwartz test functions to (possibly unbounded)
  operators on a Hilbert space, satisfying appropriate continuity and linearity properties.
* `OperatorValuedDistribution.isHermitian` - Property that φ(f)* = φ(f̄) for real f
* `OperatorValuedDistribution.domain` - The common domain for all φ(f)

## Mathematical Background

In the Wightman framework, quantum fields are operator-valued distributions. A field φ
is not a pointwise operator φ(x), but rather assigns to each test function f ∈ 𝒮(ℝ^d)
an operator φ(f) on the Hilbert space of states.

The key requirements are:
1. **Linearity**: f ↦ φ(f) is linear
2. **Domain**: There exists a dense domain D ⊂ H such that φ(f)D ⊂ D for all f
3. **Continuity**: For each ψ, χ ∈ D, the map f ↦ ⟨χ, φ(f)ψ⟩ is a tempered distribution

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 3
* Reed-Simon, "Methods of Modern Mathematical Physics II", Chapter X
* Wightman-Gårding, "Fields as operator-valued distributions"
-/

noncomputable section

open scoped SchwartzMap InnerProductSpace
open Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (d : ℕ) [NeZero d]

/-! ### Basic definitions for operator-valued distributions -/

/-- The spacetime dimension type for Schwartz functions.
    For d spatial dimensions, spacetime is ℝ^{d+1}. -/
abbrev SpacetimeDim (d : ℕ) := Fin (d + 1) → ℝ

/-- Schwartz space on d+1 dimensional spacetime with complex values -/
abbrev SchwartzSpacetime (d : ℕ) := SchwartzMap (SpacetimeDim d) ℂ

/-- A dense subspace of a Hilbert space, used as the domain for field operators.
    We use a Submodule with an additional density hypothesis. -/
structure DenseSubspace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The underlying submodule -/
  toSubmodule : Submodule ℂ H
  /-- Density: the closure equals the whole space -/
  dense : Dense (toSubmodule : Set H)

namespace DenseSubspace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Membership: x ∈ D means x is in the underlying submodule -/
instance instMembership : Membership H (DenseSubspace H) where
  mem := fun (D : DenseSubspace H) (x : H) => x ∈ D.toSubmodule

/-- The zero vector is in any dense subspace -/
theorem zero_mem (D : DenseSubspace H) : (0 : H) ∈ D :=
  Submodule.zero_mem D.toSubmodule

/-- Addition is closed -/
theorem add_mem (D : DenseSubspace H) {x y : H} (hx : x ∈ D) (hy : y ∈ D) : x + y ∈ D :=
  Submodule.add_mem D.toSubmodule hx hy

/-- Scalar multiplication is closed -/
theorem smul_mem (D : DenseSubspace H) {x : H} (hx : x ∈ D) (c : ℂ) : c • x ∈ D :=
  Submodule.smul_mem D.toSubmodule c hx

end DenseSubspace

/-- An operator-valued distribution is a map from Schwartz test functions to
    operators on a Hilbert space, with a common dense domain.

    The key property distinguishing this from arbitrary operator-valued maps is
    the continuity requirement: for any χ, ψ in the domain, the matrix element
    f ↦ ⟨χ, φ(f)ψ⟩ must be a tempered distribution (continuous linear functional
    on the Schwartz space). -/
structure OperatorValuedDistribution (d : ℕ) [NeZero d]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The common dense domain for all field operators -/
  domain : DenseSubspace H
  /-- The field operator applied to a test function f -/
  operator : SchwartzSpacetime d → (H → H)
  /-- Linearity of the field in test function: φ(f + g) = φ(f) + φ(g) -/
  operator_add : ∀ f g : SchwartzSpacetime d, ∀ ψ ∈ domain,
    operator (f + g) ψ = operator f ψ + operator g ψ
  /-- Scalar linearity in test function: φ(c·f) = c·φ(f) -/
  operator_smul : ∀ (c : ℂ) (f : SchwartzSpacetime d), ∀ ψ ∈ domain,
    operator (c • f) ψ = c • operator f ψ
  /-- Linearity of φ(f) in vector argument: φ(f)(ψ₁ + ψ₂) = φ(f)ψ₁ + φ(f)ψ₂ -/
  operator_vector_add : ∀ f : SchwartzSpacetime d, ∀ ψ₁ ψ₂ : H,
    ψ₁ ∈ domain → ψ₂ ∈ domain → operator f (ψ₁ + ψ₂) = operator f ψ₁ + operator f ψ₂
  /-- Scalar linearity of φ(f) in vector argument: φ(f)(c·ψ) = c·φ(f)ψ -/
  operator_vector_smul : ∀ f : SchwartzSpacetime d, ∀ (c : ℂ) (ψ : H),
    ψ ∈ domain → operator f (c • ψ) = c • operator f ψ
  /-- Domain invariance: φ(f) maps D to D -/
  operator_domain : ∀ f : SchwartzSpacetime d, ∀ ψ ∈ domain, operator f ψ ∈ domain
  /-- Temperedness: for any χ, ψ ∈ D, the matrix element f ↦ ⟨χ, φ(f)ψ⟩ is continuous.
      This makes f ↦ ⟨χ, φ(f)ψ⟩ a tempered distribution on 𝒮(ℝ^{d+1}). -/
  matrix_element_continuous : ∀ χ ψ : H, χ ∈ domain → ψ ∈ domain →
    Continuous (fun f : SchwartzSpacetime d => ⟪χ, operator f ψ⟫_ℂ)

namespace OperatorValuedDistribution

variable {d : ℕ} [NeZero d]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The matrix element ⟨χ, φ(f)ψ⟩ as a function of f -/
def matrixElement (φ : OperatorValuedDistribution d H)
    (χ ψ : H) (_hχ : χ ∈ φ.domain) (_hψ : ψ ∈ φ.domain) :
    SchwartzSpacetime d → ℂ :=
  fun f => ⟪χ, φ.operator f ψ⟫_ℂ

/-- A field is hermitian (self-adjoint) if ⟨φ(f)χ, ψ⟩ = ⟨χ, φ(f̄)ψ⟩.
    Here f̄ denotes pointwise complex conjugation of the test function.
    For real-valued test functions, this implies φ(f) is symmetric. -/
def IsHermitian (φ : OperatorValuedDistribution d H)
    (conj : SchwartzSpacetime d → SchwartzSpacetime d) : Prop :=
  ∀ (f : SchwartzSpacetime d) (χ ψ : H),
    χ ∈ φ.domain → ψ ∈ φ.domain →
    ⟪φ.operator f χ, ψ⟫_ℂ = ⟪χ, φ.operator (conj f) ψ⟫_ℂ

/-- The n-fold application of field operators: φ(f₁)φ(f₂)···φ(fₙ)ψ
    Applied right-to-left: φ(fₙ) is applied first, then φ(fₙ₋₁), ..., then φ(f₁). -/
def operatorPow (φ : OperatorValuedDistribution d H) :
    (n : ℕ) → (Fin n → SchwartzSpacetime d) → H → H
  | 0, _, ψ => ψ
  | n + 1, fs, ψ =>
    let ψ' := operatorPow φ n (fun i => fs (Fin.succ i)) ψ
    φ.operator (fs 0) ψ'

/-- The n-fold application preserves the domain -/
theorem operatorPow_domain (φ : OperatorValuedDistribution d H)
    (n : ℕ) (fs : Fin n → SchwartzSpacetime d) (ψ : H) (hψ : ψ ∈ φ.domain) :
    φ.operatorPow n fs ψ ∈ φ.domain := by
  induction n with
  | zero => exact hψ
  | succ n ih =>
    simp only [operatorPow]
    exact φ.operator_domain _ _ (ih _)

/-- The algebraic span of vectors φ(f₁)···φ(fₙ)Ω -/
def algebraicSpan (φ : OperatorValuedDistribution d H) (Ω : H) : Submodule ℂ H :=
  Submodule.span ℂ { ψ | ∃ (n : ℕ) (fs : Fin n → SchwartzSpacetime d), ψ = φ.operatorPow n fs Ω }

end OperatorValuedDistribution

/-! ### Wightman n-point functions -/

/-- The Wightman n-point function W_n(f₁, ..., fₙ) = ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩.
    This is the vacuum expectation value of the product of smeared fields. -/
def WightmanNPoint (φ : OperatorValuedDistribution d H)
    (Ω : H) (n : ℕ) : (Fin n → SchwartzSpacetime d) → ℂ :=
  fun fs => ⟪Ω, φ.operatorPow n fs Ω⟫_ℂ

/-- The 2-point Wightman function (propagator) -/
def Wightman2Point (φ : OperatorValuedDistribution d H)
    (Ω : H) : SchwartzSpacetime d → SchwartzSpacetime d → ℂ :=
  fun f g => WightmanNPoint d φ Ω 2 ![f, g]

namespace WightmanNPoint

variable {d : ℕ} [NeZero d]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The 0-point function is 1 (assuming Ω is normalized).
    W_0 = ⟨Ω, Ω⟩ = ‖Ω‖² = 1 -/
theorem zero_point (d : ℕ) [NeZero d] (φ : OperatorValuedDistribution d H)
    (Ω : H) (hΩ_norm : ‖Ω‖ = 1) :
    _root_.WightmanNPoint d φ Ω 0 (fun _ => 0) = 1 := by
  simp only [WightmanNPoint]
  -- operatorPow 0 fs Ω = Ω by definition
  simp only [OperatorValuedDistribution.operatorPow]
  -- Now ⟨Ω, Ω⟩ = ‖Ω‖² = 1
  rw [inner_self_eq_norm_sq_to_K, hΩ_norm]
  simp

/-- Linearity of operatorPow in the k-th test function.
    This helper lemma shows that replacing fs(k) with f+g gives the sum of the two applications. -/
theorem operatorPow_linear_at (φ : OperatorValuedDistribution d H)
    (n : ℕ) (k : Fin n) (f g : SchwartzSpacetime d) (fs : Fin n → SchwartzSpacetime d)
    (ψ : H) (hψ : ψ ∈ φ.domain) :
    φ.operatorPow n (Function.update fs k (f + g)) ψ =
    φ.operatorPow n (Function.update fs k f) ψ + φ.operatorPow n (Function.update fs k g) ψ := by
  -- Induction on n
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    -- For n+1, operatorPow applies operator at fs(0) to the result of operatorPow n on the tail
    simp only [OperatorValuedDistribution.operatorPow]
    -- Case split on whether k = 0 or k > 0
    by_cases hk : k.val = 0
    · -- k = 0: the first operator gets (f + g)
      have hk0 : k = 0 := Fin.ext hk
      subst hk0
      -- For any h, (fun i => update fs 0 h (succ i)) = (fun i => fs (succ i))
      -- because succ i ≠ 0
      have htail_eq : ∀ h : SchwartzSpacetime d,
          (fun i => Function.update fs 0 h (Fin.succ i)) = (fun i => fs (Fin.succ i)) := by
        intro h
        ext i
        rw [Function.update_of_ne (Fin.succ_ne_zero i)]
      simp only [Function.update_self, htail_eq]
      -- Apply operator_add
      have h_domain := OperatorValuedDistribution.operatorPow_domain φ n
        (fun i => fs (Fin.succ i)) ψ hψ
      rw [φ.operator_add f g _ h_domain]
    · -- k > 0: the first operator is unchanged, linearity is in the tail
      have hk_pos : 0 < k.val := Nat.pos_of_ne_zero hk
      have hk_pred : k.val - 1 < n := by omega
      let k' : Fin n := ⟨k.val - 1, hk_pred⟩
      -- Function.update at k ≠ 0 doesn't change fs(0)
      have h0_ne : k ≠ 0 := fun h => hk (congrArg Fin.val h)
      simp only [Function.update_of_ne h0_ne.symm]
      -- Need to show the tail updates are correct
      have htail : ∀ h : SchwartzSpacetime d,
          (fun i => Function.update fs k h (Fin.succ i)) = Function.update (fun i => fs (Fin.succ i)) k' h := by
        intro h
        ext i
        simp only [Function.update]
        by_cases hi : i = k'
        · simp only [hi]
          have : Fin.succ k' = k := by
            ext
            simp only [Fin.val_succ, k']
            omega
          simp [this]
        · simp only [hi]
          have : Fin.succ i ≠ k := by
            intro heq
            apply hi
            ext
            simp only [k']
            have := congrArg Fin.val heq
            simp only [Fin.val_succ] at this
            omega
          simp [this]
      rw [htail (f + g), htail f, htail g]
      -- Now use the induction hypothesis
      rw [ih k' (fun i => fs (Fin.succ i))]
      -- The result is φ.operator (fs 0) applied to a sum, which distributes
      -- using operator_vector_add
      have h1 : φ.operatorPow n (Function.update (fun i => fs (Fin.succ i)) k' f) ψ ∈ φ.domain :=
        OperatorValuedDistribution.operatorPow_domain φ n _ ψ hψ
      have h2 : φ.operatorPow n (Function.update (fun i => fs (Fin.succ i)) k' g) ψ ∈ φ.domain :=
        OperatorValuedDistribution.operatorPow_domain φ n _ ψ hψ
      rw [φ.operator_vector_add (fs 0) _ _ h1 h2]

/-- Linearity in an argument: W_n is linear in each test function slot.
    The full proof requires careful handling of Fin indices. -/
theorem linear_arg (d : ℕ) [NeZero d] (φ : OperatorValuedDistribution d H)
    (Ω : H) (hΩ : Ω ∈ φ.domain) (n : ℕ) (k : Fin n)
    (f g : SchwartzSpacetime d) (fs : Fin n → SchwartzSpacetime d) :
    _root_.WightmanNPoint d φ Ω n (Function.update fs k (f + g)) =
    _root_.WightmanNPoint d φ Ω n (Function.update fs k f) +
    _root_.WightmanNPoint d φ Ω n (Function.update fs k g) := by
  simp only [WightmanNPoint]
  rw [operatorPow_linear_at φ n k f g fs Ω hΩ]
  rw [inner_add_right]

end WightmanNPoint

/-! ### Covariance under Poincaré transformations -/

/-- A unitary representation of the Poincaré group on the Hilbert space -/
structure PoincareRepresentation (d : ℕ) [NeZero d]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The representation map -/
  U : PoincareGroup d → (H →L[ℂ] H)
  /-- Unitarity: U(g)* U(g) = 1 -/
  unitary : ∀ g, (U g).adjoint.comp (U g) = ContinuousLinearMap.id ℂ H
  /-- Group homomorphism property -/
  mul_map : ∀ g₁ g₂, U (g₁ * g₂) = (U g₁).comp (U g₂)
  /-- Identity maps to identity -/
  one_map : U 1 = ContinuousLinearMap.id ℂ H

namespace PoincareRepresentation

variable {d : ℕ} [NeZero d]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The standard basis vector e_μ in ℝ^{d+1} -/
def basisVector (d : ℕ) [NeZero d] (μ : Fin (d + 1)) : MinkowskiSpace d :=
  fun ν => if ν = μ then 1 else 0

/-- The pure translation by t · e_μ in the Poincaré group -/
def translationInDirection (d : ℕ) [NeZero d] (μ : Fin (d + 1)) (t : ℝ) : PoincareGroup d :=
  PoincareGroup.translation' (t • basisVector d μ)

/-- Strong continuity of the translation subgroup in the `μ`-th direction. -/
def translationContinuousInDirection (π : PoincareRepresentation d H) (μ : Fin (d + 1)) : Prop :=
  ∀ x : H, Continuous fun t => π.U (translationInDirection d μ t) x

/-- Strong continuity of all one-parameter translation subgroups. -/
def translationStronglyContinuous (π : PoincareRepresentation d H) : Prop :=
  ∀ μ : Fin (d + 1), translationContinuousInDirection π μ

/-- The generator of translations in direction μ, applied to ψ.

    The momentum operator P_μ is defined as the infinitesimal generator of the
    translation subgroup in direction μ. Concretely:
      i P_μ ψ = lim_{t→0} (U(t·e_μ, 1) - 1) ψ / t

    This definition gives a partial function - the limit exists only for vectors
    in the domain of the generator. By Stone's theorem (not formalized here),
    when the representation is strongly continuous, P_μ is self-adjoint.

    We use Filter.Tendsto to express the limit rigorously. -/
def momentumApplied (π : PoincareRepresentation d H) (μ : Fin (d + 1)) (ψ : H) : H :=
  limUnder (𝓝[≠] (0 : ℝ)) (fun t : ℝ =>
    (Complex.I : ℂ)⁻¹ • (t⁻¹ • (π.U (translationInDirection d μ t) ψ - ψ)))

/-- The energy-momentum operators (generators of translations).

    P_μ is the infinitesimal generator of translations in the μ-th direction:
      U(t·e_μ, 1) = exp(-i t P_μ)   (by Stone's theorem)

    The limit defining this operator may not exist for all ψ ∈ H. The domain
    of P_μ consists of those ψ for which the limit exists. -/
def momentum (π : PoincareRepresentation d H) (μ : Fin (d + 1)) : H → H :=
  momentumApplied π μ

/-- A vector ψ is in the domain of the momentum operator P_μ if the limit defining
    P_μ ψ exists. -/
def inMomentumDomain (π : PoincareRepresentation d H) (μ : Fin (d + 1)) (ψ : H) : Prop :=
  Filter.Tendsto (fun t : ℝ =>
    (Complex.I : ℂ)⁻¹ • (t⁻¹ • (π.U (translationInDirection d μ t) ψ - ψ)))
    (𝓝[≠] 0) (nhds (momentumApplied π μ ψ))

/-- The Hamiltonian H = P₀ (time component of momentum) -/
def hamiltonian (π : PoincareRepresentation d H) : H → H :=
  π.momentum 0

/-- The spatial momentum operators (P₁, ..., P_d) -/
def spatialMomentum (π : PoincareRepresentation d H) (i : Fin d) : H → H :=
  π.momentum (Fin.succ i)

/-! ### Connection to Stone's theorem -/

/-- A Poincaré representation gives rise to a one-parameter unitary group
    for translations in each direction μ.

    The translation group t ↦ U(t·e_μ, 1) is a one-parameter group:
    - U(0) = 1
    - U(s+t) = U(s)·U(t)
    - Each U(t) is unitary

    By Stone's theorem, this group has a self-adjoint generator P_μ with
    U(t·e_μ) = exp(itP_μ). This P_μ is the momentum operator.

    Note: Strong continuity must be verified separately - it follows from
    the physical requirement that translations act continuously on states. -/
def translationGroup (π : PoincareRepresentation d H)
    (μ : Fin (d + 1)) (stronglyContinuous : translationContinuousInDirection π μ) :
    OneParameterUnitaryGroup H where
  U := fun t => π.U (translationInDirection d μ t)
  unitary_left := fun t => by
    have h := π.unitary (translationInDirection d μ t)
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h ⊢
    have := congrFun (congrArg DFunLike.coe h) x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    exact this
  unitary_right := fun t => by
    -- U(t) is unitary, so U(t)·U(t)* = 1
    -- This follows from U(t)*·U(t) = 1 and the fact that U(t) is invertible
    -- For a unitary operator, we have U* = U⁻¹, so U·U* = U·U⁻¹ = 1
    let g := translationInDirection d μ t
    have hunit := π.unitary g
    -- hunit : U(g)*.comp U(g) = id
    -- The inverse of g in the Poincaré group
    have hg_inv : g⁻¹ = translationInDirection d μ (-t) := by
      ext
      · -- translation component: g⁻¹.translation = -mulVec g.lorentz⁻¹.val g.translation
        simp only [PoincareGroup.inv_translation, translationInDirection,
          PoincareGroup.translation', g]
        simp only [inv_one, PoincareGroup.one_lorentz_val, Matrix.one_mulVec, neg_smul]
      · -- lorentz component
        simp only [PoincareGroup.inv_lorentz, translationInDirection, PoincareGroup.translation', g]
        simp only [inv_one]
    -- U(g) · U(g⁻¹) = U(g · g⁻¹) = U(1) = 1
    have hU_right_inv : (π.U g).comp (π.U g⁻¹) = ContinuousLinearMap.id ℂ H := by
      rw [← π.mul_map g g⁻¹, mul_inv_cancel, π.one_map]
    -- U(g⁻¹) · U(g) = U(g⁻¹ · g) = U(1) = 1
    have hU_left_inv : (π.U g⁻¹).comp (π.U g) = ContinuousLinearMap.id ℂ H := by
      rw [← π.mul_map g⁻¹ g, inv_mul_cancel, π.one_map]
    -- From hunit: U(g)* is a left inverse of U(g)
    -- From hU_left_inv: U(g⁻¹) is a left inverse of U(g)
    -- Both are left inverses, and U(g) has a right inverse U(g⁻¹)
    -- So U(g)* = U(g⁻¹) (left inverses equal when right inverse exists)
    have hadj_eq_inv : (π.U g).adjoint = π.U g⁻¹ := by
      -- If AB = 1 and CB = 1, and BD = 1, then A = ABD = D and C = CBD = D, so A = C
      -- Here: A = U(g)*, B = U(g), C = U(g⁻¹), D = U(g⁻¹)
      -- We have: U(g)* ∘ U(g) = 1 (hunit)
      -- And: U(g⁻¹) ∘ U(g) = 1 (hU_left_inv)
      -- And: U(g) ∘ U(g⁻¹) = 1 (hU_right_inv)
      -- So U(g)* = U(g)* ∘ (U(g) ∘ U(g⁻¹)) = (U(g)* ∘ U(g)) ∘ U(g⁻¹) = 1 ∘ U(g⁻¹) = U(g⁻¹)
      calc (π.U g).adjoint
          = (π.U g).adjoint.comp (ContinuousLinearMap.id ℂ H) := by rw [ContinuousLinearMap.comp_id]
        _ = (π.U g).adjoint.comp ((π.U g).comp (π.U g⁻¹)) := by rw [hU_right_inv]
        _ = ((π.U g).adjoint.comp (π.U g)).comp (π.U g⁻¹) := by rw [ContinuousLinearMap.comp_assoc]
        _ = (ContinuousLinearMap.id ℂ H).comp (π.U g⁻¹) := by rw [hunit]
        _ = π.U g⁻¹ := ContinuousLinearMap.id_comp _
    -- Now: U(g) ∘ U(g)* = U(g) ∘ U(g⁻¹) = 1
    rw [hadj_eq_inv]
    exact hU_right_inv
  zero := by
    have h : translationInDirection d μ 0 = 1 := by
      ext <;> simp [translationInDirection, PoincareGroup.translation']
    rw [h, π.one_map]
    rfl
  add := fun s t => by
    have hmul : translationInDirection d μ (s + t) =
        translationInDirection d μ s * translationInDirection d μ t := by
      ext
      · -- translation component
        simp only [translationInDirection, PoincareGroup.translation',
          PoincareGroup.mul_translation, PoincareGroup.one_lorentz_val, Matrix.one_mulVec]
        rw [add_smul]
      · -- lorentz component
        simp only [translationInDirection, PoincareGroup.translation',
          PoincareGroup.mul_lorentz, mul_one]
    rw [hmul, π.mul_map]
  continuous := stronglyContinuous

/-- The momentum operator P_μ from Stone's theorem equals our definition.

    When the translation group is strongly continuous, Stone's theorem provides
    a self-adjoint generator A. We show that A equals the momentum operator P_μ
    defined by the limit formula.

    The key insight is that both definitions use the same limit:
    - momentumApplied uses `limUnder (nhds 0) (fun t => I⁻¹ • t⁻¹ • (U(t)ψ - ψ))`
    - generatorApply uses `Classical.choose` of the same limit existence

    By uniqueness of limits in Hausdorff spaces (Hilbert spaces are T2),
    these must agree when the limit exists. -/
theorem momentum_eq_generator (π : PoincareRepresentation d H) (μ : Fin (d + 1))
    (hcont : translationContinuousInDirection π μ)
    (ψ : H) (hψ : ψ ∈ (π.translationGroup μ hcont).generatorDomain) :
    π.momentumApplied μ ψ = (π.translationGroup μ hcont).generatorApply ψ hψ := by
  -- Both are limits of the same function on 𝓝[≠] 0; by uniqueness of limits (T2), they agree.
  have hspec := (π.translationGroup μ hcont).generatorApply_spec ψ hψ
  -- Rewrite goal to use translationGroup.U instead of π.U (translationInDirection ...)
  change limUnder (𝓝[≠] (0 : ℝ)) (fun t =>
    (Complex.I : ℂ)⁻¹ • (t⁻¹ • ((π.translationGroup μ hcont).U t ψ - ψ))) = _
  exact hspec.limUnder_eq

/-! ### Stone-theorem momentum operators -/

/-- The momentum operator in direction `μ`, defined as the Stone generator of
    the strongly continuous translation subgroup `t ↦ U(t e_μ)`. -/
noncomputable def momentumOp (π : PoincareRepresentation d H) (μ : Fin (d + 1))
    (hcont : translationContinuousInDirection π μ) : UnboundedOperator H :=
  (π.translationGroup μ hcont).generator

/-- The Hamiltonian `P₀`, defined as the Stone generator of time translations. -/
noncomputable def hamiltonianOp (π : PoincareRepresentation d H)
    (hcont : translationContinuousInDirection π 0) : UnboundedOperator H :=
  π.momentumOp 0 hcont

/-- The spatial momentum operator `Pᵢ`, defined as the Stone generator of
    translations in the `i`-th spatial direction. -/
noncomputable def spatialMomentumOp (π : PoincareRepresentation d H) (i : Fin d)
    (hcont : translationContinuousInDirection π (Fin.succ i)) : UnboundedOperator H :=
  π.momentumOp (Fin.succ i) hcont

/-- The Stone-defined momentum operator is densely defined. -/
theorem momentumOp_denselyDefined (π : PoincareRepresentation d H) (μ : Fin (d + 1))
    (hcont : translationContinuousInDirection π μ) :
    (π.momentumOp μ hcont).IsDenselyDefined :=
  (π.translationGroup μ hcont).generator_densely_defined

/-- The Stone-defined momentum operator is self-adjoint. -/
theorem momentumOp_selfAdjoint (π : PoincareRepresentation d H) (μ : Fin (d + 1))
    (hcont : translationContinuousInDirection π μ) :
    (π.momentumOp μ hcont).IsSelfAdjoint (π.momentumOp_denselyDefined μ hcont) :=
  (π.translationGroup μ hcont).generator_selfadjoint

/-- The Stone-defined Hamiltonian is densely defined. -/
theorem hamiltonianOp_denselyDefined (π : PoincareRepresentation d H)
    (hcont : translationContinuousInDirection π 0) :
    (π.hamiltonianOp hcont).IsDenselyDefined :=
  π.momentumOp_denselyDefined 0 hcont

/-- The Stone-defined Hamiltonian is self-adjoint. -/
theorem hamiltonianOp_selfAdjoint (π : PoincareRepresentation d H)
    (hcont : translationContinuousInDirection π 0) :
    (π.hamiltonianOp hcont).IsSelfAdjoint (π.hamiltonianOp_denselyDefined hcont) :=
  π.momentumOp_selfAdjoint 0 hcont

/-- The Stone-defined spatial momentum operator is densely defined. -/
theorem spatialMomentumOp_denselyDefined (π : PoincareRepresentation d H) (i : Fin d)
    (hcont : translationContinuousInDirection π (Fin.succ i)) :
    (π.spatialMomentumOp i hcont).IsDenselyDefined :=
  π.momentumOp_denselyDefined (Fin.succ i) hcont

/-- The Stone-defined spatial momentum operator is self-adjoint. -/
theorem spatialMomentumOp_selfAdjoint (π : PoincareRepresentation d H) (i : Fin d)
    (hcont : translationContinuousInDirection π (Fin.succ i)) :
    (π.spatialMomentumOp i hcont).IsSelfAdjoint
      (π.spatialMomentumOp_denselyDefined i hcont) :=
  π.momentumOp_selfAdjoint (Fin.succ i) hcont

/-- On vectors lying in the Stone generator domain, the legacy `momentumApplied`
    coincides with the Stone-defined momentum operator. -/
theorem momentumApplied_eq_momentumOp (π : PoincareRepresentation d H) (μ : Fin (d + 1))
    (hcont : translationContinuousInDirection π μ)
    (ψ : H) (hψ : ψ ∈ (π.translationGroup μ hcont).generatorDomain) :
    π.momentumApplied μ ψ = π.momentumOp μ hcont ⟨ψ, by
      change ψ ∈ ((π.translationGroup μ hcont).generatorDomainSubmodule : Set H)
      rw [(π.translationGroup μ hcont).generatorDomainSubmodule_carrier]
      exact hψ⟩ := by
  simpa [momentumOp] using π.momentum_eq_generator μ hcont ψ hψ

end PoincareRepresentation

/-- The action of a Poincaré transformation on a test function as a plain function.
    (g · f)(x) = f(g⁻¹ · x) where g · x = Λx + a.

    The Schwartz class is preserved under Poincaré transformations (linear transformations
    preserve rapid decrease), but proving this requires substantial analysis machinery. -/
def poincareActionOnTestFun (g : PoincareGroup d) (f : SpacetimeDim d → ℂ) :
    SpacetimeDim d → ℂ :=
  fun x => f (PoincareGroup.act g⁻¹ x)

/-- Covariance of a field under Poincaré transformations (weak form).

    For scalar fields, the covariance condition is:
      U(g) φ(f) U(g)⁻¹ = φ(g · f)
    where (g · f)(x) = f(g⁻¹ · x).

    This weak formulation expresses covariance at the level of the underlying
    functions, avoiding the need to prove that Poincaré action preserves
    the Schwartz class (which it does, but requires more analysis infrastructure). -/
def IsCovariantWeak (φ : OperatorValuedDistribution d H)
    (π : PoincareRepresentation d H)
    (poincareActionOnSchwartz : PoincareGroup d → SchwartzSpacetime d → SchwartzSpacetime d)
    : Prop :=
  ∀ (g : PoincareGroup d) (f : SchwartzSpacetime d) (χ ψ : H)
    (_hχ : χ ∈ φ.domain) (_hψ : ψ ∈ φ.domain),
    ⟪π.U g χ, φ.operator f (π.U g ψ)⟫_ℂ =
    ⟪χ, φ.operator (poincareActionOnSchwartz g f) ψ⟫_ℂ

end
