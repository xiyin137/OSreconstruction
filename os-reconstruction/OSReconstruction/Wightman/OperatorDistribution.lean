/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Init
import OSReconstruction.Wightman.Spacetime.Metric
import OSReconstruction.Wightman.Groups.Lorentz
import OSReconstruction.Wightman.Groups.Poincare
import OSReconstruction.vNA.Unbounded.StoneTheorem
































noncomputable section

open scoped SchwartzMap InnerProductSpace
open Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (d : ℕ) [NeZero d]



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

/-- The n-fold application of field operators: φ(f₁)φ(f₂)···φ(fₙ)ψ
    Applied right-to-left: φ(fₙ) is applied first, then φ(fₙ₋₁), ..., then φ(f₁). -/
def operatorPow (φ : OperatorValuedDistribution d H) :
    (n : ℕ) → (Fin n → SchwartzSpacetime d) → H → H
  | 0, _, ψ => ψ
  | n + 1, fs, ψ =>
    let ψ' := operatorPow φ n (fun i => fs (Fin.succ i)) ψ
    φ.operator (fs 0) ψ'

/-- The algebraic span of vectors φ(f₁)···φ(fₙ)Ω -/
def algebraicSpan (φ : OperatorValuedDistribution d H) (Ω : H) : Submodule ℂ H :=
  Submodule.span ℂ { ψ | ∃ (n : ℕ) (fs : Fin n → SchwartzSpacetime d), ψ = φ.operatorPow n fs Ω }

end OperatorValuedDistribution



namespace WightmanNPoint

variable {d : ℕ} [NeZero d]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end WightmanNPoint



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



/-- The momentum operator in direction `μ`, defined as the Stone generator of
    the strongly continuous translation subgroup `t ↦ U(t e_μ)`. -/
noncomputable def momentumOp (π : PoincareRepresentation d H) (μ : Fin (d + 1))
    (hcont : translationContinuousInDirection π μ) : UnboundedOperator H :=
  (π.translationGroup μ hcont).generator

end PoincareRepresentation

end
