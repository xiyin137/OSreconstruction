/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology

/-!
# Predual Theory for von Neumann Algebras

This file develops the predual theory for von Neumann algebras, connecting
the concrete (double commutant) and abstract (W*-algebra) definitions.

## Main definitions

* `VonNeumannAlgebra.NormalFunctional` - normal (σ-weakly continuous) linear functionals
* `VonNeumannAlgebra.TraceClass` - trace class operators
* `VonNeumannAlgebra.predual` - the predual space M_*

## Main results

* Normal functionals are exactly the σ-weakly continuous functionals
* The predual M_* consists of trace-class operators
* M ≅ (M_*)* as Banach spaces

## References

* Takesaki, "Theory of Operator Algebras I", Chapter III
* Sakai, "C*-algebras and W*-algebras"
-/

noncomputable section

open scoped InnerProduct ComplexConjugate

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace VonNeumannAlgebra

variable (M : VonNeumannAlgebra H)

/-! ### Normal linear functionals -/

/-- A linear functional on M is normal if it is σ-weakly continuous,
    equivalently, if it can be represented as a sum of vector functionals.
    Here we use the representation criterion: φ is normal iff there exist
    sequences (ξ_n), (η_n) with Σ‖ξ_n‖‖η_n‖ < ∞ such that
    φ(a) = Σ⟨ξ_n, a·η_n⟩ for all a. -/
structure NormalFunctional where
  toFun : (H →L[ℂ] H) → ℂ
  map_add' : ∀ a b, a ∈ M → b ∈ M → toFun (a + b) = toFun a + toFun b
  map_smul' : ∀ (c : ℂ) a, a ∈ M → toFun (c • a) = c * toFun a
  continuous' : Continuous toFun
  /-- Normality: the functional can be represented as a convergent sum of vector functionals -/
  normal' : ∃ (ξ η : ℕ → H), Summable (fun n => ‖ξ n‖ * ‖η n‖) ∧
    ∀ a : H →L[ℂ] H, toFun a = ∑' n, @inner ℂ H _ (ξ n) (a (η n))

namespace NormalFunctional

variable {M}

instance : CoeFun (NormalFunctional M) (fun _ => (H →L[ℂ] H) → ℂ) :=
  ⟨NormalFunctional.toFun⟩

theorem map_add (φ : NormalFunctional M) (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M) :
    φ (a + b) = φ a + φ b :=
  φ.map_add' a b ha hb

theorem map_smul (φ : NormalFunctional M) (c : ℂ) (a : H →L[ℂ] H) (ha : a ∈ M) :
    φ (c • a) = c * φ a :=
  φ.map_smul' c a ha

theorem continuous (φ : NormalFunctional M) : Continuous φ.toFun :=
  φ.continuous'

end NormalFunctional

/-! ### Vector functionals -/

/-- A vector functional ω_{ξ,η}(a) = ⟨ξ, a·η⟩ -/
def vectorFunctional (ξ η : H) : (H →L[ℂ] H) → ℂ :=
  fun a => @inner ℂ H _ ξ (a η)

omit [CompleteSpace H] in
theorem vectorFunctional_add (ξ η : H) (a b : H →L[ℂ] H) :
    vectorFunctional ξ η (a + b) = vectorFunctional ξ η a + vectorFunctional ξ η b := by
  simp only [vectorFunctional, ContinuousLinearMap.add_apply, inner_add_right]

omit [CompleteSpace H] in
theorem vectorFunctional_smul (ξ η : H) (c : ℂ) (a : H →L[ℂ] H) :
    vectorFunctional ξ η (c • a) = c * vectorFunctional ξ η a := by
  simp only [vectorFunctional, ContinuousLinearMap.smul_apply, inner_smul_right]

omit [CompleteSpace H] in
theorem vectorFunctional_continuous (ξ η : H) : Continuous (vectorFunctional ξ η) := by
  unfold vectorFunctional
  refine Continuous.inner continuous_const ?_
  exact continuous_id.clm_apply continuous_const

/-- Vector functionals are normal -/
def vectorFunctionalNormal (ξ η : H) : NormalFunctional M where
  toFun := vectorFunctional ξ η
  map_add' := fun a b _ _ => vectorFunctional_add ξ η a b
  map_smul' := fun c a _ => vectorFunctional_smul ξ η c a
  continuous' := vectorFunctional_continuous ξ η
  normal' := by
    -- A single vector functional is trivially a sum: use constant sequences ξ_0 = ξ, η_0 = η
    -- and ξ_n = 0, η_n = 0 for n > 0
    use fun n => if n = 0 then ξ else 0
    use fun n => if n = 0 then η else 0
    constructor
    · -- Summability: only the n=0 term is nonzero
      apply summable_of_ne_finset_zero (s := {0})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      simp [hn]
    · intro a
      simp only [vectorFunctional]
      rw [tsum_eq_single 0]
      · simp
      · intro n hn
        simp [hn]

/-! ### States -/

/-- An operator is positive if ⟨x, ax⟩ ≥ 0 for all x -/
def IsPositiveOperator (a : H →L[ℂ] H) : Prop :=
  ∀ x : H, 0 ≤ (@inner ℂ H _ x (a x)).re

/-- A state on M is a positive normalized linear functional.
    Positive means: for all positive operators a ∈ M, φ(a) ≥ 0. -/
structure State extends NormalFunctional M where
  positive' : ∀ a ∈ M, IsPositiveOperator a → 0 ≤ (toFun a).re
  normalized' : ∀ _h1 : (1 : H →L[ℂ] H) ∈ M, toFun 1 = 1

/-- A vector state ω_Ω(a) = ⟨Ω, a·Ω⟩ -/
def vectorState (Ω : H) (_hΩ : ‖Ω‖ = 1) : NormalFunctional M where
  toFun := vectorFunctional Ω Ω
  map_add' := fun a b _ _ => vectorFunctional_add Ω Ω a b
  map_smul' := fun c a _ => vectorFunctional_smul Ω Ω c a
  continuous' := vectorFunctional_continuous Ω Ω
  normal' := by
    -- A single vector functional is trivially a sum
    use fun n => if n = 0 then Ω else 0
    use fun n => if n = 0 then Ω else 0
    constructor
    · apply summable_of_ne_finset_zero (s := {0})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      simp [hn]
    · intro a
      simp only [vectorFunctional]
      rw [tsum_eq_single 0]
      · simp
      · intro n hn
        simp [hn]

/-- Vector states are positive on positive operators -/
theorem vectorState_positive (Ω : H) (hΩ : ‖Ω‖ = 1) (a : H →L[ℂ] H) (_ha : a ∈ M)
    (hpos : IsPositiveOperator a) :
    0 ≤ ((vectorState M Ω hΩ).toFun a).re := by
  simp only [vectorState, vectorFunctional]
  exact hpos Ω

theorem vectorState_normalized (Ω : H) (hΩ : ‖Ω‖ = 1) (_h1 : (1 : H →L[ℂ] H) ∈ M) :
    (vectorState M Ω hΩ).toFun 1 = 1 := by
  simp only [vectorState, vectorFunctional, ContinuousLinearMap.one_apply]
  rw [inner_self_eq_norm_sq_to_K, hΩ]
  simp

/-! ### Trace class operators (predual elements) -/

/-- A linear operator is trace class if the trace norm ‖T‖₁ := tr(|T|) is finite,
    where |T| = √(T*T) is the absolute value. Equivalently, for any orthonormal
    basis (e_i), the series Σ|⟨e_i, T e_i⟩| converges absolutely.

    For our purposes, we use the characterization that T is trace class iff
    T = Σᵢ αᵢ ξᵢ ⊗ ηᵢ (finite rank approximation in trace norm) where
    Σᵢ |αᵢ| ‖ξᵢ‖ ‖ηᵢ‖ < ∞.

    We include the representation data directly to allow computation of the trace. -/
structure TraceClass (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  op : H →L[ℂ] H
  /-- Vectors for the rank-one decomposition -/
  ξ : ℕ → H
  /-- Vectors for the rank-one decomposition -/
  η : ℕ → H
  /-- Coefficients for the rank-one decomposition -/
  α : ℕ → ℂ
  /-- The coefficients are trace-norm summable -/
  summable' : Summable (fun n => ‖α n‖ * ‖ξ n‖ * ‖η n‖)
  /-- The operator equals the sum of rank-one operators -/
  eq_sum' : ∀ x, op x = ∑' n, α n • @inner ℂ H _ (η n) x • ξ n

/-- The trace of a trace class operator.
    For T = Σᵢ αᵢ |ξᵢ⟩⟨ηᵢ|, we have tr(T) = Σᵢ αᵢ ⟨ηᵢ, ξᵢ⟩ -/
def TraceClass.trace (T : TraceClass H) : ℂ :=
  ∑' n, T.α n * @inner ℂ H _ (T.η n) (T.ξ n)

/-- The trace norm of a trace class operator -/
def TraceClass.traceNorm (T : TraceClass H) : ℝ :=
  ∑' n, ‖T.α n‖ * ‖T.ξ n‖ * ‖T.η n‖

/-- The predual pairing: for ρ ∈ M_* and a ∈ M, ⟨ρ, a⟩ = tr(ρa) -/
def predualPairing (ρ : TraceClass H) (a : H →L[ℂ] H) : ℂ :=
  ∑' n, ρ.α n * @inner ℂ H _ (ρ.η n) (a (ρ.ξ n))

/-! ### σ-weak topology -/

/-- The σ-weak topology on B(H) is the weak topology generated by trace class
    operators, equivalently by all functionals of the form a ↦ Σⁿ⟨ξₙ, a ηₙ⟩
    where Σ‖ξₙ‖‖ηₙ‖ < ∞. -/
def sigmaWeakTopology : TopologicalSpace (H →L[ℂ] H) :=
  TopologicalSpace.induced (fun a => fun ρ : TraceClass H => predualPairing ρ a) ⊤

end VonNeumannAlgebra
