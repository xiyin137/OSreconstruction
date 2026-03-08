/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Basic
import OSReconstruction.vNA.Antilinear
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Tomita-Takesaki Modular Theory

This file develops the Tomita-Takesaki modular theory for von Neumann algebras
with a cyclic-separating vector.

## Main definitions

* `TomitaOperator` - the antilinear operator S₀: aΩ ↦ a*Ω
* `ModularOperator` - the positive self-adjoint operator Δ = S*S
* `ModularConjugation` - the antiunitary operator J from polar decomposition S = JΔ^{1/2}

## Main results

This file currently provides the core Tomita/modular data structures and the
basic algebraic properties that follow directly from those structures. The full
Tomita-Takesaki theorem surfaces are intentionally not exposed here until the
unbounded polar-decomposition and commutant machinery is formalized.

## References

* Tomita, "On canonical forms of von Neumann algebras" (unpublished, 1967)
* Takesaki, "Tomita's theory of modular Hilbert algebras" (1970)
* Takesaki, "Theory of Operator Algebras II", Chapter VIII
* Bratteli-Robinson, "Operator Algebras and Quantum Statistical Mechanics", Vol. 1
-/

noncomputable section

open scoped InnerProduct ComplexConjugate

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace VonNeumannAlgebra

variable (M : VonNeumannAlgebra H)

/-! ### The Tomita operator S₀ -/

/-- The dense domain of the Tomita operator: M·Ω -/
def tomitaDomain (Ω : H) : Set H :=
  M.orbit Ω

/-- The Tomita operator S₀ is the antilinear map aΩ ↦ a*Ω defined on M·Ω.
    This is initially defined as a partial function on the orbit. -/
structure TomitaOperator (Ω : H) where
  /-- The cyclic-separating vector -/
  vec : H
  /-- Proof that vec = Ω -/
  vec_eq : vec = Ω
  /-- The vector is cyclic-separating -/
  cyclic_sep : M.IsCyclicSeparating Ω

namespace TomitaOperator

variable {M} {Ω : H}

/-- The action of S₀ on elements of the form aΩ -/
def apply (_S : TomitaOperator M Ω) (a : H →L[ℂ] H) (_ha : a ∈ M) : H :=
  (ContinuousLinearMap.adjoint a) Ω

/-- S₀(aΩ) = a*Ω -/
theorem apply_eq (S : TomitaOperator M Ω) (a : H →L[ℂ] H) (ha : a ∈ M) :
    S.apply a ha = (ContinuousLinearMap.adjoint a) Ω := rfl

/-- S₀ is well-defined: if aΩ = bΩ then a*Ω = b*Ω (using separating property) -/
theorem well_defined (S : TomitaOperator M Ω) (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M)
    (h : a Ω = b Ω) : S.apply a ha = S.apply b hb := by
  simp only [apply]
  have hab : (a - b) Ω = 0 := by simp [h]
  have hmem : a - b ∈ M := M.toStarSubalgebra.sub_mem ha hb
  have heq : a - b = 0 := S.cyclic_sep.2 (a - b) hmem hab
  have : a = b := eq_of_sub_eq_zero heq
  simp [this]

/-- S₀ is conjugate-linear in the operator: S₀((c·a)Ω) = c̄ · S₀(aΩ)
    This follows from the conjugate-linearity of the adjoint operation. -/
theorem conjugate_linear_smul (_S : TomitaOperator M Ω) (c : ℂ) (a : H →L[ℂ] H) (_ha : a ∈ M) :
    (ContinuousLinearMap.adjoint (c • a)) Ω = starRingEnd ℂ c • (ContinuousLinearMap.adjoint a) Ω := by
  -- Uses: adjoint(c·a) = c̄ · adjoint(a) (conjugate-linearity of adjoint)
  -- The adjoint is a semilinear map with respect to star
  have h := ContinuousLinearMap.adjoint.map_smulₛₗ c a
  simp only [starRingEnd_apply] at h
  rw [h]
  rfl

/-- S₀ is involutive: S₀² = 1 on its domain -/
theorem involutive (S : TomitaOperator M Ω) (a : H →L[ℂ] H) (ha : a ∈ M) :
    S.apply (ContinuousLinearMap.adjoint a) (star_mem ha) = a Ω := by
  simp only [apply, ContinuousLinearMap.adjoint_adjoint]

/-- S₀ is densely defined (M·Ω is dense since Ω is cyclic) -/
theorem densely_defined (S : TomitaOperator M Ω) : M.cyclicSubspace Ω = ⊤ :=
  S.cyclic_sep.1

end TomitaOperator

/-! ### The modular operator Δ -/

/-- The modular operator Δ = S̄*S̄ where S̄ is the closure of S₀.
    Δ is a positive self-adjoint (generally unbounded) operator. -/
structure ModularOperator (Ω : H) where
  /-- The cyclic-separating vector -/
  vec : H
  /-- The vector is cyclic-separating -/
  cyclic_sep : M.IsCyclicSeparating Ω
  /-- Domain of Δ -/
  domain : Submodule ℂ H
  /-- Δ is densely defined -/
  dense_domain : domain.topologicalClosure = ⊤
  /-- The cyclic vector belongs to the domain of Δ.
      This follows from S₀(1·Ω) = 1*Ω = Ω, so Ω ∈ dom(S̄) ⊆ dom(Δ). -/
  vec_mem_domain : vec ∈ domain
  /-- The action of Δ on elements of its domain -/
  apply : domain → H
  /-- Δ fixes the cyclic vector: ΔΩ = Ω.
      This follows from S̄Ω = Ω (since S₀(1·Ω) = 1*Ω = Ω) and Δ = S̄*S̄. -/
  fixes_vec : apply ⟨vec, vec_mem_domain⟩ = vec

namespace ModularOperator

variable {M} {Ω : H}

/-- The modular operator has dense domain (inherited from cyclic property) -/
theorem has_dense_domain (Δ : ModularOperator M Ω) : Δ.domain.topologicalClosure = ⊤ :=
  Δ.dense_domain

/-- Ω is in the domain of the modular operator -/
theorem Ω_in_domain (Δ : ModularOperator M Ω) : Δ.vec ∈ Δ.domain :=
  Δ.vec_mem_domain

/-- The cyclic vector Ω is in the domain of the modular operator.
    This follows from the construction of Δ = S̄*S̄ and the fact that
    S₀(1·Ω) = 1*Ω = Ω (the Tomita operator fixes Ω). -/
theorem Ω_in_modular_domain (_Δ : ModularOperator M Ω) : _Δ.vec ∈ _Δ.domain :=
  _Δ.vec_mem_domain

/-- The modular operator satisfies ΔΩ = Ω (Ω is in the kernel of log Δ).
    This follows from S₀(1·Ω) = 1*Ω = Ω, so S₀Ω = Ω.
    Since Δ = S̄*S̄ and S̄Ω = Ω, we have ΔΩ = Ω.

    This is now an axiom of the `ModularOperator` structure. -/
theorem fixes_cyclic_vector (Δ : ModularOperator M Ω) :
    Δ.apply ⟨Δ.vec, Δ.vec_mem_domain⟩ = Δ.vec :=
  Δ.fixes_vec

end ModularOperator

/-! ### The modular conjugation J -/

/-- The modular conjugation J from the polar decomposition S = JΔ^{1/2}.
    J is an antiunitary involution. We include the actual operator J as data. -/
structure ModularConjugation (Ω : H) where
  /-- The cyclic-separating vector -/
  vec : H
  /-- The vector is cyclic-separating -/
  cyclic_sep : M.IsCyclicSeparating Ω
  /-- The antiunitary operator J -/
  J : AntiunitaryOp H
  /-- J fixes the cyclic vector -/
  fixes_vec : J Ω = Ω

namespace ModularConjugation

variable {M} {Ω : H}

/-- J is antilinear: J(αξ + η) = ᾱJ(ξ) + J(η).
    This is the defining property of an antilinear operator.
    The modular conjugation J arises from the polar decomposition S = JΔ^{1/2}
    where S is the closure of the Tomita operator. Since S is antilinear
    (aΩ ↦ a*Ω involves the star operation which is conjugate-linear),
    and Δ^{1/2} is linear, J must be antilinear. -/
theorem is_antilinear (J : ModularConjugation M Ω) (c : ℂ) (ξ η : H) :
    J.J (c • ξ + η) = starRingEnd ℂ c • J.J ξ + J.J η := by
  rw [J.J.toAntilinearMap.map_add, J.J.toAntilinearMap.map_smul]

/-- J is isometric: ‖Jξ‖ = ‖ξ‖.
    Combined with antilinearity, this makes J antiunitary.
    This follows from the fact that S preserves a certain sesquilinear form,
    and the polar decomposition properties. -/
theorem is_isometric (J : ModularConjugation M Ω) (ξ : H) :
    ‖J.J ξ‖ = ‖ξ‖ := J.J.norm_map ξ

/-- J is antiunitary: ⟨Jξ, Jη⟩ = ⟨η, ξ⟩.
    This is equivalent to J being antilinear and isometric.
    An antiunitary operator preserves inner products up to complex conjugation. -/
theorem is_antiunitary (J : ModularConjugation M Ω) (ξ η : H) :
    @inner ℂ H _ (J.J ξ) (J.J η) = @inner ℂ H _ η ξ := J.J.inner_map_map ξ η

/-- J is an involution: J² = 1.
    This follows from the polar decomposition S = JΔ^{1/2} and the fact
    that S₀² = 1 on its domain (S₀(S₀(aΩ)) = S₀(a*Ω) = aΩ). -/
theorem is_involution (J : ModularConjugation M Ω) (ξ : H) :
    J.J (J.J ξ) = ξ := J.J.apply_apply ξ

/-- J fixes Ω: JΩ = Ω.
    The cyclic-separating vector is fixed by the modular conjugation.
    Proof: S₀(1·Ω) = 1*Ω = Ω, and Δ^{1/2}Ω = Ω (since ΔΩ = Ω).
    From S = JΔ^{1/2}, we have Ω = SΩ = JΔ^{1/2}Ω = JΩ. -/
theorem fixes_cyclic_vector (J : ModularConjugation M Ω) : J.J Ω = Ω := J.fixes_vec

end ModularConjugation

/-! ### Conjugation by modular conjugation -/

/-- The map a ↦ JaJ for bounded operators, where J is an antiunitary operator.
    This is used in the fundamental theorem JMJ = M'. -/
def conjugateByJ (J : AntiunitaryOp H) (a : H →L[ℂ] H) : H → H :=
  fun ξ => J (a (J ξ))

/-! ### Standard form -/

/-- A von Neumann algebra in standard form with its modular data -/
structure StandardForm where
  /-- The von Neumann algebra -/
  algebra : VonNeumannAlgebra H
  /-- The cyclic-separating vector -/
  Ω : H
  /-- Proof that Ω is cyclic-separating -/
  cyclic_sep : algebra.IsCyclicSeparating Ω
  /-- The modular operator -/
  modular_op : ModularOperator algebra Ω
  /-- The modular conjugation -/
  modular_conj : ModularConjugation algebra Ω

/-- The natural positive cone P^♮ in the standard form.
    P^♮ = closure of {JaJaΩ : a ∈ M} = closure of {Δ^{1/4} a Ω : a ≥ 0}
    This is self-dual and gives the standard positive cone in the Hilbert space.

    The definition uses the characterization: ξ ∈ P^♮ iff ξ = lim JaₙJaₙΩ for some
    sequence (aₙ) in M. Equivalently, using Δ^{1/4}: ξ ∈ P^♮ iff ξ = Δ^{1/4}aΩ
    for some positive a ∈ M.

    Properties:
    - P^♮ is a closed convex cone
    - P^♮ is self-dual: P^♮ = {ξ : ⟨ξ, η⟩ ≥ 0 for all η ∈ P^♮}
    - P^♮ ∩ (-P^♮) = {0} (P^♮ is pointed) -/
def StandardForm.positiveCone (S : StandardForm (H := H)) : Set H :=
  -- P^♮ = closure of {JaJaΩ : a ∈ M}
  -- Using the modular conjugation J from the standard form
  closure { ξ : H | ∃ (a : H →L[ℂ] H), a ∈ S.algebra ∧
    ξ = S.modular_conj.J (a (S.modular_conj.J (a S.Ω))) }

end VonNeumannAlgebra
