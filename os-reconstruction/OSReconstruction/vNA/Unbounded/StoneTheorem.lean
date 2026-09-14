/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Init
import OSReconstruction.vNA.Unbounded.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
























































set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped InnerProduct ComplexConjugate
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



/-- A strongly continuous one-parameter unitary group on a Hilbert space H.

    A map U : ℝ → B(H) is a strongly continuous one-parameter unitary group if:
    1. Each U(t) is unitary: U(t)*U(t) = U(t)U(t)* = 1
    2. Group property: U(s)U(t) = U(s+t) and U(0) = 1
    3. Strong continuity: t ↦ U(t)x is continuous for all x ∈ H

    Examples:
    - Time evolution in quantum mechanics: U(t) = exp(-itH/ℏ)
    - Spatial translations: U(a) = exp(-iaP)
    - Rotations: U(θ) = exp(-iθL)

    The strong continuity condition is equivalent to requiring U(t)x → x as t → 0
    for all x ∈ H (since U(t) are unitary, this implies full continuity). -/
structure OneParameterUnitaryGroup (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The map t ↦ U(t) -/
  U : ℝ → (H →L[ℂ] H)
  /-- Unitarity: U(t)* U(t) = 1 -/
  unitary_left : ∀ t, (U t).adjoint ∘L (U t) = 1
  /-- Unitarity: U(t) U(t)* = 1 -/
  unitary_right : ∀ t, (U t) ∘L (U t).adjoint = 1
  /-- Group identity: U(0) = 1 -/
  zero : U 0 = 1
  /-- Group multiplication: U(s+t) = U(s) U(t) -/
  add : ∀ s t, U (s + t) = (U s) ∘L (U t)
  /-- Strong continuity: t ↦ U(t)x is continuous for each x -/
  continuous : ∀ x : H, Continuous (fun t => U t x)

namespace OneParameterUnitaryGroup

variable (𝒰 : OneParameterUnitaryGroup H)



/-- The domain of the infinitesimal generator consists of vectors x for which
    the limit lim_{t→0} (U(t)x - x)/(it) exists.

    Equivalently, x ∈ dom(A) iff the map t ↦ U(t)x is differentiable at t = 0
    with derivative iAx.

    This domain is always dense in H (a key fact for Stone's theorem). -/
def generatorDomain : Set H :=
  { x | ∃ y : H, Tendsto (fun t : ℝ =>
      (Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x - x))) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds y) }

/-- The generator applied to a vector in its domain.
    Ax = lim_{t→0} (U(t)x - x)/(it) -/
def generatorApply (x : H) (hx : x ∈ 𝒰.generatorDomain) : H :=
  Classical.choose hx

/-- The defining property of the generator -/
theorem generatorApply_spec (x : H) (hx : x ∈ 𝒰.generatorDomain) :
    Tendsto (fun t : ℝ =>
      (Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x - x))) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (𝒰.generatorApply x hx)) :=
  Classical.choose_spec hx

/-- Zero is in the domain of the generator, with A(0) = 0 -/
theorem zero_mem_generatorDomain : (0 : H) ∈ 𝒰.generatorDomain := by
  use 0
  simp only [map_zero, sub_zero, smul_zero]
  exact tendsto_const_nhds

/-- The domain of the generator is a subspace -/
theorem generatorDomain_submodule : ∃ S : Submodule ℂ H, (S : Set H) = 𝒰.generatorDomain := by
  -- The domain is closed under addition and scalar multiplication
  -- because limits commute with these operations
  use {
    carrier := 𝒰.generatorDomain
    add_mem' := fun {x y} hx hy => by
      obtain ⟨ax, hax⟩ := hx
      obtain ⟨ay, hay⟩ := hy
      use ax + ay
      have hsum : ∀ t : ℝ, 𝒰.U t (x + y) - (x + y) = (𝒰.U t x - x) + (𝒰.U t y - y) := by
        intro t; simp only [map_add]; abel
      refine (hax.add hay).congr (fun t => ?_)
      rw [hsum, smul_add, smul_add]
    zero_mem' := 𝒰.zero_mem_generatorDomain
    smul_mem' := fun c x hx => by
      obtain ⟨ax, hax⟩ := hx
      use c • ax
      have hsmul : ∀ t : ℝ, 𝒰.U t (c • x) - c • x = c • (𝒰.U t x - x) := by
        intro t; simp only [map_smul, smul_sub]
      refine (hax.const_smul c).congr (fun t => ?_)
      rw [hsmul, smul_comm c (Complex.I)⁻¹, smul_comm c t⁻¹]
  }
  rfl

/-- The domain of the generator as a submodule -/
def generatorDomainSubmodule : Submodule ℂ H :=
  (𝒰.generatorDomain_submodule).choose

theorem generatorDomainSubmodule_carrier :
    (𝒰.generatorDomainSubmodule : Set H) = 𝒰.generatorDomain :=
  (𝒰.generatorDomain_submodule).choose_spec

/-- The infinitesimal generator of the one-parameter group.

    A is defined by: iAx = lim_{t→0} (U(t)x - x)/t
    or equivalently: Ax = lim_{t→0} (U(t)x - x)/(it)

    By Stone's theorem, A is self-adjoint and U(t) = exp(itA). -/
def generator : UnboundedOperator H where
  domain := 𝒰.generatorDomainSubmodule
  toFun := fun x => 𝒰.generatorApply x.1 (by
    rw [← 𝒰.generatorDomainSubmodule_carrier]
    exact x.2)
  map_add' := fun x y => by
    -- A(x+y) = Ax + Ay follows from uniqueness of limits
    -- Key: limits are unique in Hausdorff spaces (Hilbert spaces are T2)
    have hx_mem : x.1 ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact x.2
    have hy_mem : y.1 ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact y.2
    have hxy_mem : (x + y).1 ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact (x + y).2
    -- The limit for x+y on nhdsWithin
    have h_sum_limit : Tendsto (fun t : ℝ =>
        (Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t (x + y).1 - (x + y).1)))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (𝒰.generatorApply x.1 hx_mem + 𝒰.generatorApply y.1 hy_mem)) := by
      have hx_lim := 𝒰.generatorApply_spec x.1 hx_mem
      have hy_lim := 𝒰.generatorApply_spec y.1 hy_mem
      refine (hx_lim.add hy_lim).congr (fun t => ?_)
      simp only [Submodule.coe_add, map_add, add_sub_add_comm, smul_add]
    -- By uniqueness of limits (Hilbert spaces are T2)
    have h_unique := tendsto_nhds_unique (𝒰.generatorApply_spec (x + y).1 hxy_mem) h_sum_limit
    simp only [Submodule.coe_add] at h_unique
    exact h_unique
  map_smul' := fun c x => by
    -- A(cx) = c(Ax) follows from uniqueness of limits and linearity of scalar mult
    have hx_mem : x.1 ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact x.2
    have hcx_mem : (c • x).1 ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact (c • x).2
    -- The limit for c • x on nhdsWithin
    have h_smul_limit : Tendsto (fun t : ℝ =>
        (Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t (c • x).1 - (c • x).1)))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds (c • 𝒰.generatorApply x.1 hx_mem)) := by
      have hx_lim := 𝒰.generatorApply_spec x.1 hx_mem
      refine (hx_lim.const_smul c).congr (fun t => ?_)
      -- Goal: c • I⁻¹ • t⁻¹ • (U(t)x - x) = I⁻¹ • t⁻¹ • (U(t)(c•x) - c•x)
      -- Simplify RHS coercion and U-linearity
      have hcoe : (c • x : ↥𝒰.generatorDomainSubmodule).1 = c • x.1 := rfl
      rw [hcoe, map_smul, ← smul_sub c]
      -- Goal: c • I⁻¹ • t⁻¹ • (U(t)x - x) = I⁻¹ • t⁻¹ • (c • (U(t)x - x))
      -- Both sides are ℂ-scalar multiples of (U(t)x - x)
      -- LHS = (c * I⁻¹) • t⁻¹ • v, RHS = I⁻¹ • t⁻¹ • c • v
      -- Convert all to single scalar: use smul_smul and mul_comm
      set v := 𝒰.U t x.1 - x.1
      simp only [smul_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      ring_nf
    have h_unique := tendsto_nhds_unique (𝒰.generatorApply_spec (c • x).1 hcx_mem) h_smul_limit
    simp only [Submodule.coe_smul] at h_unique
    exact h_unique


































end OneParameterUnitaryGroup



end
