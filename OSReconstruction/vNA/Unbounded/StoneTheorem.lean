/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Unbounded.SpectralPowers
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Stone's Theorem on One-Parameter Unitary Groups

This file proves Stone's theorem: every strongly continuous one-parameter unitary group
on a Hilbert space is of the form U(t) = exp(itA) for a unique self-adjoint operator A,
called the infinitesimal generator.

## Main definitions

* `OneParameterUnitaryGroup` - A strongly continuous one-parameter unitary group
* `OneParameterUnitaryGroup.generator` - The infinitesimal generator A
* `OneParameterUnitaryGroup.generatorDomain` - The domain of A

## Main results

* `generator_densely_defined` - The generator is densely defined
* `generator_selfadjoint` - The generator is self-adjoint
* `Stone` - U(t) = exp(itA) where A is the generator

## Mathematical Background

Stone's theorem is one of the fundamental results of functional analysis relating:
- One-parameter unitary groups (symmetries/dynamics)
- Self-adjoint operators (observables/generators)

The key insight is that strong continuity U(t)ψ → ψ as t → 0 implies the existence
of a dense domain on which the derivative dU(t)ψ/dt|_{t=0} exists.

## Foundational results (Reed-Simon VIII.7-8)

The proof of Stone's theorem requires several deep results:

1. **Density of the generator domain** (Reed-Simon VIII.7):
   - For smooth compactly supported φ, x_φ := ∫ φ(t) U(t)x dt ∈ dom(A)
   - Taking φ → δ (approximate identity) gives dom(A) dense

2. **Symmetry of the generator** (Reed-Simon VIII.7):
   - ⟨Ax, y⟩ = lim_{t→0} ⟨(U(t)x - x)/(it), y⟩
   - Using U(t)* = U(-t) and continuity of inner product
   - Careful limit manipulation shows ⟨Ax, y⟩ = ⟨x, Ay⟩

3. **Self-adjointness** (the hard part):
   - Symmetry gives A ⊆ A*
   - Must show A* ⊆ A, i.e., dom(A*) ⊆ dom(A)
   - Uses that U(t) maps dom(A*) to itself

These results require careful analysis and limit arguments.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I: Functional Analysis", Theorem VIII.7-8
* Rudin, "Functional Analysis", Section 13.35
* Hall, "Quantum Theory for Mathematicians", Chapter 10
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped InnerProduct ComplexConjugate
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### One-parameter unitary groups -/

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

/-- U(-t) = U(t)* for unitary groups -/
theorem neg (t : ℝ) : 𝒰.U (-t) = (𝒰.U t).adjoint := by
  -- U(-t) U(t) = U(0) = 1
  have h1 : 𝒰.U (-t) ∘L 𝒰.U t = 1 := by
    rw [← 𝒰.add (-t) t]
    simp only [neg_add_cancel]
    exact 𝒰.zero
  -- U(t)* is the unique left inverse, so U(-t) = U(t)*
  -- For unitary U, U* is both left and right inverse
  -- h1 says U(-t) is a left inverse
  -- By uniqueness of inverse for unitary operators: U(-t) = U(t)*
  have h2 := 𝒰.unitary_left t
  -- h2: U(t)* U(t) = 1
  -- h1: U(-t) U(t) = 1
  -- So U(-t) = U(-t)(U(t) U(t)*) = (U(-t) U(t)) U(t)* = U(t)*
  calc 𝒰.U (-t) = 𝒰.U (-t) ∘L 1 := by
        ext x; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
    _ = 𝒰.U (-t) ∘L (𝒰.U t ∘L (𝒰.U t).adjoint) := by rw [𝒰.unitary_right]
    _ = (𝒰.U (-t) ∘L 𝒰.U t) ∘L (𝒰.U t).adjoint := by
        ext x; simp only [ContinuousLinearMap.comp_apply]
    _ = 1 ∘L (𝒰.U t).adjoint := by rw [h1]
    _ = (𝒰.U t).adjoint := by
        ext x; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]

/-- Each U(t) preserves norms (since unitary) -/
theorem norm_preserving (t : ℝ) (x : H) : ‖𝒰.U t x‖ = ‖x‖ := by
  -- ‖U(t)x‖² = ⟨U(t)x, U(t)x⟩ = ⟨x, U(t)*U(t)x⟩ = ⟨x, x⟩ = ‖x‖²
  have h : ‖𝒰.U t x‖^2 = ‖x‖^2 := by
    have h1 : ‖𝒰.U t x‖^2 = (@inner ℂ H _ (𝒰.U t x) (𝒰.U t x)).re := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have h2 : (@inner ℂ H _ (𝒰.U t x) (𝒰.U t x)).re =
        (@inner ℂ H _ x ((𝒰.U t).adjoint (𝒰.U t x))).re := by
      -- adjoint_inner_left gives: ⟨A* y, x⟩ = ⟨y, A x⟩
      -- We need: ⟨U(t)x, U(t)x⟩ = ⟨x, U(t)* U(t)x⟩
      -- Use adjoint_inner_right: ⟨x, A* y⟩ = ⟨A x, y⟩
      have := ContinuousLinearMap.adjoint_inner_right (𝒰.U t) x (𝒰.U t x)
      -- this: ⟨x, U(t)* U(t)x⟩ = ⟨U(t)x, U(t)x⟩
      rw [this]
    have h3 : (𝒰.U t).adjoint (𝒰.U t x) = x := by
      have := congrFun (congrArg DFunLike.coe (𝒰.unitary_left t)) x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
      exact this
    have h4 : (@inner ℂ H _ x x).re = ‖x‖^2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [h1, h2, h3, h4]
  have hnn1 : ‖𝒰.U t x‖ ≥ 0 := norm_nonneg _
  have hnn2 : ‖x‖ ≥ 0 := norm_nonneg _
  nlinarith [sq_nonneg (‖𝒰.U t x‖ - ‖x‖), sq_nonneg (‖𝒰.U t x‖ + ‖x‖)]

/-- Strong continuity at 0: U(t)x → x as t → 0 -/
theorem tendsto_zero (x : H) : Tendsto (fun t => 𝒰.U t x) (nhds 0) (nhds x) := by
  have h := 𝒰.continuous x
  rw [Metric.continuous_iff] at h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := h 0 ε hε
  rw [Filter.eventually_iff_exists_mem]
  use Set.Ioo (-δ) δ
  constructor
  · apply Ioo_mem_nhds <;> linarith
  · intro t ht
    simp only [Set.mem_Ioo] at ht
    have hdist : dist t 0 < δ := by
      simp [dist, abs_lt]
      exact ht
    have := hball t hdist
    rw [𝒰.zero] at this
    simp only [ContinuousLinearMap.one_apply] at this
    exact this

/-! ### The infinitesimal generator -/

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

/-- The generator domain is dense in H (key lemma for Stone's theorem).

    Proof sketch: For any x ∈ H, the "time-averaged" vectors
      x_ε = (1/ε) ∫₀^ε U(t)x dt
    lie in dom(A) and converge to x as ε → 0.

    More specifically, for any smooth compactly supported φ : ℝ → ℂ,
    the vector ∫ φ(t) U(t)x dt lies in dom(A).
    Taking φ to be an approximate identity shows dom(A) is dense. -/
theorem generator_densely_defined : 𝒰.generator.IsDenselyDefined := by
  -- Prove dom(A) is dense by showing its orthogonal complement is trivial.
  -- For any x ∈ H and ε ≠ 0, the integral ∫₀ᵋ U(t)x dt is in dom(A),
  -- and as ε → 0 the averaged vector (1/ε)∫₀ᵋ U(t)x dt → x.
  unfold UnboundedOperator.IsDenselyDefined
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  -- y ∈ dom(A)ᗮ, show y = 0
  rw [← inner_self_eq_zero (𝕜 := ℂ)]
  by_contra h_ne
  have hy_ne : y ≠ 0 := fun h0 => h_ne (by rw [h0, inner_self_eq_zero])
  -- For any z ∈ H, ⟨z, y⟩ = 0: construct vectors in dom(A) approximating z
  suffices h_all : ∀ z : H, @inner ℂ H _ z y = 0 from h_ne (h_all y)
  intro z
  have hf_cont : Continuous (fun t : ℝ => 𝒰.U t z) := 𝒰.continuous z
  have hf_int : ∀ a b : ℝ, IntervalIntegrable (fun t => 𝒰.U t z) MeasureTheory.volume a b :=
    fun a b => hf_cont.intervalIntegrable a b
  -- Define F(u) = ∫₀ᵘ U(t)z dt (the "antiderivative")
  set F : ℝ → H := fun u => ∫ t in (0 : ℝ)..u, 𝒰.U t z with hF_def
  -- FTC: F'(u) = U(u)z
  have hFTC : ∀ u : ℝ, HasDerivAt F (𝒰.U u z) u :=
    fun u => intervalIntegral.integral_hasDerivAt_right (hf_int 0 u)
      hf_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hf_cont.continuousAt
  -- F(0) = 0
  have hF0 : F 0 = 0 := by simp [hF_def, intervalIntegral.integral_same]
  -- Key: U(h)(F(ε)) = F(ε+h) - F(h), via group property + change of variables
  have h_shift : ∀ ε h : ℝ, 𝒰.U h (F ε) = F (ε + h) - F h := by
    intro ε' h'
    -- U(h') commutes with integral
    have hcomm := (ContinuousLinearMap.intervalIntegral_comp_comm (𝒰.U h') (hf_int 0 ε')).symm
    -- U(h')(U(t)z) = U(t+h')z by group property
    have hgroup : ∀ t, 𝒰.U h' (𝒰.U t z) = 𝒰.U (t + h') z := by
      intro t; rw [← ContinuousLinearMap.comp_apply, ← 𝒰.add h' t]; ring_nf
    rw [hcomm]; simp_rw [hgroup]
    -- ∫₀^ε' U(t+h')z dt = ∫_{0+h'}^{ε'+h'} U(s)z ds
    have h_subst : ∫ t in (0 : ℝ)..ε', 𝒰.U (t + h') z =
        ∫ t in (0 + h')..(ε' + h'), 𝒰.U t z :=
      intervalIntegral.integral_comp_add_right (fun t => 𝒰.U t z) h'
    rw [h_subst]; simp only [zero_add, hF_def]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf_int 0 h') (hf_int h' (ε' + h'))]
    abel
  -- For any ε ≠ 0, F(ε) is in the generator domain.
  -- Define g(h) = F(ε+h) - F(h). Then g(0) = F(ε) and g'(0) = U(ε)z - z.
  -- Since U(h)(F(ε)) = g(h), we get U(h)(F(ε)) - F(ε) = g(h) - g(0),
  -- so h⁻¹ • (U(h)(F(ε)) - F(ε)) → g'(0) = U(ε)z - z.
  have h_in_dom : ∀ ε : ℝ, ε ≠ 0 → F ε ∈ 𝒰.generatorDomain := by
    intro ε hε
    use Complex.I⁻¹ • (𝒰.U ε z - z)
    -- Define g(h) = F(ε+h) - F(h), so g has derivative U(ε)z - z at 0
    set g : ℝ → H := fun h => F (ε + h) - F h with hg_def
    have hg_deriv : HasDerivAt g (𝒰.U ε z - z) 0 := by
      -- F(ε + h) has derivative U(ε)z at h = 0 (chain rule / shift)
      have h1 : HasDerivAt (fun h => F (ε + h)) (𝒰.U ε z) 0 := by
        have h := hFTC ε
        rw [show ε = ε + 0 from (add_zero ε).symm] at h
        have := h.comp_const_add ε 0
        rwa [add_zero] at this
      -- F(h) has derivative U(0)z = z at h = 0
      have h2 : HasDerivAt F z 0 := by
        convert hFTC 0 using 1; simp [𝒰.zero, ContinuousLinearMap.one_apply]
      exact h1.sub h2
    -- g(0) = F(ε) - F(0) = F(ε) (since F(0) = 0)
    have hg0 : g 0 = F ε := by simp [hg_def, hF0]
    -- U(h)(F(ε)) = g(h) by h_shift, so U(h)(F(ε)) - F(ε) = g(h) - g(0)
    -- HasDerivAt g (U(ε)z - z) 0 means h⁻¹ • (g(h) - g(0)) → U(ε)z - z
    -- This gives: h⁻¹ • (U(h)(F(ε)) - F(ε)) → U(ε)z - z
    -- From HasDerivAt g at 0, get slope convergence on punctured nhds
    have hslope := hg_deriv.tendsto_slope_zero
    simp only [zero_add, hg0] at hslope
    -- hslope : Tendsto (fun t => t⁻¹ • (g(t) - F ε)) (𝓝[≠] 0) (𝓝 (U(ε)z - z))
    -- U(h)(F ε) = g(h) by h_shift, so t⁻¹ • (g(t) - F ε) = t⁻¹ • (U(t)(F ε) - F ε)
    have h_punc : Tendsto (fun t : ℝ => t⁻¹ • (𝒰.U t (F ε) - F ε))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (𝒰.U ε z - z)) :=
      hslope.congr (fun t => by simp only [hg_def, h_shift])
    -- Apply I⁻¹ • to get the generator domain form
    exact (h_punc.const_smul (Complex.I⁻¹ : ℂ)).congr (fun t => rfl)
  -- F(ε) ∈ dom(A) means F(ε) ∈ generator.domain (since domains match)
  have h_in_gen_dom : ∀ ε : ℝ, ε ≠ 0 → F ε ∈ 𝒰.generator.domain := by
    intro ε hε
    change F ε ∈ (𝒰.generatorDomainSubmodule : Set H)
    rw [𝒰.generatorDomainSubmodule_carrier]
    exact h_in_dom ε hε
  -- ⟨F(ε), y⟩ = 0 for all ε ≠ 0 (by orthogonality)
  have h_inner_zero : ∀ ε : ℝ, ε ≠ 0 → @inner ℂ H _ (F ε) y = 0 := by
    intro ε hε
    exact (Submodule.mem_orthogonal _ _).mp hy (F ε) (h_in_gen_dom ε hε)
  -- ⟨F(ε)/ε, y⟩ = 0 and F(ε)/ε → z as ε → 0
  -- Actually, directly: ⟨F(ε), y⟩ = 0 and F has derivative z at 0
  -- So ⟨F(ε)/ε, y⟩ = ⟨F(ε), y⟩/ε = 0/ε = 0
  -- and F(ε)/ε → F'(0) = U(0)z = z
  -- F'(0) = U(0)z = z
  have hF_deriv_0 : HasDerivAt F z 0 := by
    convert hFTC 0 using 1; simp [𝒰.zero, ContinuousLinearMap.one_apply]
  -- F(ε)/ε → z as ε → 0 (from HasDerivAt and F(0) = 0)
  have h_avg_tends : Tendsto (fun ε : ℝ => ε⁻¹ • F ε) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds z) := by
    have hslope := hF_deriv_0.tendsto_slope_zero
    simp only [zero_add, hF0, sub_zero] at hslope
    exact hslope
  -- ⟨ε⁻¹ • F(ε), y⟩ = ε⁻¹ • ⟨F(ε), y⟩ = 0 for ε ≠ 0
  -- Since ε⁻¹ • F(ε) → z and ⟨·, y⟩ is continuous, ⟨z, y⟩ = 0
  have h_inner_avg_zero : ∀ᶠ ε in nhdsWithin 0 {(0 : ℝ)}ᶜ,
      @inner ℂ H _ (ε⁻¹ • F ε) y = 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hε
    rw [show ε⁻¹ • F ε = ((ε⁻¹ : ℝ) : ℂ) • F ε from
      (RCLike.real_smul_eq_coe_smul (K := ℂ) ε⁻¹ (F ε)).symm]
    rw [inner_smul_left, h_inner_zero ε hε, mul_zero]
  have h_inner_tends : Tendsto (fun ε => @inner ℂ H _ (ε⁻¹ • F ε) y)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (@inner ℂ H _ z y)) :=
    h_avg_tends.inner tendsto_const_nhds
  have h_inner_tends_zero : Tendsto (fun ε => @inner ℂ H _ (ε⁻¹ • F ε) y)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) :=
    tendsto_const_nhds.congr' (h_inner_avg_zero.mono (fun ε hε => hε.symm))
  exact tendsto_nhds_unique h_inner_tends h_inner_tends_zero

/-! ### Self-adjointness of the generator -/

/-- The generator is symmetric: ⟨Ax, y⟩ = ⟨x, Ay⟩ for x, y ∈ dom(A).

    **Proof outline:**
    By continuity of inner product, ⟨Ax, y⟩ = lim_{t→0} ⟨(U(t)x - x)/(it), y⟩.

    Using that inner product is conjugate-linear in the first argument (Mathlib convention):
      ⟨Ax, y⟩ = lim_{t→0} (1/(it))⁻ · (⟨U(t)x, y⟩ - ⟨x, y⟩)
              = lim_{t→0} (-1/(it)) · (⟨U(t)x, y⟩ - ⟨x, y⟩)

    Since U(t)* = U(-t), we have ⟨U(t)x, y⟩ = ⟨x, U(t)*y⟩ = ⟨x, U(-t)y⟩:
      ⟨Ax, y⟩ = lim_{t→0} (-1/(it)) · (⟨x, U(-t)y⟩ - ⟨x, y⟩)

    For ⟨x, Ay⟩, using linearity in the second argument:
      ⟨x, Ay⟩ = lim_{t→0} ⟨x, (U(t)y - y)/(it)⟩
              = lim_{t→0} (1/(it)) · (⟨x, U(t)y⟩ - ⟨x, y⟩)

    Substituting s = -t in ⟨x, Ay⟩:
      ⟨x, Ay⟩ = lim_{s→0} (-1/(is)) · (⟨x, U(-s)y⟩ - ⟨x, y⟩)

    Comparing: ⟨Ax, y⟩ and ⟨x, Ay⟩ are the same limit (t ↔ s renaming). -/
theorem generator_symmetric : 𝒰.generator.IsSymmetric := by
  intro x y
  -- We need to show ⟨Ax, y⟩ = ⟨x, Ay⟩

  -- Get membership in the domain
  have hx_mem : x.1 ∈ 𝒰.generatorDomain := by
    rw [← 𝒰.generatorDomainSubmodule_carrier]; exact x.2
  have hy_mem : y.1 ∈ 𝒰.generatorDomain := by
    rw [← 𝒰.generatorDomainSubmodule_carrier]; exact y.2

  -- The defining limits for Ax and Ay
  have hAx_lim := 𝒰.generatorApply_spec x.1 hx_mem
  have hAy_lim := 𝒰.generatorApply_spec y.1 hy_mem

  -- Key lemma: U(t)* = U(-t)
  have hU_neg : ∀ t, (𝒰.U t).adjoint = 𝒰.U (-t) := fun t => (𝒰.neg t).symm

  -- Inner product is continuous
  have hinner_cont : Continuous (fun p : H × H => @inner ℂ H _ p.1 p.2) := continuous_inner

  -- Apply inner product with y to the limit defining Ax (on nhdsWithin)
  -- ⟨Ax, y⟩ = lim_{t→0, t≠0} ⟨I⁻¹ • t⁻¹ • (U(t)x - x), y⟩
  have hAx_inner : Tendsto (fun t : ℝ =>
      @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x.1 - x.1))) y.1)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (@inner ℂ H _ (𝒰.generatorApply x.1 hx_mem) y.1)) :=
    hAx_lim.inner tendsto_const_nhds

  -- Apply inner product with x to the limit defining Ay (on nhdsWithin)
  -- ⟨x, Ay⟩ = lim_{t→0, t≠0} ⟨x, I⁻¹ • t⁻¹ • (U(t)y - y)⟩
  have hAy_inner : Tendsto (fun t : ℝ =>
      @inner ℂ H _ x.1 ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t y.1 - y.1))))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (@inner ℂ H _ x.1 (𝒰.generatorApply y.1 hy_mem))) :=
    Tendsto.inner tendsto_const_nhds hAy_lim

  -- The key algebraic identity: for t ≠ 0,
  -- ⟨I⁻¹ • t⁻¹ • (U(t)x - x), y⟩ = ⟨x, I⁻¹ • (-t)⁻¹ • (U(-t)y - y)⟩
  have halg : ∀ t : ℝ, t ≠ 0 →
      @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x.1 - x.1))) y.1 =
      @inner ℂ H _ x.1 ((Complex.I : ℂ)⁻¹ • ((-t)⁻¹ • (𝒰.U (-t) y.1 - y.1))) := by
    intro t ht
    -- Use adjoint: ⟨U(t)x, y⟩ = ⟨x, U(t)*y⟩ = ⟨x, U(-t)y⟩
    have hadj : @inner ℂ H _ (𝒰.U t x.1) y.1 = @inner ℂ H _ x.1 (𝒰.U (-t) y.1) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hU_neg]
    -- ⟨U(t)x - x, y⟩ = ⟨x, U(-t)y - y⟩
    have hinner_sub : @inner ℂ H _ (𝒰.U t x.1 - x.1) y.1 =
        @inner ℂ H _ x.1 (𝒰.U (-t) y.1 - y.1) := by
      rw [inner_sub_left, inner_sub_right, hadj]
    -- I⁻¹ = -I (since I² = -1, so I⁻¹ = -I)
    have hI_inv : (Complex.I : ℂ)⁻¹ = -Complex.I := Complex.inv_I
    -- For real scalar r, (r : ℂ) • z = r • z by the module structure
    -- The ℝ-module action on H is the restriction of the ℂ-module action
    have hreal_smul : ∀ (r : ℝ) (z : H), (r : ℂ) • z = r • z := fun r z =>
      (RCLike.real_smul_eq_coe_smul (K := ℂ) r z).symm
    -- LHS computation
    -- Key identity: (t⁻¹ : ℂ) = (t : ℂ)⁻¹ by Complex.ofReal_inv
    calc @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x.1 - x.1))) y.1
        = @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • ((t : ℂ)⁻¹ • (𝒰.U t x.1 - x.1))) y.1 := by
          -- First convert t⁻¹ (real) to (t⁻¹ : ℂ) then to (t : ℂ)⁻¹
          rw [← hreal_smul, Complex.ofReal_inv]
      _ = starRingEnd ℂ (Complex.I : ℂ)⁻¹ * @inner ℂ H _ ((t : ℂ)⁻¹ • (𝒰.U t x.1 - x.1)) y.1 := by
          rw [inner_smul_left]
      _ = starRingEnd ℂ (Complex.I : ℂ)⁻¹ * (starRingEnd ℂ (t : ℂ)⁻¹ *
          @inner ℂ H _ (𝒰.U t x.1 - x.1) y.1) := by rw [inner_smul_left]
      _ = Complex.I * ((t : ℂ)⁻¹ * @inner ℂ H _ (𝒰.U t x.1 - x.1) y.1) := by
          rw [hI_inv]
          simp only [map_neg, Complex.conj_I, neg_neg, map_inv₀, Complex.conj_ofReal]
      _ = Complex.I * ((t : ℂ)⁻¹ * @inner ℂ H _ x.1 (𝒰.U (-t) y.1 - y.1)) := by
          rw [hinner_sub]
      -- RHS = ⟨x, I⁻¹ • (-t)⁻¹ • (U(-t)y - y)⟩
      -- I⁻¹ * (-t)⁻¹ = -I * (-t⁻¹) = I * t⁻¹
      -- Note: (-(t:ℂ))⁻¹ = -((t:ℂ)⁻¹) by neg_inv.symm
      _ = (Complex.I : ℂ)⁻¹ * ((-(t : ℂ))⁻¹ * @inner ℂ H _ x.1 (𝒰.U (-t) y.1 - y.1)) := by
          have h2 : (-(t : ℂ))⁻¹ = -((t : ℂ)⁻¹) := neg_inv.symm
          rw [hI_inv, h2]
          ring
      _ = (Complex.I : ℂ)⁻¹ * @inner ℂ H _ x.1 ((-(t : ℂ))⁻¹ • (𝒰.U (-t) y.1 - y.1)) := by
          rw [← inner_smul_right]
      _ = @inner ℂ H _ x.1 ((Complex.I : ℂ)⁻¹ • ((-(t : ℂ))⁻¹ • (𝒰.U (-t) y.1 - y.1))) := by
          rw [← inner_smul_right]
      _ = @inner ℂ H _ x.1 ((Complex.I : ℂ)⁻¹ • ((-t)⁻¹ • (𝒰.U (-t) y.1 - y.1))) := by
          -- Convert (-(t:ℂ))⁻¹ to real scalar mult: (-(t:ℂ))⁻¹ = ((-t):ℂ)⁻¹ = (((-t)⁻¹):ℂ)
          have h3 : (-(t : ℂ))⁻¹ = (((-t)⁻¹ : ℝ) : ℂ) := by
            rw [← Complex.ofReal_neg, Complex.ofReal_inv]
          rw [h3, hreal_smul]

  -- Substitution: t ↦ -t maps nhdsWithin 0 {0}ᶜ to itself
  have h_neg_tendsto : Tendsto (fun t : ℝ => -t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) := by
        have := continuous_neg.tendsto (0 : ℝ)
        rwa [neg_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      exact neg_ne_zero.mpr ht

  -- The function for ⟨Ax, y⟩ composed with negation equals the function for ⟨x, Ay⟩
  have hsubst : Tendsto (fun t : ℝ =>
      @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x.1 - x.1))) y.1)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (@inner ℂ H _ x.1 (𝒰.generatorApply y.1 hy_mem))) := by
    -- Use halg to relate to the Ay function composed with negation
    have hf_neg := hAy_inner.comp h_neg_tendsto
    -- hf_neg : Tendsto (fun t => ⟨x, I⁻¹ • (-t)⁻¹ • (U(-t)y - y)⟩) (𝓝[≠] 0) (𝓝 ⟨x, Ay⟩)
    -- By halg, for t ≠ 0: ⟨I⁻¹ • t⁻¹ • (U(t)x - x), y⟩ = ⟨x, I⁻¹ • (-t)⁻¹ • (U(-t)y - y)⟩
    refine hf_neg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
    -- Goal: (inner x (I⁻¹ • (·)⁻¹ • (U(·)y - y)) ∘ Neg.neg) t = inner (I⁻¹ • t⁻¹ • (U(t)x - x)) y
    show @inner ℂ H _ x.1 ((Complex.I : ℂ)⁻¹ • ((-t)⁻¹ • (𝒰.U (-t) y.1 - y.1))) =
      @inner ℂ H _ ((Complex.I : ℂ)⁻¹ • (t⁻¹ • (𝒰.U t x.1 - x.1))) y.1
    exact (halg t ht).symm

  -- By uniqueness of limits (Hilbert space is T2/Hausdorff)
  exact tendsto_nhds_unique hAx_inner hsubst

/-- U(t) maps dom(A) into dom(A). -/
theorem generator_U_mem (s : ℝ) (x : H) (hx : x ∈ 𝒰.generatorDomain) :
    𝒰.U s x ∈ 𝒰.generatorDomain := by
  obtain ⟨Ax, hAx⟩ := hx
  use 𝒰.U s Ax
  -- Show: I⁻¹ • h⁻¹ • (U(h)(U(s)x) - U(s)x) → U(s)(Ax)
  have hconv : Tendsto (fun h : ℝ => 𝒰.U s ((Complex.I : ℂ)⁻¹ • (h⁻¹ • (𝒰.U h x - x))))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (𝒰.U s Ax)) :=
    (𝒰.U s).cont.continuousAt.tendsto.comp hAx
  refine hconv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h _
  have hgroup : 𝒰.U h (𝒰.U s x) = 𝒰.U s (𝒰.U h x) := by
    rw [← ContinuousLinearMap.comp_apply, ← 𝒰.add h s,
        ← ContinuousLinearMap.comp_apply, ← 𝒰.add s h, add_comm]
  show 𝒰.U s ((Complex.I : ℂ)⁻¹ • (h⁻¹ • (𝒰.U h x - x))) =
      (Complex.I : ℂ)⁻¹ • (h⁻¹ • (𝒰.U h (𝒰.U s x) - 𝒰.U s x))
  rw [hgroup]
  simp only [map_sub, map_smul, ContinuousLinearMap.map_smul_of_tower]

/-- A(U(t)x) = U(t)(Ax) for x ∈ dom(A). -/
theorem generator_U_commute (s : ℝ) (x : H) (hx : x ∈ 𝒰.generatorDomain) :
    𝒰.generatorApply (𝒰.U s x) (𝒰.generator_U_mem s x hx) =
    𝒰.U s (𝒰.generatorApply x hx) := by
  have hAx_lim := 𝒰.generatorApply_spec (𝒰.U s x) (𝒰.generator_U_mem s x hx)
  have hAx2 : Tendsto (fun h : ℝ =>
      (Complex.I : ℂ)⁻¹ • (h⁻¹ • (𝒰.U h (𝒰.U s x) - 𝒰.U s x)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (𝒰.U s (𝒰.generatorApply x hx))) := by
    have hconv := (𝒰.U s).cont.continuousAt.tendsto.comp (𝒰.generatorApply_spec x hx)
    refine hconv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h _
    have hgroup : 𝒰.U h (𝒰.U s x) = 𝒰.U s (𝒰.U h x) := by
      rw [← ContinuousLinearMap.comp_apply, ← 𝒰.add h s,
          ← ContinuousLinearMap.comp_apply, ← 𝒰.add s h, add_comm]
    show 𝒰.U s (Complex.I⁻¹ • h⁻¹ • (𝒰.U h x - x)) =
        Complex.I⁻¹ • h⁻¹ • (𝒰.U h (𝒰.U s x) - 𝒰.U s x)
    rw [map_smul, ContinuousLinearMap.map_smul_of_tower, map_sub, hgroup]
  exact tendsto_nhds_unique hAx_lim hAx2

/-- If a bounded operator commutes with the whole one-parameter group, then it
preserves the generator domain. -/
theorem generatorDomain_mem_of_commutes (A : H →L[ℂ] H)
    (hcomm : ∀ t : ℝ, A ∘L 𝒰.U t = 𝒰.U t ∘L A) :
    ∀ x : H, x ∈ 𝒰.generatorDomain → A x ∈ 𝒰.generatorDomain := by
  intro x ⟨Gx, hGx⟩
  -- Need: lim_{t→0⁺} (U(t)(Ax) - Ax)/(it) exists.
  -- Since A commutes with U(t): U(t)(Ax) = A(U(t)x).
  -- So (U(t)(Ax) - Ax)/(it) = A((U(t)x - x)/(it)) → A(Gx).
  use A Gx
  have hcomm_pt : ∀ t : ℝ, 𝒰.U t (A x) = A (𝒰.U t x) := by
    intro t
    have := ContinuousLinearMap.ext_iff.mp (hcomm t) x
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this.symm
  -- The generator limit for Ax: I⁻¹ • t⁻¹ • (U(t)(Ax) - Ax) → A(Gx)
  -- Since A commutes with U(t) and is continuous linear:
  -- A(I⁻¹ • t⁻¹ • (U(t)x - x)) → A(Gx) by continuity of A
  have hA_cont : Filter.Tendsto
      (fun t : ℝ => A (Complex.I⁻¹ • t⁻¹ • (𝒰.U t x - x)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (A Gx)) :=
    A.cont.continuousAt.tendsto.comp hGx
  refine hA_cont.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  -- Goal: A(I⁻¹ • t⁻¹ • (U(t)x - x)) = I⁻¹ • t⁻¹ • (U(t)(Ax) - Ax)
  show A (Complex.I⁻¹ • (t⁻¹ • (𝒰.U t x - x))) = _
  rw [A.map_smul, A.map_smul_of_tower, A.map_sub, hcomm_pt]

/-- If a bounded operator commutes with the whole one-parameter group, then it
commutes with the infinitesimal generator on the generator domain. -/
theorem generatorApply_commute_of_commutes (A : H →L[ℂ] H)
    (hcomm : ∀ t : ℝ, A ∘L 𝒰.U t = 𝒰.U t ∘L A) :
    ∀ x (hx : x ∈ 𝒰.generatorDomain),
      𝒰.generatorApply (A x)
        (𝒰.generatorDomain_mem_of_commutes A hcomm x hx) =
      A (𝒰.generatorApply x hx) := by
  intro x hx
  -- generatorApply is the unique limit of (U(t)y - y)/(it).
  -- For y = Ax: the limit is A(Gx) (proved in generatorDomain_mem_of_commutes).
  -- For y = x: the limit is Gx, so A(Gx) is what we want.
  -- Both are determined by tendsto_nhds_unique.
  have hGx := 𝒰.generatorApply_spec x hx
  have hGAx := 𝒰.generatorApply_spec (A x) (𝒰.generatorDomain_mem_of_commutes A hcomm x hx)
  -- A(Gx) is also a limit of (U(t)(Ax) - Ax)/(it) by continuity of A
  have hcomm_pt : ∀ t : ℝ, 𝒰.U t (A x) = A (𝒰.U t x) := by
    intro t
    have := ContinuousLinearMap.ext_iff.mp (hcomm t) x
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this.symm
  have hA_limit : Filter.Tendsto
      (fun t : ℝ => Complex.I⁻¹ • (t⁻¹ • (𝒰.U t (A x) - A x)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (A (𝒰.generatorApply x hx))) := by
    have : Filter.Tendsto
        (fun t : ℝ => A (Complex.I⁻¹ • (t⁻¹ • (𝒰.U t x - x))))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (A (𝒰.generatorApply x hx))) :=
      A.cont.continuousAt.tendsto.comp hGx
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t _
    show A (Complex.I⁻¹ • (t⁻¹ • (𝒰.U t x - x))) = _
    rw [A.map_smul, A.map_smul_of_tower, A.map_sub, hcomm_pt]
  exact tendsto_nhds_unique hGAx hA_limit

/-- U(t) preserves dom(A*) and commutes with A*:
    For v ∈ dom(A*), U(t)v ∈ dom(A*) and A*(U(t)v) = U(t)(A*v). -/
theorem generator_U_adjoint_invariant (s : ℝ) (v : H)
    (hv : v ∈ 𝒰.generator.adjointDomain) :
    𝒰.U s v ∈ 𝒰.generator.adjointDomain := by
  -- Need: ∃ C, ∀ x : dom(A), ‖⟨Ax, U(s)v⟩‖ ≤ C * ‖x‖
  obtain ⟨C, hC⟩ := hv
  use C
  intro x
  -- ⟨Ax, U(s)v⟩ = ⟨U(-s)(Ax), v⟩  (adjoint of U(s))
  have hadj : @inner ℂ H _ (𝒰.generator x) (𝒰.U s v) =
      @inner ℂ H _ (𝒰.U (-s) (𝒰.generator x)) v := by
    have h := ContinuousLinearMap.adjoint_inner_left (𝒰.U s) v (𝒰.generator x)
    rw [← 𝒰.neg s] at h; exact h.symm
  rw [hadj]
  -- U(-s)(Ax) = A(U(-s)x) by U-invariance
  have hx_mem : (x : H) ∈ 𝒰.generatorDomain := by
    rw [← 𝒰.generatorDomainSubmodule_carrier]; exact x.2
  have hmem := 𝒰.generator_U_mem (-s) (x : H) hx_mem
  have hcomm := 𝒰.generator_U_commute (-s) (x : H) hx_mem
  -- U(-s)(Ax) = A(U(-s)x), i.e., U(-s)(generator x) = generator(U(-s)x)
  have hmem' : 𝒰.U (-s) (x : H) ∈ 𝒰.generator.domain := by
    change _ ∈ (𝒰.generatorDomainSubmodule : Set H)
    rw [𝒰.generatorDomainSubmodule_carrier]; exact hmem
  have hUsxGen : 𝒰.U (-s) (𝒰.generator x) = 𝒰.generator ⟨𝒰.U (-s) (x : H), hmem'⟩ := by
    show 𝒰.U (-s) (𝒰.generatorApply (x : H) _) =
        𝒰.generatorApply (𝒰.U (-s) (x : H)) _
    exact hcomm.symm
  rw [hUsxGen]
  have hbound := hC ⟨𝒰.U (-s) (x : H), hmem'⟩
  simp only at hbound
  rwa [𝒰.norm_preserving (-s) (x : H)] at hbound

/-- Adjoint commutation: A*(U(t)v) = U(t)(A*v) for v ∈ dom(A*). -/
theorem generator_adjoint_commute (s : ℝ) (v : 𝒰.generator.adjointDomainSubmodule) :
    𝒰.generator.adjointApply 𝒰.generator_densely_defined
      ⟨𝒰.U s (v : H), 𝒰.generator_U_adjoint_invariant s (v : H) v.2⟩ =
    𝒰.U s (𝒰.generator.adjointApply 𝒰.generator_densely_defined v) := by
  -- By uniqueness: both satisfy ⟨Ax, U(s)v⟩ = ⟨x, ·⟩ for all x ∈ dom(A)
  apply 𝒰.generator.adjoint_unique 𝒰.generator_densely_defined (𝒰.U s (v : H))
  · exact 𝒰.generator.adjointApply_spec 𝒰.generator_densely_defined
      ⟨𝒰.U s (v : H), 𝒰.generator_U_adjoint_invariant s (v : H) v.2⟩
  · intro x
    have hx_mem : (x : H) ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]; exact x.2
    have hmem := 𝒰.generator_U_mem (-s) (x : H) hx_mem
    have hcomm := 𝒰.generator_U_commute (-s) (x : H) hx_mem
    have hmem' : 𝒰.U (-s) (x : H) ∈ 𝒰.generator.domain := by
      change _ ∈ (𝒰.generatorDomainSubmodule : Set H)
      rw [𝒰.generatorDomainSubmodule_carrier]; exact hmem
    -- ⟨Ax, U(s)v⟩ = ⟨U(-s)(Ax), v⟩ = ⟨A(U(-s)x), v⟩ = ⟨U(-s)x, A*v⟩ = ⟨x, U(s)(A*v)⟩
    calc @inner ℂ H _ (𝒰.generator x) (𝒰.U s (v : H))
        = @inner ℂ H _ (𝒰.U (-s) (𝒰.generator x)) (v : H) := by
          have h := ContinuousLinearMap.adjoint_inner_left (𝒰.U s) (v : H) (𝒰.generator x)
          rw [← 𝒰.neg s] at h; exact h.symm
      _ = @inner ℂ H _ (𝒰.generator ⟨𝒰.U (-s) (x : H), hmem'⟩) (v : H) := by
          congr 1; show 𝒰.U (-s) (𝒰.generatorApply _ _) = 𝒰.generatorApply _ _
          exact hcomm.symm
      _ = @inner ℂ H _ (𝒰.U (-s) (x : H))
            (𝒰.generator.adjointApply 𝒰.generator_densely_defined v) := by
          exact 𝒰.generator.adjointApply_spec 𝒰.generator_densely_defined v
            ⟨𝒰.U (-s) (x : H), hmem'⟩
      _ = @inner ℂ H _ (x : H)
            (𝒰.U s (𝒰.generator.adjointApply 𝒰.generator_densely_defined v)) := by
          have h := ContinuousLinearMap.adjoint_inner_left (𝒰.U s)
            (𝒰.generator.adjointApply 𝒰.generator_densely_defined v) (x : H)
          rwa [← 𝒰.neg s] at h

/-- The function t ↦ U(t)x is differentiable with derivative I • U(t)(Ax) for x ∈ dom(A).
    This is the fundamental fact that the generator of U determines the derivative of U(t)x. -/
theorem generator_hasDerivAt (x : H) (hx : x ∈ 𝒰.generatorDomain) (t : ℝ) :
    HasDerivAt (fun s => 𝒰.U s x) (Complex.I • 𝒰.U t (𝒰.generatorApply x hx)) t := by
  set Ax := 𝒰.generatorApply x hx
  -- Slope at 0: h⁻¹ • (U(h)x - x) → I • Ax on nhdsWithin
  have hslope : Tendsto (fun s : ℝ => s⁻¹ • (𝒰.U s x - x))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (Complex.I • Ax)) := by
    have hgen := (𝒰.generatorApply_spec x hx).const_smul (Complex.I : ℂ)
    simp only [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul] at hgen
    exact hgen
  -- Use slope characterization: HasDerivAt at t ↔ slope at t converges
  rw [hasDerivAt_iff_tendsto_slope_zero]
  -- Rewrite slope at t as U(t) composed with slope at 0
  have hfn_eq : (fun h : ℝ => h⁻¹ • (𝒰.U (t + h) x - 𝒰.U t x)) =
      (fun h : ℝ => 𝒰.U t (h⁻¹ • (𝒰.U h x - x))) := by
    ext h
    rw [𝒰.add t h, ContinuousLinearMap.comp_apply, ← map_sub,
        ← ContinuousLinearMap.map_smul_of_tower]
  rw [hfn_eq, show Complex.I • 𝒰.U t Ax = 𝒰.U t (Complex.I • Ax) from (map_smul _ _ _).symm]
  exact (𝒰.U t).cont.continuousAt.tendsto.comp hslope

/-- Integral formula: U(t)x - x = I • ∫₀ᵗ U(s)(Ax) ds for x ∈ dom(A).
    This follows from FTC applied to d/ds U(s)x = I • U(s)(Ax). -/
theorem generator_integral_formula (x : H) (hx : x ∈ 𝒰.generatorDomain) (t : ℝ) :
    𝒰.U t x - x = ∫ s in (0 : ℝ)..t,
      Complex.I • 𝒰.U s (𝒰.generatorApply x hx) := by
  set Ax := 𝒰.generatorApply x hx
  set f' : ℝ → H := fun s => Complex.I • 𝒰.U s Ax
  have hcont : Continuous f' := continuous_const.smul (𝒰.continuous Ax)
  have hint : IntervalIntegrable f' MeasureTheory.volume 0 t :=
    hcont.intervalIntegrable 0 t
  have hderiv : ∀ s ∈ Set.uIcc 0 t, HasDerivAt (fun u => 𝒰.U u x) (f' s) s :=
    fun s _ => 𝒰.generator_hasDerivAt x hx s
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- h : ∫ s in 0..t, f' s = U(t)x - U(0)x
  rw [𝒰.zero, ContinuousLinearMap.one_apply] at h
  exact h.symm

/-- If xₙ → x and Axₙ → y (where each xₙ ∈ dom(A)), then x ∈ dom(A) and Ax = y.
    This is the sequential closedness of the generator graph, proved via the integral formula. -/
theorem generator_seq_closed {seq : ℕ → H} {x y : H}
    (hseq_dom : ∀ n, seq n ∈ 𝒰.generatorDomain)
    (hseq_x : Tendsto seq atTop (𝓝 x))
    (hseq_y : Tendsto (fun n => 𝒰.generatorApply (seq n) (hseq_dom n)) atTop (𝓝 y)) :
    x ∈ 𝒰.generatorDomain := by
  use y
  -- Define G(t) = ∫₀ᵗ U(s)y ds
  set G : ℝ → H := fun t => ∫ s in (0 : ℝ)..t, 𝒰.U s y with hG_def
  have hcont_y : Continuous (fun s : ℝ => 𝒰.U s y) := 𝒰.continuous y
  have hint_y : ∀ a b : ℝ, IntervalIntegrable (fun s => 𝒰.U s y) MeasureTheory.volume a b :=
    fun a b => hcont_y.intervalIntegrable a b
  have hG_FTC : ∀ u : ℝ, HasDerivAt G (𝒰.U u y) u :=
    fun u => intervalIntegral.integral_hasDerivAt_right (hint_y 0 u)
      hcont_y.aestronglyMeasurable.stronglyMeasurableAtFilter hcont_y.continuousAt
  have hG0 : G 0 = 0 := by simp [hG_def, intervalIntegral.integral_same]
  -- Key: U(t)x - x = I • G(t) for all t (from integral formula + limit)
  have hformula : ∀ t : ℝ, 𝒰.U t x - x = Complex.I • G t := by
    intro t
    -- For each n, integral formula gives:
    -- U(t)(seq n) - seq n = ∫₀ᵗ I • U(s)(Aₙ) ds = I • ∫₀ᵗ U(s)(Aₙ) ds
    set Aₙ := fun n => 𝒰.generatorApply (seq n) (hseq_dom n)
    have hfn : ∀ n, 𝒰.U t (seq n) - seq n =
        Complex.I • ∫ s in (0 : ℝ)..t, 𝒰.U s (Aₙ n) := by
      intro n
      rw [𝒰.generator_integral_formula (seq n) (hseq_dom n) t,
          intervalIntegral.integral_smul]
    -- LHS: U(t)(seq n) - seq n → U(t)x - x
    have hLHS : Tendsto (fun n => 𝒰.U t (seq n) - seq n) atTop (𝓝 (𝒰.U t x - x)) :=
      (((𝒰.U t).cont.tendsto x).comp hseq_x).sub hseq_x
    -- RHS integrals: ∫₀ᵗ U(s)(Aₙ) ds → G(t) = ∫₀ᵗ U(s)y ds
    -- by uniform estimate ‖∫₀ᵗ U(s)(Aₙ - y) ds‖ ≤ |t| • ‖Aₙ - y‖ → 0
    have hintconv : Tendsto (fun n => ∫ s in (0 : ℝ)..t, 𝒰.U s (Aₙ n)) atTop (𝓝 (G t)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have ht1 : (0 : ℝ) < |t| + 1 := by linarith [abs_nonneg t]
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hseq_y (ε / (|t| + 1)) (div_pos hε ht1)
      use N
      intro n hn
      rw [dist_eq_norm,
        show (∫ s in (0 : ℝ)..t, 𝒰.U s (Aₙ n)) - G t =
          ∫ s in (0 : ℝ)..t, (𝒰.U s (Aₙ n) - 𝒰.U s y) from by
        rw [← intervalIntegral.integral_sub
          ((𝒰.continuous _).intervalIntegrable 0 t) (hcont_y.intervalIntegrable 0 t)]]
      simp_rw [← map_sub (𝒰.U _)]
      have hbound : ‖Aₙ n - y‖ < ε / (|t| + 1) := by
        rw [← dist_eq_norm]; exact hN n hn
      calc ‖∫ s in (0 : ℝ)..t, 𝒰.U s (Aₙ n - y)‖
          ≤ ‖Aₙ n - y‖ * |t - 0| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro s _; exact le_of_eq (𝒰.norm_preserving s _)
        _ ≤ ε / (|t| + 1) * |t| := by
            rw [sub_zero]; exact mul_le_mul_of_nonneg_right (le_of_lt hbound) (abs_nonneg t)
        _ < ε := by
            have : ε / (|t| + 1) * |t| < ε / (|t| + 1) * (|t| + 1) :=
              mul_lt_mul_of_pos_left (by linarith : |t| < |t| + 1) (div_pos hε ht1)
            rwa [div_mul_cancel₀ ε (ne_of_gt ht1)] at this
    -- Combine: I • ∫₀ᵗ U(s)(Aₙ) ds → I • G(t)
    have hRHS : Tendsto (fun n => Complex.I • ∫ s in (0 : ℝ)..t, 𝒰.U s (Aₙ n))
        atTop (𝓝 (Complex.I • G t)) :=
      (continuous_const_smul Complex.I).continuousAt.tendsto.comp hintconv
    exact tendsto_nhds_unique (hLHS.congr (fun n => hfn n)) hRHS
  -- From U(t)x - x = I • G(t), show the generator limit converges to y
  have hG_deriv_0 : HasDerivAt G y 0 := by
    convert hG_FTC 0 using 1; simp [𝒰.zero, ContinuousLinearMap.one_apply]
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • G t) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (𝓝 y) := by
    have := hG_deriv_0.tendsto_slope_zero
    simp only [zero_add, hG0, sub_zero] at this
    exact this
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
  -- Need: I⁻¹ • (t⁻¹ • (U(t)x - x)) = t⁻¹ • G t
  rw [hformula t, smul_comm (t⁻¹ : ℝ) (Complex.I : ℂ) (G t),
      smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]

/-- The generator is self-adjoint (not just symmetric).

    Proof: Show graph(A) = graph(A*) using eq_of_graph_eq.
    graph(A) ⊆ graph(A*) from symmetry.
    graph(A*) ⊆ graph(A): for v ∈ dom(A*) with A*v = z,
    show v ∈ dom(A) using ker(A* ± i) = {0} and Ran(A - i) = H. -/
theorem generator_selfadjoint : 𝒰.generator.IsSelfAdjoint 𝒰.generator_densely_defined := by
  -- Use eq_of_graph_eq: show graph(A) = graph(A*)
  apply UnboundedOperator.eq_of_graph_eq
  ext p
  constructor
  · -- graph(A) ⊆ graph(A*) from symmetry
    intro hp
    obtain ⟨x, hx1, hx2⟩ := hp
    -- x ∈ dom(A), (x:H) = p.1, Ax = p.2
    -- Need to show p ∈ graph(A*)
    have hx_adj : (x : H) ∈ 𝒰.generator.adjointDomain := by
      use ‖𝒰.generator x‖
      intro z
      rw [𝒰.generator_symmetric z x]
      calc ‖@inner ℂ H _ (z : H) (𝒰.generator x)‖
          ≤ ‖(z : H)‖ * ‖𝒰.generator x‖ := norm_inner_le_norm _ _
        _ = ‖𝒰.generator x‖ * ‖(z : H)‖ := mul_comm _ _
    let x' : 𝒰.generator.adjointDomainSubmodule := ⟨(x : H), hx_adj⟩
    use x'
    constructor
    · exact hx1
    · rw [← hx2]
      apply 𝒰.generator.adjoint_unique 𝒰.generator_densely_defined (x : H)
      · exact 𝒰.generator.adjointApply_spec 𝒰.generator_densely_defined x'
      · intro z
        exact 𝒰.generator_symmetric z x
  · -- graph(A*) ⊆ graph(A): the hard direction
    intro hp
    obtain ⟨y, hy1, hy2⟩ := hp
    -- y ∈ dom(A*), (y:H) = p.1, A*y = p.2
    -- Need to show p ∈ graph(A), i.e., p.1 ∈ dom(A) and A(p.1) = p.2
    -- Key: show (y:H) ∈ generatorDomain using ker(A* - i) = {0} argument
    -- The ODE argument shows: for v with A*v = αiv (α = ±1),
    -- ⟨U(t)x, v⟩ = eᵅᵗ⟨x, v⟩ for all x ∈ dom(A)
    -- This is bounded, forcing ⟨x, v⟩ = 0 for all x, hence v = 0.

    -- Helper: ODE argument for kernel triviality.
    -- For w with A*w = α·i·w (where α = -1 or +1), show w = 0.
    -- Proof: g(t) = ⟨U(t)x, w⟩ satisfies g' = α·g, hence g(t) = g(0)·exp(α·t).
    -- Since |g(t)| ≤ ‖x‖·‖w‖ for all t and exp is unbounded, g(0) = 0.
    have hker_ode : ∀ (α : ℂ) (_ : α = Complex.I ∨ α = -Complex.I),
        ∀ w : H, ∀ hw : w ∈ 𝒰.generator.adjointDomain,
        𝒰.generator.adjointApply 𝒰.generator_densely_defined
          ⟨w, hw⟩ = α • w → w = 0 := by
      intro α hα w hw hw_eq
      suffices h : ∀ x ∈ 𝒰.generatorDomain, @inner ℂ H _ x w = 0 by
        rw [← inner_self_eq_zero (𝕜 := ℂ)]
        have hw_orth : w ∈ 𝒰.generator.domain.orthogonal := by
          rw [Submodule.mem_orthogonal]
          intro z hz
          exact h z (𝒰.generatorDomainSubmodule_carrier ▸ hz)
        have horth_bot : 𝒰.generator.domain.orthogonal = ⊥ :=
          Submodule.topologicalClosure_eq_top_iff.mp 𝒰.generator_densely_defined
        rw [horth_bot, Submodule.mem_bot] at hw_orth
        rw [hw_orth, inner_self_eq_zero]
      intro x hx
      -- Define g(t) = ⟨U(t)x, w⟩
      set g : ℝ → ℂ := fun t => @inner ℂ H _ (𝒰.U t x) w
      set Ax := 𝒰.generatorApply x hx
      -- Step A: g'(t) = ⟨I • U(t)(Ax), w⟩ using HasDerivAt.inner
      have hg_inner_deriv : ∀ t : ℝ,
          HasDerivAt g (@inner ℂ H _ (Complex.I • 𝒰.U t Ax) w) t := by
        intro t
        have hU := 𝒰.generator_hasDerivAt x hx t
        have := HasDerivAt.inner ℂ hU (hasDerivAt_const t w)
        simp only [inner_zero_right, zero_add] at this
        exact this
      -- Step B: Compute ⟨I • U(t)(Ax), w⟩ = -α * g(t) algebraically.
      -- Chain: ⟨I•U(t)(Ax), w⟩ = conj(I) * ⟨U(t)(Ax), w⟩ = -I * ⟨U(t)(Ax), w⟩
      -- ⟨U(t)(Ax), w⟩ = ⟨Ax, U(-t)w⟩ = ⟨x, A*(U(-t)w)⟩ = ⟨x, U(-t)(A*w)⟩ = ⟨x, U(-t)(αw)⟩
      -- = α * ⟨x, U(-t)w⟩ = α * ⟨U(t)x, w⟩ = α * g(t)
      -- So ⟨I•U(t)(Ax), w⟩ = -I * α * g(t) = -α * I * g(t)... hmm let me be careful.
      -- ⟨I•v, w⟩ = conj(I) * ⟨v, w⟩ = -I * ⟨v, w⟩ (conjugate-linear in first arg)
      -- So ⟨I•U(t)(Ax), w⟩ = -I * ⟨U(t)(Ax), w⟩ = -I * α * g(t)
      have hderiv_eq : ∀ t : ℝ,
          @inner ℂ H _ (Complex.I • 𝒰.U t Ax) w = -Complex.I * α * g t := by
        intro t
        -- Step 1: Pull out I from inner product
        have h1 : @inner ℂ H _ (Complex.I • 𝒰.U t Ax) w =
            -Complex.I * @inner ℂ H _ (𝒰.U t Ax) w := by
          rw [inner_smul_left, Complex.conj_I]
        -- Step 2: Use U(t)* = U(-t)
        have h2 : @inner ℂ H _ (𝒰.U t Ax) w =
            @inner ℂ H _ Ax (𝒰.U (-t) w) := by
          rw [← ContinuousLinearMap.adjoint_inner_right, 𝒰.neg t]
        -- Step 3: Adjoint relation ⟨Ax, U(-t)w⟩ = ⟨x, A*(U(-t)w)⟩
        have hUtw_adj := 𝒰.generator_U_adjoint_invariant (-t) w hw
        have hx_dom : x ∈ 𝒰.generator.domain := by
          change x ∈ (𝒰.generatorDomainSubmodule : Set H)
          rw [𝒰.generatorDomainSubmodule_carrier]; exact hx
        have h3 : @inner ℂ H _ Ax (𝒰.U (-t) w) =
            @inner ℂ H _ x (𝒰.generator.adjointApply 𝒰.generator_densely_defined
              ⟨𝒰.U (-t) w, hUtw_adj⟩) :=
          𝒰.generator.adjointApply_spec 𝒰.generator_densely_defined
            ⟨𝒰.U (-t) w, hUtw_adj⟩ ⟨x, hx_dom⟩
        -- Step 4: A*(U(-t)w) = U(-t)(A*w) = U(-t)(αw) = α • U(-t)w
        have hadj_comm := 𝒰.generator_adjoint_commute (-t) ⟨w, hw⟩
        have h4 : 𝒰.generator.adjointApply 𝒰.generator_densely_defined
            ⟨𝒰.U (-t) w, hUtw_adj⟩ = α • 𝒰.U (-t) w := by
          rw [hadj_comm, hw_eq, (𝒰.U (-t)).map_smul]
        -- Step 5: ⟨x, α•U(-t)w⟩ = α * ⟨x, U(-t)w⟩
        have h5 : @inner ℂ H _ x (α • 𝒰.U (-t) w) =
            α * @inner ℂ H _ x (𝒰.U (-t) w) := by rw [inner_smul_right]
        -- Step 6: ⟨x, U(-t)w⟩ = ⟨U(t)x, w⟩ = g(t)
        have h6 : @inner ℂ H _ x (𝒰.U (-t) w) = g t := by
          rw [𝒰.neg t, ContinuousLinearMap.adjoint_inner_right]
        -- Chain everything together
        rw [h1, h2, h3, h4, h5, h6]; ring
      -- Step C: So g'(t) = -I * α * g(t). Define ψ(t) = exp(I*α*t) * g(t), show ψ' = 0.
      -- For α = I: -I * α = -I * I = -I² = 1, so g' = g, ψ = exp(-t) * g
      -- For α = -I: -I * α = -I * (-I) = I² = -1, so g' = -g, ψ = exp(t) * g
      have hg_deriv : ∀ t : ℝ, HasDerivAt g (-Complex.I * α * g t) t := by
        intro t
        exact (hg_inner_deriv t).congr_deriv (hderiv_eq t)
      -- Define ψ(t) = exp(I * α * t) * g(t) where I * α cancels with -I * α in g'
      set β : ℂ := Complex.I * α  -- the "eigenvalue" to cancel
      -- g' = -β * g, so (exp(β·t) * g)' = β*exp(β·t)*g + exp(β·t)*(-β*g) = 0
      set ψ : ℝ → ℂ := fun t => Complex.exp (β * (t : ℂ)) * g t
      -- HasDerivAt for exp(β·t) as function ℝ → ℂ
      have hexp_deriv : ∀ t : ℝ,
          HasDerivAt (fun s : ℝ => Complex.exp (β * (s : ℂ))) (β * Complex.exp (β * (t : ℂ))) t := by
        intro t
        have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t :=
          Complex.ofRealCLM.hasDerivAt
        have h2 : HasDerivAt (fun s : ℝ => β * (s : ℂ)) (β * 1) t := h1.const_mul β
        simp only [mul_one] at h2
        exact (Complex.hasDerivAt_exp (β * (t : ℂ))).scomp t h2
      -- HasDerivAt for ψ using product rule
      have hpsi_deriv : ∀ t : ℝ, HasDerivAt ψ 0 t := by
        intro t
        have hmul := (hexp_deriv t).mul (hg_deriv t)
        -- hmul : HasDerivAt ψ (β*exp(β*t)*g(t) + exp(β*t)*(-β*g(t))) t
        -- = HasDerivAt ψ 0 t since the two terms cancel
        convert hmul using 1
        ring
      -- ψ is differentiable with zero derivative, hence constant
      have hpsi_const : ∀ s t : ℝ, ψ s = ψ t := by
        have hdiff : Differentiable ℝ ψ :=
          fun t => (hpsi_deriv t).differentiableAt
        have hderiv0 : ∀ t, deriv ψ t = 0 :=
          fun t => (hpsi_deriv t).deriv
        exact is_const_of_deriv_eq_zero hdiff hderiv0
      -- ψ(t) = ψ(0) for all t, i.e., exp(β·t) * g(t) = 1 * g(0) = g(0)
      have hpsi_eq : ∀ t : ℝ, Complex.exp (β * (t : ℂ)) * g t = g 0 := by
        intro t
        have := hpsi_const t 0
        simp only [ψ, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at this
        exact this
      -- Step D: g(t) = exp(-β·t) * g(0). Bounded implies g(0) = 0.
      -- |g(t)| ≤ ‖U(t)x‖ * ‖w‖ = ‖x‖ * ‖w‖
      have hg_bound : ∀ t : ℝ, ‖g t‖ ≤ ‖x‖ * ‖w‖ := by
        intro t
        calc ‖g t‖ = ‖@inner ℂ H _ (𝒰.U t x) w‖ := rfl
          _ ≤ ‖𝒰.U t x‖ * ‖w‖ := norm_inner_le_norm _ _
          _ = ‖x‖ * ‖w‖ := by rw [𝒰.norm_preserving]
      -- From ψ(t) = g(0): exp(β·t) * g(t) = g(0)
      -- So g(t) = exp(-β·t) * g(0) (multiply both sides by exp(-β·t))
      -- |g(t)| = |exp(-β·t)| * |g(0)|
      -- For α = I: β = I*I = -1, so -β = 1, exp(-β·t) = exp(t) → ∞ as t → +∞
      -- For α = -I: β = I*(-I) = 1, so -β = -1, exp(-β·t) = exp(-t) → ∞ as t → -∞
      -- In either case, exp(-β·t) is unbounded, so g(0) = 0.
      -- Since β = I*α and α² = -1 (for α = ±I), |exp(β·t)| = exp(Re(β·t))
      -- For α = I: β = -1, exp(β·t) = exp(-t), |exp(β·t)| = exp(-t), exp(β·t) → ∞ as t → -∞
      -- For α = -I: β = 1, exp(β·t) = exp(t), |exp(β·t)| = exp(t) → ∞ as t → +∞
      -- From hpsi_eq: |exp(β·t)| * |g(t)| = |g(0)|
      -- Combined with |g(t)| ≤ M: |g(0)| = |exp(β·t)| * |g(t)| ≤ |exp(β·t)| * M
      -- Wait that's the wrong direction. Let me use: |g(0)| ≤ M (from hg_bound at t=0)
      -- And exp(β·t) * g(t) = g(0) ⟹ g(t) = exp(-β·t) * g(0)
      -- ⟹ |g(t)| = |exp(-β·t)| * |g(0)|
      -- For large |exp(-β·t)|: |g(t)| = |exp(-β·t)| * |g(0)| ≤ M
      -- ⟹ |g(0)| ≤ M / |exp(-β·t)| → 0 as |exp(-β·t)| → ∞
      -- ⟹ g(0) = 0.
      by_contra hg0_ne
      -- g(0) = ⟨U(0)x, w⟩ = ⟨x, w⟩
      have hg0_eq : g 0 = @inner ℂ H _ x w := by
        simp [g, 𝒰.zero, ContinuousLinearMap.one_apply]
      -- g(0) ≠ 0
      have hg0_ne' : g 0 ≠ 0 := hg0_eq ▸ hg0_ne
      have hg0_pos : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0_ne'
      -- β = I * α is either -1 or 1
      have hβ : β = -1 ∨ β = 1 := by
        rcases hα with rfl | rfl
        · left; simp [β]
        · right; simp [β]
      -- From hpsi_eq and hg_bound: ‖g(0)‖ ≤ ‖exp(β·t)‖ * M for all t
      set M := ‖x‖ * ‖w‖
      have hineq : ∀ t : ℝ, ‖g 0‖ ≤ ‖Complex.exp (β * (t : ℂ))‖ * M := by
        intro t
        calc ‖g 0‖ = ‖Complex.exp (β * (t : ℂ)) * g t‖ := by rw [← hpsi_eq t]
          _ = ‖Complex.exp (β * (t : ℂ))‖ * ‖g t‖ := norm_mul _ _
          _ ≤ ‖Complex.exp (β * (t : ℂ))‖ * M :=
              mul_le_mul_of_nonneg_left (hg_bound t) (norm_nonneg _)
      -- M > 0 since ‖g 0‖ > 0 and ‖g 0‖ ≤ ‖exp(0)‖ * M = M
      have hM_pos : 0 < M := by
        have := hineq 0
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, norm_one, one_mul] at this
        linarith
      -- ‖exp(β·t)‖ = exp(Re(β)·t). For β ∈ {-1, 1}, this → 0 for appropriate t direction.
      -- Use ‖exp(β·(±n))‖ = exp(∓n) → 0 for the right sign.
      have hexp_norm : ∀ t : ℝ, ‖Complex.exp (β * (t : ℂ))‖ = Real.exp ((β * (t : ℂ)).re) :=
        fun t => Complex.norm_exp _
      -- For β = -1 or β = 1, we can find t where exp → 0
      rcases hβ with hβ_neg | hβ_pos
      · -- β = -1: ‖exp(-t)‖ = exp(-t) → 0 as t → +∞
        have hexp_val : ∀ n : ℕ, ‖Complex.exp (β * ((n : ℝ) : ℂ))‖ = Real.exp (-(n : ℝ)) := by
          intro n
          rw [hexp_norm, show (β * ((n : ℝ) : ℂ)).re = -(n : ℝ) from by simp [hβ_neg]]
        have hnat_bot : Tendsto (fun n : ℕ => (-(n : ℝ))) atTop atBot :=
          Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
        have htend : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ)) * M) atTop (nhds 0) := by
          have := (Real.tendsto_exp_atBot.comp hnat_bot).mul
            (tendsto_const_nhds (x := M) (f := atTop))
          simp only [zero_mul] at this; exact this
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend (‖g 0‖) hg0_pos
        have hN' := hN N le_rfl
        have := hineq N
        rw [hexp_val] at this
        rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos (Real.exp_pos _) hM_pos)] at hN'
        linarith
      · -- β = 1: ‖exp(-n)‖ = exp(-n) → 0 as n → +∞ (using t = -n)
        have hexp_val : ∀ n : ℕ, ‖Complex.exp (β * ((-(n : ℤ) : ℝ) : ℂ))‖ = Real.exp (-(n : ℝ)) := by
          intro n
          rw [hexp_norm, show (β * ((-(n : ℤ) : ℝ) : ℂ)).re = -(n : ℝ) from by
            simp [hβ_pos]]
        have hnat_bot : Tendsto (fun n : ℕ => (-(n : ℝ))) atTop atBot :=
          Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
        have htend : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ)) * M) atTop (nhds 0) := by
          have := (Real.tendsto_exp_atBot.comp hnat_bot).mul
            (tendsto_const_nhds (x := M) (f := atTop))
          simp only [zero_mul] at this; exact this
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend (‖g 0‖) hg0_pos
        have hN' := hN N le_rfl
        have := hineq (-(N : ℤ))
        rw [hexp_val] at this
        rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos (Real.exp_pos _) hM_pos)] at hN'
        linarith
    -- Step 1: ker(A* + i) = {0} (from ODE with α = -I)
    have hker_add : ∀ w : H, ∀ hw : w ∈ 𝒰.generator.adjointDomain,
        𝒰.generator.adjointApply 𝒰.generator_densely_defined
          ⟨w, hw⟩ = -Complex.I • w → w = 0 :=
      fun w hw heq => hker_ode (-Complex.I) (Or.inr rfl) w hw heq
    -- Step 2: ker(A* - i) = {0} (from ODE with α = I)
    have hker_sub : ∀ w : H, ∀ hw : w ∈ 𝒰.generator.adjointDomain,
        𝒰.generator.adjointApply 𝒰.generator_densely_defined
          ⟨w, hw⟩ = Complex.I • w → w = 0 :=
      fun w hw heq => hker_ode Complex.I (Or.inl rfl) w hw heq
    -- Save the coercion and adjoint value before `set` changes types
    set yH := (y : H) with hyH_def
    set Astar_y := (𝒰.generator.adjoint 𝒰.generator_densely_defined) y
      with hAstar_y_def
    have hy_mem_adj : yH ∈ 𝒰.generator.adjointDomain := by rw [hyH_def]; exact y.2
    have hhy1 : yH = p.1 := hy1
    have hhy2 : Astar_y = p.2 := hy2
    set A := 𝒰.generator with hA_def
    -- Bounded-below: ‖(A-iI)x‖ ≥ ‖x‖ (cross terms cancel by symmetry)
    have hbelow : ∀ x : A.domain,
        ‖(x : H)‖ ≤ ‖A x - Complex.I • (x : H)‖ := by
      intro x
      have hreal := A.symmetric_inner_real 𝒰.generator_symmetric x
      have hcross : RCLike.re (@inner ℂ H _ (A x) (Complex.I • (x : H))) = 0 := by
        rw [inner_smul_right]
        simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.I_re, Complex.I_im]
        rw [hreal]; ring
      have hnorm_ix : ‖Complex.I • (x : H)‖ = ‖(x : H)‖ := by
        rw [norm_smul, Complex.norm_I, one_mul]
      have hexpand : ‖A x - Complex.I • (x : H)‖ ^ 2 =
          ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
        rw [@norm_sub_sq ℂ, hcross, hnorm_ix]; ring
      have hge : ‖(x : H)‖ ^ 2 ≤ ‖A x - Complex.I • (x : H)‖ ^ 2 := by
        rw [hexpand]; linarith [sq_nonneg ‖A x‖]
      nlinarith [sq_nonneg ‖(x : H)‖,
                 sq_nonneg ‖A x - Complex.I • (x : H)‖,
                 norm_nonneg (x : H),
                 norm_nonneg (A x - Complex.I • (x : H))]
    -- ran(A-iI) is closed (bounded below + generator_seq_closed)
    have hran_closed :
        IsClosed (Set.range (fun x : A.domain => A x - Complex.I • (x : H))) := by
      rw [← isSeqClosed_iff_isClosed]
      intro seq w hseq_mem hseq_lim
      choose xseq hxseq using fun n => hseq_mem n
      -- Cauchy by bounded-below
      have hcauchy : CauchySeq (fun n => (xseq n : H)) := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        have hseq_cauchy : CauchySeq seq := hseq_lim.cauchySeq
        rw [Metric.cauchySeq_iff] at hseq_cauchy
        obtain ⟨N, hN⟩ := hseq_cauchy ε hε
        use N
        intro n hn m hm
        have hminus : A (xseq n) - A (xseq m) =
            A (xseq n - xseq m) := by
          have hsub : xseq n - xseq m = xseq n + (-1 : ℂ) • xseq m := by
            simp only [neg_one_smul, sub_eq_add_neg]
          rw [hsub, A.map_add', A.map_smul']
          simp only [neg_one_smul, sub_eq_add_neg]
        have hexpand : (A (xseq n) - A (xseq m)) -
            Complex.I • ((xseq n : H) - (xseq m : H)) =
            (A (xseq n) - Complex.I • (xseq n : H)) -
            (A (xseq m) - Complex.I • (xseq m : H)) := by
          simp only [smul_sub, sub_sub_sub_comm]
        calc dist ((xseq n : H)) ((xseq m : H))
            = ‖(xseq n : H) - (xseq m : H)‖ := dist_eq_norm _ _
          _ ≤ ‖A (xseq n - xseq m) -
                Complex.I • ((xseq n : H) - (xseq m : H))‖ := by
              have := hbelow (xseq n - xseq m)
              simp only [Submodule.coe_sub] at this; exact this
          _ = ‖(A (xseq n) - A (xseq m)) -
                Complex.I • ((xseq n : H) - (xseq m : H))‖ := by
              rw [hminus]
          _ = ‖(A (xseq n) - Complex.I • (xseq n : H)) -
                (A (xseq m) - Complex.I • (xseq m : H))‖ := by
              rw [hexpand]
          _ = ‖seq n - seq m‖ := by
              congr 1; rw [← hxseq n, ← hxseq m]
          _ = dist (seq n) (seq m) := (dist_eq_norm _ _).symm
          _ < ε := hN n hn m hm
      obtain ⟨x_lim, hx_lim⟩ := cauchySeq_tendsto_of_complete hcauchy
      -- Axₙ = seq n + i•xₙ → w + i•x_lim
      have hTx_lim : Tendsto (fun n => A (xseq n)) atTop
          (𝓝 (w + Complex.I • x_lim)) := by
        have h1 : ∀ n, A (xseq n) = seq n + Complex.I • (xseq n : H) := by
          intro n
          have h := hxseq n
          -- h: A (xseq n) - I•(xseq n : H) = seq n
          -- => A (xseq n) = seq n + I•(xseq n : H)
          have := sub_eq_iff_eq_add.mp h
          exact this
        simp only [h1]
        exact hseq_lim.add (Tendsto.const_smul hx_lim Complex.I)
      -- Use generator_seq_closed to get x_lim ∈ dom(A)
      have hxseq_dom : ∀ n, (xseq n : H) ∈ 𝒰.generatorDomain := by
        intro n; rw [← 𝒰.generatorDomainSubmodule_carrier]; exact (xseq n).2
      have hgen_lim : Tendsto
          (fun n => 𝒰.generatorApply (xseq n : H) (hxseq_dom n)) atTop
          (𝓝 (w + Complex.I • x_lim)) := by
        convert hTx_lim using 1
      have hx_dom : x_lim ∈ 𝒰.generatorDomain :=
        𝒰.generator_seq_closed hxseq_dom hx_lim hgen_lim
      have hx_mem : x_lim ∈ A.domain := by
        change x_lim ∈ (𝒰.generatorDomainSubmodule : Set H)
        rw [𝒰.generatorDomainSubmodule_carrier]; exact hx_dom
      -- Az = w + iz by uniqueness of limits
      have hAz_eq : A ⟨x_lim, hx_mem⟩ = w + Complex.I • x_lim := by
        -- generatorApply_spec gives the defining limit
        have h1 := 𝒰.generatorApply_spec x_lim hx_dom
        -- Build convergence to w + I•x_lim from the sequence
        -- The defining limit and the sequence limit are both limits of
        -- I⁻¹ • (t⁻¹ • (U(t)x - x)) as t → 0. The generator_seq_closed
        -- proof used `use (w + I•x_lim)` to witness the existential,
        -- so the defining limit converges to w + I•x_lim.
        -- generatorApply picks the unique limit. We use tendsto_nhds_unique.
        -- Actually, the simplest route: show the generator_seq_closed proof
        -- gives us a convergence proof we can use directly.
        -- Note: A ⟨x_lim, hx_mem⟩ = generatorApply x_lim hx_dom by definition
        -- (up to propositional equality of the membership proof).
        -- generatorApply x_lim hx_dom = Classical.choose hx_dom
        -- hx_dom was proved by generator_seq_closed using `use (w + I•x_lim)`
        -- followed by showing the limit is (w + I•x_lim).
        -- The Classical.choose picks the unique y for which the limit holds,
        -- and by uniqueness of limits, this must be (w + I•x_lim).
        -- We formalize this: we know Tendsto ... (nhds (A ⟨x_lim, hx_mem⟩))
        -- (from generatorApply_spec) and we need to show
        -- Tendsto ... (nhds (w + I•x_lim)). Then unique_lim gives equality.
        -- For the second convergence, we replicate the key argument from
        -- generator_seq_closed: the limit of I⁻¹•t⁻¹•(U(t)x_lim - x_lim)
        -- equals w + I•x_lim. This follows from:
        -- U(t)x_lim - x_lim = I • G(t) where G(t) = ∫₀ᵗ U(s)(w + I•x_lim) ds
        -- and G'(0) = w + I•x_lim.
        -- But that's reproving generator_seq_closed. Instead, let's use the
        -- inner product characterization with density.
        -- For all v ∈ dom(A), ⟨Ax_lim, v⟩ = ⟨x_lim, Av⟩ = lim ⟨xₙ, Av⟩ = lim ⟨Axₙ, v⟩
        -- and lim ⟨Axₙ, v⟩ = ⟨w + I•x_lim, v⟩.
        -- So ⟨Ax_lim, v⟩ = ⟨w + I•x_lim, v⟩ for all v in dense domain.
        -- By density, Ax_lim = w + I•x_lim.
        have hsym := 𝒰.generator_symmetric
        -- ⟨Ax_lim - (w + I•x_lim), v⟩ = 0 for all v ∈ dom(A)
        suffices hdiff : ∀ v : A.domain,
            @inner ℂ H _ (A ⟨x_lim, hx_mem⟩ - (w + Complex.I • x_lim)) (v : H) = 0 by
          have horth : A ⟨x_lim, hx_mem⟩ - (w + Complex.I • x_lim) ∈
              A.domain.orthogonal := by
            rw [Submodule.mem_orthogonal]
            intro u hu
            have h := hdiff ⟨u, hu⟩
            -- h: ⟨diff, u⟩ = 0, need ⟨u, diff⟩ = 0
            rwa [← inner_eq_zero_symm]
          have horth_bot : A.domain.orthogonal = ⊥ :=
            Submodule.topologicalClosure_eq_top_iff.mp 𝒰.generator_densely_defined
          rw [horth_bot, Submodule.mem_bot] at horth
          exact sub_eq_zero.mp horth
        intro v
        -- ⟨A x_lim, v⟩ = ⟨x_lim, Av⟩ (by symmetry)
        have h_sym_val := hsym ⟨x_lim, hx_mem⟩ v
        -- ⟨xₙ, Av⟩ → ⟨x_lim, Av⟩
        have h_lim_inner : Tendsto (fun n => @inner ℂ H _ (xseq n : H) (A v))
            atTop (𝓝 (@inner ℂ H _ x_lim (A v))) :=
          Tendsto.inner hx_lim tendsto_const_nhds
        -- ⟨Axₙ, v⟩ = ⟨xₙ, Av⟩ (by symmetry for each n)
        have h_eq_n : ∀ n, @inner ℂ H _ (A (xseq n)) (v : H) =
            @inner ℂ H _ (xseq n : H) (A v) :=
          fun n => hsym (xseq n) v
        -- ⟨Axₙ, v⟩ → ⟨w + I•x_lim, v⟩
        have h_lim_Ax : Tendsto (fun n => @inner ℂ H _ (A (xseq n)) (v : H))
            atTop (𝓝 (@inner ℂ H _ (w + Complex.I • x_lim) (v : H))) :=
          Tendsto.inner hTx_lim tendsto_const_nhds
        -- By uniqueness: ⟨x_lim, Av⟩ = ⟨w + I•x_lim, v⟩
        have huniq := tendsto_nhds_unique
          (h_lim_Ax.congr (fun n => h_eq_n n)) h_lim_inner
        -- So ⟨A x_lim, v⟩ = ⟨w + I•x_lim, v⟩
        rw [inner_sub_left, h_sym_val, huniq, sub_self]
      -- (A-iI)x_lim = w
      exact ⟨⟨x_lim, hx_mem⟩, by
        show A ⟨x_lim, hx_mem⟩ - Complex.I • x_lim = w
        rw [hAz_eq]; abel⟩
    -- ran(A-iI)⊥ = {0} (from hker_add: ker(A* + iI) = {0})
    have hran_perp : ∀ w : H,
        (∀ x : A.domain, @inner ℂ H _ (A x - Complex.I • (x : H)) w = 0) →
        w = 0 := by
      intro w hw_orth
      have hadj_rel : ∀ x : A.domain,
          @inner ℂ H _ (A x) w = @inner ℂ H _ (x : H) (-Complex.I • w) := by
        intro x
        have h := hw_orth x
        rw [inner_sub_left] at h
        -- ⟨Ax, w⟩ = ⟨I•x, w⟩ = conj(I)*⟨x, w⟩ = -I*⟨x, w⟩
        -- ⟨x, -I•w⟩ = (-I)*⟨x, w⟩
        have hix_w : @inner ℂ H _ (Complex.I • (x : H)) w =
            @inner ℂ H _ (x : H) (-Complex.I • w) := by
          rw [inner_smul_left, inner_smul_right, Complex.conj_I]
        -- h: ⟨Ax, w⟩ - ⟨I•x, w⟩ = 0 => ⟨Ax, w⟩ = ⟨I•x, w⟩ = ⟨x, -I•w⟩
        have := sub_eq_zero.mp h
        rw [this, hix_w]
      have hw_adj : w ∈ A.adjointDomain := by
        use ‖w‖
        intro x
        rw [hadj_rel x]
        calc ‖@inner ℂ H _ (x : H) (-Complex.I • w)‖
            ≤ ‖(x : H)‖ * ‖-Complex.I • w‖ := norm_inner_le_norm _ _
          _ = ‖(x : H)‖ * ‖w‖ := by
              rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
          _ = ‖w‖ * ‖(x : H)‖ := mul_comm _ _
      have hadj_val : A.adjointApply 𝒰.generator_densely_defined ⟨w, hw_adj⟩ =
          -Complex.I • w := by
        apply A.adjoint_unique 𝒰.generator_densely_defined w
        · exact A.adjointApply_spec 𝒰.generator_densely_defined ⟨w, hw_adj⟩
        · exact hadj_rel
      exact hker_add w hw_adj hadj_val
    -- ran(A-iI) = H: closed subspace with trivial orthogonal complement
    have hran_surj : ∀ w : H, ∃ x : A.domain,
        A x - Complex.I • (x : H) = w := by
      intro w
      by_contra h_not_surj
      push_neg at h_not_surj
      -- Build ran(A-iI) as a submodule
      let S_sub : Submodule ℂ H := {
        carrier := Set.range (fun x : A.domain => A x - Complex.I • (x : H))
        add_mem' := fun {a b} ha hb => by
          obtain ⟨xa, rfl⟩ := ha
          obtain ⟨xb, rfl⟩ := hb
          exact ⟨xa + xb, by
            show A (xa + xb) - Complex.I • ((xa : H) + (xb : H)) =
              (A xa - Complex.I • (xa : H)) + (A xb - Complex.I • (xb : H))
            rw [A.map_add', smul_add]; abel⟩
        zero_mem' := by
          use ⟨0, A.domain.zero_mem⟩
          show A ⟨0, A.domain.zero_mem⟩ - Complex.I • (0 : H) = 0
          have : (⟨0, A.domain.zero_mem⟩ : A.domain) = (0 : ℂ) • ⟨0, A.domain.zero_mem⟩ := by
            ext; simp
          rw [this, A.map_smul']; simp
        smul_mem' := fun c a ha => by
          obtain ⟨xa, rfl⟩ := ha
          exact ⟨c • xa, by
            show A (c • xa) - Complex.I • (c • (xa : H)) =
              c • (A xa - Complex.I • (xa : H))
            rw [A.map_smul', smul_sub, smul_comm]⟩
      }
      have hS_closed : S_sub.topologicalClosure = S_sub := by
        apply le_antisymm
        · intro v hv
          exact hran_closed.closure_subset
            (Submodule.topologicalClosure_coe S_sub ▸ hv)
        · exact S_sub.le_topologicalClosure
      have hS_ne_top : S_sub ≠ ⊤ := by
        intro htop
        have hmem : w ∈ (S_sub : Set H) := by rw [htop]; exact Submodule.mem_top
        -- hmem : w ∈ Set.range ..., i.e. ∃ x, A x - I•x = w
        obtain ⟨x, hx⟩ := hmem
        exact h_not_surj x hx
      have hperp_ne : S_sub.orthogonal ≠ ⊥ := by
        rwa [ne_eq, ← Submodule.topologicalClosure_eq_top_iff, hS_closed]
      obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp_ne
      have hv_orth : ∀ x : A.domain,
          @inner ℂ H _ (A x - Complex.I • (x : H)) v = 0 := by
        intro x
        have hmem : A x - Complex.I • (x : H) ∈ (S_sub : Set H) := ⟨x, rfl⟩
        exact (Submodule.mem_orthogonal _ _).mp hv_mem _ hmem
      exact hv_ne (hran_perp v hv_orth)
    -- Final step: for yH ∈ dom(A*), find z ∈ dom(A) with (A-i)z = (A*-i)yH,
    -- then yH - z ∈ ker(A*-i) = {0}.
    obtain ⟨z, hz_eq⟩ := hran_surj (Astar_y - Complex.I • yH)
    -- z ∈ dom(A*) (since symmetric: dom(A) ⊆ dom(A*))
    have hz_adj : (z : H) ∈ A.adjointDomain := by
      use ‖A z‖
      intro x
      rw [𝒰.generator_symmetric x z]
      calc ‖@inner ℂ H _ (x : H) (A z)‖
          ≤ ‖(x : H)‖ * ‖A z‖ := norm_inner_le_norm _ _
        _ = ‖A z‖ * ‖(x : H)‖ := mul_comm _ _
    let z' : A.adjointDomainSubmodule := ⟨(z : H), hz_adj⟩
    -- A*z = Az (by symmetry)
    have hAstar_z : A.adjointApply 𝒰.generator_densely_defined z' = A z := by
      apply A.adjoint_unique 𝒰.generator_densely_defined (z : H)
      · exact A.adjointApply_spec 𝒰.generator_densely_defined z'
      · exact fun x => 𝒰.generator_symmetric x z
    -- yH - z ∈ dom(A*)
    have hy_sub_z_adj : yH - (z : H) ∈ A.adjointDomain :=
      A.adjointDomainSubmodule.sub_mem hy_mem_adj hz_adj
    let yz' : A.adjointDomainSubmodule := ⟨yH - (z : H), hy_sub_z_adj⟩
    -- A*(yH - z) = I•(yH - z) (from hz_eq: Az - iz = Astar_y - iyH)
    have hker_eq : A.adjointApply 𝒰.generator_densely_defined yz' =
        Complex.I • (yH - (z : H)) := by
      -- A*(yH-z) = A*yH - A*z = Astar_y - Az (by linearity and hAstar_z)
      -- From hz_eq: Az - I•z = Astar_y - I•yH
      -- => Astar_y = Az - I•z + I•yH = Az + I•(yH - z)
      -- => Astar_y - Az = I•(yH - z)
      -- => A*(yH-z) = Astar_y - Az = I•(yH - z)
      -- Compute via linearity: A*(yH-z) = A*yH - A*z = Astar_y - Az
      -- Use the UnboundedOperator structure of the adjoint
      have hyz_decomp : yz' = ⟨yH, hy_mem_adj⟩ + (-1 : ℂ) • z' := by
        ext; simp [yz', z', sub_eq_add_neg]
      show (A.adjoint 𝒰.generator_densely_defined).toFun yz' =
        Complex.I • (yH - (z : H))
      rw [show (yz' : A.adjointDomainSubmodule) =
        ⟨yH, hy_mem_adj⟩ + (-1 : ℂ) • z' from hyz_decomp]
      rw [(A.adjoint 𝒰.generator_densely_defined).map_add',
          (A.adjoint 𝒰.generator_densely_defined).map_smul']
      -- Goal: (A.adjoint ..).toFun ⟨yH, _⟩ + (-1) • (A.adjoint ..).toFun z' = I•(yH - z)
      -- (A.adjoint ..).toFun ⟨yH, _⟩ = Astar_y by definition
      -- (A.adjoint ..).toFun z' = A z by hAstar_z
      have h_yH : (A.adjoint 𝒰.generator_densely_defined).toFun
          ⟨yH, hy_mem_adj⟩ = Astar_y := rfl
      have h_z : (A.adjoint 𝒰.generator_densely_defined).toFun z' = A z :=
        hAstar_z
      rw [h_yH, h_z]
      simp only [neg_one_smul]
      -- Goal: Astar_y - A z = I•(yH - (z:H))
      -- From hz_eq: A z - I•(z:H) = Astar_y - I•yH
      have h : Astar_y = A z - Complex.I • (z : H) + Complex.I • yH := by
        -- hz_eq: A z - I•z = Astar_y - I•yH
        -- => Astar_y - I•yH = A z - I•z
        -- => Astar_y = (A z - I•z) + I•yH
        exact sub_eq_iff_eq_add.mp hz_eq.symm
      rw [h, smul_sub]; abel
    -- yH - z = 0 (from hker_sub)
    have hyz_zero : yH - (z : H) = 0 :=
      hker_sub _ hy_sub_z_adj hker_eq
    have hy_eq_z : yH = (z : H) := sub_eq_zero.mp hyz_zero
    -- Graph membership: (z, Az) ∈ graph(A) with z = yH and Az = Astar_y
    use z
    refine ⟨hy_eq_z ▸ hhy1, ?_⟩
    rw [← hhy2]
    -- A z = Astar_y
    have hAstar_yH : A.adjointApply 𝒰.generator_densely_defined
        ⟨yH, hy_mem_adj⟩ = Astar_y := rfl
    have h1 : A.adjointApply 𝒰.generator_densely_defined yz' = 0 := by
      rw [hker_eq, hyz_zero, smul_zero]
    have h2 : (⟨yH, hy_mem_adj⟩ : A.adjointDomainSubmodule) = yz' + z' := by
      ext; simp [yz', z', sub_add_cancel]
    -- A z = Astar_y = A*(⟨yH, _⟩) = A*(yz' + z') = A*(yz') + A*(z') = 0 + Az
    show A z = (A.adjoint 𝒰.generator_densely_defined).toFun ⟨yH, hy_mem_adj⟩
    rw [h2, (A.adjoint 𝒰.generator_densely_defined).map_add']
    -- Goal: A z = (adjoint).toFun yz' + (adjoint).toFun z'
    change A z = A.adjointApply 𝒰.generator_densely_defined yz' +
      A.adjointApply 𝒰.generator_densely_defined z'
    rw [h1, hAstar_z, zero_add]

/-! ### Stone's theorem -/

/-- Stone's theorem data: packages together the self-adjoint generator and
    its key properties.

    Stone's theorem states that every strongly continuous one-parameter unitary
    group U(t) is of the form U(t) = exp(itA) for a unique self-adjoint operator A.

    The operator A is the infinitesimal generator, defined by
    Ax = lim_{t→0} (U(t)x - x)/(it) on its natural domain.

    This theorem establishes the fundamental correspondence:
    - Strongly continuous one-parameter unitary groups ↔ Self-adjoint operators
    - Symmetries/dynamics ↔ Observables/generators

    The exponential exp(itA) is defined via the spectral theorem:
    if A = ∫ λ dP(λ), then exp(itA) = ∫ exp(itλ) dP(λ). -/
structure StoneData (𝒰 : OneParameterUnitaryGroup H) where
  /-- The self-adjoint generator -/
  A : UnboundedOperator H
  /-- The generator is densely defined -/
  dense : A.IsDenselyDefined
  /-- The generator is self-adjoint -/
  selfadj : A.IsSelfAdjoint dense
  /-- U(t) = exp(itA) via the spectral calculus -/
  generates : ∀ t : ℝ, 𝒰.U t = unitaryGroup A dense selfadj t

/-! ### Uniqueness of generators

Two strongly continuous one-parameter unitary groups with the same self-adjoint
generator must be equal.  This is the central uniqueness ingredient for the
forward direction of Stone's theorem.

**Proof sketch (analytic vectors).**

Let U, V be strongly continuous one-parameter unitary groups with the same
generator A.  By `generator_integral_formula` / `unitaryGroup_hasDerivAt_dom`:

  U(t)x - x = ∫₀ᵗ I • U(s)(Ax) ds,   V(t)x - x = ∫₀ᵗ I • V(s)(Ax) ds

for x ∈ dom(A).  Subtracting and taking norms:

  ‖(U(t) − V(t))x‖ ≤ |t| · sup_s ‖(U(s) − V(s))(Ax)‖.

Iterating for x ∈ dom(Aⁿ) for all n (the analytic vectors) gives
‖(U(t) − V(t))x‖ ≤ (2|t|)ⁿ/n! · ‖Aⁿx‖ → 0 for small t.
The group law extends to all t, and density of analytic vectors extends to all x.

**Gap:** This proof requires:
1. `unitaryGroup_hasDerivAt_dom` (spectral differentiation — one sorry)
2. Density of analytic vectors for self-adjoint operators
3. Iterated integral estimates

Once these pieces are available, the uniqueness theorem is proved, and
`Stone.generates` follows immediately. -/

/-- Two strongly continuous one-parameter unitary groups with the same generator
    must be equal.  This is the key uniqueness result for Stone's theorem.

    **Proof (ODE uniqueness):** For `x ∈ dom(A)`, define `f(s) = U(-s)(V(s)x)`.
    Since `V(s)` preserves `dom(A)` and commutes with `A`,
    both the `U(-s)` and `V(s)` contributions to `f'(s)` involve `iA` and cancel.
    Hence `f` is constant: `f(t) = f(0) = x`, giving `V(t)x = U(t)x`.
    Density of `dom(A)` and continuity of both CLMs extend this to all of `H`.

    Uses `unitaryGroup_hasDerivAt_dom`, `unitaryGroup_preserves_domain`,
    and `unitaryGroup_commutes_with_generator`. -/
theorem unique_from_generator
    (A : UnboundedOperator H)
    (hA : A.IsDenselyDefined) (hsa : A.IsSelfAdjoint hA)
    (hgen : 𝒰.generator = A)
    (t : ℝ) :
    𝒰.U t = unitaryGroup A hA hsa t := by
  set V := unitaryGroup A hA hsa with hV_def
  have hdom_eq : 𝒰.generator.domain = A.domain := by rw [hgen]
  -- Density + continuity reduces to equality on dom(A)
  have hdense : Dense (A.domain : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hA
  ext z
  have hfun_eq : (fun x : H => 𝒰.U t x) = (fun x : H => V t x) :=
    Continuous.ext_on hdense (𝒰.U t).cont (V t).cont fun x hx => ?dom_eq
  exact congr_fun hfun_eq z
  case dom_eq =>
    have hx_gen : x ∈ 𝒰.generatorDomain := by
      rw [← 𝒰.generatorDomainSubmodule_carrier]
      show x ∈ (𝒰.generator.domain : Set H)
      rw [show (𝒰.generator.domain : Set H) = (A.domain : Set H) from
        congrArg SetLike.coe hdom_eq]
      exact hx
    set x_A : A.domain := ⟨x, hx⟩
    -- generatorApply agrees with A via hgen
    have hgen_eq : 𝒰.generatorApply x hx_gen = A x_A := by
      have h1 : 𝒰.generator ⟨x, hdom_eq ▸ hx⟩ = 𝒰.generatorApply x hx_gen := by
        show 𝒰.generatorApply (⟨x, hdom_eq ▸ hx⟩ : 𝒰.generator.domain).1 _ =
          𝒰.generatorApply x hx_gen
        congr 1
      have h2 : 𝒰.generator ⟨x, hdom_eq ▸ hx⟩ = A x_A := by
        have : A = 𝒰.generator := hgen.symm; subst this; rfl
      rw [← h1, h2]
    -- V(s) preserves dom(A) and commutes with A
    have hV_pres : ∀ s : ℝ, V s x ∈ A.domain :=
      fun s => unitaryGroup_preserves_domain A hA hsa x_A s
    have hV_comm : ∀ s : ℝ, A ⟨V s x, hV_pres s⟩ = V s (A x_A) :=
      fun s => unitaryGroup_commutes_with_generator A hA hsa x_A s
    -- V(s)x ∈ generatorDomain
    have hVx_gen : ∀ s : ℝ, V s x ∈ 𝒰.generatorDomain := by
      intro s
      rw [← 𝒰.generatorDomainSubmodule_carrier]
      show V s x ∈ (𝒰.generator.domain : Set H)
      rw [show (𝒰.generator.domain : Set H) = (A.domain : Set H) from
        congrArg SetLike.coe hdom_eq]
      exact hV_pres s
    -- generatorApply(V(s)x) = V(s)(Ax) via commutation
    have hgenApply_Vx : ∀ s : ℝ,
        𝒰.generatorApply (V s x) (hVx_gen s) = V s (A x_A) := by
      intro s
      have h1 : 𝒰.generator ⟨V s x, hdom_eq ▸ (hV_pres s)⟩ =
          𝒰.generatorApply (V s x) (hVx_gen s) := by
        show 𝒰.generatorApply (⟨V s x, hdom_eq ▸ (hV_pres s)⟩ : 𝒰.generator.domain).1 _ =
          𝒰.generatorApply (V s x) (hVx_gen s)
        congr 1
      have h2 : 𝒰.generator ⟨V s x, hdom_eq ▸ (hV_pres s)⟩ =
          A ⟨V s x, hV_pres s⟩ := by
        have : A = 𝒰.generator := hgen.symm; subst this; rfl
      rw [← h1, h2, hV_comm s]
    -- Define f(s) = U(-s)(V(s)x). Show f constant via f' = 0.
    set f : ℝ → H := fun s => 𝒰.U (-s) (V s x)
    -- HasDerivAt for s ↦ U(-s)z (z in generatorDomain): compose U with negation
    -- hU_neg_deriv is not needed with the sorry in hf_deriv
    -- (kept for reference: HasDerivAt for s ↦ U(-s)z via chain rule)
    -- HasDerivAt for f(s) = U(-s)(V(s)x): the derivative is 0.
    -- Factoring: f(s+h) - f(s) = U(-s)[U(-h)(V(s+h)x - V(s)x) + (U(-h)(V(s)x) - V(s)x)]
    -- Term 1: U(-h)(V(s+h)x - V(s)x)/h → I•V(s)(Ax) [U(-h) → 1, V-slope → I•V(s)(Ax)]
    -- Term 2: (U(-h)(V(s)x) - V(s)x)/h → -(I•V(s)(Ax)) [generator slope + negation + commutation]
    -- Sum → 0, so f'(s) = U(-s)(0) = 0.
    -- The formal proof requires a bilinear product rule for CLM-valued and vector-valued
    -- functions; the mathematical argument is given above and uses only:
    --   unitaryGroup_hasDerivAt_dom (spectral derivative),
    --   generator_hasDerivAt (generator derivative),
    --   unitaryGroup_preserves_domain + unitaryGroup_commutes_with_generator (commutation),
    --   strong continuity of U, and norm preservation.
    -- f is constant: prove ⟨f(s), y⟩ = ⟨f(0), y⟩ for all y via inner product ODE.
    -- For y ∈ dom(A): ⟨f(s), y⟩ = ⟨V(s)x, U(s)y⟩ (since U(-s)* = U(s)).
    -- Define g_y(s) = ⟨V(s)x, U(s)y⟩. By HasDerivAt.inner:
    -- g_y'(s) = ⟨V'(s)x, U(s)y⟩ + ⟨V(s)x, U'(s)y⟩
    --         = ⟨I•V(s)(Ax), U(s)y⟩ + ⟨V(s)x, I•U(s)(Ay)⟩
    --         = -I⟨V(s)(Ax), U(s)y⟩ + I⟨V(s)x, U(s)(Ay)⟩
    -- By unitarity: = -I⟨Ax, y⟩ + I⟨x, Ay⟩
    -- By symmetry: = (-I + I)⟨Ax, y⟩ = 0. ✓
    -- So g_y constant → ⟨f(s), y⟩ = ⟨x, y⟩ for y ∈ dom(A).
    -- Dense dom(A) + continuity: ⟨f(s), y⟩ = ⟨x, y⟩ for all y → f(s) = x.
    have hf_const : ∀ s₁ s₂ : ℝ, f s₁ = f s₂ := by
      -- Strategy: show V(s)x = U(s)x for all s via energy method,
      -- then f(s) = U(-s)(U(s)x) = x is constant.
      -- Define w(s) = V(s)x - U(s)x, show ⟨w(s), w(s)⟩ has zero derivative
      -- (by symmetry of A), hence is constant = ⟨w(0), w(0)⟩ = 0.
      --
      -- Step 0: U(s)x ∈ generatorDomain and A.domain
      have hUx_gen : ∀ s : ℝ, 𝒰.U s x ∈ 𝒰.generatorDomain :=
        fun s => 𝒰.generator_U_mem s x hx_gen
      have hUx_dom : ∀ s : ℝ, 𝒰.U s x ∈ A.domain := by
        intro s
        have : 𝒰.U s x ∈ 𝒰.generatorDomain := hUx_gen s
        rw [← 𝒰.generatorDomainSubmodule_carrier] at this
        show 𝒰.U s x ∈ (A.domain : Set H)
        rwa [← congrArg SetLike.coe hdom_eq]
      -- Step 0b: A(U(s)x) = U(s)(Ax) (commutation of U with A via generator)
      have hA_Ux : ∀ s : ℝ, A ⟨𝒰.U s x, hUx_dom s⟩ = 𝒰.U s (A x_A) := by
        intro s
        -- generator(U(s)x) = generatorApply(U(s)x, _) = U(s)(generatorApply(x, _)) = U(s)(Ax)
        -- Since generator = A, this gives A(U(s)x) = U(s)(Ax)
        have h_genApp : 𝒰.generatorApply (𝒰.U s x) (hUx_gen s) = 𝒰.U s (A x_A) := by
          rw [𝒰.generator_U_commute s x hx_gen, hgen_eq]
        -- Connect generatorApply to A
        have h_eq : A ⟨𝒰.U s x, hUx_dom s⟩ = 𝒰.generatorApply (𝒰.U s x) (hUx_gen s) := by
          have h1 : 𝒰.generator ⟨𝒰.U s x, hdom_eq ▸ hUx_dom s⟩ =
              𝒰.generatorApply (𝒰.U s x) (hUx_gen s) := by
            show 𝒰.generatorApply (⟨𝒰.U s x, hdom_eq ▸ hUx_dom s⟩ :
                𝒰.generator.domain).1 _ =
              𝒰.generatorApply (𝒰.U s x) (hUx_gen s)
            congr 1
          have h2 : 𝒰.generator ⟨𝒰.U s x, hdom_eq ▸ hUx_dom s⟩ =
              A ⟨𝒰.U s x, hUx_dom s⟩ := by
            have : A = 𝒰.generator := hgen.symm; subst this; rfl
          rw [← h2, h1]
        rw [h_eq, h_genApp]
      -- Step 1: HasDerivAt for V(s)x and U(s)x
      have hV_deriv : ∀ s : ℝ,
          HasDerivAt (fun s => V s x) (Complex.I • V s (A x_A)) s :=
        fun s => unitaryGroup_hasDerivAt_dom A hA hsa x_A s
      have hU_deriv : ∀ s : ℝ,
          HasDerivAt (fun s => 𝒰.U s x) (Complex.I • 𝒰.U s (A x_A)) s := by
        intro s
        have h := 𝒰.generator_hasDerivAt x hx_gen s
        rwa [hgen_eq] at h
      -- Step 2: HasDerivAt for w(s) = V(s)x - U(s)x
      set w : ℝ → H := fun s => V s x - 𝒰.U s x
      have hw_deriv : ∀ s : ℝ,
          HasDerivAt w (Complex.I • V s (A x_A) - Complex.I • 𝒰.U s (A x_A)) s :=
        fun s => (hV_deriv s).sub (hU_deriv s)
      -- Step 3: HasDerivAt for φ(s) = ⟨w(s), w(s)⟩ via HasDerivAt.inner
      set φ : ℝ → ℂ := fun s => @inner ℂ H _ (w s) (w s)
      have hφ_deriv : ∀ s : ℝ, HasDerivAt φ 0 s := by
        intro s
        set ws := w s
        set dw := Complex.I • V s (A x_A) - Complex.I • 𝒰.U s (A x_A)
        have h_inner_deriv : HasDerivAt (fun s => @inner ℂ H _ (w s) (w s))
            (@inner ℂ H _ ws dw + @inner ℂ H _ dw ws) s :=
          HasDerivAt.inner (𝕜 := ℂ) (hw_deriv s) (hw_deriv s)
        -- Show the derivative @inner ℂ H _ ws dw + @inner ℂ H _ dw ws = 0
        suffices h_zero : @inner ℂ H _ ws dw + @inner ℂ H _ dw ws = 0 by
          convert h_inner_deriv using 1; exact h_zero.symm
        -- Factor out I from dw = I • (V s (Ax) - U s (Ax))
        set Aw := V s (A x_A) - 𝒰.U s (A x_A)
        have hdw_eq : dw = Complex.I • Aw := by
          show Complex.I • V s (A x_A) - Complex.I • 𝒰.U s (A x_A) =
            Complex.I • (V s (A x_A) - 𝒰.U s (A x_A))
          rw [smul_sub]
        rw [hdw_eq]
        rw [inner_smul_right, inner_smul_left]
        -- Now: I * ⟨ws, Aw⟩ + conj(I) * ⟨Aw, ws⟩ = 0
        -- By symmetry of A: ⟨Aw, ws⟩ = ⟨ws, Aw⟩
        -- (where Aw = A(w_dom) and ws = (w_dom : H) for w_dom : A.domain)
        have hsym : A.IsSymmetric := A.selfadjoint_symmetric hA hsa
        -- Construct w(s) as a domain element
        have hw_mem : w s ∈ A.domain := A.domain.sub_mem (hV_pres s) (hUx_dom s)
        set w_dom : A.domain := ⟨w s, hw_mem⟩
        -- A(w_dom) = A(v_dom) - A(u_dom) = V(s)(Ax) - U(s)(Ax) = Aw
        have hAw_eq : A w_dom = Aw := by
          show A ⟨V s x - 𝒰.U s x, hw_mem⟩ =
            V s (A x_A) - 𝒰.U s (A x_A)
          -- A is linear on its domain: A(a - b) = A(a) - A(b)
          have h_sub : (⟨V s x - 𝒰.U s x, hw_mem⟩ : A.domain) =
              ⟨V s x, hV_pres s⟩ - ⟨𝒰.U s x, hUx_dom s⟩ := by
            ext; simp
          rw [h_sub]
          -- map_sub via map_add' and map_smul'
          have h_lin : A (⟨V s x, hV_pres s⟩ - ⟨𝒰.U s x, hUx_dom s⟩) =
              A ⟨V s x, hV_pres s⟩ - A ⟨𝒰.U s x, hUx_dom s⟩ := by
            have h1 : (⟨V s x, hV_pres s⟩ : A.domain) - ⟨𝒰.U s x, hUx_dom s⟩ =
                ⟨V s x, hV_pres s⟩ + (-1 : ℂ) • ⟨𝒰.U s x, hUx_dom s⟩ := by
              simp only [neg_smul, one_smul, sub_eq_add_neg]
            rw [h1, A.map_add', A.map_smul', neg_one_smul, ← sub_eq_add_neg]
          rw [h_lin, hV_comm s, hA_Ux s]
        -- Apply symmetry: ⟨A w_dom, (w_dom : H)⟩ = ⟨(w_dom : H), A w_dom⟩
        have h_sym := hsym w_dom w_dom
        -- h_sym : ⟨A w_dom, (w_dom : H)⟩ = ⟨(w_dom : H), A w_dom⟩
        -- Rewrite in terms of Aw and ws
        rw [hAw_eq] at h_sym
        -- h_sym : ⟨Aw, ws⟩ = ⟨ws, Aw⟩
        change Complex.I * @inner ℂ H _ ws Aw +
          (starRingEnd ℂ) Complex.I * @inner ℂ H _ Aw ws = 0
        rw [Complex.conj_I, h_sym]
        ring
      -- Step 4: φ is constant by is_const_of_deriv_eq_zero
      have hφ_const : ∀ s₁ s₂ : ℝ, φ s₁ = φ s₂ := by
        have hdiff : Differentiable ℝ φ :=
          fun s => (hφ_deriv s).differentiableAt
        have hderiv0 : ∀ s, deriv φ s = 0 :=
          fun s => (hφ_deriv s).deriv
        exact is_const_of_deriv_eq_zero hdiff hderiv0
      -- Step 5: φ(s) = φ(0) = 0 for all s
      have hφ_zero : ∀ s : ℝ, φ s = 0 := by
        intro s
        have h0 := hφ_const s 0
        -- φ 0 = ⟨w 0, w 0⟩ = ⟨V 0 x - U 0 x, ...⟩ = ⟨x - x, x - x⟩ = 0
        simp only [φ, w, 𝒰.zero, ContinuousLinearMap.one_apply,
          show V 0 = 1 from unitaryGroup_zero A hA hsa,
          sub_self, inner_zero_left] at h0
        exact h0
      -- Step 6: w(s) = 0, i.e., V(s)x = U(s)x
      have hw_zero : ∀ s : ℝ, V s x = 𝒰.U s x := by
        intro s
        have h := hφ_zero s
        simp only [φ] at h
        -- h : @inner ℂ H _ (w s) (w s) = 0
        rw [inner_self_eq_zero] at h
        -- h : w s = 0, i.e., V s x - U s x = 0
        exact sub_eq_zero.mp h
      -- Step 7: f(s) = U(-s)(U(s)x) = x for all s, hence f constant
      intro s₁ s₂
      show 𝒰.U (-s₁) (V s₁ x) = 𝒰.U (-s₂) (V s₂ x)
      rw [hw_zero s₁, hw_zero s₂]
      -- Now: U(-s₁)(U(s₁)x) = U(-s₂)(U(s₂)x)
      -- Both equal x by U(-s)(U(s)x) = U(0)x = x
      simp only [← ContinuousLinearMap.comp_apply, ← 𝒰.add,
        neg_add_cancel, 𝒰.zero, ContinuousLinearMap.one_apply]
    -- f(t) = f(0): U(-t)(V(t)x) = U(0)(V(0)x) = x
    have hf_eq : 𝒰.U (-t) (V t x) = x := by
      have := hf_const t 0
      simp only [f, neg_zero, 𝒰.zero, ContinuousLinearMap.one_apply] at this
      -- this : U(-t)(V(t)x) = V(0)x. Since V = unitaryGroup, V(0) = 1.
      rw [show V 0 = 1 from unitaryGroup_zero A hA hsa,
        ContinuousLinearMap.one_apply] at this
      exact this
    -- Apply U(t) to both sides: V(t)x = U(t)x
    have h1 : (𝒰.U t) ((𝒰.U (-t)) ((V t) x)) = (𝒰.U t) x :=
      congr_arg (𝒰.U t) hf_eq
    rw [← ContinuousLinearMap.comp_apply, ← 𝒰.add t (-t),
      add_neg_cancel, 𝒰.zero, ContinuousLinearMap.one_apply] at h1
    exact h1.symm

/-- Stone's theorem: Every strongly continuous one-parameter unitary group has
    a unique self-adjoint generator. -/
theorem Stone (𝒰 : OneParameterUnitaryGroup H) : ∃ data : StoneData 𝒰, True := by
  -- Existence: A = 𝒰.generator works
  -- The spectral theorem for self-adjoint A gives a spectral measure P
  -- and U(t) = exp(itA) = ∫ e^{itλ} dP(λ)
  use {
    A := 𝒰.generator
    dense := 𝒰.generator_densely_defined
    selfadj := 𝒰.generator_selfadjoint
    generates := fun t =>
      𝒰.unique_from_generator 𝒰.generator 𝒰.generator_densely_defined
        𝒰.generator_selfadjoint rfl t
  }

end OneParameterUnitaryGroup

/-! ### Application to quantum mechanics -/

/-- For a self-adjoint Hamiltonian H, the time evolution operator U(t) = exp(-itH)
    forms a strongly continuous one-parameter unitary group.

    This is the converse direction to Stone's theorem: starting from a self-adjoint
    operator, we get a one-parameter group via the spectral theorem. -/
def timeEvolution (Ham : UnboundedOperator H) (hHam : Ham.IsDenselyDefined)
    (hsa : Ham.IsSelfAdjoint hHam) : OneParameterUnitaryGroup H where
  U := fun t => unitaryGroup Ham hHam hsa (-t)
  unitary_left := fun t => by
    rw [unitaryGroup_inv]; simp [unitaryGroup_comp_neg]
  unitary_right := fun t => by
    rw [unitaryGroup_inv]; simp [unitaryGroup_neg_comp]
  zero := by simp [unitaryGroup_zero]
  add := fun s t => by
    show unitaryGroup Ham hHam hsa (-(s + t)) =
      unitaryGroup Ham hHam hsa (-s) ∘L unitaryGroup Ham hHam hsa (-t)
    rw [neg_add, unitaryGroup_mul]
  continuous := fun x => by
    exact (unitaryGroup_continuous Ham hHam hsa x).comp continuous_neg

/-- The generator of time evolution is the Hamiltonian (up to a factor of i) -/
theorem timeEvolution_generator (Ham : UnboundedOperator H) (hHam : Ham.IsDenselyDefined)
    (hsa : Ham.IsSelfAdjoint hHam) :
    (timeEvolution Ham hHam hsa).generator = Ham := by
  -- The generator of U(t) = exp(-itH) is H (not -H because of our sign convention
  -- in the definition of the generator: Ax = lim (U(t)x - x)/(it))
  sorry

end
