/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import OSReconstruction.SCV.Analyticity

/-!
# Identity Theorem for Several Complex Variables

This file provides the identity theorem (uniqueness of analytic continuation)
for holomorphic functions of several complex variables, together with the
Hartogs analyticity bridge from ℂ-differentiability to analyticity.

## Main results

* `DifferentiableOn.analyticOnNhd_of_finiteDimensional` — Hartogs analyticity:
  ℂ-Fréchet differentiable on an open set implies analytic (sorry: requires
  iterated Cauchy integral formula)
* `identity_theorem_SCV` — identity theorem for `f, g : ℂᵐ → ℂ`:
  if they agree on a nonempty open subset of a connected open set, they agree everywhere
* `identity_theorem_tubeDomain` — specialization to tube domains `ℝᵐ + iC`

## Mathematical Background

In one complex variable, `DifferentiableOn.analyticOnNhd` (Mathlib) gives
holomorphic ⟹ analytic via Cauchy's integral formula. The identity theorem
then follows from isolated zeros of analytic functions.

In several complex variables (ℂⁿ, n ≥ 2), the same implications hold but
with a crucial difference: zero sets can be complex hypersurfaces (codimension 1),
so agreement at a cluster point is insufficient. Instead, agreement on an
open set (or equivalently, `f =ᶠ[nhds z₀] g`) is required.

The proof of Hartogs analyticity uses iterated Cauchy integrals: fix all
variables except one, apply the 1D Cauchy formula, then assemble the
multivariate power series. This is ~200 LOC of careful analysis not yet
in Mathlib.

## References

* Krantz, S. "Function Theory of Several Complex Variables", Theorems 1.2.5–1.2.6
* Hörmander, L. "An Introduction to Complex Analysis in Several Variables", Ch. 2
-/

noncomputable section

open Complex Topology Set

/-! ### Hartogs Analyticity -/

/-- **Hartogs' analyticity theorem** for several complex variables:
    A function `f : ℂᵐ → F` that is ℂ-Fréchet differentiable on an open set
    is analytic (has convergent power series expansions) on that set.

    In one complex variable, this is `DifferentiableOn.analyticOnNhd` in Mathlib
    (proved via Cauchy's integral formula). In several variables, the proof uses
    iterated Cauchy integrals: fix all variables except one, apply the 1D result,
    then use the Cauchy integral representation to get the multi-variable power series.

    This is NOT the same as Hartogs' separate analyticity theorem (which says
    separately holomorphic implies jointly holomorphic). This is the simpler fact
    that jointly ℂ-differentiable implies analytic.

    Ref: Krantz, "Function Theory of Several Complex Variables", Theorem 1.2.5 -/
theorem DifferentiableOn.analyticOnNhd_of_finiteDimensional
    {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set (Fin m → ℂ)} {f : (Fin m → ℂ) → F}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    AnalyticOnNhd ℂ f U :=
  fun _z hz => SCV.differentiableOn_analyticAt hU hf hz

/-! ### Identity Theorem -/

/-- **Identity theorem for several complex variables**: if two holomorphic functions
    on a connected open set `U ⊂ ℂᵐ` agree in a neighborhood of some point `z₀ ∈ U`,
    they agree on all of `U`.

    This is the several-variable generalization of `identity_theorem_connected`
    (EdgeOfWedge.lean). The key difference from 1D: in ℂⁿ (n ≥ 2), zero sets
    of holomorphic functions can be complex hypersurfaces, so agreement at a
    cluster point is NOT sufficient — we need agreement on an open set
    (i.e., `f =ᶠ[nhds z₀] g`).

    Proof: from Hartogs analyticity (`analyticOnNhd_of_finiteDimensional`) and
    Mathlib's `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.

    Ref: Krantz, "Function Theory of Several Complex Variables", Theorem 1.2.6 -/
theorem identity_theorem_SCV {m : ℕ}
    {U : Set (Fin m → ℂ)} (hU : IsOpen U) (hconn : IsConnected U)
    {f g : (Fin m → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {z₀ : Fin m → ℂ} (hz₀ : z₀ ∈ U)
    (hagree : f =ᶠ[nhds z₀] g) :
    EqOn f g U :=
  (hf.analyticOnNhd_of_finiteDimensional hU).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd_of_finiteDimensional hU) hconn.isPreconnected hz₀ hagree

/-! ### Tube Domain Specialization -/

/-- The tube domain `T(C) = { z ∈ ℂᵐ : Im(z) ∈ C }` where `C ⊂ ℝᵐ` is an
    open convex cone. -/
def SCV.TubeDomain' {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℂ) :=
  { z | (fun i => (z i).im) ∈ C }

/-- Tube domains with open cones are open. -/
theorem SCV.tubeDomain'_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (SCV.TubeDomain' C) :=
  hC.preimage (continuous_pi (fun i => Complex.continuous_im.comp (continuous_apply i)))

/-- Tube domains with convex nonempty cones are connected. -/
theorem SCV.tubeDomain'_isConnected {m : ℕ} {C : Set (Fin m → ℝ)}
    (_hC_open : IsOpen C) (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty) :
    IsConnected (SCV.TubeDomain' C) := by
  constructor
  · obtain ⟨y, hy⟩ := hC_ne
    refine ⟨fun i => Complex.mk 0 (y i), ?_⟩
    show (fun i => (Complex.mk 0 (y i)).im) ∈ C
    simp; exact hy
  · apply Convex.isPreconnected
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    show (fun i => ((a • z₁ + b • z₂) i).im) ∈ C
    have : (fun i => ((a • z₁ + b • z₂) i).im) =
        a • (fun i => (z₁ i).im) + b • (fun i => (z₂ i).im) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        smul_eq_mul]
    rw [this]
    exact hC_conv hz₁ hz₂ ha hb hab

/-- Identity theorem for tube domains: two holomorphic functions on a tube domain
    `T(C) = ℝᵐ + iC` (where C is a nonempty open convex cone) that agree in a
    neighborhood of some point must agree on the entire tube domain.

    Tube domains are connected (since C is convex), so this follows directly
    from `identity_theorem_SCV`. -/
theorem identity_theorem_tubeDomain {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {f g : (Fin m → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (SCV.TubeDomain' C))
    (hg : DifferentiableOn ℂ g (SCV.TubeDomain' C))
    {z₀ : Fin m → ℂ} (hz₀ : z₀ ∈ SCV.TubeDomain' C)
    (hagree : f =ᶠ[nhds z₀] g) :
    EqOn f g (SCV.TubeDomain' C) :=
  identity_theorem_SCV (SCV.tubeDomain'_isOpen hC)
    (SCV.tubeDomain'_isConnected hC hconv hne)
    hf hg hz₀ hagree

/-! ### Product Type Generalization -/

/-- Continuous linear equivalence flattening `Fin n → Fin m → ℂ` to `Fin (n*m) → ℂ`.
    Composed from currying + reindexing via `finProdFinEquiv`. -/
noncomputable def SCV.flattenCLE (n m : ℕ) :
    (Fin n → Fin m → ℂ) ≃L[ℂ] (Fin (n * m) → ℂ) := by
  apply LinearEquiv.toContinuousLinearEquiv
  exact (LinearEquiv.piCurry ℂ (fun (_ : Fin n) (_ : Fin m) => ℂ)).symm.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ => ℂ)
      (finProdFinEquiv.symm.trans (Equiv.sigmaEquivProd (Fin n) (Fin m)).symm)).symm

/-- **Hartogs analyticity for product-indexed domains**: a function
    `f : (Fin n → Fin m → ℂ) → ℂ` that is ℂ-differentiable on an open set is analytic.

    Proof: transfer through `flattenCLE` to `Fin (n*m) → ℂ`, apply
    `SCV.differentiableOn_analyticAt`, then compose back. -/
theorem analyticAt_of_differentiableOn_product {n m : ℕ}
    {f : (Fin n → Fin m → ℂ) → ℂ} {U : Set (Fin n → Fin m → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {z : Fin n → Fin m → ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ f z := by
  set φ := SCV.flattenCLE n m
  have hU' : IsOpen (⇑φ '' U) := (φ.toHomeomorph.isOpenMap U) hU
  have hz' : φ z ∈ ⇑φ '' U := Set.mem_image_of_mem _ hz
  have hf' : DifferentiableOn ℂ (f ∘ ⇑φ.symm) (⇑φ '' U) := by
    apply DifferentiableOn.comp hf φ.symm.differentiableOn
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hw
    simp [ContinuousLinearEquiv.symm_apply_apply]; exact hv
  have h_anal : AnalyticAt ℂ (f ∘ ⇑φ.symm) (φ z) :=
    SCV.differentiableOn_analyticAt hU' hf' hz'
  have h_comp := h_anal.comp (φ.analyticAt z)
  rwa [show (f ∘ ⇑φ.symm) ∘ ⇑φ = f from by
    ext v; simp [Function.comp, ContinuousLinearEquiv.symm_apply_apply]] at h_comp

/-- **Identity theorem for product-indexed domains**: if two holomorphic functions
    on a connected open `U ⊆ (Fin n → Fin m → ℂ)` agree in a neighborhood of
    some point `z₀ ∈ U`, they agree on all of `U`.

    This generalizes `identity_theorem_SCV` from `Fin k → ℂ` to the product type
    `Fin n → Fin m → ℂ` used in the BHW theorem. -/
theorem identity_theorem_product {n m : ℕ}
    {U : Set (Fin n → Fin m → ℂ)} (hU : IsOpen U) (hconn : IsConnected U)
    {f g : (Fin n → Fin m → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {z₀ : Fin n → Fin m → ℂ} (hz₀ : z₀ ∈ U)
    (hagree : f =ᶠ[nhds z₀] g) :
    EqOn f g U :=
  (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun _ hz => analyticAt_of_differentiableOn_product hU hf hz)
    (fun _ hz => analyticAt_of_differentiableOn_product hU hg hz)
    hconn.isPreconnected hz₀ hagree)

end
