/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
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
import OSReconstruction.SCV.Osgood







































noncomputable section

open Complex Topology Set



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





/-- Continuous linear equivalence flattening `Fin n → Fin m → ℂ` to `Fin (n*m) → ℂ`.
    Composed from currying + reindexing via `finProdFinEquiv`. -/
noncomputable def SCV.flattenCLE (n m : ℕ) :
    (Fin n → Fin m → ℂ) ≃L[ℂ] (Fin (n * m) → ℂ) := by
  apply LinearEquiv.toContinuousLinearEquiv
  exact (LinearEquiv.piCurry ℂ (fun (_ : Fin n) (_ : Fin m) => ℂ)).symm.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ => ℂ)
      (finProdFinEquiv.symm.trans (Equiv.sigmaEquivProd (Fin n) (Fin m)).symm)).symm



/-- The inverse of `flattenCLE` recovers coordinates via `finProdFinEquiv`. -/
theorem SCV.flattenCLE_symm_apply {n m : ℕ}
    (w : Fin (n * m) → ℂ) (i : Fin n) (j : Fin m) :
    (SCV.flattenCLE n m).symm w i j = w (finProdFinEquiv (i, j)) := by
  simp only [SCV.flattenCLE, LinearEquiv.coe_toContinuousLinearEquiv_symm',
    LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.piCurry_apply]
  unfold LinearEquiv.piCongrLeft Sigma.curry
  simp

/-- `flattenCLE` maps coordinates via `finProdFinEquiv`. -/
theorem SCV.flattenCLE_apply {n m : ℕ}
    (z : Fin n → Fin m → ℂ) (k : Fin (n * m)) :
    (SCV.flattenCLE n m) z k = z (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  have h := SCV.flattenCLE_symm_apply ((SCV.flattenCLE n m) z)
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  simp only [Prod.mk.eta, Equiv.apply_symm_apply] at h
  exact h.symm

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

/-- Product-indexed SCV identity theorem from a nonempty open seed.

This is the form used by local analytic-continuation galleries: once two
holomorphic branches agree on a complex-open seed inside a connected product
domain, the equality propagates to the full domain. -/
theorem identity_theorem_product_of_eqOn_open {n m : ℕ}
    {U W : Set (Fin n → Fin m → ℂ)} (hU : IsOpen U) (hconn : IsConnected U)
    (hW : IsOpen W) (hne : W.Nonempty) (hWU : W ⊆ U)
    {f g : (Fin n → Fin m → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hagree : Set.EqOn f g W) :
    Set.EqOn f g U := by
  rcases hne with ⟨z₀, hz₀W⟩
  have hz₀U : z₀ ∈ U := hWU hz₀W
  have hlocal : f =ᶠ[nhds z₀] g := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨W, hW.mem_nhds hz₀W, hagree⟩
  exact identity_theorem_product hU hconn hf hg hz₀U hlocal



end
