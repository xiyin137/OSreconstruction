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

/-! ### Coordinate lemmas for `flattenCLE` -/

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

/-- Updating a flattened vector at index `k` and unflattening equals a nested update. -/
theorem SCV.flattenCLE_symm_update {n m : ℕ}
    (z : Fin n → Fin m → ℂ) (k : Fin (n * m)) (w : ℂ) :
    (SCV.flattenCLE n m).symm (Function.update ((SCV.flattenCLE n m) z) k w) =
      Function.update z (finProdFinEquiv.symm k).1
        (Function.update (z (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 w) := by
  ext a b
  rw [SCV.flattenCLE_symm_apply]
  by_cases hEq : finProdFinEquiv (a, b) = k
  · have hab : (a, b) = finProdFinEquiv.symm k :=
      finProdFinEquiv.injective (hEq.trans (finProdFinEquiv.apply_symm_apply k).symm)
    rcases Prod.ext_iff.mp hab with ⟨ha, hb⟩
    subst ha; subst hb
    rw [finProdFinEquiv.apply_symm_apply]; simp
  · rw [Function.update_of_ne hEq, SCV.flattenCLE_apply]
    by_cases ha : a = (finProdFinEquiv.symm k).1
    · subst ha
      have hb : b ≠ (finProdFinEquiv.symm k).2 := by
        intro hb; apply hEq
        simpa [hb] using (finProdFinEquiv.apply_symm_apply k)
      simpa using (Function.update_of_ne hb (v := w) (f := z (finProdFinEquiv.symm k).1)).symm
    · have hz : Function.update z (finProdFinEquiv.symm k).1
            (Function.update (z (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 w) a = z a :=
          Function.update_of_ne ha _ _
      simpa using (congrFun hz b).symm

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

/-! ### Osgood's lemma for product-indexed domains -/

/-- **Osgood's Lemma for product-indexed domains**: A continuous function
    `f : (Fin n → Fin m → ℂ) → ℂ` on an open set `U` that is holomorphic in
    each coordinate `(i, j)` separately (with all others fixed) is jointly holomorphic.

    Proof: flatten the domain via `flattenCLE`, transport continuity and separate
    holomorphicity using `flattenCLE_symm_update`, apply `SCV.osgood_lemma`, then unflatten. -/
theorem SCV.osgood_lemma_product {n m : ℕ} {U : Set (Fin n → Fin m → ℂ)} (hU : IsOpen U)
    (f : (Fin n → Fin m → ℂ) → ℂ)
    (hf_cont : ContinuousOn f U)
    (hf_sep : ∀ z ∈ U, ∀ i : Fin n, ∀ j : Fin m,
      DifferentiableAt ℂ (fun w => f (Function.update z i (Function.update (z i) j w))) (z i j)) :
    DifferentiableOn ℂ f U := by
  let φ := SCV.flattenCLE n m
  let f' : (Fin (n * m) → ℂ) → ℂ := fun z => f (φ.symm z)
  have hU' : IsOpen (φ '' U) := (φ.toHomeomorph.isOpenMap U) hU
  have hf'_cont : ContinuousOn f' (φ '' U) := by
    refine hf_cont.comp φ.symm.continuous.continuousOn ?_
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    simpa using hx
  have hf'_sep : ∀ z ∈ φ '' U, ∀ k : Fin (n * m),
      DifferentiableAt ℂ (fun w => f' (Function.update z k w)) (z k) := by
    intro z hz k
    rcases hz with ⟨x, hx, rfl⟩
    let i : Fin n := (finProdFinEquiv.symm k).1
    let j : Fin m := (finProdFinEquiv.symm k).2
    have hfun : (fun w => f' (Function.update (φ x) k w)) =
        (fun w => f (Function.update x i (Function.update (x i) j w))) := by
      ext w
      change f (φ.symm (Function.update (φ x) k w)) =
        f (Function.update x i (Function.update (x i) j w))
      rw [show φ.symm (Function.update (φ x) k w) =
          Function.update x i (Function.update (x i) j w) from by
        simpa [φ, i, j] using SCV.flattenCLE_symm_update x k w]
    have hpoint : (φ x) k = x i j := by
      simp [φ, SCV.flattenCLE_apply, i, j]
    rw [hfun, hpoint]
    exact hf_sep x hx i j
  have hflat : DifferentiableOn ℂ f' (φ '' U) :=
    SCV.osgood_lemma hU' f' hf'_cont hf'_sep
  -- Unflatten: f = f' ∘ φ, and φ maps U homeomorphically to φ '' U
  have hcomp : DifferentiableOn ℂ (f' ∘ φ) U :=
    hflat.comp φ.differentiableOn (fun z hz => Set.mem_image_of_mem φ hz)
  have hEq : (f' ∘ φ) = f := by ext z; simp [f', Function.comp]
  rwa [hEq] at hcomp

end
