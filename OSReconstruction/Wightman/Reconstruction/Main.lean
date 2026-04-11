/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.GNSHilbertSpace
import OSReconstruction.Wightman.Reconstruction.WickRotation
import OSReconstruction.GeneralResults.DenseIsometryExtension
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Main Reconstruction Theorems (Wiring)

This file assembles the main reconstruction theorems by wiring together
proofs from the GNS construction and Wick rotation modules.

## Main Results

* `wightman_reconstruction` — Given Wightman functions, reconstruct a Wightman QFT
  whose n-point functions match on product test functions.
  (Proof: GNS construction via `wightman_reconstruction'` in GNSHilbertSpace.lean)

* `wightman_uniqueness` — Two Wightman QFTs with matching n-point functions are
  unitarily equivalent. (Sorry: standard GNS uniqueness argument)

* `wightman_to_os` — Theorem R→E: Wightman functions → honest zero-diagonal
  Euclidean Schwinger family on the Euclidean side
  (Proof: `wightman_to_os_full` in WickRotation.lean)

* `os_to_wightman` — Theorem E'→R': corrected OS axioms with linear growth →
  Wightman functions
  (Proof: `os_to_wightman_full` in WickRotation.lean)

## Import Structure

This file exists to resolve circular import constraints:
- `Reconstruction.lean` defines `WightmanFunctions`, `OsterwalderSchraderAxioms`, etc.
- `GNSHilbertSpace.lean` imports `Reconstruction.lean` (needs `WightmanFunctions`)
-- `WickRotation.lean` imports `Reconstruction.lean` (needs `IsWickRotationPair`)
- This file imports both and wires the proofs.
-/

noncomputable section

open Reconstruction

variable {d : ℕ} [NeZero d]

/-- **Wightman Reconstruction Theorem**: Given Wightman functions satisfying all
    required properties, there exists a Wightman QFT whose n-point functions
    reproduce the given Wightman functions on product test functions:
      ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ)

    The Hilbert space is constructed via the GNS construction:
    1. Form the Borchers algebra of test function sequences
    2. Define the inner product from the Wightman 2-point function
    3. Quotient by null vectors to get the pre-Hilbert space
    4. Complete to obtain the Hilbert space
    5. Field operators act by prepending test functions to sequences

    References: Wightman (1956), Streater-Wightman (1964) Chapter 3 -/
theorem wightman_reconstruction (Wfn : WightmanFunctions d) :
    ∃ (qft : WightmanQFT.{0} d),
      ∀ (n : ℕ) (fs : Fin n → SchwartzSpacetime d),
        qft.wightmanFunction n fs = Wfn.W n (SchwartzMap.productTensor fs) :=
  wightman_reconstruction' Wfn

/-- **Wightman Uniqueness**: Two Wightman QFTs with the same smeared n-point functions
    are unitarily equivalent.

    More precisely, if for all n and all test functions f₁,...,fₙ we have
      ⟨Ω₁, φ₁(f₁)···φ₁(fₙ)Ω₁⟩ = ⟨Ω₂, φ₂(f₁)···φ₂(fₙ)Ω₂⟩
    then there exists a unitary U : H₁ → H₂ such that:
      - U Ω₁ = Ω₂
      - U intertwines the field operators: U φ₁(f) U⁻¹ = φ₂(f) for all f -/
theorem wightman_uniqueness (qft₁ qft₂ : WightmanQFT d)
    (h : ∀ n : ℕ, ∀ fs : Fin n → SchwartzSpacetime d,
      qft₁.wightmanFunction n fs = qft₂.wightmanFunction n fs) :
    ∃ U : qft₁.HilbertSpace →ₗᵢ[ℂ] qft₂.HilbertSpace,
      U qft₁.vacuum = qft₂.vacuum ∧
      (∀ (f : SchwartzSpacetime d) (ψ : qft₁.HilbertSpace),
        ψ ∈ qft₁.field.domain →
        U (qft₁.field.operator f ψ) = qft₂.field.operator f (U ψ)) := by
  classical
  let Gen : Type := Σ n : ℕ, Fin n → SchwartzSpacetime d
  let toVec₁ : Gen → qft₁.HilbertSpace := fun g =>
    qft₁.field.operatorPow g.1 g.2 qft₁.vacuum
  let toVec₂ : Gen → qft₂.HilbertSpace := fun g =>
    qft₂.field.operatorPow g.1 g.2 qft₂.vacuum
  let S₁ : Submodule ℂ qft₁.HilbertSpace := Submodule.span ℂ (Set.range toVec₁)
  let S₂ : Submodule ℂ qft₂.HilbertSpace := qft₂.field.algebraicSpan qft₂.vacuum
  let L₁ : (Gen →₀ ℂ) →ₗ[ℂ] qft₁.HilbertSpace :=
    Finsupp.linearCombination ℂ toVec₁
  let L₂ : (Gen →₀ ℂ) →ₗ[ℂ] qft₂.HilbertSpace :=
    Finsupp.linearCombination ℂ toVec₂
  have hGenSet :
      Set.range toVec₁ =
        { ψ : qft₁.HilbertSpace |
          ∃ (n : ℕ) (fs : Fin n → SchwartzSpacetime d),
            ψ = qft₁.field.operatorPow n fs qft₁.vacuum } := by
    ext ψ
    constructor
    · rintro ⟨⟨n, fs⟩, rfl⟩
      exact ⟨n, fs, rfl⟩
    · rintro ⟨n, fs, rfl⟩
      exact ⟨⟨n, fs⟩, rfl⟩
  have hDenseS₁ : Dense (S₁ : Set qft₁.HilbertSpace) := by
    simpa [S₁, OperatorValuedDistribution.algebraicSpan, hGenSet] using qft₁.cyclicity
  have hRange : S₁ = L₁.range := by
    simpa [S₁, L₁] using (Finsupp.range_linearCombination (R := ℂ) (v := toVec₁)).symm
  have hFormalInner :
      ∀ c d : Gen →₀ ℂ,
        inner ℂ (L₂ c) (L₂ d) = inner ℂ (L₁ c) (L₁ d) := by
    have hGenInner :
        ∀ g₁ g₂ : Gen,
          inner ℂ (toVec₂ g₁) (toVec₂ g₂) = inner ℂ (toVec₁ g₁) (toVec₁ g₂) := by
      -- Generator case: move the left operator power to the right using
      -- `field_hermitian`, identify both sides with the same Wightman
      -- function, then apply `h`.
      sorry
    intro c d
    calc
      inner ℂ (L₂ c) (L₂ d)
          = d.sum (fun g₂ a₂ =>
              a₂ * c.sum (fun g₁ a₁ =>
                star a₁ * inner ℂ (toVec₂ g₁) (toVec₂ g₂))) := by
            simp [L₂, Finsupp.linearCombination_apply, Finsupp.sum_inner,
              Finsupp.inner_sum, inner_smul_left, inner_smul_right]
      _ = d.sum (fun g₂ a₂ =>
            a₂ * c.sum (fun g₁ a₁ =>
              star a₁ * inner ℂ (toVec₁ g₁) (toVec₁ g₂))) := by
            simp_rw [hGenInner]
      _ = inner ℂ (L₁ c) (L₁ d) := by
            simp [L₁, Finsupp.linearCombination_apply, Finsupp.sum_inner,
              Finsupp.inner_sum, inner_smul_left, inner_smul_right]
  have hker : LinearMap.ker L₁ ≤ LinearMap.ker L₂ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have hself := hFormalInner c c
    rw [hc] at hself
    have hzero : inner ℂ (L₂ c) (L₂ c) = 0 := by
      simpa using hself
    exact inner_self_eq_zero.mp hzero
  let Tq : ((Gen →₀ ℂ) ⧸ LinearMap.ker L₁) →ₗ[ℂ] qft₂.HilbertSpace :=
    (LinearMap.ker L₁).liftQ L₂ hker
  let eRange : ((Gen →₀ ℂ) ⧸ LinearMap.ker L₁) ≃ₗ[ℂ] S₁ :=
    L₁.quotKerEquivRange.trans (LinearEquiv.ofEq L₁.range S₁ hRange.symm)
  let TspanLin : S₁ →ₗ[ℂ] qft₂.HilbertSpace :=
    Tq.comp eRange.symm.toLinearMap
  have hTspanInner :
      ∀ x y : S₁,
        inner ℂ (TspanLin x) (TspanLin y) = inner ℂ x y := by
    intro x y
    obtain ⟨qx, rfl⟩ := eRange.surjective x
    obtain ⟨qy, rfl⟩ := eRange.surjective y
    simp [TspanLin]
    refine Quotient.inductionOn₂ qx qy ?_
    intro c d
    simpa [Tq, eRange] using hFormalInner c d
  let Tspan : S₁ →ₗᵢ[ℂ] qft₂.HilbertSpace :=
    LinearMap.isometryOfInner TspanLin hTspanInner
  obtain ⟨U, hUext⟩ :=
    dense_submodule_isometry_extension S₁ hDenseS₁ Tspan
  have hgen_mem₁ :
      ∀ n (fs : Fin n → SchwartzSpacetime d),
        qft₁.field.operatorPow n fs qft₁.vacuum ∈ S₁ := by
    intro n fs
    exact Submodule.subset_span (by
      show qft₁.field.operatorPow n fs qft₁.vacuum ∈ Set.range toVec₁
      exact ⟨⟨n, fs⟩, rfl⟩)
  have hgen_mem₂ :
      ∀ n (fs : Fin n → SchwartzSpacetime d),
        qft₂.field.operatorPow n fs qft₂.vacuum ∈ S₂ := by
    intro n fs
    exact Submodule.subset_span ⟨n, fs, rfl⟩
  have hTspan_gen :
      ∀ n (fs : Fin n → SchwartzSpacetime d),
        Tspan ⟨qft₁.field.operatorPow n fs qft₁.vacuum, hgen_mem₁ n fs⟩ =
          qft₂.field.operatorPow n fs qft₂.vacuum := by
    intro n fs
    let g : Gen := ⟨n, fs⟩
    let c : Gen →₀ ℂ := Finsupp.single g 1
    have hc :
        eRange (Submodule.Quotient.mk c) =
          ⟨qft₁.field.operatorPow n fs qft₁.vacuum, hgen_mem₁ n fs⟩ := by
      ext
      change (L₁ c : qft₁.HilbertSpace) = qft₁.field.operatorPow n fs qft₁.vacuum
      simp [L₁, c, g, toVec₁]
    have hq :
        eRange.symm ⟨qft₁.field.operatorPow n fs qft₁.vacuum, hgen_mem₁ n fs⟩ =
          Submodule.Quotient.mk c := by
      exact eRange.symm_apply_eq.mpr hc.symm
    change TspanLin ⟨qft₁.field.operatorPow n fs qft₁.vacuum, hgen_mem₁ n fs⟩ =
      qft₂.field.operatorPow n fs qft₂.vacuum
    rw [show TspanLin ⟨qft₁.field.operatorPow n fs qft₁.vacuum, hgen_mem₁ n fs⟩ =
        Tq (eRange.symm ⟨qft₁.field.operatorPow n fs qft₁.vacuum, hgen_mem₁ n fs⟩) by rfl]
    rw [hq, Submodule.liftQ_apply]
    simp [L₂, toVec₂, c, g]
  refine ⟨U, ?_, ?_⟩
  · let Ω₁S : S₁ := ⟨qft₁.vacuum, hgen_mem₁ 0 (fun i => Fin.elim0 i)⟩
    have hΩ : U Ω₁S =
        qft₂.vacuum := by
      rw [hUext]
      simpa [Ω₁S, OperatorValuedDistribution.operatorPow] using
        (hTspan_gen 0 (fun i => Fin.elim0 i))
    simpa using hΩ
  · intro f ψ hψ
    -- The extension constructed above intertwines the fields on the cyclic span.
    -- Extending this from the cyclic span to the full common domain requires an
    -- additional domain-compatibility argument that is not yet formalized here.
    sorry

/-- **Theorem R→E** (Wightman -> zero-diagonal Euclidean side): a Wightman QFT,
    together with explicit forward-tube growth input for its holomorphic
    continuation, yields an honest zero-diagonal Schwinger family related to
    the Wightman functions by Wick rotation.

    The Schwinger functionals are only packaged on `ZeroDiagonalSchwartz` in this
    direction; no full-Schwartz OS-II extension is claimed here. This is
    intentional: the natural Euclidean kernels may have inverse-power
    coincidence singularities, and the honest general pairing surface is the
    zero-diagonal test space. The extra growth input is kept separate from
    `WightmanFunctions` so the core distributional theorem surface is not
    strengthened globally. -/
theorem wightman_to_os (Wfn : WightmanFunctions d) :
    ∃ (S : SchwingerFunctions d),
      (∀ n, Continuous (S n)) ∧
      (∀ n, IsLinearMap ℂ (S n)) ∧
      IsWickRotationPair S Wfn.W :=
  wightman_to_os_full Wfn

/-- **Theorem E'→R'** (OS II): Schwinger functions satisfying the linear growth
    condition E0' together with E1-E4 can be analytically continued to
    Wightman distributions satisfying R0-R5.

    **Critical**: Without the linear growth condition, this theorem may be FALSE.
    The issue is that analytic continuation involves infinitely many Sₖ, and
    without growth control, the boundary values may fail to be tempered.

    The input `OsterwalderSchraderAxioms` is already the corrected OS surface:
    its E0 temperedness clause is only on `ZeroDiagonalSchwartz`. The extra
    OS-II content used here is the linear growth condition, not a return to a
    false full-Schwartz Euclidean axiom.

    The main mathematical content is exactly the hard passage from Euclidean
    Schwinger data on `ZeroDiagonalSchwartz` to full tempered Wightman
    distributions on Schwartz space. If that passage were already built into the
    Euclidean hypothesis, there would be little OS reconstruction left to prove. -/
theorem os_to_wightman (OS : OsterwalderSchraderAxioms d)
    (linear_growth : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      IsWickRotationPair OS.schwinger Wfn.W :=
  os_to_wightman_full OS linear_growth

end
