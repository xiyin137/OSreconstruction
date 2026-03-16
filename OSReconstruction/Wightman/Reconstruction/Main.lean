/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.GNSHilbertSpace
import OSReconstruction.Wightman.Reconstruction.WickRotation

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
