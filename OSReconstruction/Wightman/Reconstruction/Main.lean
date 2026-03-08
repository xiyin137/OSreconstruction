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

* `wightman_reconstruction` — Given Wightman functions together with the remaining
  operator-side inputs not yet formalized in the GNS layer, reconstruct a
  Wightman QFT whose n-point functions match on product test functions.
  (Proof: GNS construction via `wightman_reconstruction'` in GNSHilbertSpace.lean)

* `wightman_to_os` — Theorem R→E: Wightman functions together with the required
  forward-tube regularity data, the explicit BHW permutation/connectedness inputs,
  the Euclidean Wick polynomial bound, and the a.e.-PET Wick-rotation input →
  Schwinger functions (OS axioms)
  (Proof: `wightman_to_os_full` in WickRotation.lean)

* `os_to_wightman` — Theorem E'→R': Schwinger functions with linear growth
  together with the explicit forward-tube boundary-value package and explicit
  transfer inputs → Wightman functions
  (Proof: `os_to_wightman_full` in WickRotation.lean)

## Import Structure

This file exists to resolve circular import constraints:
- `Reconstruction.lean` defines `WightmanFunctions`, `OsterwalderSchraderAxioms`, etc.
- `GNSHilbertSpace.lean` imports `Reconstruction.lean` (needs `WightmanFunctions`)
- `WickRotation.lean` imports `Reconstruction.lean` (needs `IsWickRotationPair`)
- This file imports both and wires the proofs.
-/

noncomputable section

open Reconstruction

variable {d : ℕ} [NeZero d]

/-- **Wightman Reconstruction Theorem**: Given Wightman functions together with the
    remaining operator-side inputs not yet formalized in the GNS layer, there
    exists a Wightman QFT whose n-point functions reproduce the given Wightman
    functions on product test functions:
      ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ)

    The Hilbert space is constructed via the GNS construction:
    1. Form the Borchers algebra of test function sequences
    2. Define the inner product from the Wightman 2-point function
    3. Quotient by null vectors to get the pre-Hilbert space
    4. Complete to obtain the Hilbert space
    5. Field operators act by prepending test functions to sequences

    References: Wightman (1956), Streater-Wightman (1964) Chapter 3 -/
theorem wightman_reconstruction (Wfn : WightmanFunctions d)
    (hSpectrum : SpectralCondition d (gnsPoincareRep Wfn))
    (hCyclic : Dense ((OperatorValuedDistribution.algebraicSpan (gnsField Wfn)
      (PreHilbertSpace.gnsVacuum Wfn)).carrier : Set (PreHilbertSpace.GNSHilbertSpace Wfn)))
    (hVacuumUnique : VacuumUnique d (gnsPoincareRep Wfn) (PreHilbertSpace.gnsVacuum Wfn)) :
    ∃ (qft : WightmanQFT.{0} d),
      ∀ (n : ℕ) (fs : Fin n → SchwartzSpacetime d),
        qft.wightmanFunction n fs = Wfn.W n (SchwartzMap.productTensor fs) :=
  wightman_reconstruction' Wfn hSpectrum hCyclic hVacuumUnique

/-- **Theorem R→E** (Wightman → OS): A Wightman QFT together with the required
    forward-tube regularity data, the explicit BHW permutation/connectedness
    inputs, and the explicit E0/E1a/E2/E4 transport inputs yields Schwinger
    functions satisfying OS axioms E0-E4, related by Wick rotation.

    The Schwinger functions are Euclidean restrictions of the BHW analytic
    continuation, whose boundary values are the Wightman functions. -/
theorem wightman_to_os (Wfn : WightmanFunctions d)
    (hRegular : ∀ n : ℕ,
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
        ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 : ∀ n : ℕ,
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) n σ))
    (hExtPerm_d1 : ∀ n : ℕ,
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 →
        ∀ (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d n →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d n →
          BHW.extendF ((Wfn.spectrum_condition n).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition n).choose) z)
    (hEuclidPoly : ∀ n : ℕ,
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
          ‖(W_analytic_BHW Wfn n (hRegular n) (hSeedConn_hd2 n) (hExtPerm_d1 n)).val (fun k => wickRotatePoint (x k))‖ ≤
            C_bd * (1 + ‖x‖) ^ N)
    (hPET_ae : ∀ n : ℕ,
      ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
        (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n)
    (hTranslation : ∀ (n : ℕ) (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun i => x i + a)) →
      constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n f =
        constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n g)
    (hReflectionPositive : ∀ (F : BorchersSequence d),
      (∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 →
        x ∈ PositiveTimeRegion d n) →
      (OSInnerProduct d (constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1) F F).re ≥ 0)
    (hCluster : ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
      (ε : ℝ), ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 (n + m) (f.tensorProduct g_a) -
              constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 n f *
              constructSchwingerFunctions Wfn hRegular hSeedConn_hd2 hExtPerm_d1 m g‖ < ε) :
    ∃ (OS : OsterwalderSchraderAxioms d),
      IsWickRotationPair OS.S Wfn.W :=
  wightman_to_os_full Wfn hRegular hSeedConn_hd2 hExtPerm_d1 hEuclidPoly hPET_ae
    hTranslation hReflectionPositive hCluster

/-- **Theorem E'→R'** (OS II): Schwinger functions satisfying the linear growth
    condition E0' together with an explicit forward-tube boundary-value package
    and the corresponding raw transfer inputs yield Wightman distributions
    satisfying R0-R5.

    **Critical**: Without the linear growth condition, this theorem may be FALSE.
    The issue is that analytic continuation involves infinitely many Sₖ, and
    without growth control, the boundary values may fail to be tempered. -/
theorem os_to_wightman (OS : OsterwalderSchraderAxioms d)
    (linear_growth : OSLinearGrowthCondition d OS)
    (hBVT : ∀ n : ℕ,
      ∃ (W_n : SchwartzNPoint d n → ℂ) (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        Continuous W_n ∧
        IsLinearMap ℂ W_n ∧
        DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
        (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
          InForwardCone d n η →
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d n,
              F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (W_n f))) ∧
        (∀ (f : SchwartzNPoint d n),
          OS.S n f = ∫ x : NPointDomain d n,
            F_analytic (fun k => wickRotatePoint (x k)) * (f x)))
    (hTranslation : ∀ (n : ℕ) (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun i => x i + a)) →
      (hBVT n).choose f = (hBVT n).choose g)
    (hLorentz : ∀ (n : ℕ) (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      (hBVT n).choose f = (hBVT n).choose g)
    (hLocal : ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      (hBVT n).choose f = (hBVT n).choose g)
    (hPositive : ∀ F : BorchersSequence d,
      (WightmanInnerProduct d (fun n => (hBVT n).choose) F F).re ≥ 0)
    (hHermitian : ∀ (n : ℕ) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      (hBVT n).choose g = starRingEnd ℂ ((hBVT n).choose f))
    (hCluster : ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖(hBVT (n + m)).choose (f.tensorProduct g_a) -
              (hBVT n).choose f * (hBVT m).choose g‖ < ε) :
    ∃ (Wfn : WightmanFunctions d),
      IsWickRotationPair OS.S Wfn.W :=
  os_to_wightman_full OS linear_growth hBVT
    hTranslation hLorentz hLocal hPositive hHermitian hCluster

end
