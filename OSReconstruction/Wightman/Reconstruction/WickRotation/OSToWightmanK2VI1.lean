/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1Support
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1InputA
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1InputAInvariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1InputAKernelReduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1InputAFixedTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1InputAWitness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1DCT

/-!
# OS to Wightman `k = 2` VI.1 Frontier

This file now contains only the surviving OS II Section VI.1 `k = 2` frontier:
the direct descended-shell convergence seam behind the probe limit and the
final distributional assembly theorem.

All proved support infrastructure has been moved to `OSToWightmanK2VI1Support.lean` so that the hard `sorry`s stay on a small, readable theorem surface.
-/

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal
open BigOperators Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

variable {d : ℕ} [NeZero d]

private theorem exists_fixed_strip_fixedTimeKernel_constBound_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ)
    (hs : 0 < s)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) :
    let K := OSReconstruction.twoPointFixedTimeKernel G (((s + s) : ℂ) * Complex.I)
    Continuous K ∧
      ∃ (C_bd : ℝ),
        ∃ hC : 0 < C_bd,
          ∃ hK_meas : AEStronglyMeasurable K volume,
            ∀ᵐ x : NPointDomain d 2 ∂volume,
              ‖K x‖ ≤ C_bd := by
  /-
  Genuine remaining Input A seam after the fixed-strip product-shell theorem:

  establish the analytic control of the standard fixed-time kernel on the real
  positive-time section, with the common Euclidean witness `G` still exposed on
  the surface.

  Once this smaller real-section package is available, the verified transport
  theorem in `OSToWightmanK2VI1InputAFixedTime.lean` upgrades it formally to the
  center/difference polynomial package required by the kernel-reduction layer.
  -/
  sorry

private theorem exists_fixed_strip_fixedTimeCenterDiff_productShell_to_difference_local
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_int : ∀ n, ∫ u : SpacetimeDim d, φ_seq n u = 1)
    (K₂ : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K₂ volume)
    (C_bd : ℝ)
    (N : ℕ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K₂ x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    ∀ n,
      let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
        OSReconstruction.twoPointFlatKernelCLM K₂ hK_meas C_bd N hC hK_bound
      T (OSReconstruction.reindexSchwartzFin
            (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift (φ_seq n)
                  (reflectedSchwartzSpacetime (φ_seq n)))))) =
        T (OSReconstruction.reindexSchwartzFin
            (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift (φ_seq n)
                  (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                    (reflectedSchwartzSpacetime (φ_seq n))))))) := by
  /-
  Honest remaining Input A family-level descent seam after the weaker kernel
  reduction: for the concrete fixed-strip `xiShift` kernel package, prove the
  product shell -> canonical difference shell equality.
  -/
  sorry

private theorem exists_fixed_strip_fixedTimeCenterDiff_center_replacement_local
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_int : ∀ n, ∫ u : SpacetimeDim d, φ_seq n u = 1)
    (K₂ : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K₂ volume)
    (C_bd : ℝ)
    (N : ℕ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K₂ x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    ∀ n,
      let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
        OSReconstruction.twoPointFlatKernelCLM K₂ hK_meas C_bd N hC hK_bound
      T (OSReconstruction.reindexSchwartzFin
            (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift (φ_seq n)
                  (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                    (reflectedSchwartzSpacetime (φ_seq n))))))) =
        T (OSReconstruction.reindexSchwartzFin
            (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χc
                  (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                    (reflectedSchwartzSpacetime (φ_seq n))))))) := by
  /-
  Honest remaining Input A family-level descent seam after the weaker kernel
  reduction: for the concrete fixed-time center/difference kernel package, prove the
  auxiliary normalized center-cutoff replacement equality.
  -/
  sorry

private theorem exists_fixed_strip_common_difference_kernel_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (s : ℝ)
    (hs : 0 < s) :
    ∃ K_s : SpacetimeDim d → ℂ,
      Continuous K_s ∧
      (∀ n,
        let xφ : OSHilbertSpace OS :=
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                  (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                    (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
              OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
          ∫ x : NPointDomain d 2,
            OSReconstruction.twoPointDifferenceKernel K_s x *
              (twoPointDifferenceLift χ₀
                (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                  (reflectedSchwartzSpacetime (φ_seq n))) x)) := by
  obtain ⟨G, hG_holo, hG_euclid, hprod⟩ :=
    OSReconstruction.exists_common_fixed_strip_fixedTimeCenterDiff_productShell_pairing_with_witness_local
      (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg (s + s) (add_pos hs hs)
  obtain ⟨hK_fixed_cont, C0, hC0, hK_fixed_meas, hK_fixed_bdd⟩ :=
    exists_fixed_strip_fixedTimeKernel_constBound_package_local
      (d := d) OS lgc s hs G hG_holo hG_euclid
  obtain ⟨hK_cont, C_bd, N, hC, hK_meas, hK_bound⟩ :=
    OSReconstruction.exists_polyBound_package_twoPointFixedTimeCenterDiffKernel_of_constBound_local
      (d := d) G (((s + s) : ℂ) * Complex.I) hK_fixed_cont hK_fixed_meas C0 hC0 hK_fixed_bdd
  obtain ⟨χc_seq, _hχc_nonneg, _hχc_real, hχc_int, hχc_compact, _hχc_neg, _hχc_ball⟩ :=
    exists_negative_approx_identity_sequence (d := d)
  let χc : SchwartzSpacetime d := χc_seq 0
  have hdesc :
      ∀ n,
        let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
          OSReconstruction.twoPointFlatKernelCLM
            (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
              (d := d) G ((((s + s) : ℂ) * Complex.I)))
            hK_meas C_bd N hC hK_bound
        T (OSReconstruction.reindexSchwartzFin
              (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
              (OSReconstruction.flattenSchwartzNPoint (d := d)
                (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointProductLift (φ_seq n)
                    (reflectedSchwartzSpacetime (φ_seq n)))))) =
            T (OSReconstruction.reindexSchwartzFin
              (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
              (OSReconstruction.flattenSchwartzNPoint (d := d)
                (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift (φ_seq n)
                    (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                      (reflectedSchwartzSpacetime (φ_seq n))))))) :=
    exists_fixed_strip_fixedTimeCenterDiff_productShell_to_difference_local
      (d := d) χc (hχc_int 0) φ_seq hφ_int
      (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
        (d := d) G ((((s + s) : ℂ) * Complex.I))) hK_meas C_bd N hC hK_bound
  have hcenter :
      ∀ n,
        let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
          OSReconstruction.twoPointFlatKernelCLM
            (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
              (d := d) G ((((s + s) : ℂ) * Complex.I)))
            hK_meas C_bd N hC hK_bound
        T (OSReconstruction.reindexSchwartzFin
              (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
              (OSReconstruction.flattenSchwartzNPoint (d := d)
                (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift (φ_seq n)
                    (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                      (reflectedSchwartzSpacetime (φ_seq n))))))) =
            T (OSReconstruction.reindexSchwartzFin
              (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
              (OSReconstruction.flattenSchwartzNPoint (d := d)
                (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χc
                    (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                      (reflectedSchwartzSpacetime (φ_seq n))))))) :=
    exists_fixed_strip_fixedTimeCenterDiff_center_replacement_local
      (d := d) χc (hχc_int 0) φ_seq hφ_int
      (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
        (d := d) G ((((s + s) : ℂ) * Complex.I))) hK_meas C_bd N hC hK_bound
  let I : ℕ → ℂ := fun n =>
    let xφ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
          OSHilbertSpace OS))
    osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ)
  have hdesc_compact : ∀ n,
      HasCompactSupport
        (((OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
          (reflectedSchwartzSpacetime (φ_seq n))) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) := by
    intro n
    rcases (hφ_compact n).isCompact.isBounded.subset_closedBall (0 : SpacetimeDim d) with ⟨Rφ, hRφ⟩
    rcases (reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n) (hφ_compact n)).isCompact.isBounded.subset_closedBall
      (0 : SpacetimeDim d) with ⟨Rψ, hRψ⟩
    let Rφ' : ℝ := max Rφ 0
    let Rψ' : ℝ := max Rψ 0
    let Rφ'' : ℝ := Rφ' + 1
    let Rψ'' : ℝ := Rψ' + 1
    have hRφ' : tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆ Metric.closedBall (0 : SpacetimeDim d) Rφ' := by
      intro x hx
      exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hRφ hx)
    have hRψ' :
        tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ) ⊆
          Metric.closedBall (0 : SpacetimeDim d) Rψ' := by
      intro x hx
      exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hRψ hx)
    have hRφ'' : tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆ Metric.ball (0 : SpacetimeDim d) Rφ'' := by
      intro x hx
      have hx' : dist x 0 ≤ Rφ' := by
        simpa [Metric.mem_closedBall] using hRφ' hx
      have hx'' : dist x 0 < Rφ'' := by
        dsimp [Rφ''] at *
        linarith
      simpa [Metric.mem_ball] using hx''
    have hRψ'' :
        tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ) ⊆
          Metric.ball (0 : SpacetimeDim d) Rψ'' := by
      intro x hx
      have hx' : dist x 0 ≤ Rψ' := by
        simpa [Metric.mem_closedBall] using hRψ' hx
      have hx'' : dist x 0 < Rψ'' := by
        dsimp [Rψ''] at *
        linarith
      simpa [Metric.mem_ball] using hx''
    have hclosed :=
      OSReconstruction.twoPointCenterShearDescent_tsupport_subset_closedBall
        (d := d) (φ_seq n) (reflectedSchwartzSpacetime (φ_seq n))
        (by positivity) (by positivity) hRφ'' hRψ''
    exact HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : SpacetimeDim d) (Rφ'' + Rψ''))
      (fun x hx => hclosed (subset_tsupport _ hx))
  have hpair : ∀ n,
      I n =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1)) := by
    intro n
    simpa [I] using hprod n
  exact OSReconstruction.exists_common_difference_kernel_of_common_productShell_pairing_local
    (d := d) χc (hχc_int 0) (hχc_compact 0) χ₀ hχ₀
    (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
      (d := d) G ((((s + s) : ℂ) * Complex.I)))
    hK_cont hK_meas C_bd N hC hK_bound
    φ_seq (fun n => reflectedSchwartzSpacetime (φ_seq n)) hφ_int hdesc_compact
    hdesc hcenter I hpair

private theorem exists_fixed_strip_diagonal_limit_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : ℝ)
    (hs : 0 < s) :
    ∃ z : ℂ,
      Filter.Tendsto
        (fun n =>
          let xφ : OSHilbertSpace OS :=
            (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single 1
                    (SchwartzNPoint.osConj (d := d) (n := 1)
                      (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                    (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
                OSHilbertSpace OS))
          osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ))
        Filter.atTop
        (nhds z) := by
  obtain ⟨K_s, hK_cont, hpair⟩ :=
    exists_fixed_strip_common_difference_kernel_local
      OS lgc χ₀ hχ₀ φ_seq hφ_real hφ_int hφ_compact hφ_neg s hs
  exact
    OSReconstruction.exists_fixed_strip_diagonal_limit_of_difference_kernel_pairing_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int
      hφ_compact hφ_neg hφ_ball s hs K_s hK_cont hpair

private theorem exists_shell_pointwise_limit_function_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ g : SpacetimeDim d → ℂ,
      (∀ᵐ ξ : SpacetimeDim d ∂volume,
        Filter.Tendsto
          (fun n =>
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ))
          Filter.atTop
          (nhds (g ξ * ((h : SchwartzSpacetime d) ξ)))) ∧
      ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h =
        ∫ ξ : SpacetimeDim d, g ξ * ((h : SchwartzSpacetime d) ξ)) := by
  /-
  Genuine remaining Input B:

  identify the pointwise almost-everywhere shell limit and the corresponding
  target integral. The intended direct OS route is again a descended-center
  approximate-identity argument on the positive-time shell, using the orbit
  continuity layer from `OSToWightmanK2VI1OrbitBridge.lean`.
  -/
  sorry

private theorem k2Probe_pairing_fixed_normalized_center_tendsto_schwingerDifferencePositive_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
          twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
        (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      Filter.Tendsto
        (fun n =>
          ∫ x : NPointDomain d 2,
            k2TimeParametricKernel (d := d)
                (k2ProbeWitness_local (d := d) OS lgc
                  (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
              twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x)
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) := by
  intro h
  obtain ⟨ε, hε_pos, hmargin0⟩ :=
    exists_positive_time_margin_of_mem_positiveTimeCompactSupport_local (d := d) h
  have hs : 0 < ε / 4 := by linarith
  have hmargin :
      tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | ε / 4 + ε / 4 < ξ 0} := by
    refine Set.Subset.trans hmargin0 ?_
    intro ξ hξ
    simp only [Set.mem_setOf] at hξ ⊢
    linarith
  obtain ⟨z, hdiag⟩ :=
    exists_fixed_strip_diagonal_limit_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int
      hφ_compact hφ_neg hφ_ball (ε / 4) hs
  obtain ⟨g, hpointwise, htarget⟩ :=
    exists_shell_pointwise_limit_function_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball h
  have hshell :
      Filter.Tendsto
        (fun n =>
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ))
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) :=
    OSReconstruction.translatedProductShell_boundary_tendsto_of_tendsto_damped_diagonal_and_ae_pointwise_vi1DCT_local
      (d := d) OS lgc χ₀ φ_seq hφ_real hφ_compact hφ_neg h (ε / 4) hs
      hmargin g hdiag hpointwise htarget
  refine Filter.Tendsto.congr' ?_ hshell
  filter_upwards with n
  simpa [hχ₀, one_mul] using (hpair n χ₀ h).symm

private theorem k2DifferenceKernel_real_pairing_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
          twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
        (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      Filter.Tendsto
        (fun n =>
          ∫ ξ : SpacetimeDim d,
            k2DifferenceKernel_real_local (μ_seq n) ξ *
              (h : SchwartzSpacetime d) ξ)
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) := by
  intro h
  have hpair_fixed :
      ∀ n,
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (μ_seq n) ξ *
            (h : SchwartzSpacetime d) ξ =
          ∫ x : NPointDomain d 2,
            k2TimeParametricKernel (d := d)
                (k2ProbeWitness_local (d := d) OS lgc
                  (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
              twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
    intro n
    exact integral_k2DifferenceKernel_real_eq_probe_pairing_fixed_normalized_center_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_int hφ_ball hφ_real hφ_compact
      hφ_neg μ_seq _hμfin hsupp hμrepr hpair n h
  simpa [hpair_fixed] using
    k2Probe_pairing_fixed_normalized_center_tendsto_schwingerDifferencePositive_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball hpair h

private theorem translatedProductShell_boundary_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
          twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
        (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      Filter.Tendsto
        (fun n =>
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ))
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) := by
  intro h
  have hred :=
    k2DifferenceKernel_real_pairing_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local
      OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball μ_seq _hμfin hsupp hμrepr hpair h
  refine Filter.Tendsto.congr' ?_ hred
  filter_upwards with n
  exact
    integral_translatedProductShell_boundary_eq_reduced_differenceKernel_pairing_of_negativeApproxIdentity_local
      OS lgc φ_seq hφ_real hφ_compact hφ_neg μ_seq _hμfin hsupp hμrepr n h |>.symm

/-- Route-independent final payoff: once an honest Euclidean two-point kernel
has the correct sector formulas, measurable polynomial bounds, and agreement
with `OS.S 2` on the flat-origin difference-shell generators, reproduction on
all of `ZeroDiagonalSchwartz d 2` is purely formal. This packages the last
non-VI.1 bookkeeping step so the remaining assembly theorem only has to produce
the limiting witness/kernel data. -/
private theorem k2_distributional_reproduction_of_flatOrigin_shell_agreement_local
    (OS : OsterwalderSchraderAxioms d)
    (K : NPointDomain d 2 → ℂ)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hShell :
      ∀ (χ h : SchwartzSpacetime d)
        (hzero : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0),
        OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
            (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)))
    (f : ZeroDiagonalSchwartz d 2) :
    OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x) := by
  have hCLM :
      OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound =
        OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2 :=
    zeroDiagKernelCLM_eq_schwinger_of_flatOrigin_differenceShell_agreement
      (d := d) OS K hK_meas C_bd N hC hK_bound hShell
  have happly :=
    congrArg (fun L : ZeroDiagonalSchwartz d 2 →L[ℂ] ℂ => L f) hCLM
  simpa [OSReconstruction.twoPointZeroDiagonalKernelCLM_apply] using happly.symm

private theorem exists_k2_timeParametric_distributional_assembly
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) (K : NPointDomain d 2 → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ x : NPointDomain d 2, x 0 0 < x 1 0 →
        K x = k2TimeParametricKernel (d := d) G x) ∧
      (∀ x : NPointDomain d 2, x 1 0 < x 0 0 →
        K x = k2TimeParametricKernel (d := d) G
          (fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i))) ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x)) := by
  /-
  Honest remaining assembly step after the VI.1 refactor:

  * obtain the shrinking negative approximate-identity sequence and its
    per-probe shell package from `exists_k2_VI1_regularization_input_local`;
  * use
    `translatedProductShell_boundary_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local`
    to identify the reduced boundary functional on the positive-time edge;
  * choose the resulting honest Euclidean kernel/witness pair `(G, K)` coming
    from the OS II VI.1 limit construction, not from a single fixed probe;
  * discharge the final reproduction clause through
    `k2_distributional_reproduction_of_flatOrigin_shell_agreement_local`.
  -/
  sorry

/-- The `k = 2` time-parametric base step on the honest OS route.

The previous kernel / difference-lift transport chain has been removed from the
critical path. The remaining gap is now exactly the OS-faithful semigroup /
distributional assembly theorem. -/
theorem schwinger_continuation_base_step_timeParametric_k2
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) (K : NPointDomain d 2 → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ x : NPointDomain d 2, x 0 0 < x 1 0 →
        K x = k2TimeParametricKernel (d := d) G x) ∧
      (∀ x : NPointDomain d 2, x 1 0 < x 0 0 →
        K x = k2TimeParametricKernel (d := d) G
          (fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i))) ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x)) := by
  exact exists_k2_timeParametric_distributional_assembly OS lgc

end
