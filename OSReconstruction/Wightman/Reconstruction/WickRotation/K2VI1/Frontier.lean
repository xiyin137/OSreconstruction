/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Support
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputA
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAInvariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAKernelReduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTimeInvariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAHdescReduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAHeadBlockTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAOneVariableUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAShiftedRepresentative
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAWitness
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputACommonBoundary
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputADiffBlock
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputBPointwise
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCKernelPackage
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCCollarSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.DCT

/-!
# OS to Wightman `k = 2` VI.1 Frontier

This file now contains only the surviving OS II Section VI.1 `k = 2` frontier:
the direct descended-shell convergence seam behind the probe limit and the
final distributional assembly theorem.

All proved support infrastructure has been moved to `K2VI1/Support.lean` so that the hard `sorry`s stay on a small, readable theorem surface.
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

private theorem hasCompactSupport_twoPointCenterShearDescent_reflected_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ)) :
    ∀ n,
      HasCompactSupport
        (((OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
          (reflectedSchwartzSpacetime (φ_seq n))) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) := by
  intro n
  rcases (hφ_compact n).isCompact.isBounded.subset_closedBall (0 : SpacetimeDim d) with
    ⟨Rφ, hRφ⟩
  rcases (reflectedSchwartzSpacetime_hasCompactSupport
      (d := d) (φ_seq n) (hφ_compact n)).isCompact.isBounded.subset_closedBall
      (0 : SpacetimeDim d) with ⟨Rψ, hRψ⟩
  let Rφ' : ℝ := max Rφ 0
  let Rψ' : ℝ := max Rψ 0
  let Rφ'' : ℝ := Rφ' + 1
  let Rψ'' : ℝ := Rψ' + 1
  have hRφ' :
      tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
        Metric.closedBall (0 : SpacetimeDim d) Rφ' := by
    intro x hx
    exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hRφ hx)
  have hRψ' :
      tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ) ⊆
        Metric.closedBall (0 : SpacetimeDim d) Rψ' := by
    intro x hx
    exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hRψ hx)
  have hRφ'' :
      tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) Rφ'' := by
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

/- Legacy probe-Euclid route retained only for archeology while the common-`G`
repair is being completed. This block is no longer part of the active
production path. -/

/- private theorem exists_probeSeq_euclid_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∀ n (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f =
        ∫ x : NPointDomain d 2,
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
            (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x) := by
  /-
  Honest root Input A seam on the probe side:

  prove Euclidean reproduction for each probe witness on all zero-diagonal
  tests. Once this is available, the product-shell identity, fixed-center shell
  identity, and fixed-strip common-functional route are all formal from the
  current production support.
  -/
  sorry

private theorem exists_fixed_strip_shell_pairings_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χc : SchwartzSpacetime d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ)
    (ht : 0 < t) :
    (∀ n,
      ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) ∧
    (∀ n (h : SchwartzSpacetime d),
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} →
      ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) * h (z 1)) =
      ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χc (z 0) * h (z 1))) := by
  have hprobe_euclid :=
    exists_probeSeq_euclid_local
      (d := d) OS lgc φ_seq hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨?_, ?_⟩
  · intro n
    calc
      ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))
        =
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ t (0 : Fin d → ℝ) := by
          symm
          simpa using
            OSReconstruction.fixedTimeCenterDiff_productShell_pairing_eq_matrixElement_of_euclid_local
              (d := d) OS lgc G hG_euclid (φ_seq n) (hφ_real n) (hφ_compact n)
              (hφ_neg n) t ht
      _ =
      ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
          simpa using
            OSReconstruction.fixedTimeCenterDiff_productShell_pairing_eq_matrixElement_of_euclid_local
              (d := d) OS lgc
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq n) (hφ_compact n) (hφ_neg n))
              (hprobe_euclid n) (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n)
              t ht
  · intro n h hh_pos
    calc
      ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((t : ℂ) * Complex.I) z *
            (χc (z 0) * h (z 1))
        =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χc (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
          exact
            OSReconstruction.fixedTimeCenterDiffKernel_fixed_center_pairing_eq_schwinger_timeShift_local
              (d := d) OS G hG_euclid χc h hh_pos t ht
      _ =
      ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((t : ℂ) * Complex.I) z *
            (χc (z 0) * h (z 1)) := by
          symm
          exact
            OSReconstruction.fixedTimeCenterDiffKernel_fixed_center_pairing_eq_schwinger_timeShift_local
              (d := d) OS
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq n) (hφ_compact n) (hφ_neg n))
              (hprobe_euclid n) χc h hh_pos t ht

private theorem exists_shifted_realDifference_productShell_to_same_center_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (t : ℝ)
    (_ht : 0 < t)
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (hKpkg : ∀ n,
      ∃ (C_bd : ℝ) (N : ℕ), 0 < C_bd ∧
        AEStronglyMeasurable
          (fun z : NPointDomain d 2 =>
            k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t))
          volume ∧
        (∀ᵐ z : NPointDomain d 2 ∂volume,
          ‖k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t)‖ ≤
            C_bd * (1 + ‖z‖) ^ N)) :
    ∀ n,
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) *
            (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n))) (z 1)) := by
  /-
  Honest shifted-representative shell seam:

  because the explicit shifted real-difference representative depends only on
  the difference variable, it should pair equally with the reflected product
  shell and with its descended same-center representative.
  -/
  intro n
  rcases hKpkg n with ⟨C_bd, N, hC, hK_meas, hK_bound⟩
  exact
    OSReconstruction.shifted_realDifferenceKernel_productShell_to_same_center_of_package_local
      (d := d) (μ := μ_seq n) (t := t) hK_meas C_bd N hC hK_bound
      (φ_seq n) (hφ_int n) (reflectedSchwartzSpacetime (d := d) (φ_seq n))

private theorem exists_fixed_strip_aux_center_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (hχc_compact : HasCompactSupport (χc : SpacetimeDim d → ℂ))
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (s : ℝ)
    (hs : 0 < s)
    (hprod : ∀ n,
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1))) :
    ∀ n,
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      let hdesc_n : SchwartzSpacetime d :=
        OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
          (reflectedSchwartzSpacetime (φ_seq n))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            (χc (z 0) * hdesc_n (z 1)) := by
  have hcommon_probe_shells :=
    exists_fixed_strip_shell_pairings_local
      (d := d) OS lgc χc G hG_euclid φ_seq hφ_real hφ_int hφ_compact hφ_neg
      (s + s) (add_pos hs hs)
  have hcommon_probe_prod := hcommon_probe_shells.1
  have hcommon_probe_fixed_center := hcommon_probe_shells.2
  obtain ⟨μ_seq, _hμfin, hrepr, hshifted_pkg_all⟩ :=
    OSReconstruction.exists_probeSeq_fixedTimeCenterDiffKernel_eq_and_shifted_realDifference_package_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  have hcommon_shifted_prod :
      ∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d (s + s)) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
    simpa [Complex.ofReal_add] using
      OSReconstruction.common_shifted_realDifference_productShell_of_common_probe_productShell_bridge_of_repr_local
        (d := d) OS lgc G φ_seq hφ_compact hφ_neg (s + s) (add_pos hs hs) μ_seq
        (fun n z hz => hrepr n (s + s) z (add_pos hs hs) hz)
        hcommon_probe_prod
  have hcommon_shifted_same_center :
      ∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d (s + s)) *
            ((φ_seq n) (z 0) *
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) := by
    simpa [Complex.ofReal_add] using
      OSReconstruction.common_shifted_realDifference_same_center_of_common_probe_fixed_center_bridge_of_repr_local
        (d := d) OS lgc χc hχc G hG_euclid φ_seq hφ_int hφ_compact hφ_neg
        (s + s) (add_pos hs hs) μ_seq
        (fun n z hz => hrepr n (s + s) z (add_pos hs hs) hz)
        (fun n => by
          let hdesc_n : SchwartzSpacetime d :=
            OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))
          have hdesc_pos :
              tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
            dsimp [hdesc_n]
            exact OSReconstruction.twoPointCenterShearDescent_reflected_tsupport_pos_local
              (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
          simpa [hdesc_n, Complex.ofReal_add] using hcommon_probe_fixed_center n hdesc_n hdesc_pos)
  have hshifted_pkg :
      ∀ n,
        ∃ (C_bd : ℝ) (N : ℕ), 0 < C_bd ∧
          AEStronglyMeasurable
            (fun z : NPointDomain d 2 =>
              k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d (s + s)))
            volume ∧
          (∀ᵐ z : NPointDomain d 2 ∂volume,
            ‖k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d (s + s))‖ ≤
              C_bd * (1 + ‖z‖) ^ N) := by
    intro n
    simpa using hshifted_pkg_all n (s + s)
  have hshifted_prod_to_same_center :=
    exists_shifted_realDifference_productShell_to_same_center_local
      (d := d) φ_seq hφ_int (s + s) (add_pos hs hs) μ_seq hshifted_pkg
  have htime : (((s + s) : ℂ) * Complex.I) = ((↑s + ↑s) * Complex.I) := by
    ring
  intro n
  let hdesc_n : SchwartzSpacetime d :=
    OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (φ_seq n))
  have hdesc_pos :
      tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
    dsimp [hdesc_n]
    exact OSReconstruction.twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
  obtain ⟨c, hc⟩ :=
    OSReconstruction.schwinger_twoPoint_fixedTimeCenterDiffKernel_exists_const_local
      (d := d) OS G hG_euclid hdesc_n hdesc_pos (s + s) (add_pos hs hs)
  have hcommon_center_n :
      ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) =
      ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          (χc (z 0) * hdesc_n (z 1)) := by
    calc
      ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) * hdesc_n (z 1))
        = c * ∫ u : SpacetimeDim d, φ_seq n u := by
            simpa [hdesc_n] using hc (φ_seq n)
      _ = c * ∫ u : SpacetimeDim d, χc u := by rw [hφ_int n, hχc]
      _ =
      ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            (χc (z 0) * hdesc_n (z 1)) := by
              simpa [hdesc_n] using (hc χc).symm
  have hpair_aux_n :
      ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          (χc (z 0) * hdesc_n (z 1)) := by
    exact
      OSReconstruction.fixedTimeCenterDiff_productShell_to_difference_of_shifted_realDifference_via_common_shell_invariance_local
        (d := d)
        (K := OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)))
        (μ := μ_seq n)
        (t := s + s)
        (χ := φ_seq n)
        (χ₀ := χc)
        (g := reflectedSchwartzSpacetime (φ_seq n))
        (by simpa [htime] using hcommon_shifted_prod n)
        (by simpa using hshifted_prod_to_same_center n)
        (by simpa [hdesc_n, htime] using hcommon_shifted_same_center n)
        hcommon_center_n
  simpa [hdesc_n] using (hprod n).trans hpair_aux_n

private theorem exists_fixed_strip_common_difference_kernel_local
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
    (s : ℝ)
    (hs : 0 < s) :
    ∃ K_s : SpacetimeDim d → ℂ,
      ContinuousOn K_s {ξ : SpacetimeDim d | -(s + s) < ξ 0} ∧
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
  obtain ⟨G, _hG_holo, hG_euclid, hprod⟩ :=
    OSReconstruction.exists_common_fixed_strip_fixedTimeCenterDiff_productShell_pairing_with_witness_local
      (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg (s + s) (add_pos hs hs)
  obtain ⟨μ_seq_pkg, _hμfin_pkg, hrepr_pkg, hKpkg⟩ :=
    OSReconstruction.exists_probeSeq_fixedTimeCenterDiffKernel_eq_and_shifted_realDifference_package_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  obtain ⟨_Gcont, μ_seq_cont, _hGcont_holo, _hGcont_euclid, _hμfin_cont,
      _hprod_cont, _hrepr_cont, hcont_cont⟩ :=
    OSReconstruction.exists_common_fixed_strip_fixedTimeCenterDiff_with_probe_realDifference_continuous_package_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      (s + s) (add_pos hs hs)
  obtain ⟨χc_seq, _hχc_nonneg, _hχc_real, hχc_int, hχc_compact, _hχc_neg, _hχc_ball⟩ :=
    exists_negative_approx_identity_sequence (d := d)
  let χc : SchwartzSpacetime d := χc_seq 0
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
  have htime : (((s + s) : ℂ) * Complex.I) = ((↑s + ↑s) * Complex.I) := by
    ring
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
  have hcommon_probe_shells :=
    exists_fixed_strip_shell_pairings_local
      (d := d) OS lgc χc G hG_euclid φ_seq hφ_real hφ_int hφ_compact hφ_neg
      (s + s) (add_pos hs hs)
  have hcommon_probe_prod :
      ∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
    intro n
    simpa [htime] using hcommon_probe_shells.1 n
  have hcommon_probe_fixed_center :
      ∀ n (h : SchwartzSpacetime d),
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} →
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            (χc (z 0) * h (z 1)) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((((s + s) : ℂ) * Complex.I)) z *
            (χc (z 0) * h (z 1)) := by
    intro n h hh_pos
    simpa [htime] using hcommon_probe_shells.2 n h hh_pos
  have hpair_prod_common : ∀ n,
      I n =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1)) := by
    intro n
    simpa [I] using hprod n
  have hpair_eq_pkg_cont :
      ∀ n (h : SchwartzSpacetime d),
        HasCompactSupport (h : SpacetimeDim d → ℂ) →
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) * h ξ =
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0) (ξ + timeShiftVec d (s + s)) * h ξ := by
    intro n h hh_compact hh_pos
    let f : SchwartzMap (NPointDomain d 2) ℂ :=
      OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χc h)
    have hf_compact : HasCompactSupport (f : NPointDomain d 2 → ℂ) := by
      have hprod_eq :
          (SchwartzMap.productTensor ![χc, h] : SchwartzNPoint d 2) =
            twoPointProductLift χc h := by
        ext z
        simp [SchwartzMap.productTensor_apply, twoPointProductLift_apply]
      rw [show f = (twoPointProductLift χc h : SchwartzNPoint d 2) by
            rw [show f = SchwartzMap.productTensor ![χc, h] by
                  simp [f]]
            exact hprod_eq]
      exact OSReconstruction.hasCompactSupport_twoPointProductLift_for_reflected_local
        (d := d) χc h (hχc_compact 0) hh_compact
    have hf_support :
        Function.support (f : NPointDomain d 2 → ℂ) ⊆
          {z : NPointDomain d 2 | 0 < z 1 0} := by
      intro z hz
      rw [Function.mem_support] at hz
      have hmul : χc (z 0) * h (z 1) ≠ 0 := by
        simpa [f, OSReconstruction.twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift] using hz
      have hz1_mem : z 1 ∈ tsupport (h : SpacetimeDim d → ℂ) :=
        subset_tsupport _ (Function.mem_support.mpr (right_ne_zero_of_mul hmul))
      exact hh_pos hz1_mem
    have hcommon_n :
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z * f z =
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) * h ξ := by
      calc
        ∫ z : NPointDomain d 2,
            OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
              (d := d) G ((((s + s) : ℂ) * Complex.I)) z * f z
          =
        ∫ z : NPointDomain d 2,
            OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
              (d := d)
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq n) (hφ_compact n) (hφ_neg n))
              ((((s + s) : ℂ) * Complex.I)) z * f z := by
                simpa [f, OSReconstruction.twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift,
                  htime] using
                  hcommon_probe_fixed_center n h hh_pos
        _ =
        ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
              f z := by
                refine integral_congr_ae ?_
                filter_upwards with z
                by_cases hz : f z = 0
                · simp [hz]
                · have hz_mem : z ∈ Function.support (f : NPointDomain d 2 → ℂ) :=
                    Function.mem_support.mpr hz
                  have hz_pos : 0 < z 1 0 := hf_support hz_mem
                  have hz_strip : -(s + s) < z 1 0 := by
                    have hneg : -(s + s) < 0 := by linarith
                    exact lt_trans hneg hz_pos
                  rw [show OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
                        (d := d)
                        (k2ProbeWitness_local (d := d) OS lgc
                          (φ_seq n) (hφ_compact n) (hφ_neg n))
                        ((((s + s) : ℂ) * Complex.I)) z =
                        k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n)
                          (z 1 + timeShiftVec d (s + s)) by
                        simpa [htime] using hrepr_pkg n (s + s) z (add_pos hs hs) hz_strip]
        _ = (∫ u : SpacetimeDim d, χc u) *
            ∫ ξ : SpacetimeDim d,
              k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
                h ξ := by
                  simpa [f, OSReconstruction.twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift] using
                    OSReconstruction.integral_centerDiff_differenceOnly_kernel_factorizes
                    (d := d)
                    (fun ξ : SpacetimeDim d =>
                      k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n)
                        (ξ + timeShiftVec d (s + s)))
                    χc h
        _ =
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
            h ξ := by
              rw [hχc_int 0]
              ring
    have hcommon0 :
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z * f z =
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0) (ξ + timeShiftVec d (s + s)) * h ξ := by
      calc
        ∫ z : NPointDomain d 2,
            OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
              (d := d) G ((((s + s) : ℂ) * Complex.I)) z * f z
          =
        ∫ z : NPointDomain d 2,
            OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
              (d := d)
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq 0) (hφ_compact 0) (hφ_neg 0))
              ((((s + s) : ℂ) * Complex.I)) z * f z := by
                simpa [f, OSReconstruction.twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift,
                  htime] using
                  hcommon_probe_fixed_center 0 h hh_pos
        _ =
        ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0) (z 1 + timeShiftVec d (s + s)) *
              f z := by
                refine integral_congr_ae ?_
                filter_upwards with z
                by_cases hz : f z = 0
                · simp [hz]
                · have hz_mem : z ∈ Function.support (f : NPointDomain d 2 → ℂ) :=
                    Function.mem_support.mpr hz
                  have hz_pos : 0 < z 1 0 := hf_support hz_mem
                  have hz_strip : -(s + s) < z 1 0 := by
                    have hneg : -(s + s) < 0 := by linarith
                    exact lt_trans hneg hz_pos
                  rw [show OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
                        (d := d)
                        (k2ProbeWitness_local (d := d) OS lgc
                          (φ_seq 0) (hφ_compact 0) (hφ_neg 0))
                        ((((s + s) : ℂ) * Complex.I)) z =
                        k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0)
                          (z 1 + timeShiftVec d (s + s)) by
                        simpa [htime] using (_hrepr_cont 0) z hz_strip]
        _ = (∫ u : SpacetimeDim d, χc u) *
            ∫ ξ : SpacetimeDim d,
              k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0) (ξ + timeShiftVec d (s + s)) *
                h ξ := by
                  simpa [f, OSReconstruction.twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift] using
                    OSReconstruction.integral_centerDiff_differenceOnly_kernel_factorizes
                    (d := d)
                    (fun ξ : SpacetimeDim d =>
                      k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0)
                        (ξ + timeShiftVec d (s + s)))
                    χc h
        _ =
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0) (ξ + timeShiftVec d (s + s)) *
            h ξ := by
              rw [hχc_int 0]
              ring
    exact hcommon_n.symm.trans hcommon0
  have hK0_strip :
      ContinuousOn
        (fun ξ : SpacetimeDim d =>
          k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0) (ξ + timeShiftVec d (s + s)))
        {ξ : SpacetimeDim d | -(s + s) < ξ 0} := by
    let emb : SpacetimeDim d → NPointDomain d 2 := fun ξ => ![(0 : SpacetimeDim d), ξ]
    have hemb : Continuous emb := by
      refine continuous_pi ?_
      intro i
      fin_cases i
      · simpa [emb] using
          (continuous_const : Continuous fun _ : SpacetimeDim d => (0 : SpacetimeDim d))
      · simpa [emb] using (continuous_id : Continuous fun ξ : SpacetimeDim d => ξ)
    have hmaps :
        Set.MapsTo emb
          {ξ : SpacetimeDim d | -(s + s) < ξ 0}
          {z : NPointDomain d 2 | -(s + s) < z 1 0} := by
      intro ξ hξ
      simpa [emb] using hξ
    refine ((hcont_cont 0).comp hemb.continuousOn hmaps).congr ?_
    intro ξ hξ
    simp [emb]
  let K_s : SpacetimeDim d → ℂ := fun ξ =>
    k2DifferenceKernel_real_local (d := d) (μ_seq_cont 0) (ξ + timeShiftVec d (s + s))
  have hK_cont0 : ContinuousAt K_s 0 := by
    exact OSReconstruction.continuousAt_zero_of_continuousOn_fixedStrip_local
      (d := d) (s + s) (add_pos hs hs) hK0_strip
  have hfactor :
      ∀ n,
        I n =
          ∫ ξ : SpacetimeDim d,
            k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) ξ := by
    intro n
    let hdesc_n : SchwartzSpacetime d :=
      OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
        (reflectedSchwartzSpacetime (d := d) (φ_seq n))
    have hcommon_shifted_prod :
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
      calc
        ∫ z : NPointDomain d 2,
            OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
              (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
              ((φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))
          =
        ∫ z : NPointDomain d 2,
            OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
              (d := d)
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq n) (hφ_compact n) (hφ_neg n))
              ((((s + s) : ℂ) * Complex.I)) z *
              ((φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
                  simpa [htime] using hcommon_probe_prod n
        _ =
        ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
              ((φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
              refine integral_congr_ae ?_
              filter_upwards with z
              by_cases hz :
                  (φ_seq n) (z 0) *
                    reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1) = 0
              · rw [hz]
                simp
              · have hz0_neg : z 0 0 < 0 := by
                  exact hφ_neg n <|
                    subset_tsupport _ (Function.mem_support.mpr (left_ne_zero_of_mul hz))
                have hzsum_pos : 0 < (z 0 + z 1) 0 := by
                  exact reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n) <|
                    subset_tsupport _ (Function.mem_support.mpr (right_ne_zero_of_mul hz))
                have hzsum : (z 0 + z 1) 0 = z 0 0 + z 1 0 := by simp
                rw [hzsum] at hzsum_pos
                have hz1_pos : 0 < z 1 0 := by
                  linarith
                have hz_strip : -(s + s) < z 1 0 := by
                  have hneg : -(s + s) < 0 := by linarith
                  exact lt_trans hneg hz1_pos
                rw [show OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
                      (d := d)
                      (k2ProbeWitness_local (d := d) OS lgc
                        (φ_seq n) (hφ_compact n) (hφ_neg n))
                      ((((s + s) : ℂ) * Complex.I)) z =
                      k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n)
                        (z 1 + timeShiftVec d (s + s)) by
                      simpa [htime] using hrepr_pkg n (s + s) z (add_pos hs hs) hz_strip]
    have hshifted_prod_to_same_center :
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
            ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
      rcases hKpkg n (s + s) with ⟨C_bd, N, hC, hK_meas, hK_bound⟩
      simpa [hdesc_n] using
        exists_shifted_realDifference_productShell_to_same_center_local
          (d := d) φ_seq hφ_int (s + s) (add_pos hs hs) μ_seq_pkg
          (fun m => by
            rcases hKpkg m (s + s) with ⟨C', N', hC', hK_meas', hK_bound'⟩
            exact ⟨C', N', hC', hK_meas', hK_bound'⟩) n
    calc
      I n = ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hpair_prod_common n
      _ = ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
              ((φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hcommon_shifted_prod
      _ = ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (z 1 + timeShiftVec d (s + s)) *
              ((φ_seq n) (z 0) * hdesc_n (z 1)) := hshifted_prod_to_same_center
      _ = (∫ u : SpacetimeDim d, φ_seq n u) *
            ∫ ξ : SpacetimeDim d,
              k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
                hdesc_n ξ := by
              exact OSReconstruction.integral_centerDiff_differenceOnly_kernel_factorizes
                (d := d)
                (fun ξ : SpacetimeDim d =>
                  k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n)
                    (ξ + timeShiftVec d (s + s)))
                (φ_seq n) hdesc_n
      _ = ∫ ξ : SpacetimeDim d,
            k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
              hdesc_n ξ := by
            rw [hφ_int n]
            ring
  refine ⟨K_s, hK0_strip, ?_⟩
  intro n
  let hdesc_n : SchwartzSpacetime d :=
    OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (d := d) (φ_seq n))
  have hdesc_pos :
      tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
    dsimp [hdesc_n]
    exact OSReconstruction.twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
  have hsame :
      ∫ ξ : SpacetimeDim d,
        k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
          hdesc_n ξ =
      ∫ ξ : SpacetimeDim d,
        K_s ξ * hdesc_n ξ := by
    exact hpair_eq_pkg_cont n hdesc_n (hdesc_compact n) hdesc_pos
  calc
    I n = ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq_pkg n) (ξ + timeShiftVec d (s + s)) *
            hdesc_n ξ := hfactor n
    _ = ∫ ξ : SpacetimeDim d, K_s ξ * hdesc_n ξ := hsame
    _ = (∫ u : SpacetimeDim d, χ₀ u) *
          ∫ ξ : SpacetimeDim d, K_s ξ * hdesc_n ξ := by
          rw [hχ₀]
          ring
    _ =
        ∫ x : NPointDomain d 2,
          OSReconstruction.twoPointDifferenceKernel K_s x *
            (twoPointDifferenceLift χ₀ hdesc_n x) := by
          symm
          exact OSReconstruction.integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
            (d := d) K_s χ₀ hdesc_n -/

private def commonDiffWitness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    (Fin (2 * (d + 1)) → ℂ) → ℂ :=
  Classical.choose
    (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
      (d := d) OS lgc)

private theorem commonDiffWitness_spec_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsTimeHolomorphicFlatPositiveTimeDiffWitness
        (commonDiffWitness_local (d := d) OS lgc) ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          commonDiffWitness_local (d := d) OS lgc
            (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) := by
  have hspec := Classical.choose_spec
      (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
        (d := d) OS lgc)
  rcases hspec with ⟨hG_holo, hG_euclid, _hG_diff, _hG_bound⟩
  exact ⟨by simpa [commonDiffWitness_local] using hG_holo,
    by simpa [commonDiffWitness_local] using hG_euclid⟩

private theorem norm_timeShiftVec_le_abs_local
    (t : ℝ) :
    ‖timeShiftVec d t‖ ≤ |t| := by
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg t)]
  intro μ
  by_cases hμ0 : μ = 0
  · subst hμ0
    simp [timeShiftVec]
  · simp [timeShiftVec, hμ0]

/-- Honest remaining common-`G` Input A seam after replacing the false
probe-Euclid route with the strengthened upstream translation-invariant
common witness.

At this point the witness, Euclidean reproduction, and diff-block dependence
are already fixed in production. The only remaining analytic content is a
polynomial bound for the ordinary `k = 2` time-parametric kernel of that
witness on the explicit zero-center shifted section `![(0), ξ + 2s e₀]`. -/
private theorem exists_common_k2TimeParametricKernel_zeroCenterShift_bound_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ)
    (hs : 0 < s) :
    ∃ (C_bd : ℝ) (N : ℕ),
      0 < C_bd ∧
      (∀ ξ : SpacetimeDim d, -(s + s) < ξ 0 →
        ‖k2TimeParametricKernel (d := d)
            (commonDiffWitness_local (d := d) OS lgc)
            (![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] : NPointDomain d 2)‖ ≤
          C_bd * (1 + ‖ξ‖) ^ N) := by
  have hspec := by
    simpa [commonDiffWitness_local] using
      (Classical.choose_spec
        (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
          (d := d) OS lgc))
  rcases hspec with ⟨_hG_holo, _hG_euclid, _hG_diff, hbound⟩
  rcases hbound with ⟨C₀, hC₀, N, hpos_bound⟩
  refine ⟨C₀ * (1 + (s + s)) ^ N, N, ?_, ?_⟩
  · positivity
  · intro ξ hξ
    change
      ‖k2TimeParametricKernel (d := d)
          (Classical.choose
            (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
              (d := d) OS lgc))
          (![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] : NPointDomain d 2)‖ ≤
        (C₀ * (1 + (s + s)) ^ N) * (1 + ‖ξ‖) ^ N
    have hshift_pos : 0 < (ξ + timeShiftVec d (s + s)) 0 := by
      simp [timeShiftVec]
      linarith
    have hbase := hpos_bound (ξ + timeShiftVec d (s + s)) hshift_pos
    have hbase' :
        ‖k2TimeParametricKernel (d := d)
            (Classical.choose
              (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
                (d := d) OS lgc))
            (![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] : NPointDomain d 2)‖ ≤
          C₀ * (1 + ‖ξ + timeShiftVec d (s + s)‖) ^ N := by
      simpa using hbase
    have hshift_norm : ‖timeShiftVec d (s + s)‖ ≤ s + s := by
      calc
        ‖timeShiftVec d (s + s)‖ ≤ |s + s| :=
          norm_timeShiftVec_le_abs_local (d := d) (s + s)
        _ = s + s := by rw [abs_of_nonneg (by linarith : 0 ≤ s + s)]
    have harg :
        1 + ‖ξ + timeShiftVec d (s + s)‖ ≤
          (1 + (s + s)) * (1 + ‖ξ‖) := by
      have htri : ‖ξ + timeShiftVec d (s + s)‖ ≤ ‖ξ‖ + ‖timeShiftVec d (s + s)‖ :=
        norm_add_le _ _
      nlinarith [htri, hshift_norm, norm_nonneg ξ]
    calc
      ‖k2TimeParametricKernel (d := d)
          (Classical.choose
            (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
              (d := d) OS lgc))
          (![(0 : SpacetimeDim d), ξ + timeShiftVec d (s + s)] : NPointDomain d 2)‖
          ≤ C₀ * (1 + ‖ξ + timeShiftVec d (s + s)‖) ^ N := hbase'
      _ ≤ C₀ * ((1 + (s + s)) * (1 + ‖ξ‖)) ^ N := by
            apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₀)
            exact pow_le_pow_left₀ (by positivity) harg N
      _ = (C₀ * (1 + (s + s)) ^ N) * (1 + ‖ξ‖) ^ N := by
            rw [mul_assoc, mul_pow]
      _ = (C₀ * (1 + (s + s)) ^ N) * (1 + ‖ξ‖) ^ N := rfl

/-- Derived lifted-slice strip bound for the strengthened common witness.

Once the common witness is bounded on the explicit zero-center shifted section,
the current lifted-slice strip estimate follows formally from the existing
diff-block support theorem. -/
private theorem exists_common_lifted_difference_slice_strip_bound_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (s : ℝ)
    (hs : 0 < s) :
    ∃ (C_bd : ℝ) (N : ℕ),
      0 < C_bd ∧
      (∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖OSReconstruction.commonLiftedDifferenceSliceKernel_local
            (d := d) (commonDiffWitness_local (d := d) OS lgc) s (z 1)‖ ≤
          C_bd * (1 + ‖z‖) ^ N) := by
  have hGpkg := by
    simpa [commonDiffWitness_local] using
      (Classical.choose_spec
        (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
          (d := d) OS lgc))
  rcases hGpkg with ⟨_hG_holo, _hG_euclid, hG_diff, _hG_bound⟩
  obtain ⟨C_bd, N, hC, hK_bound⟩ :=
    exists_common_k2TimeParametricKernel_zeroCenterShift_bound_local
      (d := d) OS lgc s hs
  exact
    OSReconstruction.exists_common_lifted_difference_slice_strip_bound_of_k2TimeParametricKernel_zeroCenterShift_bound_of_diffBlockDependence_local
      (d := d)
      (commonDiffWitness_local (d := d) OS lgc)
      hG_diff s C_bd N hC hK_bound

/-- Honest remaining common-`G` Input A seam after replacing the false
probe-Euclid route.

The strengthened upstream witness now already carries the `k = 2` diff-block
dependence needed to identify the reflected product-shell pairing. So the root
analytic work has been reduced to the strip bound alone, and the product-shell
pairing is derived formally from `InputADiffBlock`. -/
private theorem exists_common_lifted_difference_slice_productShell_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (s : ℝ)
    (hs : 0 < s) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) (C_bd : ℝ) (N : ℕ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      0 < C_bd ∧
      (∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
        ‖OSReconstruction.commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
          C_bd * (1 + ‖z‖) ^ N) ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) := by
  have hspec := commonDiffWitness_spec_local (d := d) OS lgc
  rcases hspec with ⟨hG_holo, hG_euclid⟩
  have hGpkg := by
    simpa [commonDiffWitness_local] using
      (Classical.choose_spec
        (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
          (d := d) OS lgc))
  rcases hGpkg with ⟨_hG_holo', _hG_euclid', hG_diff, _hG_bound⟩
  obtain ⟨C_bd, N, hC, hK_bound⟩ :=
    exists_common_lifted_difference_slice_strip_bound_local
      (d := d) OS lgc s hs
  exact
    OSReconstruction.exists_common_lifted_difference_slice_productShell_package_of_diffBlockDependence_local
      (d := d) OS φ_seq hφ_compact hφ_neg
      (commonDiffWitness_local (d := d) OS lgc)
      hG_holo hG_euclid hG_diff s C_bd N hC hK_bound

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
  obtain hpkg :=
    exists_common_lifted_difference_slice_productShell_package_local
      (d := d) OS lgc φ_seq hφ_compact hφ_neg s hs
  exact
    OSReconstruction.exists_fixed_strip_diagonal_limit_of_common_lifted_difference_slice_productShell_package_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
      hφ_compact hφ_neg s hs hpkg

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
  obtain ⟨ε, hε_pos, hmargin0⟩ :=
    exists_positive_time_margin_of_mem_positiveTimeCompactSupport_local (d := d) h
  have hs : 0 < ε / 4 := by
    linarith
  have hmargin :
      tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | ε / 4 + ε / 4 < ξ 0} := by
    refine Set.Subset.trans hmargin0 ?_
    intro ξ hξ
    simp only [Set.mem_setOf] at hξ ⊢
    linarith
  have hspec :=
    Classical.choose_spec
      (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
        (d := d) OS lgc)
  rcases hspec with ⟨hG_holo_raw, hG_euclid_raw, hG_diff_raw, hG_bound_pkg_raw⟩
  have hG_holo :
      IsTimeHolomorphicFlatPositiveTimeDiffWitness
        (commonDiffWitness_local (d := d) OS lgc) := by
    simpa [commonDiffWitness_local] using hG_holo_raw
  have hG_euclid :
      ∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          commonDiffWitness_local (d := d) OS lgc
            (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x) := by
    simpa [commonDiffWitness_local] using hG_euclid_raw
  have hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
            v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
        commonDiffWitness_local (d := d) OS lgc u =
          commonDiffWitness_local (d := d) OS lgc v := by
    simpa [commonDiffWitness_local] using hG_diff_raw
  have hG_bound_pkg :
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ ξ : SpacetimeDim d, 0 < ξ 0 →
          ‖k2TimeParametricKernel (d := d)
              (commonDiffWitness_local (d := d) OS lgc)
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖ ≤
            C_bd * (1 + ‖ξ‖) ^ N := by
    simpa [commonDiffWitness_local] using hG_bound_pkg_raw
  rcases hG_bound_pkg with ⟨C_bd, N, hC, hG_bound⟩
  have hshell_repr :
      ∀ n : ℕ, ∀ ξ : SpacetimeDim d, ε / 4 + ε / 4 < ξ 0 →
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift (φ_seq n)
            (SCV.translateSchwartz (-ξ)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))))) =
          ∫ u : SpacetimeDim d,
            (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) u *
              k2TimeParametricKernel (d := d)
                (commonDiffWitness_local (d := d) OS lgc)
                (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2) := by
    intro n ξ hξ
    have hξ_pos : 0 < ξ 0 := by
      linarith
    simpa [commonDiffWitness_local] using
      (OSReconstruction.shell_scalar_eq_descended_convolution_commonZeroAnchor_local
        (d := d) OS
        (commonDiffWitness_local (d := d) OS lgc)
        hG_holo hG_euclid hG_diff C_bd N hC hG_bound
        (φ_seq n) (hφ_int n) (hφ_compact n) (hφ_neg n) ξ hξ_pos)
  exact
    OSReconstruction.exists_shell_pointwise_limit_function_of_commonZeroAnchor_local
      (d := d) OS χ₀ hχ₀
      (commonDiffWitness_local (d := d) OS lgc)
      hG_holo hG_euclid hG_diff
      φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
      (ε / 4) hs h hmargin hshell_repr

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

/-- Final assembly shrinks one step further for the common sectorwise kernel.

Once the measurable/polynomial package is available for
`commonK2TimeParametricKernel_real_local G`, the remaining reproduction problem
does not need shell agreement on all flat-origin generators. By
`InputCReduced`, it is enough to know the compact origin-avoiding shell
identity at one fixed normalized center cutoff `χ₀`; the flat-origin closure
bridge and the route-independent CLM packaging then finish the distributional
reproduction formally. -/
private theorem k2_distributional_reproduction_of_zeroOriginCompactFixedCenter_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_meas : AEStronglyMeasurable
      (OSReconstruction.commonK2TimeParametricKernel_real_local G) volume)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖OSReconstruction.commonK2TimeParametricKernel_real_local G x‖ ≤
        C_bd * (1 + ‖x‖) ^ N)
    (hShell₀ :
      ∀ h : zeroOriginAvoidingSubmodule d,
        HasCompactSupport (((h : zeroOriginAvoidingSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) →
              OSReconstruction.twoPointZeroDiagonalKernelCLM
                  (d := d)
                  (OSReconstruction.commonK2TimeParametricKernel_real_local G)
                  hK_meas C_bd N hC hK_bound
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))))
    (f : ZeroDiagonalSchwartz d 2) :
    OS.S 2 f =
      ∫ x : NPointDomain d 2,
        OSReconstruction.commonK2TimeParametricKernel_real_local G x * (f.1 x) := by
  refine
    k2_distributional_reproduction_of_flatOrigin_shell_agreement_local
      OS
      (OSReconstruction.commonK2TimeParametricKernel_real_local G)
      C_bd N hC hK_meas hK_bound ?_ f
  intro χ h hzero
  exact
    OSReconstruction.commonK2TimeParametricKernel_real_eq_schwinger_on_flatOrigin_differenceShell_of_zeroOriginCompactFixedCenter_local
      OS χ₀ hχ₀ G hK_meas C_bd N hC hK_bound hShell₀ χ h

/-- Formal final-assembly wrapper after the last reduction step.

To construct the final witness/kernel pair it is now enough to package the
canonical common sectorwise kernel:
- sector formulas come from the common diff-block witness,
- reproduction comes from one fixed-center compact-shell theorem via
  `k2_distributional_reproduction_of_zeroOriginCompactFixedCenter_local`.

So the last honest assembly seam is no longer arbitrary flat-origin shell
agreement; it is the common-kernel measurable/polynomial package together with
compact origin-avoiding shell equality at the single normalized cutoff `χ₀`. -/
private theorem exists_k2_timeParametric_distributional_assembly_of_commonZeroOriginCompactFixedCenter_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_meas : AEStronglyMeasurable
      (OSReconstruction.commonK2TimeParametricKernel_real_local
        (commonDiffWitness_local (d := d) OS lgc)) volume)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖OSReconstruction.commonK2TimeParametricKernel_real_local
          (commonDiffWitness_local (d := d) OS lgc) x‖ ≤
        C_bd * (1 + ‖x‖) ^ N)
    (hShell₀ :
      ∀ h : zeroOriginAvoidingSubmodule d,
        HasCompactSupport (((h : zeroOriginAvoidingSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) →
              OSReconstruction.twoPointZeroDiagonalKernelCLM
                  (d := d)
                  (OSReconstruction.commonK2TimeParametricKernel_real_local
                    (commonDiffWitness_local (d := d) OS lgc))
                  hK_meas C_bd N hC hK_bound
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d)))) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) (K : NPointDomain d 2 → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ x : NPointDomain d 2, x 0 0 < x 1 0 →
        K x = k2TimeParametricKernel (d := d) G x) ∧
      (∀ x : NPointDomain d 2, x 1 0 < x 0 0 →
        K x = k2TimeParametricKernel (d := d) G
          (fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i))) ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x)) := by
  have hspec := Classical.choose_spec
      (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
        (d := d) OS lgc)
  rcases hspec with ⟨hG_holo_raw, _hG_euclid_raw, hG_diff_raw, _hG_bound_raw⟩
  have hG_holo :
      IsTimeHolomorphicFlatPositiveTimeDiffWitness
        (commonDiffWitness_local (d := d) OS lgc) := by
    simpa [commonDiffWitness_local] using hG_holo_raw
  have hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
            v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
        commonDiffWitness_local (d := d) OS lgc u =
          commonDiffWitness_local (d := d) OS lgc v := by
    simpa [commonDiffWitness_local] using hG_diff_raw
  refine
    ⟨commonDiffWitness_local (d := d) OS lgc,
      OSReconstruction.commonK2TimeParametricKernel_real_local
        (commonDiffWitness_local (d := d) OS lgc),
      hG_holo, ?_, ?_, ?_⟩
  · intro x hx
    exact OSReconstruction.commonK2TimeParametricKernel_real_eq_of_pos_local
      (d := d) (commonDiffWitness_local (d := d) OS lgc) hG_diff x hx
  · intro x hx
    exact OSReconstruction.commonK2TimeParametricKernel_real_eq_of_neg_local
      (d := d) (commonDiffWitness_local (d := d) OS lgc) hG_diff x hx
  · intro f
    exact
      k2_distributional_reproduction_of_zeroOriginCompactFixedCenter_local
        OS χ₀ hχ₀
        (commonDiffWitness_local (d := d) OS lgc)
        C_bd N hC hK_meas hK_bound hShell₀ f

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
  obtain ⟨φ_seq, hφ_nonneg, hφ_real, hφ_int, _hφ_compact, _hφ_neg, hφ_ball,
      _μ_seq, _hμfin, _hhol, _hsupp, _hμrepr, _hkernel, _hpair⟩ :=
    exists_k2_VI1_regularization_input_local (d := d) OS lgc
  obtain ⟨χ_seq, _hχ_eq, _hχ_nonneg, _hχ_real, hχ_int, _hχ_trans, _hχ_support⟩ :=
    exists_k2_VI1_descended_center_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
  let χ₀ : SchwartzSpacetime d := χ_seq 0
  have hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1 := by
    simpa [χ₀] using hχ_int 0
  have hspec := Classical.choose_spec
      (OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_and_posSectionBound_local
        (d := d) OS lgc)
  rcases hspec with ⟨hG_holo_raw, hG_euclid_raw, hG_diff_raw, hG_bound_raw⟩
  have hG_holo :
      IsTimeHolomorphicFlatPositiveTimeDiffWitness
        (commonDiffWitness_local (d := d) OS lgc) := by
    simpa [commonDiffWitness_local] using hG_holo_raw
  have hG_euclid :
      ∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          commonDiffWitness_local (d := d) OS lgc
            (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x) := by
    simpa [commonDiffWitness_local] using hG_euclid_raw
  have hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
            v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
        commonDiffWitness_local (d := d) OS lgc u =
          commonDiffWitness_local (d := d) OS lgc v := by
    simpa [commonDiffWitness_local] using hG_diff_raw
  rcases hG_bound_raw with ⟨C_bd, N, hC, hG_bound⟩
  obtain ⟨C_real, hC_real, hK_meas, hK_bound⟩ :=
    OSReconstruction.exists_commonK2TimeParametricKernel_real_package_local
      (d := d)
      (commonDiffWitness_local (d := d) OS lgc)
      hG_holo hG_diff C_bd N hC hG_bound
  refine
    exists_k2_timeParametric_distributional_assembly_of_commonZeroOriginCompactFixedCenter_local
      (d := d) OS lgc χ₀ hχ₀ C_real N hC_real hK_meas hK_bound ?_
  /-
  Honest remaining assembly step after the collar split:

  prove the fixed-center compact origin-avoiding shell theorem only on the
  equal-time collar `|ξ₀| ≤ 1` for the canonical common sectorwise kernel at
  the chosen normalized cutoff `χ₀`:

    ∀ h : zeroOriginAvoidingSubmodule d,
      HasCompactSupport (((h : zeroOriginAvoidingSubmodule d) :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ) →
      tsupport (((h : zeroOriginAvoidingSubmodule d) :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
        {ξ : SpacetimeDim d | |ξ 0| ≤ 1} →
        twoPointZeroDiagonalKernelCLM(commonK2TimeParametricKernel_real_local
          (commonDiffWitness_local OS lgc))(differenceLift χ₀ h)
        = OS.S 2(differenceLift χ₀ h).

  `InputCCollarSplit` now pays the positive-time and negative-time pieces
  formally, so the final seam is genuinely localized to the equal-time collar.
  -/
  intro h hh_compact
  refine
    OSReconstruction.commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_zeroOriginCompactFixedCenter_of_timeCollar_local
      (d := d) OS χ₀ hχ₀
      (commonDiffWitness_local (d := d) OS lgc)
      hG_euclid hG_diff hK_meas C_real N hC_real hK_bound
      1 (by norm_num) ?_ h hh_compact
  intro h hh_compact hh_collar
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
