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

private theorem exists_fixed_strip_common_probe_shell_bridges_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) :
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
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
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
  /-
  Honest root Input A seam on the common-witness side:

  prove the two concrete common-vs-probe shell bridges actually consumed
  downstream:

  1. reflected product shell, and
  2. fixed-center difference shells `χc(z₀) * h(z₁)` with compact positive-time
     `h`.

  This is smaller and more honest than asking for equality on every compactly
  supported positive-strip test `f : SchwartzMap (NPointDomain d 2) ℂ`.
  -/
  sorry

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
    (hφ_int : ∀ n, ∫ u : SpacetimeDim d, φ_seq n u = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hdesc_compact : ∀ n,
      HasCompactSupport
        (((OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
          (reflectedSchwartzSpacetime (φ_seq n))) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
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
  obtain ⟨hcommon_probe_prod, hcommon_probe_fixed_center⟩ :=
    exists_fixed_strip_common_probe_shell_bridges_local
      (d := d) OS lgc χc hχc G hG_euclid φ_seq hφ_compact hφ_neg (s + s)
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
  have hcommon_probe_fixed_center_descended :
      ∀ n,
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            (χc (z 0) *
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((((s + s) : ℂ) * Complex.I)) z *
            (χc (z 0) *
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) := by
    intro n
    let hdesc_n : SchwartzSpacetime d :=
      OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
        (reflectedSchwartzSpacetime (d := d) (φ_seq n))
    have hdesc_pos :
        tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} := by
      dsimp [hdesc_n]
      exact OSReconstruction.twoPointCenterShearDescent_reflected_tsupport_pos_local
        (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
    simpa [hdesc_n, Complex.ofReal_add] using
      hcommon_probe_fixed_center n hdesc_n (hdesc_compact n) hdesc_pos
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
          convert hcommon_probe_fixed_center_descended n using 2 <;> simp [Complex.ofReal_add])
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
  calc
    osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
        (s + s) (0 : Fin d → ℝ)
      =
    ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1)) := by
            simpa using hprod n
    _ =
    ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          (χc (z 0) *
            (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n))) (z 1)) := hpair_aux_n

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
                have hcommon_probe_fixed_center :=
                  (exists_fixed_strip_common_probe_shell_bridges_local
                    (d := d) OS lgc χc (hχc_int 0) G hG_euclid φ_seq hφ_compact hφ_neg (s + s)).2
                simpa [f, OSReconstruction.twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift, htime] using
                  hcommon_probe_fixed_center n h hh_compact hh_pos
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
                have hcommon_probe_fixed_center :=
                  (exists_fixed_strip_common_probe_shell_bridges_local
                    (d := d) OS lgc χc (hχc_int 0) G hG_euclid φ_seq hφ_compact hφ_neg (s + s)).2
                simpa [f, OSReconstruction.twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift, htime] using
                  hcommon_probe_fixed_center 0 h hh_compact hh_pos
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
      · simpa [emb] using (continuous_const : Continuous fun _ : SpacetimeDim d => (0 : SpacetimeDim d))
      · simpa [emb] using (continuous_id : Continuous fun ξ : SpacetimeDim d => ξ)
    have hmaps :
        Set.MapsTo emb
          {ξ : SpacetimeDim d | -(s + s) < ξ 0}
          {z : NPointDomain d 2 | -(s + s) < z 1 0} := by
      intro ξ hξ
      simpa [emb] using hξ
    refine (hcont_cont 0).comp hemb.continuousOn hmaps |>.congr ?_
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
    have hcommon_probe_prod :
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
      simpa [htime] using
        (exists_fixed_strip_common_probe_shell_bridges_local
          (d := d) OS lgc χc (hχc_int 0) G hG_euclid φ_seq hφ_compact hφ_neg (s + s)).1 n
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
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hcommon_probe_prod
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
            (d := d) K_s χ₀ hdesc_n

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
  obtain ⟨K_s, hK_strip, hpair⟩ :=
    exists_fixed_strip_common_difference_kernel_local
      OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg s hs
  simpa using
    OSReconstruction.exists_fixed_strip_diagonal_limit_of_difference_kernel_pairing_on_fixedStrip_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int
      hφ_compact hφ_neg hφ_ball s hs K_s hK_strip hpair

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
  continuity layer from `K2VI1/OrbitBridge.lean`.
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
