import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Support
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2BaseStep
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAHeadBlockTransport
import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Concrete original-coordinate section for the fixed-time probe route:
freeze the center slot and realize the shifted difference by moving only the
second point forward by `t`. -/
private def probeFixedTimeRepresentativeSection_local
    (t : ℝ) : NPointDomain d 2 → NPointDomain d 2 :=
  fun z => ![z 0, z 0 + z 1 + timeShiftVec d t]

private theorem probeFixedTimeRepresentativeSection_diff_local
    (t : ℝ) (z : NPointDomain d 2) :
    probeFixedTimeRepresentativeSection_local (d := d) t z 1 -
        probeFixedTimeRepresentativeSection_local (d := d) t z 0 =
      z 1 + timeShiftVec d t := by
  ext μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [probeFixedTimeRepresentativeSection_local, timeShiftVec]
    ring
  · simp [probeFixedTimeRepresentativeSection_local, timeShiftVec, hμ]

private theorem probeFixedTimeRepresentativeSection_pos_iff_local
    (t : ℝ) (z : NPointDomain d 2) :
    (probeFixedTimeRepresentativeSection_local (d := d) t z) 0 0 <
        (probeFixedTimeRepresentativeSection_local (d := d) t z) 1 0 ↔
      -t < z 1 0 := by
  have hdiff0 :
      (probeFixedTimeRepresentativeSection_local (d := d) t z 1) 0 -
          (probeFixedTimeRepresentativeSection_local (d := d) t z 0) 0 =
        z 1 0 + t := by
    have hdiff := congrArg (fun v : SpacetimeDim d => v 0)
      (probeFixedTimeRepresentativeSection_diff_local (d := d) t z)
    simpa [timeShiftVec] using hdiff
  constructor
  · intro h
    have : 0 < z 1 0 + t := by linarith [hdiff0]
    linarith
  · intro h
    have : 0 < z 1 0 + t := by linarith
    linarith [hdiff0]

private theorem continuous_probeFixedTimeRepresentativeSection_local
    (t : ℝ) :
    Continuous (probeFixedTimeRepresentativeSection_local (d := d) t) := by
  refine continuous_pi ?_
  intro i
  fin_cases i
  · simpa [probeFixedTimeRepresentativeSection_local] using continuous_apply (0 : Fin 2)
  ·
    simpa [probeFixedTimeRepresentativeSection_local] using
      ((continuous_apply (0 : Fin 2)).add (continuous_apply (1 : Fin 2))).add continuous_const

private def probeFixedTimeRepresentativeCenterDiffShift_local
    (t : ℝ) : NPointDomain d 2 → NPointDomain d 2 :=
  fun z => ![z 0, z 1 + timeShiftVec d t]

private theorem probeFixedTimeRepresentativeSection_eq_centerDiff_comp_local
    (t : ℝ) :
    probeFixedTimeRepresentativeSection_local (d := d) t =
      fun z =>
        (twoPointCenterDiffCLE d)
          (probeFixedTimeRepresentativeCenterDiffShift_local (d := d) t z) := by
  funext z
  ext i μ
  fin_cases i
  ·
    simp [probeFixedTimeRepresentativeSection_local,
      probeFixedTimeRepresentativeCenterDiffShift_local,
      twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv]
  ·
    by_cases hμ : μ = 0
    ·
      subst hμ
      simp [probeFixedTimeRepresentativeSection_local,
        probeFixedTimeRepresentativeCenterDiffShift_local,
        twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, timeShiftVec]
      ring
    ·
      simp [probeFixedTimeRepresentativeSection_local,
        probeFixedTimeRepresentativeCenterDiffShift_local,
        twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, timeShiftVec, hμ]

private theorem probeFixedTimeRepresentativeCenterDiffShift_measurePreserving_local
    (t : ℝ) :
    MeasureTheory.MeasurePreserving
      (probeFixedTimeRepresentativeCenterDiffShift_local (d := d) t)
      MeasureTheory.volume MeasureTheory.volume := by
  let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
    MeasurableEquiv.finTwoArrow
  have heprod :
      MeasureTheory.MeasurePreserving eprod
        MeasureTheory.volume MeasureTheory.volume := by
    simpa [eprod] using
      (MeasureTheory.volume_preserving_finTwoArrow (SpacetimeDim d))
  have hshift :
      MeasureTheory.MeasurePreserving
        (Prod.map id (fun x : SpacetimeDim d => x + timeShiftVec d t))
        MeasureTheory.volume MeasureTheory.volume :=
    (MeasureTheory.MeasurePreserving.id
      (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))).prod
      (translate_spacetime_measurePreserving (d := d) (timeShiftVec d t))
  simpa [probeFixedTimeRepresentativeCenterDiffShift_local, eprod]
    using heprod.symm.comp (hshift.comp heprod)

private theorem probeFixedTimeRepresentativeSection_measurePreserving_local
    (t : ℝ) :
    MeasureTheory.MeasurePreserving
      (probeFixedTimeRepresentativeSection_local (d := d) t)
      MeasureTheory.volume MeasureTheory.volume := by
  let eCD : NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
    (twoPointCenterDiffCLE d).toHomeomorph.toMeasurableEquiv
  have hCD :
      MeasureTheory.MeasurePreserving eCD
        MeasureTheory.volume MeasureTheory.volume := by
    simpa [eCD] using twoPointCenterDiff_measurePreserving (d := d)
  have hshift :
      MeasureTheory.MeasurePreserving
        (probeFixedTimeRepresentativeCenterDiffShift_local (d := d) t)
        MeasureTheory.volume MeasureTheory.volume :=
    probeFixedTimeRepresentativeCenterDiffShift_measurePreserving_local (d := d) t
  rw [probeFixedTimeRepresentativeSection_eq_centerDiff_comp_local (d := d) t]
  simpa [eCD] using hCD.comp hshift

private theorem twoPointCenterDiff_toDiffFlat_wickRotate_probe_local
    (z : NPointDomain d 2) :
    BHW.toDiffFlat 2 d (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)) =
      BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)) := by
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  fin_cases i
  ·
    simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
      twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint]
  ·
    by_cases hμ : μ = 0
    ·
      subst hμ
      simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint]
      ring_nf
    ·
      simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint, hμ]

private theorem twoPointCenterDiffCLE_symm_probeFixedTimeRepresentativeSection_local
    (t : ℝ) (z : NPointDomain d 2) :
    (twoPointCenterDiffCLE d).symm
        (probeFixedTimeRepresentativeSection_local (d := d) t z) =
      ![z 0, z 1 + timeShiftVec d t] := by
  ext i μ
  fin_cases i
  ·
    simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
      probeFixedTimeRepresentativeSection_local]
  ·
    by_cases hμ : μ = 0
    ·
      subst hμ
      simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
        probeFixedTimeRepresentativeSection_local, timeShiftVec]
      ring_nf
    ·
      simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
        probeFixedTimeRepresentativeSection_local, timeShiftVec, hμ]

private theorem flattenCfg_wickRotate_probeFixedTimeRepresentative_centerDiff_eq_update_local
    (t : ℝ) (z : NPointDomain d 2) :
    BHW.flattenCfg 2 d
        (fun i =>
          wickRotatePoint
            (((twoPointCenterDiffCLE d).symm
              (probeFixedTimeRepresentativeSection_local (d := d) t z)) i)) =
      Function.update
        (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
        (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
        (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
          (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
          (t : ℂ) * Complex.I) := by
  rw [twoPointCenterDiffCLE_symm_probeFixedTimeRepresentativeSection_local (d := d) t z]
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  fin_cases i
  ·
    simp [BHW.flattenCfg, Function.update]
  ·
    by_cases hμ : μ = 0
    ·
      subst hμ
      simp [BHW.flattenCfg, Function.update, wickRotatePoint, timeShiftVec]
      ring
    ·
      simp [BHW.flattenCfg, Function.update, wickRotatePoint, timeShiftVec, hμ]

/-- The fixed-time probe representative realizes exactly the same flattened
update as the concrete center/difference fixed-time kernel. -/
theorem k2TimeParametricKernel_eq_twoPointFixedTimeCenterDiffKernel_on_probeFixedTimeRepresentative_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℝ) (z : NPointDomain d 2) :
    k2TimeParametricKernel (d := d) G
        (probeFixedTimeRepresentativeSection_local (d := d) t z) =
      OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
        (d := d) G ((t : ℂ) * Complex.I) z := by
  rw [k2TimeParametricKernel, OSReconstruction.twoPointFixedTimeCenterDiffKernel_local]
  congr 1
  calc
    BHW.toDiffFlat 2 d
        (fun i =>
          wickRotatePoint
            (probeFixedTimeRepresentativeSection_local (d := d) t z i))
      =
        BHW.flattenCfg 2 d
          (fun i =>
            wickRotatePoint
              (((twoPointCenterDiffCLE d).symm
                (probeFixedTimeRepresentativeSection_local (d := d) t z)) i)) := by
          simpa using
            twoPointCenterDiff_toDiffFlat_wickRotate_probe_local
              (d := d)
              ((twoPointCenterDiffCLE d).symm
                (probeFixedTimeRepresentativeSection_local (d := d) t z))
    _ =
        Function.update
          (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
          (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
          (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
            (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
            (t : ℂ) * Complex.I) := by
          exact
            flattenCfg_wickRotate_probeFixedTimeRepresentative_centerDiff_eq_update_local
              (d := d) t z

/-- For the public approximate-identity probe package, the probe fixed-time
center/difference kernel is exactly the shifted real-difference kernel on the
open strip `-t < ξ₀`. -/
theorem exists_probeSeq_fixedTimeCenterDiffKernel_eq_shifted_realDifferenceKernel_on_strip_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      ∀ n (t : ℝ) (z : NPointDomain d 2), 0 < t → -t < z 1 0 →
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z =
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) := by
  obtain ⟨μ_seq, hμfin, _hhol, _hsupp, _hμrepr, hkernel, _hpair⟩ :=
    exists_k2_positiveTime_shell_package_of_negativeApproxIdentity_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨μ_seq, hμfin, ?_⟩
  intro n t z ht hz
  have hpos_section :
      (probeFixedTimeRepresentativeSection_local (d := d) t z) 0 0 <
        (probeFixedTimeRepresentativeSection_local (d := d) t z) 1 0 := by
    exact (probeFixedTimeRepresentativeSection_pos_iff_local (d := d) t z).2 hz
  calc
    OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
        (d := d)
        (k2ProbeWitness_local (d := d) OS lgc
          (φ_seq n) (hφ_compact n) (hφ_neg n))
        ((t : ℂ) * Complex.I) z
      =
        k2TimeParametricKernel (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          (probeFixedTimeRepresentativeSection_local (d := d) t z) := by
            symm
            exact
              k2TimeParametricKernel_eq_twoPointFixedTimeCenterDiffKernel_on_probeFixedTimeRepresentative_local
                (d := d)
                (k2ProbeWitness_local (d := d) OS lgc
                  (φ_seq n) (hφ_compact n) (hφ_neg n))
                t z
    _ =
        laplaceFourierKernel (d := d) (μ_seq n)
          (fun i =>
            (probeFixedTimeRepresentativeSection_local (d := d) t z) 1 i -
              (probeFixedTimeRepresentativeSection_local (d := d) t z) 0 i) := by
              exact hkernel n
                (probeFixedTimeRepresentativeSection_local (d := d) t z) hpos_section
    _ = laplaceFourierKernel (d := d) (μ_seq n) (z 1 + timeShiftVec d t) := by
      congr 1
      ext i
      simpa using
        congrArg (fun v : SpacetimeDim d => v i)
          (probeFixedTimeRepresentativeSection_diff_local (d := d) t z)
    _ = k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) := by
      have hξ : 0 < (z 1 + timeShiftVec d t) 0 := by
        simp [timeShiftVec]
        linarith
      dsimp [k2DifferenceKernel_real_local]
      by_cases hpos : 0 < (z 1 + timeShiftVec d t) 0
      · have hpos' : 0 < z 1 0 + timeShiftVec d t 0 := by simpa using hpos
        simp [hpos']
      · exact False.elim (hpos hξ)

/-- The canonical probe-side shifted real-difference representatives can be
chosen together with both the strip identification and the global
`twoPointFlatKernelCLM` package needed for difference-only shell transport. -/
theorem exists_probeSeq_fixedTimeCenterDiffKernel_eq_and_shifted_realDifference_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      (∀ n (t : ℝ) (z : NPointDomain d 2), 0 < t → -t < z 1 0 →
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z =
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t)) ∧
      (∀ n (t : ℝ),
        ∃ (C_bd : ℝ) (N : ℕ), 0 < C_bd ∧
          AEStronglyMeasurable
            (fun z : NPointDomain d 2 =>
              k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t))
            volume ∧
          (∀ᵐ z : NPointDomain d 2 ∂volume,
            ‖k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t)‖ ≤
              C_bd * (1 + ‖z‖) ^ N)) := by
  obtain ⟨μ_seq, hμfin, _hhol, _hsupp, hμrepr, hkernel, _hpair⟩ :=
    exists_k2_positiveTime_shell_package_of_negativeApproxIdentity_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨μ_seq, hμfin, ?_, ?_⟩
  · intro n t z ht hz
    have hpos_section :
        (probeFixedTimeRepresentativeSection_local (d := d) t z) 0 0 <
          (probeFixedTimeRepresentativeSection_local (d := d) t z) 1 0 := by
      exact (probeFixedTimeRepresentativeSection_pos_iff_local (d := d) t z).2 hz
    calc
      OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z
        =
          k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            (probeFixedTimeRepresentativeSection_local (d := d) t z) := by
              symm
              exact
                k2TimeParametricKernel_eq_twoPointFixedTimeCenterDiffKernel_on_probeFixedTimeRepresentative_local
                  (d := d)
                  (k2ProbeWitness_local (d := d) OS lgc
                    (φ_seq n) (hφ_compact n) (hφ_neg n))
                  t z
      _ =
          laplaceFourierKernel (d := d) (μ_seq n)
            (fun i =>
              (probeFixedTimeRepresentativeSection_local (d := d) t z) 1 i -
                (probeFixedTimeRepresentativeSection_local (d := d) t z) 0 i) := by
              exact hkernel n
                (probeFixedTimeRepresentativeSection_local (d := d) t z) hpos_section
      _ = laplaceFourierKernel (d := d) (μ_seq n) (z 1 + timeShiftVec d t) := by
        congr 1
        ext i
        simpa using
          congrArg (fun v : SpacetimeDim d => v i)
            (probeFixedTimeRepresentativeSection_diff_local (d := d) t z)
      _ = k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) := by
        have hξ : 0 < (z 1 + timeShiftVec d t) 0 := by
          simp [timeShiftVec]
          linarith
        dsimp [k2DifferenceKernel_real_local]
        by_cases hpos : 0 < (z 1 + timeShiftVec d t) 0
        · have hpos' : 0 < z 1 0 + timeShiftVec d t 0 := by simpa using hpos
          simp [hpos']
        · exact False.elim (hpos hξ)
  · intro n t
    obtain ⟨C_bd, hC, hK_bound⟩ :=
      exists_k2TimeParametricKernel_real_bound_local
        (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n)
    have hcomp_meas :=
      (aestronglyMeasurable_k2TimeParametricKernel_real_local
        (d := d) OS lgc (φ_seq n) (hφ_compact n) (hφ_neg n)).comp_measurePreserving
        (probeFixedTimeRepresentativeSection_measurePreserving_local (d := d) t)
    refine ⟨C_bd, 0, hC, ?_, ?_⟩
    · refine hcomp_meas.congr ?_
      filter_upwards with z
      have hEq :=
        k2TimeParametricKernel_real_eq_twoPointDifferenceKernel_local
          (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n)
          (μ_seq n) (hμrepr n)
      have hval0 := congrArg
        (fun F =>
          F (probeFixedTimeRepresentativeSection_local (d := d) t z)) hEq
      symm
      simpa [OSReconstruction.twoPointDifferenceKernel,
        probeFixedTimeRepresentativeSection_diff_local] using hval0.symm
    · refine Filter.Eventually.of_forall ?_
      intro z
      have hEq :=
        k2TimeParametricKernel_real_eq_twoPointDifferenceKernel_local
          (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n)
          (μ_seq n) (hμrepr n)
      have hval0 := congrArg
        (fun F =>
          F (probeFixedTimeRepresentativeSection_local (d := d) t z)) hEq
      have hval := hval0
      have hz_shifted :
          ‖k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t)‖ ≤ C_bd := by
        simp [OSReconstruction.twoPointDifferenceKernel,
          probeFixedTimeRepresentativeSection_diff_local] at hval
        rw [← hval]
        exact hK_bound (probeFixedTimeRepresentativeSection_local (d := d) t z)
      simpa using hz_shifted

/-- On compactly supported tests inside the positive strip, the probe fixed-time
center/difference kernel and the explicit shifted real-difference representative
already have identical pairings. This is the exact compact-support pairing
surface used later for the common-witness comparison, but here it is completely
formal from the pointwise strip identity. -/
theorem exists_probeSeq_fixedTimeCenterDiffKernel_compactSupport_positiveStrip_pairing_eq_shifted_realDifference_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      ∀ n (t : ℝ), 0 < t →
        ∀ f : SchwartzMap (NPointDomain d 2) ℂ,
          HasCompactSupport (f : NPointDomain d 2 → ℂ) →
          Function.support (f : NPointDomain d 2 → ℂ) ⊆
            {z : NPointDomain d 2 | 0 < z 1 0} →
          ∫ z : NPointDomain d 2,
            twoPointFixedTimeCenterDiffKernel_local
              (d := d)
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq n) (hφ_compact n) (hφ_neg n))
              ((t : ℂ) * Complex.I) z * f z =
          ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) * f z := by
  obtain ⟨μ_seq, hμfin, hrepr⟩ :=
    exists_probeSeq_fixedTimeCenterDiffKernel_eq_shifted_realDifferenceKernel_on_strip_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨μ_seq, hμfin, ?_⟩
  intro n t ht f _hf_compact hf_support
  refine integral_congr_ae ?_
  filter_upwards with z
  by_cases hz : f z = 0
  · simp [hz]
  · have hz_mem : z ∈ Function.support (f : NPointDomain d 2 → ℂ) :=
      Function.mem_support.mpr hz
    have hz_pos : 0 < z 1 0 := hf_support hz_mem
    have hz_strip : -t < z 1 0 := by
      have hneg : -t < 0 := by linarith
      exact lt_trans hneg hz_pos
    rw [hrepr n t z ht hz_strip]

/-- Package together the two fixed-strip sides that now drive the production
Input-A route:

1. one common fixed-time witness `G` for the reflected product-shell matrix
   elements, and
2. one per-probe shifted real-difference representative `μ_seq` realizing the
   actual probe fixed-time kernels on the open strip.

This keeps the common-witness side and the explicit probe representative on one
shared production surface without adding any new mathematical content. -/
theorem exists_common_fixed_strip_fixedTimeCenterDiff_with_probe_realDifference_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
        IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
        (∀ (f : ZeroDiagonalSchwartz d 2),
          OS.S 2 f = ∫ x : NPointDomain d 2,
            G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
        (∀ n, IsFiniteMeasure (μ_seq n)) ∧
        (∀ n,
          let xφ : OSHilbertSpace OS :=
            (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single 1
                    (SchwartzNPoint.osConj (d := d) (n := 1)
                      (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                    (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
                OSHilbertSpace OS))
          osSemigroupGroupMatrixElement (d := d) OS lgc xφ t (0 : Fin d → ℝ) =
            ∫ z : NPointDomain d 2,
              OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
                (d := d) G ((t : ℂ) * Complex.I) z *
                ((φ_seq n) (z 0) *
                  reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1))) ∧
        (∀ n (z : NPointDomain d 2), -t < z 1 0 →
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((t : ℂ) * Complex.I) z =
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t)) := by
  obtain ⟨G, hG_holo, hG_euclid, hprod⟩ :=
    exists_common_fixed_strip_fixedTimeCenterDiff_productShell_pairing_with_witness_local
      (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg t ht
  obtain ⟨μ_seq, hμfin, hrepr⟩ :=
    exists_probeSeq_fixedTimeCenterDiffKernel_eq_shifted_realDifferenceKernel_on_strip_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨G, μ_seq, hG_holo, hG_euclid, hμfin, ?_, ?_⟩
  · intro n
    simpa using hprod n
  · intro n z hz
    simpa using hrepr n t z ht hz

private theorem shifted_realDifferenceKernel_continuousOn_strip_of_probe_repr_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (t : ℝ) (ht : 0 < t)
    (hrepr : ∀ n (z : NPointDomain d 2), -t < z 1 0 →
      OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
        (d := d)
        (k2ProbeWitness_local (d := d) OS lgc
          (φ_seq n) (hφ_compact n) (hφ_neg n))
        ((t : ℂ) * Complex.I) z =
      k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t)) :
    ∀ n,
      ContinuousOn
        (fun z : NPointDomain d 2 =>
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t))
        {z : NPointDomain d 2 | -t < z 1 0} := by
  intro n
  let W :=
    k2ProbeWitness_local (d := d) OS lgc
      (φ_seq n) (hφ_compact n) (hφ_neg n)
  have hcont_time :
      ContinuousOn
        (fun z : NPointDomain d 2 =>
          k2TimeParametricKernel (d := d) W
            (probeFixedTimeRepresentativeSection_local (d := d) t z))
        {z : NPointDomain d 2 | -t < z 1 0} := by
    have hcont := continuousOn_k2TimeParametricKernel_of_pos_local
      (d := d) OS lgc (φ_seq n) (hφ_compact n) (hφ_neg n)
    have hmaps :
        Set.MapsTo (probeFixedTimeRepresentativeSection_local (d := d) t)
          {z : NPointDomain d 2 | -t < z 1 0}
          {x : NPointDomain d 2 | x 0 0 < x 1 0} := by
      intro z hz
      exact (probeFixedTimeRepresentativeSection_pos_iff_local (d := d) t z).2 hz
    exact hcont.comp
      (continuous_probeFixedTimeRepresentativeSection_local (d := d) t).continuousOn
      hmaps
  have hcont_fixed :
      ContinuousOn
        (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) W ((t : ℂ) * Complex.I))
        {z : NPointDomain d 2 | -t < z 1 0} := by
    refine hcont_time.congr ?_
    intro z hz
    symm
    exact
      k2TimeParametricKernel_eq_twoPointFixedTimeCenterDiffKernel_on_probeFixedTimeRepresentative_local
        (d := d) W t z
  refine hcont_fixed.congr ?_
  intro z hz
  symm
  exact hrepr n z hz

/-- The common fixed-strip witness/probe package can be extended with continuity
of the same shifted real-difference representatives on the strip `{-t < ξ₀}`.

This keeps the exact `μ_seq` already tied to the common witness `G`, so later
line-107 work can stay on one witness package instead of reintroducing an
existential mismatch. -/
theorem exists_common_fixed_strip_fixedTimeCenterDiff_with_probe_realDifference_continuous_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
        IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
        (∀ (f : ZeroDiagonalSchwartz d 2),
          OS.S 2 f = ∫ x : NPointDomain d 2,
            G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
        (∀ n, IsFiniteMeasure (μ_seq n)) ∧
        (∀ n,
          let xφ : OSHilbertSpace OS :=
            (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single 1
                    (SchwartzNPoint.osConj (d := d) (n := 1)
                      (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                    (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
                OSHilbertSpace OS))
          osSemigroupGroupMatrixElement (d := d) OS lgc xφ t (0 : Fin d → ℝ) =
            ∫ z : NPointDomain d 2,
              OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
                (d := d) G ((t : ℂ) * Complex.I) z *
                ((φ_seq n) (z 0) *
                  reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1))) ∧
        (∀ n (z : NPointDomain d 2), -t < z 1 0 →
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((t : ℂ) * Complex.I) z =
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t)) ∧
        (∀ n,
          ContinuousOn
            (fun z : NPointDomain d 2 =>
              k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t))
            {z : NPointDomain d 2 | -t < z 1 0}) := by
  obtain ⟨G, μ_seq, hG_holo, hG_euclid, hμfin, hprod, hrepr⟩ :=
    exists_common_fixed_strip_fixedTimeCenterDiff_with_probe_realDifference_package_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg t ht
  have hcont :=
    shifted_realDifferenceKernel_continuousOn_strip_of_probe_repr_local
      (d := d) OS lgc φ_seq hφ_compact hφ_neg μ_seq t ht hrepr
  exact ⟨G, μ_seq, hG_holo, hG_euclid, hμfin, hprod, hrepr, hcont⟩

/-- The explicit shifted real-difference representative produced by the probe
package is continuous on the fixed strip. -/
theorem exists_probeSeq_shifted_realDifferenceKernel_continuousOn_strip_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      ∀ n (t : ℝ), 0 < t →
        ContinuousOn
          (fun z : NPointDomain d 2 =>
            k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t))
          {z : NPointDomain d 2 | -t < z 1 0} := by
  obtain ⟨μ_seq, hμfin, hrepr⟩ :=
    exists_probeSeq_fixedTimeCenterDiffKernel_eq_shifted_realDifferenceKernel_on_strip_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨μ_seq, hμfin, ?_⟩
  intro n t ht
  let W :=
    k2ProbeWitness_local (d := d) OS lgc (φ_seq n) (hφ_compact n) (hφ_neg n)
  have hcont_time :
      ContinuousOn
        (fun z : NPointDomain d 2 =>
          k2TimeParametricKernel (d := d) W
            (probeFixedTimeRepresentativeSection_local (d := d) t z))
        {z : NPointDomain d 2 | -t < z 1 0} := by
    have hcont := continuousOn_k2TimeParametricKernel_of_pos_local
      (d := d) OS lgc (φ_seq n) (hφ_compact n) (hφ_neg n)
    have hmaps :
        Set.MapsTo (probeFixedTimeRepresentativeSection_local (d := d) t)
          {z : NPointDomain d 2 | -t < z 1 0}
          {x : NPointDomain d 2 | x 0 0 < x 1 0} := by
      intro z hz
      exact (probeFixedTimeRepresentativeSection_pos_iff_local (d := d) t z).2 hz
    exact hcont.comp
      (continuous_probeFixedTimeRepresentativeSection_local (d := d) t).continuousOn
      hmaps
  have hcont_fixed :
      ContinuousOn
        (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) W ((t : ℂ) * Complex.I))
        {z : NPointDomain d 2 | -t < z 1 0} := by
    refine hcont_time.congr ?_
    intro z hz
    symm
    exact
      k2TimeParametricKernel_eq_twoPointFixedTimeCenterDiffKernel_on_probeFixedTimeRepresentative_local
        (d := d) W t z
  refine hcont_fixed.congr ?_
  intro z hz
  symm
  exact hrepr n t z ht hz

/-- The fixed-time center/difference shell pairing of each probe witness
factorizes through the shifted real one-variable difference kernel on the fixed
strip. -/
theorem exists_probeSeq_fixedTimeCenterDiffKernel_differenceShell_factorization_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d) (t : ℝ),
        0 < t →
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((t : ℂ) * Complex.I) z *
            (χ (z 0) * ((h : SchwartzSpacetime d) (z 1))) =
        (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d,
            k2DifferenceKernel_real_local (d := d) (μ_seq n) (ξ + timeShiftVec d t) *
              ((h : SchwartzSpacetime d) ξ) := by
  obtain ⟨μ_seq, hμfin, hrepr⟩ :=
    exists_probeSeq_fixedTimeCenterDiffKernel_eq_shifted_realDifferenceKernel_on_strip_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨μ_seq, hμfin, ?_⟩
  intro n χ h t ht
  let Kt : SpacetimeDim d → ℂ :=
    fun ξ => k2DifferenceKernel_real_local (d := d) (μ_seq n) (ξ + timeShiftVec d t)
  calc
    ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χ (z 0) * ((h : SchwartzSpacetime d) (z 1)))
      = ∫ z : NPointDomain d 2,
          Kt (z 1) * (χ (z 0) * ((h : SchwartzSpacetime d) (z 1))) := by
            refine integral_congr_ae ?_
            filter_upwards with z
            by_cases hz0 : ((h : SchwartzSpacetime d) (z 1)) = 0
            · simp [Kt, hz0]
            · have hz_mem : z 1 ∈ tsupport ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ) :=
                subset_tsupport _ (Function.mem_support.mpr hz0)
              have hz_pos : 0 < (z 1) 0 := h.property.1 hz_mem
              have hz_strip : -t < z 1 0 := by linarith
              rw [hrepr n t z ht hz_strip]
    _ = (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d, Kt ξ * ((h : SchwartzSpacetime d) ξ) := by
            exact integral_centerDiff_differenceOnly_kernel_factorizes
              (d := d) Kt χ (h : SchwartzSpacetime d)

/-- Consequently, on every positive-support difference shell, the probe
fixed-time center/difference kernel already has the same pairing as the
explicit shifted real-difference representative. -/
theorem exists_probeSeq_fixedTimeCenterDiffKernel_differenceShell_eq_shifted_realDifference_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d) (t : ℝ),
        0 < t →
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((t : ℂ) * Complex.I) z *
            (χ (z 0) * ((h : SchwartzSpacetime d) (z 1))) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            (χ (z 0) * ((h : SchwartzSpacetime d) (z 1))) := by
  obtain ⟨μ_seq, hμfin, hfactor⟩ :=
    exists_probeSeq_fixedTimeCenterDiffKernel_differenceShell_factorization_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨μ_seq, hμfin, ?_⟩
  intro n χ h t ht
  let Kt : SpacetimeDim d → ℂ :=
    fun ξ => k2DifferenceKernel_real_local (d := d) (μ_seq n) (ξ + timeShiftVec d t)
  calc
    ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χ (z 0) * ((h : SchwartzSpacetime d) (z 1)))
      = (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d, Kt ξ * ((h : SchwartzSpacetime d) ξ) := by
            exact hfactor n χ h t ht
    _ = ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            (χ (z 0) * ((h : SchwartzSpacetime d) (z 1))) := by
            exact
              (integral_centerDiff_differenceOnly_kernel_factorizes
                (d := d) Kt χ (h : SchwartzSpacetime d)).symm

/-- Specialization of the previous shell equality to the fixed-center descended
shell used on the Input A route. -/
theorem exists_probeSeq_fixedTimeCenterDiffKernel_fixed_center_eq_shifted_realDifference_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χc : SchwartzSpacetime d)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hdesc_compact : ∀ n,
      HasCompactSupport
        (((twoPointCenterShearDescent (d := d) (φ_seq n)
          (reflectedSchwartzSpacetime (d := d) (φ_seq n))) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      ∀ n (t : ℝ), 0 < t →
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((t : ℂ) * Complex.I) z *
            (χc (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            (χc (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) := by
  obtain ⟨μ_seq, hμfin, hprobe_shifted⟩ :=
    exists_probeSeq_fixedTimeCenterDiffKernel_differenceShell_eq_shifted_realDifference_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨μ_seq, hμfin, ?_⟩
  intro n t ht
  let hdesc_n : SchwartzSpacetime d :=
    twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (d := d) (φ_seq n))
  have hdesc_pos :
      tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
    dsimp [hdesc_n]
    exact twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
  let hdesc_pt : positiveTimeCompactSupportSubmodule d :=
    ⟨hdesc_n, hdesc_pos, hdesc_compact n⟩
  simpa [hdesc_n] using hprobe_shifted n χc hdesc_pt t ht

/-- On the reflected product shell, each probe fixed-time kernel already agrees
with the explicit shifted real-difference representative. This is the remaining
probe-side shell equality needed to reduce the common product-shell bridge to a
common-vs-probe statement. -/
theorem exists_probeSeq_fixedTimeCenterDiffKernel_productShell_eq_shifted_realDifference_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      ∀ n (t : ℝ), 0 < t →
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
  obtain ⟨μ_seq, hμfin, hrepr⟩ :=
    exists_probeSeq_fixedTimeCenterDiffKernel_eq_shifted_realDifferenceKernel_on_strip_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨μ_seq, hμfin, ?_⟩
  intro n t ht
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
    have hz1_pos : 0 < z 1 0 := by linarith
    have hz_strip : -t < z 1 0 := by
              have h0 : -t < 0 := by linarith
              exact lt_trans h0 hz1_pos
    rw [hrepr n t z ht hz_strip]

/-- Parametric version of the previous reflected product-shell bridge: once a
single probe-side representative `μ_seq` is fixed and its pointwise strip
identity is known, any common-vs-probe reflected product-shell comparison
immediately upgrades to a common-vs-shifted comparison on that same `μ_seq`. -/
theorem common_shifted_realDifference_productShell_of_common_probe_productShell_bridge_of_repr_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t)
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (hrepr : ∀ n (z : NPointDomain d 2), -t < z 1 0 →
      OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
        (d := d)
        (k2ProbeWitness_local (d := d) OS lgc
          (φ_seq n) (hφ_compact n) (hφ_neg n))
        ((t : ℂ) * Complex.I) z =
      k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t))
    (hcommon_probe_prod : ∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) :
    ∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
  intro n
  calc
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))
      =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hcommon_probe_prod n
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
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
            have hz1_pos : 0 < z 1 0 := by linarith
            have hz_strip : -t < z 1 0 := by
              have h0 : -t < 0 := by linarith
              exact lt_trans h0 hz1_pos
            rw [hrepr n z hz_strip]

/-- Once the explicit probe-side reflected product-shell equality is available,
any future common-vs-probe reflected product-shell bridge already upgrades to
the common-vs-shifted bridge used on the Input A route. -/
theorem exists_common_shifted_realDifference_productShell_package_of_common_probe_productShell_bridges_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t)
    (hcommon_probe_prod : ∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      ∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
  obtain ⟨μ_seq, hμfin, hprobe_shifted_prod⟩ :=
    exists_probeSeq_fixedTimeCenterDiffKernel_productShell_eq_shifted_realDifference_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨μ_seq, hμfin, ?_⟩
  intro n
  calc
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))
      =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hcommon_probe_prod n
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hprobe_shifted_prod n t ht

/-- On the same-center descended shell, a fixed normalized-center bridge is
already enough.

If the common fixed-time kernel agrees with the actual probe fixed-time kernel
on one normalized shell `χc ⊗ hdesc`, then the already-paid probe
representative theorem upgrades this to agreement with the explicit shifted
real-difference representative on the actual center `φ`. -/
theorem exists_common_shifted_realDifference_same_center_package_of_common_probe_fixed_center_bridges_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
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
    (hdesc_compact : ∀ n,
      HasCompactSupport
        (((twoPointCenterShearDescent (d := d) (φ_seq n)
          (reflectedSchwartzSpacetime (d := d) (φ_seq n))) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t)
    (hcommon_probe_fixed_center : ∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1))) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1))) := by
  obtain ⟨μ_seq, hμfin, hprobe_shifted⟩ :=
    exists_probeSeq_fixedTimeCenterDiffKernel_differenceShell_eq_shifted_realDifference_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨μ_seq, hμfin, ?_⟩
  intro n
  let hdesc_n : SchwartzSpacetime d :=
    twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (d := d) (φ_seq n))
  have hdesc_pos :
      tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
    dsimp [hdesc_n]
    exact twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
  let hdesc_pt : positiveTimeCompactSupportSubmodule d :=
    ⟨hdesc_n, hdesc_pos, hdesc_compact n⟩
  obtain ⟨c, hc⟩ :=
    schwinger_twoPoint_fixedTimeCenterDiffKernel_exists_const_local
      (d := d) OS G hG_euclid hdesc_n hdesc_pos t ht
  have hcommon_center :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc_n (z 1)) := by
    calc
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) * hdesc_n (z 1))
        = c * ∫ u : SpacetimeDim d, φ_seq n u := hc (φ_seq n)
      _ = c * ∫ u : SpacetimeDim d, χc u := by rw [hφ_int n, hχc]
      _ = ∫ z : NPointDomain d 2,
            twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
              (χc (z 0) * hdesc_n (z 1)) := by
                symm
                exact hc χc
  have hprobe_shifted_fixed_center :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc_n (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          (χc (z 0) * hdesc_n (z 1)) := by
    simpa [hdesc_n] using hprobe_shifted n χc hdesc_pt t ht
  have hshifted_center :
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          (χc (z 0) * hdesc_n (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
    let Kt : SpacetimeDim d → ℂ :=
      fun ξ => k2DifferenceKernel_real_local (d := d) (μ_seq n) (ξ + timeShiftVec d t)
    calc
      ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            (χc (z 0) * hdesc_n (z 1))
        = (∫ u : SpacetimeDim d, χc u) *
            ∫ ξ : SpacetimeDim d, Kt ξ * hdesc_n ξ := by
              exact integral_centerDiff_differenceOnly_kernel_factorizes
                (d := d) Kt χc hdesc_n
      _ = (∫ u : SpacetimeDim d, φ_seq n u) *
            ∫ ξ : SpacetimeDim d, Kt ξ * hdesc_n ξ := by rw [hχc, hφ_int n]
      _ = ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
              ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
                exact
                  (integral_centerDiff_differenceOnly_kernel_factorizes
                    (d := d) Kt (φ_seq n) hdesc_n).symm
  calc
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) * hdesc_n (z 1))
      =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc_n (z 1)) := hcommon_center
    _ =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc_n (z 1)) := hcommon_probe_fixed_center n
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          (χc (z 0) * hdesc_n (z 1)) := hprobe_shifted_fixed_center
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) := hshifted_center

/-- The remaining common-vs-shifted shell package reduces to two concrete
common-vs-probe bridges: reflected product shell plus one fixed normalized
center shell. -/
theorem exists_common_shifted_realDifference_shell_package_of_common_probe_prod_and_fixed_center_bridges_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
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
    (t : ℝ) (ht : 0 < t)
    (hcommon_probe_prod : ∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)))
    (hcommon_probe_fixed_center : ∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1))) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1))) := by
  obtain ⟨μ_seq, hμfin, hrepr⟩ :=
    exists_probeSeq_fixedTimeCenterDiffKernel_eq_shifted_realDifferenceKernel_on_strip_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  have hcommon_shifted_same_center :
      ∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) := by
    intro n
    let hdesc_n : SchwartzSpacetime d :=
      twoPointCenterShearDescent (d := d) (φ_seq n)
        (reflectedSchwartzSpacetime (d := d) (φ_seq n))
    have hdesc_pos :
        tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
      dsimp [hdesc_n]
      exact twoPointCenterShearDescent_reflected_tsupport_pos_local
        (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
    have hcommon_center :
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) * hdesc_n (z 1)) =
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            (χc (z 0) * hdesc_n (z 1)) := by
      obtain ⟨c, hc⟩ :=
        schwinger_twoPoint_fixedTimeCenterDiffKernel_exists_const_local
          (d := d) OS G hG_euclid hdesc_n hdesc_pos t ht
      calc
        ∫ z : NPointDomain d 2,
            twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
              ((φ_seq n) (z 0) * hdesc_n (z 1))
          = c * ∫ u : SpacetimeDim d, φ_seq n u := hc (φ_seq n)
        _ = c * ∫ u : SpacetimeDim d, χc u := by rw [hφ_int n, hχc]
        _ = ∫ z : NPointDomain d 2,
              twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
                (χc (z 0) * hdesc_n (z 1)) := by
                  symm
                  exact hc χc
    have hprobe_shifted_fixed_center :
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((t : ℂ) * Complex.I) z *
            (χc (z 0) * hdesc_n (z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            (χc (z 0) * hdesc_n (z 1)) := by
      have hpair_strip :
          ∀ z : NPointDomain d 2, hdesc_n (z 1) ≠ 0 → -t < z 1 0 := by
        intro z hz
        have hz_mem : z 1 ∈ tsupport (hdesc_n : SpacetimeDim d → ℂ) :=
          subset_tsupport _ (Function.mem_support.mpr hz)
        have hz_pos : 0 < z 1 0 := hdesc_pos hz_mem
        have h0 : -t < 0 := by linarith
        exact lt_trans h0 hz_pos
      refine integral_congr_ae ?_
      filter_upwards with z
      by_cases hz : hdesc_n (z 1) = 0
      · simp [hz]
      · rw [hrepr n t z ht (hpair_strip z hz)]
    have hshifted_center :
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            (χc (z 0) * hdesc_n (z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
      let Kt : SpacetimeDim d → ℂ :=
        fun ξ => k2DifferenceKernel_real_local (d := d) (μ_seq n) (ξ + timeShiftVec d t)
      calc
        ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
              (χc (z 0) * hdesc_n (z 1))
          = (∫ u : SpacetimeDim d, χc u) *
              ∫ ξ : SpacetimeDim d, Kt ξ * hdesc_n ξ := by
                exact integral_centerDiff_differenceOnly_kernel_factorizes
                  (d := d) Kt χc hdesc_n
        _ = (∫ u : SpacetimeDim d, φ_seq n u) *
              ∫ ξ : SpacetimeDim d, Kt ξ * hdesc_n ξ := by rw [hχc, hφ_int n]
        _ = ∫ z : NPointDomain d 2,
              k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
                ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
                  exact
                    (integral_centerDiff_differenceOnly_kernel_factorizes
                      (d := d) Kt (φ_seq n) hdesc_n).symm
    calc
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) * hdesc_n (z 1))
        =
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            (χc (z 0) * hdesc_n (z 1)) := hcommon_center
      _ =
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local
            (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n))
            ((t : ℂ) * Complex.I) z *
            (χc (z 0) * hdesc_n (z 1)) := hcommon_probe_fixed_center n
      _ =
      ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            (χc (z 0) * hdesc_n (z 1)) := hprobe_shifted_fixed_center
      _ =
      ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) * hdesc_n (z 1)) := hshifted_center
  have hcommon_shifted_prod :
      ∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
    exact
      common_shifted_realDifference_productShell_of_common_probe_productShell_bridge_of_repr_local
        (d := d) OS lgc G φ_seq hφ_compact hφ_neg t ht μ_seq
        (fun n z hz => hrepr n t z ht hz) hcommon_probe_prod
  exact ⟨μ_seq, hμfin, hcommon_shifted_prod, hcommon_shifted_same_center⟩

/-- Parametric same-center bridge on one fixed `μ_seq`. This is the witness-
aligned form actually useful downstream: once the common fixed-time kernel
agrees with the probe fixed-time kernel on one normalized descended shell, the
pointwise probe representative identity upgrades that to common-vs-shifted
agreement on the actual center `φ`. -/
theorem common_shifted_realDifference_same_center_of_common_probe_fixed_center_bridge_of_repr_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t)
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (hrepr : ∀ n (z : NPointDomain d 2), -t < z 1 0 →
      OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
        (d := d)
        (k2ProbeWitness_local (d := d) OS lgc
          (φ_seq n) (hφ_compact n) (hφ_neg n))
        ((t : ℂ) * Complex.I) z =
      k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t))
    (hcommon_probe_fixed_center : ∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1))) :
    ∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) *
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) := by
  intro n
  let hdesc_n : SchwartzSpacetime d :=
    twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (d := d) (φ_seq n))
  have hdesc_pos :
      tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
    dsimp [hdesc_n]
    exact twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
  have hcommon_center :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc_n (z 1)) := by
    obtain ⟨c, hc⟩ :=
      schwinger_twoPoint_fixedTimeCenterDiffKernel_exists_const_local
        (d := d) OS G hG_euclid hdesc_n hdesc_pos t ht
    calc
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) * hdesc_n (z 1))
        = c * ∫ u : SpacetimeDim d, φ_seq n u := hc (φ_seq n)
      _ = c * ∫ u : SpacetimeDim d, χc u := by rw [hφ_int n, hχc]
      _ = ∫ z : NPointDomain d 2,
            twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
              (χc (z 0) * hdesc_n (z 1)) := by
                symm
                exact hc χc
  have hprobe_shifted_fixed_center :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc_n (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          (χc (z 0) * hdesc_n (z 1)) := by
    have hpair_strip :
        ∀ z : NPointDomain d 2, hdesc_n (z 1) ≠ 0 → -t < z 1 0 := by
      intro z hz
      have hz_mem : z 1 ∈ tsupport (hdesc_n : SpacetimeDim d → ℂ) :=
        subset_tsupport _ (Function.mem_support.mpr hz)
      have hz_pos : 0 < z 1 0 := hdesc_pos hz_mem
      have h0 : -t < 0 := by linarith
      exact lt_trans h0 hz_pos
    refine integral_congr_ae ?_
    filter_upwards with z
    by_cases hz : hdesc_n (z 1) = 0
    · simp [hz]
    · rw [hrepr n z (hpair_strip z hz)]
  have hshifted_center :
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          (χc (z 0) * hdesc_n (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
    let Kt : SpacetimeDim d → ℂ :=
      fun ξ => k2DifferenceKernel_real_local (d := d) (μ_seq n) (ξ + timeShiftVec d t)
    calc
      ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            (χc (z 0) * hdesc_n (z 1))
        = (∫ u : SpacetimeDim d, χc u) *
            ∫ ξ : SpacetimeDim d, Kt ξ * hdesc_n ξ := by
              exact integral_centerDiff_differenceOnly_kernel_factorizes
                (d := d) Kt χc hdesc_n
      _ = (∫ u : SpacetimeDim d, φ_seq n u) *
            ∫ ξ : SpacetimeDim d, Kt ξ * hdesc_n ξ := by rw [hχc, hφ_int n]
      _ = ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
              ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
                exact
                  (integral_centerDiff_differenceOnly_kernel_factorizes
                    (d := d) Kt (φ_seq n) hdesc_n).symm
  calc
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) * hdesc_n (z 1))
      =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc_n (z 1)) := hcommon_center
    _ =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc_n (z 1)) := hcommon_probe_fixed_center n
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          (χc (z 0) * hdesc_n (z 1)) := hprobe_shifted_fixed_center
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) := hshifted_center

/-- One compact-support positive-strip pairing theorem already pays both
concrete common-vs-probe shell bridges still needed on the Input-A route. -/
theorem exists_common_probe_shell_bridges_of_compactSupport_positiveStrip_pairing_eq_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χc : SchwartzSpacetime d)
    (hχc_compact : HasCompactSupport (χc : SpacetimeDim d → ℂ))
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hdesc_compact : ∀ n,
      HasCompactSupport
        (((twoPointCenterShearDescent (d := d) (φ_seq n)
          (reflectedSchwartzSpacetime (d := d) (φ_seq n))) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
    (t : ℝ)
    (hint_pair : ∀ n (f : SchwartzMap (NPointDomain d 2) ℂ),
      HasCompactSupport (f : NPointDomain d 2 → ℂ) →
      Function.support (f : NPointDomain d 2 → ℂ) ⊆ {z : NPointDomain d 2 | 0 < z 1 0} →
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z * f z =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z * f z) :
    (∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) ∧
    (∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1))) := by
  refine ⟨?_, ?_⟩
  · intro n
    let f : SchwartzMap (NPointDomain d 2) ℂ :=
      twoPointCenterDiffSchwartzCLM (d := d)
        (twoPointProductLift (φ_seq n)
          (reflectedSchwartzSpacetime (d := d) (φ_seq n)))
    have hpack :=
      reflected_productShell_compactSupport_support_subset_positiveStrip_local
        (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
    have hf_compact : HasCompactSupport (f : NPointDomain d 2 → ℂ) := by
      simpa [f, twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply] using hpack.1
    have hf_support :
        Function.support (f : NPointDomain d 2 → ℂ) ⊆ {z : NPointDomain d 2 | 0 < z 1 0} := by
      intro z hz
      have hz' :
          z ∈ Function.support
            (fun z : NPointDomain d 2 =>
              (φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
        simpa [f, twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply] using hz
      exact hpack.2 hz'
    simpa [f, twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply] using
      hint_pair n f hf_compact hf_support
  · intro n
    let hdesc_n : SchwartzSpacetime d :=
      twoPointCenterShearDescent (d := d) (φ_seq n)
        (reflectedSchwartzSpacetime (d := d) (φ_seq n))
    let f : SchwartzMap (NPointDomain d 2) ℂ :=
      twoPointCenterDiffSchwartzCLM (d := d)
        (twoPointDifferenceLift χc hdesc_n)
    have hf_compact : HasCompactSupport (f : NPointDomain d 2 → ℂ) := by
      have hprod :
          (SchwartzMap.productTensor ![χc, hdesc_n] : SchwartzNPoint d 2) =
            twoPointProductLift χc hdesc_n := by
        ext z
        simp [SchwartzMap.productTensor_apply, twoPointProductLift_apply]
      rw [show f = (twoPointProductLift χc hdesc_n : SchwartzNPoint d 2) by
            rw [show f = SchwartzMap.productTensor ![χc, hdesc_n] by
                  simp [f, hdesc_n]]
            exact hprod]
      exact hasCompactSupport_twoPointProductLift_for_reflected_local
        (d := d) χc hdesc_n hχc_compact (hdesc_compact n)
    have hdesc_pos :
        tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
      dsimp [hdesc_n]
      exact twoPointCenterShearDescent_reflected_tsupport_pos_local
        (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
    have hf_support :
        Function.support (f : NPointDomain d 2 → ℂ) ⊆ {z : NPointDomain d 2 | 0 < z 1 0} := by
      intro z hz
      rw [Function.mem_support] at hz
      have hmul :
          χc (z 0) * hdesc_n (z 1) ≠ 0 := by
        simpa [f, twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift] using hz
      have hz1_mem : z 1 ∈ tsupport (hdesc_n : SpacetimeDim d → ℂ) :=
        subset_tsupport _ (Function.mem_support.mpr (right_ne_zero_of_mul hmul))
      exact hdesc_pos hz1_mem
    simpa [f, hdesc_n, twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift] using
      hint_pair n f hf_compact hf_support

/-- Final production reduction of the common-witness shell content: one
compact-support positive-strip pairing theorem already produces the concrete
common-vs-shifted-real shell package needed downstream. -/
theorem exists_common_shifted_realDifference_shell_package_of_compactSupport_positiveStrip_pairing_eq_local
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
    (hdesc_compact : ∀ n,
      HasCompactSupport
        (((twoPointCenterShearDescent (d := d) (φ_seq n)
          (reflectedSchwartzSpacetime (d := d) (φ_seq n))) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t)
    (hint_pair : ∀ n (f : SchwartzMap (NPointDomain d 2) ℂ),
      HasCompactSupport (f : NPointDomain d 2 → ℂ) →
      Function.support (f : NPointDomain d 2 → ℂ) ⊆ {z : NPointDomain d 2 | 0 < z 1 0} →
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z * f z =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z * f z) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1))) := by
  obtain ⟨hcommon_probe_prod, hcommon_probe_fixed_center⟩ :=
    exists_common_probe_shell_bridges_of_compactSupport_positiveStrip_pairing_eq_local
      (d := d) OS lgc χc hχc_compact G φ_seq hφ_compact hφ_neg hdesc_compact t hint_pair
  exact
    exists_common_shifted_realDifference_shell_package_of_common_probe_prod_and_fixed_center_bridges_local
      (d := d) OS lgc χc hχc G hG_euclid φ_seq hφ_nonneg hφ_real hφ_int
      hφ_compact hφ_neg t ht hcommon_probe_prod hcommon_probe_fixed_center

/-- Variant of the previous production reduction with the fixed normalized
center shell exposed directly.

This is the exact bridge consumed by the frontier after the `hdesc` reduction:
once the common fixed-time kernel agrees with the explicit shifted
real-difference representative on compact-support positive-strip tests, we may
choose one fixed normalized center cutoff `χc` and obtain:

1. common-vs-shifted agreement on the reflected product shell, and
2. common-vs-shifted agreement on the fixed-center descended shell.

The shifted side uses difference-only center factorization, while the common
side uses the existing fixed-time center-value theorem. -/
theorem exists_common_shifted_realDifference_product_and_fixed_center_package_of_compactSupport_positiveStrip_pairing_eq_local
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
    (hdesc_compact : ∀ n,
      HasCompactSupport
        (((twoPointCenterShearDescent (d := d) (φ_seq n)
          (reflectedSchwartzSpacetime (d := d) (φ_seq n))) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t)
    (hint_pair : ∀ n (f : SchwartzMap (NPointDomain d 2) ℂ),
      HasCompactSupport (f : NPointDomain d 2 → ℂ) →
      Function.support (f : NPointDomain d 2 → ℂ) ⊆ {z : NPointDomain d 2 | 0 < z 1 0} →
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z * f z =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))
          ((t : ℂ) * Complex.I) z * f z) :
    ∃ μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) ∧
      (∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            (χc (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1)) =
        ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            (χc (z 0) *
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (d := d) (φ_seq n))) (z 1))) := by
  obtain ⟨μ_seq, hμfin, hcommon_shifted_prod, hcommon_shifted_same_center⟩ :=
    exists_common_shifted_realDifference_shell_package_of_compactSupport_positiveStrip_pairing_eq_local
      (d := d) OS lgc χc hχc hχc_compact G hG_euclid φ_seq hφ_nonneg hφ_real
      hφ_int hφ_compact hφ_neg hdesc_compact t ht hint_pair
  refine ⟨μ_seq, hμfin, hcommon_shifted_prod, ?_⟩
  intro n
  let hdesc_n : SchwartzSpacetime d :=
    twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (d := d) (φ_seq n))
  have hdesc_pos :
      tsupport (hdesc_n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
    dsimp [hdesc_n]
    exact twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
  obtain ⟨c, hc⟩ :=
    schwinger_twoPoint_fixedTimeCenterDiffKernel_exists_const_local
      (d := d) OS G hG_euclid hdesc_n hdesc_pos t ht
  have hcommon_center :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc_n (z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
    calc
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            (χc (z 0) * hdesc_n (z 1))
        = c * ∫ u : SpacetimeDim d, χc u := by
            simpa [hdesc_n] using hc χc
      _ = c * ∫ u : SpacetimeDim d, φ_seq n u := by rw [hχc, hφ_int n]
      _ = ∫ z : NPointDomain d 2,
            twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
              ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
                simpa [hdesc_n] using (hc (φ_seq n)).symm
  have hshifted_center :
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          (χc (z 0) * hdesc_n (z 1)) := by
    let Kt : SpacetimeDim d → ℂ :=
      fun ξ => k2DifferenceKernel_real_local (d := d) (μ_seq n) (ξ + timeShiftVec d t)
    calc
      ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
            ((φ_seq n) (z 0) * hdesc_n (z 1))
        = (∫ u : SpacetimeDim d, φ_seq n u) *
            ∫ ξ : SpacetimeDim d, Kt ξ * hdesc_n ξ := by
              exact integral_centerDiff_differenceOnly_kernel_factorizes
                (d := d) Kt (φ_seq n) hdesc_n
      _ = (∫ u : SpacetimeDim d, χc u) *
            ∫ ξ : SpacetimeDim d, Kt ξ * hdesc_n ξ := by rw [hφ_int n, hχc]
      _ = ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
              (χc (z 0) * hdesc_n (z 1)) := by
                exact
                  (integral_centerDiff_differenceOnly_kernel_factorizes
                    (d := d) Kt χc hdesc_n).symm
  calc
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc_n (z 1))
      =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) := hcommon_center
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
            simpa [hdesc_n] using hcommon_shifted_same_center n
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) (z 1 + timeShiftVec d t) *
          (χc (z 0) * hdesc_n (z 1)) := hshifted_center

/-- Translating only the center test does not change the pairing against the
explicit shifted real-difference representative. -/
theorem shifted_realDifferenceKernel_pairing_translate_center_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (χ h : SchwartzSpacetime d)
    (a : SpacetimeDim d)
    (t : ℝ) :
    ∫ z : NPointDomain d 2,
      k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
        ((SCV.translateSchwartz a χ) (z 0) * (h : SchwartzSpacetime d) (z 1)) =
    ∫ z : NPointDomain d 2,
      k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
        (χ (z 0) * (h : SchwartzSpacetime d) (z 1)) := by
  let Kt : SpacetimeDim d → ℂ :=
    fun ξ => k2DifferenceKernel_real_local (d := d) μ (ξ + timeShiftVec d t)
  have htrans :
      ∫ u : SpacetimeDim d, SCV.translateSchwartz a χ u =
        ∫ u : SpacetimeDim d, χ u := by
    have hraw :=
      congrArg (fun L : SchwartzSpacetime d →L[ℂ] ℂ => L χ)
        (OSReconstruction.integralCLM_translation_invariant (m := d + 1) a)
    simpa [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply] using hraw
  rw [integral_centerDiff_differenceOnly_kernel_factorizes (d := d) Kt
      (SCV.translateSchwartz a χ) (h : SchwartzSpacetime d)]
  rw [integral_centerDiff_differenceOnly_kernel_factorizes (d := d) Kt χ
      (h : SchwartzSpacetime d)]
  rw [htrans]

/-- For the explicit shifted real-difference representative, difference-shell
pairings depend only on the total integral of the center cutoff. -/
theorem shifted_realDifferenceKernel_differenceShell_depends_only_on_center_integral_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (χ₀ χ₁ h : SchwartzSpacetime d)
    (hint : ∫ u : SpacetimeDim d, χ₀ u = ∫ u : SpacetimeDim d, χ₁ u)
    (t : ℝ) :
    ∫ z : NPointDomain d 2,
      k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
        (χ₀ (z 0) * (h : SchwartzSpacetime d) (z 1)) =
    ∫ z : NPointDomain d 2,
      k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
        (χ₁ (z 0) * (h : SchwartzSpacetime d) (z 1)) := by
  let Kt : SpacetimeDim d → ℂ :=
    fun ξ => k2DifferenceKernel_real_local (d := d) μ (ξ + timeShiftVec d t)
  calc
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ₀ (z 0) * (h : SchwartzSpacetime d) (z 1))
      = (∫ u : SpacetimeDim d, χ₀ u) *
          ∫ ξ : SpacetimeDim d, Kt ξ * (h : SchwartzSpacetime d) ξ := by
            exact integral_centerDiff_differenceOnly_kernel_factorizes
              (d := d) Kt χ₀ (h : SchwartzSpacetime d)
    _ = (∫ u : SpacetimeDim d, χ₁ u) *
          ∫ ξ : SpacetimeDim d, Kt ξ * (h : SchwartzSpacetime d) ξ := by
            rw [hint]
    _ = ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
            (χ₁ (z 0) * (h : SchwartzSpacetime d) (z 1)) := by
              exact
                (integral_centerDiff_differenceOnly_kernel_factorizes
                  (d := d) Kt χ₁ (h : SchwartzSpacetime d)).symm

end OSReconstruction
