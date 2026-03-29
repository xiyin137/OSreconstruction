import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAKernelReduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Support

noncomputable section

open scoped Topology
open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Translate only the head/center block of a two-point center/difference
configuration `(u, ξ)`. -/
def twoPointHeadBlockTranslate_local (a : SpacetimeDim d) :
    NPointDomain d 2 → NPointDomain d 2 :=
  fun z i =>
    Fin.cases (z 0 + a)
      (fun _ => z 1) i

@[simp] theorem twoPointHeadBlockTranslate_local_zero
    (a : SpacetimeDim d) (z : NPointDomain d 2) :
    twoPointHeadBlockTranslate_local (d := d) a z 0 =
      z 0 + a := by
  simp [twoPointHeadBlockTranslate_local]

@[simp] theorem twoPointHeadBlockTranslate_local_one
    (a : SpacetimeDim d) (z : NPointDomain d 2) :
    twoPointHeadBlockTranslate_local (d := d) a z 1 = z 1 := by
  change Fin.cases (z 0 + a) (fun _ => z 1) (Fin.succ 0) = z 1
  rfl

theorem twoPointHeadBlockTranslate_local_eq_update
    (a : SpacetimeDim d) (z : NPointDomain d 2) :
    twoPointHeadBlockTranslate_local (d := d) a z =
      Function.update z 0 (z 0 + a) := by
  ext i μ
  fin_cases i
  · simp [twoPointHeadBlockTranslate_local, Function.update]
  · change Fin.cases (z 0 + a) (fun _ => z 1) (Fin.succ 0) μ = z 1 μ
    rfl

private theorem continuous_twoPointHeadBlockTranslate_local
    (a : SpacetimeDim d) :
    Continuous (twoPointHeadBlockTranslate_local (d := d) a) := by
  refine continuous_pi ?_
  intro i
  fin_cases i
  · simpa [twoPointHeadBlockTranslate_local] using
      ((continuous_apply (0 : Fin 2)).add continuous_const)
  · simpa [twoPointHeadBlockTranslate_local] using continuous_apply (1 : Fin 2)

private def twoPointHeadBlockTranslate_measurableEquiv_local
    (a : SpacetimeDim d) :
    NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
  let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
    MeasurableEquiv.finTwoArrow
  let etrans : SpacetimeDim d ≃ᵐ SpacetimeDim d :=
    (Homeomorph.addRight a).toMeasurableEquiv
  eprod.trans ((MeasurableEquiv.prodCongr etrans (MeasurableEquiv.refl _)).trans eprod.symm)

@[simp] private theorem twoPointHeadBlockTranslate_measurableEquiv_apply_local
    (a : SpacetimeDim d) (z : NPointDomain d 2) :
    twoPointHeadBlockTranslate_measurableEquiv_local (d := d) a z =
      twoPointHeadBlockTranslate_local (d := d) a z := by
  ext i μ
  fin_cases i
  · simp [twoPointHeadBlockTranslate_measurableEquiv_local,
      twoPointHeadBlockTranslate_local, MeasurableEquiv.prodCongr]
  · change z 1 μ = z 1 μ
    rfl

private theorem twoPointHeadBlockTranslate_measurePreserving_local
    (a : SpacetimeDim d) :
    MeasureTheory.MeasurePreserving
      (twoPointHeadBlockTranslate_measurableEquiv_local (d := d) a)
      MeasureTheory.volume MeasureTheory.volume := by
  let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
    MeasurableEquiv.finTwoArrow
  have heprod :
      MeasureTheory.MeasurePreserving eprod
        MeasureTheory.volume MeasureTheory.volume := by
    simpa [eprod] using
      (MeasureTheory.volume_preserving_finTwoArrow (SpacetimeDim d))
  have hprod :
      MeasureTheory.MeasurePreserving
        (Prod.map (fun x : SpacetimeDim d => x + a) id)
        MeasureTheory.volume MeasureTheory.volume :=
    (translate_spacetime_measurePreserving (d := d) a).prod
      (MeasureTheory.MeasurePreserving.id
        (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
  simpa [twoPointHeadBlockTranslate_measurableEquiv_local]
    using heprod.symm.comp (hprod.comp heprod)

private def twoPointRealFlatten_local (z : NPointDomain d 2) :
    Fin ((d + 1) + (d + 1)) → ℝ :=
  Fin.addCases (z 0) (z 1)

@[simp] private theorem splitFirst_twoPointRealFlatten_local
    (z : NPointDomain d 2) :
    splitFirst (d + 1) (d + 1) (twoPointRealFlatten_local (d := d) z) = z 0 := by
  ext μ
  simp [twoPointRealFlatten_local, splitFirst]

@[simp] private theorem splitLast_twoPointRealFlatten_local
    (z : NPointDomain d 2) :
    splitLast (d + 1) (d + 1) (twoPointRealFlatten_local (d := d) z) = z 1 := by
  ext μ
  rw [splitLast, twoPointRealFlatten_local]
  simpa using (Fin.append_right (z 0) (z 1) μ)

private theorem unflatten_reindex_twoPoint_apply_local
    (F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ)
    (z : NPointDomain d 2) :
    F (twoPointRealFlatten_local (d := d) z) =
      unflattenSchwartzNPoint (d := d)
        (reindexSchwartzFin (show (d + 1) + (d + 1) = 2 * (d + 1) by ring) F) z := by
  let e : (d + 1) + (d + 1) = 2 * (d + 1) := by ring
  let H : SchwartzNPoint d 2 :=
    unflattenSchwartzNPoint (d := d) (reindexSchwartzFin e F)
  have hflatten : reindexSchwartzFin e.symm (flattenSchwartzNPoint (d := d) H) = F := by
    ext x
    change reindexSchwartzFin e.symm
        (flattenSchwartzNPoint (d := d)
          (unflattenSchwartzNPoint (d := d) (reindexSchwartzFin e F))) x = F x
    rw [reindexSchwartzFin_apply, flattenSchwartzNPoint_apply, unflattenSchwartzNPoint_apply,
      reindexSchwartzFin_apply]
    congr 1
    ext i
    simp
  have happly :=
    reindex_flattenSchwartzNPoint_two_apply (d := d) H (twoPointRealFlatten_local (d := d) z)
  rw [hflatten] at happly
  have hz :
      (fun i =>
        Fin.cases
          (splitFirst (d + 1) (d + 1) (twoPointRealFlatten_local (d := d) z))
          (fun _ => splitLast (d + 1) (d + 1) (twoPointRealFlatten_local (d := d) z)) i) = z := by
    ext i μ
    fin_cases i
    · simpa using congrArg (fun v : SpacetimeDim d => v μ)
        (splitFirst_twoPointRealFlatten_local (d := d) z)
    · change splitLast (d + 1) (d + 1) (twoPointRealFlatten_local (d := d) z) μ = z 1 μ
      simpa using congrArg (fun v : SpacetimeDim d => v μ)
        (splitLast_twoPointRealFlatten_local (d := d) z)
  calc
    F (twoPointRealFlatten_local (d := d) z)
      = H
          (fun i =>
            Fin.cases
              (splitFirst (d + 1) (d + 1) (twoPointRealFlatten_local (d := d) z))
              (fun _ => splitLast (d + 1) (d + 1) (twoPointRealFlatten_local (d := d) z)) i) := by
            simpa using happly
    _ = H z := by rw [hz]

private theorem twoPointRealFlatten_headBlockTranslate_local
    (a : SpacetimeDim d) (z : NPointDomain d 2) :
    twoPointRealFlatten_local (d := d) (twoPointHeadBlockTranslate_local (d := d) a z) =
      twoPointRealFlatten_local (d := d) z +
        zeroTailBlockShift (m := d + 1) (n := d + 1) a := by
  ext p
  cases p using Fin.addCases with
  | left μ =>
      have hfirst := congrArg (fun v : SpacetimeDim d => v μ)
        (splitFirst_zeroTailBlockShift_eq (m := d + 1) (n := d + 1) a)
      simp [twoPointRealFlatten_local, twoPointHeadBlockTranslate_local, splitFirst] at hfirst ⊢
      linarith
  | right μ =>
      have hlast := congrArg (fun v : SpacetimeDim d => v μ)
        (splitLast_zeroTailBlockShift_eq_zero (m := d + 1) (n := d + 1) a)
      have hlast0 :
          zeroTailBlockShift (m := d + 1) (n := d + 1) a (Fin.natAdd (d + 1) μ) = 0 := by
        simpa [splitLast] using hlast
      have hlast0' :
          zeroTailBlockShift (m := d + 1) (n := d + 1) a (μ.addNat (d + 1)) = 0 := by
        simpa using hlast0
      calc
        twoPointRealFlatten_local (d := d) (twoPointHeadBlockTranslate_local (d := d) a z)
            (Fin.natAdd (d + 1) μ)
          = z 1 μ := by
              simpa [twoPointRealFlatten_local, twoPointHeadBlockTranslate_local] using
                (Fin.append_right (z 0 + a) (z 1) μ)
        _ = z 1 μ + zeroTailBlockShift (m := d + 1) (n := d + 1) a (Fin.natAdd (d + 1) μ) := by
              simpa [hlast0]
        _ = (twoPointRealFlatten_local (d := d) z +
              zeroTailBlockShift (m := d + 1) (n := d + 1) a) (Fin.natAdd (d + 1) μ) := by
              simpa [twoPointRealFlatten_local, hlast0'] using
                (Fin.append_right (z 0) (z 1) μ).symm

@[simp] private theorem unflatten_reindex_translate_zeroTailBlockShift_apply_local
    (a : SpacetimeDim d)
    (F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ)
    (z : NPointDomain d 2) :
    unflattenSchwartzNPoint (d := d)
        (reindexSchwartzFin (show (d + 1) + (d + 1) = 2 * (d + 1) by ring)
          (SCV.translateSchwartz (zeroTailBlockShift (m := d + 1) (n := d + 1) a) F)) z =
      unflattenSchwartzNPoint (d := d)
        (reindexSchwartzFin (show (d + 1) + (d + 1) = 2 * (d + 1) by ring) F)
          (twoPointHeadBlockTranslate_local (d := d) a z) := by
  rw [← unflatten_reindex_twoPoint_apply_local, ← unflatten_reindex_twoPoint_apply_local]
  simp [SCV.translateSchwartz_apply, twoPointRealFlatten_headBlockTranslate_local]

/-- Pointwise head-block invariance of a two-point center/difference kernel is
enough to make the induced flattened CLM head-block translation invariant. -/
theorem twoPointFlatKernelCLM_headBlockInvariant_of_pointwise_local
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hK_inv : ∀ (a : SpacetimeDim d) (z : NPointDomain d 2),
      K (twoPointHeadBlockTranslate_local (d := d) a z) = K z) :
    IsHeadBlockTranslationInvariantSchwartzCLM
      (m := d + 1) (n := d + 1)
      (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) := by
  intro a
  ext F
  let eflat : (d + 1) + (d + 1) = 2 * (d + 1) := by ring
  let H : SchwartzNPoint d 2 :=
    unflattenSchwartzNPoint (d := d) (reindexSchwartzFin eflat F)
  let e : NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
    twoPointHeadBlockTranslate_measurableEquiv_local (d := d) a
  have hmp : MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
    twoPointHeadBlockTranslate_measurePreserving_local (d := d) a
  calc
    twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
        (SCV.translateSchwartzCLM (zeroTailBlockShift (m := d + 1) (n := d + 1) a) F)
      = ∫ z : NPointDomain d 2,
          K z *
            unflattenSchwartzNPoint (d := d)
              (reindexSchwartzFin eflat
                (SCV.translateSchwartz
                  (zeroTailBlockShift (m := d + 1) (n := d + 1) a) F)) z := by
            simp [twoPointFlatKernelCLM]
    _ = ∫ z : NPointDomain d 2,
          K z * H (twoPointHeadBlockTranslate_local (d := d) a z) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            rw [unflatten_reindex_translate_zeroTailBlockShift_apply_local]
    _ = ∫ z : NPointDomain d 2,
          (fun x : NPointDomain d 2 => K x * H x) (e z) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            simp [e, hK_inv a z, H]
    _ = ∫ z : NPointDomain d 2, K z * H z := by
            exact hmp.integral_comp'
              (f := e) (g := fun x : NPointDomain d 2 => K x * H x)
    _ = twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound F := by
            simp [twoPointFlatKernelCLM, H]

/-- The explicit shifted real-difference representative is pointwise invariant
under changing only the center slot. -/
theorem shifted_realDifferenceKernel_update_head_eq_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (a : SpacetimeDim d)
    (t : ℝ)
    (z : NPointDomain d 2) :
    k2DifferenceKernel_real_local (d := d) μ
      ((twoPointHeadBlockTranslate_local (d := d) a z) 1 + timeShiftVec d t) =
    k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) := by
  rw [twoPointHeadBlockTranslate_local_one]

/-- Once the shifted real-difference representative is packaged as a
`twoPointFlatKernelCLM`, the canonical product-shell to descended-shell
equality is formal from its head-block invariance. -/
theorem shifted_realDifferenceFlatKernelCLM_productShell_to_difference_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (t : ℝ)
    (hK_meas : AEStronglyMeasurable
      (fun z : NPointDomain d 2 =>
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t)) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ z : NPointDomain d 2 ∂volume,
      ‖k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t)‖ ≤
        C_bd * (1 + ‖z‖) ^ N)
    (χ : SchwartzSpacetime d)
    (hχ : ∫ u : SpacetimeDim d, χ u = 1)
    (g : SchwartzSpacetime d) :
    let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
      twoPointFlatKernelCLM
        (fun z : NPointDomain d 2 =>
          k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t))
        hK_meas C_bd N hC hK_bound
    T (reindexSchwartzFin
          (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointProductLift χ g)))) =
      T (reindexSchwartzFin
          (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ
                (twoPointCenterShearDescent (d := d) χ g))))) := by
  let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    twoPointFlatKernelCLM
      (fun z : NPointDomain d 2 =>
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t))
      hK_meas C_bd N hC hK_bound
  have hT :
      IsHeadBlockTranslationInvariantSchwartzCLM (m := d + 1) (n := d + 1) T := by
    apply twoPointFlatKernelCLM_headBlockInvariant_of_pointwise_local
      (d := d)
      (K := fun z : NPointDomain d 2 =>
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t))
      hK_meas C_bd N hC hK_bound
    intro a z
    exact shifted_realDifferenceKernel_update_head_eq_local (d := d) μ a t z
  simpa [T] using
    map_twoPointProductShell_eq_canonicalDifferenceLift_of_headBlockTranslationInvariant
      (d := d) T hT χ hχ g

/-- Once the explicit shifted real-difference representative is packaged as a
`twoPointFlatKernelCLM`, the reflected product shell and its canonical
same-center descended shell have identical pairings. This is the formal
shell-algebra payoff behind the remaining line-107 Input-A seam. -/
theorem shifted_realDifferenceKernel_productShell_to_same_center_of_package_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (t : ℝ)
    (hK_meas : AEStronglyMeasurable
      (fun z : NPointDomain d 2 =>
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t)) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ z : NPointDomain d 2 ∂volume,
      ‖k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t)‖ ≤
        C_bd * (1 + ‖z‖) ^ N)
    (χ : SchwartzSpacetime d)
    (hχ : ∫ u : SpacetimeDim d, χ u = 1)
    (g : SchwartzSpacetime d) :
    ∫ z : NPointDomain d 2,
      k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
        (χ (z 0) * g (z 0 + z 1)) =
    ∫ z : NPointDomain d 2,
      k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
        (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := by
  let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    twoPointFlatKernelCLM
      (fun z : NPointDomain d 2 =>
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t))
      hK_meas C_bd N hC hK_bound
  have hT :
      T (reindexSchwartzFin
            (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift χ g)))) =
        T (reindexSchwartzFin
            (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χ
                  (twoPointCenterShearDescent (d := d) χ g))))) := by
    simpa [T] using
      shifted_realDifferenceFlatKernelCLM_productShell_to_difference_local
        (d := d) μ t hK_meas C_bd N hC hK_bound χ hχ g
  calc
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * g (z 0 + z 1))
      =
    T (reindexSchwartzFin
        (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
        (flattenSchwartzNPoint (d := d)
          (twoPointCenterDiffSchwartzCLM (d := d)
            (twoPointProductLift χ g)))) := by
          symm
          simpa [T, twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply] using
            (twoPointFlatKernelCLM_apply_reindex_flatten
              (d := d)
              (K := fun z : NPointDomain d 2 =>
                k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t))
              hK_meas C_bd N hC hK_bound
              (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))
    _ =
    T (reindexSchwartzFin
        (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
        (flattenSchwartzNPoint (d := d)
          (twoPointCenterDiffSchwartzCLM (d := d)
            (twoPointDifferenceLift χ
              (twoPointCenterShearDescent (d := d) χ g))))) := hT
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := by
            simpa [T] using
              (twoPointFlatKernelCLM_apply_reindex_flatten
                (d := d)
                (K := fun z : NPointDomain d 2 =>
                  k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t))
                hK_meas C_bd N hC hK_bound
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ
                    (twoPointCenterShearDescent (d := d) χ g))))

theorem hasCompactSupport_twoPointProductLift_for_reflected_local
    (χ g : SchwartzSpacetime d)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    HasCompactSupport ((twoPointProductLift χ g : SchwartzNPoint d 2) :
      NPointDomain d 2 → ℂ) := by
  let K : Set (NPointDomain d 2) :=
    (fun p : SpacetimeDim d × SpacetimeDim d => (![p.1, p.2] : NPointDomain d 2)) ''
      (tsupport (χ : SpacetimeDim d → ℂ) ×ˢ tsupport (g : SpacetimeDim d → ℂ))
  have hcont :
      Continuous (fun p : SpacetimeDim d × SpacetimeDim d => (![p.1, p.2] : NPointDomain d 2)) := by
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa using continuous_fst
    · simpa using continuous_snd
  have hK_compact : IsCompact K := by
    simpa [K] using (hχ_compact.isCompact.prod hg_compact.isCompact).image hcont
  refine HasCompactSupport.of_support_subset_isCompact hK_compact ?_
  intro x hx
  rw [Function.mem_support] at hx
  have hmul :
      χ (x 0) * g (x 1) ≠ 0 := by
    simpa [twoPointProductLift_apply] using hx
  have hx0 : x 0 ∈ tsupport (χ : SpacetimeDim d → ℂ) :=
    subset_tsupport _ (Function.mem_support.mpr (left_ne_zero_of_mul hmul))
  have hx1 : x 1 ∈ tsupport (g : SpacetimeDim d → ℂ) :=
    subset_tsupport _ (Function.mem_support.mpr (right_ne_zero_of_mul hmul))
  refine ⟨(x 0, x 1), ⟨hx0, hx1⟩, ?_⟩
  ext i μ
  fin_cases i <;> rfl

private theorem hasCompactSupport_centerDiff_productShell_for_reflected_local
    (χ g : SchwartzSpacetime d)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    HasCompactSupport
      (fun z : NPointDomain d 2 => χ (z 0) * g (z 0 + z 1)) := by
  have hprod :=
    hasCompactSupport_twoPointProductLift_for_reflected_local
      (d := d) χ g hχ_compact hg_compact
  have hcomp :
      HasCompactSupport
        (((twoPointProductLift χ g : SchwartzNPoint d 2) : NPointDomain d 2 → ℂ) ∘
          (twoPointCenterDiffCLE d)) := by
    simpa using hprod.comp_homeomorph (twoPointCenterDiffCLE d).toHomeomorph
  simpa [Function.comp, twoPointProductLift_apply,
    twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv] using hcomp

theorem reflected_productShell_compactSupport_support_subset_positiveStrip_local
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    HasCompactSupport
      (fun z : NPointDomain d 2 =>
        φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) ∧
    Function.support
      (fun z : NPointDomain d 2 =>
        φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1))
      ⊆ {z : NPointDomain d 2 | 0 < z 1 0} := by
  refine ⟨?_, ?_⟩
  · exact hasCompactSupport_centerDiff_productShell_for_reflected_local
      (d := d) φ (reflectedSchwartzSpacetime (d := d) φ)
      hφ_compact
      (reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact)
  · intro z hz
    rw [Function.mem_support] at hz
    have hmul :
        φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1) ≠ 0 := hz
    have hz0_neg : z 0 0 < 0 := by
      exact hφ_neg <|
        subset_tsupport _ (Function.mem_support.mpr (left_ne_zero_of_mul hmul))
    have hzsum_pos : 0 < (z 0 + z 1) 0 := by
      exact
        reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg <|
          subset_tsupport _ (Function.mem_support.mpr (right_ne_zero_of_mul hmul))
    have hzsum : (z 0 + z 1) 0 = z 0 0 + z 1 0 := by simp
    rw [hzsum] at hzsum_pos
    have hz1_pos : 0 < z 1 0 := by linarith
    exact hz1_pos

/-- A globally measurable kernel with an `ae` bound is already determined on
the positive strip by its compact-support Schwartz pairings there against any
continuous representative. -/
theorem ae_eq_on_positiveStrip_of_compactSupport_schwartz_integral_eq_continuousOn_local
    (K K' : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume, ‖K x‖ ≤ C_bd)
    (hK'_cont :
      ContinuousOn K' {x : NPointDomain d 2 | 0 < x 1 0})
    (hint : ∀ f : SchwartzMap (NPointDomain d 2) ℂ,
      HasCompactSupport (f : NPointDomain d 2 → ℂ) →
      Function.support (f : NPointDomain d 2 → ℂ) ⊆
        {x : NPointDomain d 2 | 0 < x 1 0} →
      ∫ x : NPointDomain d 2, K x * f x =
        ∫ x : NPointDomain d 2, K' x * f x) :
    ∀ᵐ x : NPointDomain d 2 ∂volume, 0 < x 1 0 → K x = K' x := by
  let U : Set (NPointDomain d 2) := {x : NPointDomain d 2 | 0 < x 1 0}
  have hU : IsOpen U := by
    have hcont :
        Continuous (fun x : NPointDomain d 2 => x 1 0) := by
      exact (continuous_apply (0 : Fin (d + 1))).comp (continuous_apply (1 : Fin 2))
    simpa [U] using hcont.isOpen_preimage _ isOpen_Ioi
  have hK_li : MeasureTheory.LocallyIntegrableOn K U volume := by
    exact MeasureTheory.LocallyIntegrable.locallyIntegrableOn
      ((MeasureTheory.memLp_top_of_bound hK_meas C_bd hK_bound).locallyIntegrable le_top) U
  let diff : NPointDomain d 2 → ℂ := fun x => K x - K' x
  have hdiff_li : MeasureTheory.LocallyIntegrableOn diff U volume := by
    exact hK_li.sub (hK'_cont.locallyIntegrableOn hU.measurableSet)
  have hdiff_ae_zero :
      ∀ᵐ x : NPointDomain d 2 ∂volume, x ∈ U → diff x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hdiff_li ?_
    intro φ hφ_smooth hφ_compact hφ_tsupport
    have hφC_smooth :
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => (φ x : ℂ)) := by
      rw [contDiff_infty] at hφ_smooth
      rw [contDiff_infty]
      intro n
      exact (Complex.ofRealCLM.contDiff.of_le le_top).comp (hφ_smooth n)
    have hφC_compact : HasCompactSupport (fun x : NPointDomain d 2 => (φ x : ℂ)) :=
      hφ_compact.comp_left Complex.ofReal_zero
    let φS : SchwartzMap (NPointDomain d 2) ℂ := hφC_compact.toSchwartzMap hφC_smooth
    have hφS_compact : HasCompactSupport (φS : NPointDomain d 2 → ℂ) := by
      simpa [φS] using hφC_compact
    have hφS_eval : ∀ x, φS x = (φ x : ℂ) :=
      HasCompactSupport.toSchwartzMap_toFun hφC_compact hφC_smooth
    have hφS_tsupport :
        tsupport (φS : NPointDomain d 2 → ℂ) ⊆ U := by
      intro x hx
      have hSuppEq :
          Function.support (φS : NPointDomain d 2 → ℂ) =
            Function.support (fun y : NPointDomain d 2 => (φ y : ℂ)) := by
        ext y
        simp [hφS_eval y]
      have hx_tsupport' : x ∈ tsupport (fun y : NPointDomain d 2 => (φ y : ℂ)) := by
        simpa [tsupport, hSuppEq] using hx
      have hSuppEqR :
          Function.support (fun y : NPointDomain d 2 => (φ y : ℂ)) =
            Function.support φ := by
        ext y
        simp [Complex.ofReal_eq_zero]
      have hx_tsupportR : x ∈ tsupport φ := by
        simpa [tsupport, hSuppEqR] using hx_tsupport'
      exact hφ_tsupport hx_tsupportR
    have hφS_support :
        Function.support (φS : NPointDomain d 2 → ℂ) ⊆ U := by
      intro x hx
      exact hφS_tsupport (subset_closure hx)
    have hprod_K :
        Integrable (fun x : NPointDomain d 2 => K x * φS x) := by
      have hK_loc :
          MeasureTheory.LocallyIntegrable K := by
        exact (MeasureTheory.memLp_top_of_bound hK_meas C_bd hK_bound).locallyIntegrable le_top
      simpa [mul_comm] using
        hK_loc.integrable_smul_right_of_hasCompactSupport φS.continuous hφS_compact
    have hprod_K' :
        Integrable (fun x : NPointDomain d 2 => K' x * φS x) := by
      let S : Set (NPointDomain d 2) := tsupport (φS : NPointDomain d 2 → ℂ)
      have hS_compact : IsCompact S := by
        simpa [S, HasCompactSupport] using hφS_compact
      have hK'S : IntegrableOn K' S volume := by
        exact (hK'_cont.locallyIntegrableOn hU.measurableSet).integrableOn_compact_subset
          hφS_tsupport hS_compact
      have hprod_K'_on :
          IntegrableOn (fun x : NPointDomain d 2 => K' x * φS x) S volume := by
        simpa [smul_eq_mul, mul_comm] using
          hK'S.continuousOn_smul φS.continuous.continuousOn hS_compact
      refine hprod_K'_on.integrable_of_forall_notMem_eq_zero ?_
      intro x hx
      have hx' : x ∉ Function.support (φS : NPointDomain d 2 → ℂ) := by
        exact fun hxSupp => hx (subset_closure hxSupp)
      simp [Function.mem_support] at hx'
      simp [hx']
    have hpair := hint φS hφS_compact hφS_support
    rw [show (∫ x : NPointDomain d 2, φ x • diff x) =
        ∫ x : NPointDomain d 2, diff x * φS x by
          congr 1
          ext x
          rw [hφS_eval, Complex.real_smul, mul_comm]]
    calc
      ∫ x : NPointDomain d 2, diff x * φS x
          = ∫ x : NPointDomain d 2, K x * φS x - K' x * φS x := by
              congr with x
              ring
      _ = (∫ x : NPointDomain d 2, K x * φS x) -
            (∫ x : NPointDomain d 2, K' x * φS x) := by
              rw [integral_sub hprod_K hprod_K']
      _ = 0 := by
              rw [hpair]
              simp
  filter_upwards [hdiff_ae_zero] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

/-- Compact-support positive-strip pairing equality already transports the
actual fixed-time center/difference shell integrals to the continuous
representative. -/
theorem integral_centerDiffShell_eq_of_compactSupport_schwartz_pairing_eq_continuousOn_positiveStrip_local
    (K K' : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume, ‖K x‖ ≤ C_bd)
    (hK'_cont :
      ContinuousOn K' {x : NPointDomain d 2 | 0 < x 1 0})
    (hint : ∀ f : SchwartzMap (NPointDomain d 2) ℂ,
      HasCompactSupport (f : NPointDomain d 2 → ℂ) →
      Function.support (f : NPointDomain d 2 → ℂ) ⊆
        {x : NPointDomain d 2 | 0 < x 1 0} →
      ∫ x : NPointDomain d 2, K x * f x =
        ∫ x : NPointDomain d 2, K' x * f x)
    (χ h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    ∫ x : NPointDomain d 2, K x * (χ (x 0) * h (x 1)) =
      ∫ x : NPointDomain d 2, K' x * (χ (x 0) * h (x 1)) := by
  have hKK' :=
    ae_eq_on_positiveStrip_of_compactSupport_schwartz_integral_eq_continuousOn_local
      (d := d) K K' hK_meas C_bd hK_bound hK'_cont hint
  refine integral_congr_ae ?_
  filter_upwards [hKK'] with x hx
  by_cases hxstrip : 0 < x 1 0
  · simp [hx hxstrip]
  · have hhx : h (x 1) = 0 := by
      by_cases hzero : h (x 1) = 0
      · exact hzero
      · exfalso
        have hx_support_h : x 1 ∈ Function.support (h : SpacetimeDim d → ℂ) := by
          simpa [Function.mem_support] using hzero
        exact hxstrip (hh_pos (subset_closure hx_support_h))
    simp [hhx]

/-- Specialization of the previous transport theorem to the explicit shifted
real-difference representative on the positive strip. -/
theorem integral_centerDiffShell_eq_via_shifted_realDifference_representative_local
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume, ‖K x‖ ≤ C_bd)
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (t : ℝ)
    (hK'_cont :
      ContinuousOn
        (fun x : NPointDomain d 2 =>
          k2DifferenceKernel_real_local (d := d) μ (x 1 + timeShiftVec d t))
        {x : NPointDomain d 2 | 0 < x 1 0})
    (hint_pair : ∀ f : SchwartzMap (NPointDomain d 2) ℂ,
      HasCompactSupport (f : NPointDomain d 2 → ℂ) →
      Function.support (f : NPointDomain d 2 → ℂ) ⊆
        {x : NPointDomain d 2 | 0 < x 1 0} →
      ∫ x : NPointDomain d 2, K x * f x =
        ∫ x : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) μ (x 1 + timeShiftVec d t) * f x)
    (χ h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    ∫ x : NPointDomain d 2, K x * (χ (x 0) * h (x 1)) =
      ∫ x : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (x 1 + timeShiftVec d t) *
          (χ (x 0) * h (x 1)) := by
  exact integral_centerDiffShell_eq_of_compactSupport_schwartz_pairing_eq_continuousOn_positiveStrip_local
    (d := d)
    K
    (fun x => k2DifferenceKernel_real_local (d := d) μ (x 1 + timeShiftVec d t))
    hK_meas C_bd hK_bound hK'_cont hint_pair χ h hh_pos

/-- Direct production reduction of the Input-A `hdesc` shell equality to the
explicit shifted real-difference representative route. Once the common
fixed-time kernel agrees with that representative on compact-support tests
inside the positive strip, any fixed-center shell identity proved for the
representative transfers immediately back to the common kernel. -/
theorem integral_reflected_productShell_eq_fixed_center_difference_via_shifted_realDifference_representative_local
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume, ‖K x‖ ≤ C_bd)
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (t : ℝ)
    (hK'_cont :
      ContinuousOn
        (fun x : NPointDomain d 2 =>
          k2DifferenceKernel_real_local (d := d) μ (x 1 + timeShiftVec d t))
        {x : NPointDomain d 2 | 0 < x 1 0})
    (hint_pair : ∀ f : SchwartzMap (NPointDomain d 2) ℂ,
      HasCompactSupport (f : NPointDomain d 2 → ℂ) →
      Function.support (f : NPointDomain d 2 → ℂ) ⊆
        {x : NPointDomain d 2 | 0 < x 1 0} →
      ∫ x : NPointDomain d 2, K x * f x =
        ∫ x : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) μ (x 1 + timeShiftVec d t) * f x)
    (χ₀ φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hshifted :
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ₀ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1))) :
    ∫ z : NPointDomain d 2,
      K z * (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
    ∫ z : NPointDomain d 2,
      K z * (χ₀ (z 0) *
        (twoPointCenterShearDescent (d := d) φ
          (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) := by
  let hdesc : SchwartzSpacetime d :=
    twoPointCenterShearDescent (d := d) φ
      (reflectedSchwartzSpacetime (d := d) φ)
  have hdesc_pos :
      tsupport ((hdesc : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
        {x : SpacetimeDim d | 0 < x 0} := by
    dsimp [hdesc]
    exact twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) φ hφ_compact hφ_neg
  have hpack :
      HasCompactSupport
        (fun z : NPointDomain d 2 =>
          φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) ∧
      Function.support
        (fun z : NPointDomain d 2 =>
          φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1))
        ⊆ {z : NPointDomain d 2 | 0 < z 1 0} := by
    exact reflected_productShell_compactSupport_support_subset_positiveStrip_local
      (d := d) φ hφ_compact hφ_neg
  let fprod : SchwartzMap (NPointDomain d 2) ℂ :=
    twoPointCenterDiffSchwartzCLM (d := d)
      (twoPointProductLift φ (reflectedSchwartzSpacetime (d := d) φ))
  calc
    ∫ z : NPointDomain d 2,
        K z * (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1))
      =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) := by
            simpa [fprod, twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply] using
              hint_pair fprod hpack.1 hpack.2
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ₀ (z 0) * hdesc (z 1)) := by
            simpa [hdesc] using hshifted
    _ =
    ∫ z : NPointDomain d 2,
        K z * (χ₀ (z 0) * hdesc (z 1)) := by
          symm
          exact integral_centerDiffShell_eq_via_shifted_realDifference_representative_local
            (d := d) K hK_meas C_bd hK_bound μ t hK'_cont hint_pair χ₀ hdesc hdesc_pos

end OSReconstruction
