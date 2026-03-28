import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1InputAWitness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1InputAFlatUpdate

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem twoPointCenterDiff_toDiffFlat_wickRotate_inputA_fixedTime_local
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

omit [NeZero d] in
private theorem toDiffFlat_xiShift_eq_update_fixedTime_local
    (z : Fin 2 → Fin (d + 1) → ℂ) (t : ℂ) :
    BHW.toDiffFlat 2 d (xiShift ⟨1, by omega⟩ 0 z t) =
      Function.update
        (BHW.toDiffFlat 2 d z)
        (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
        (BHW.toDiffFlat 2 d z (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + t) := by
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  simp only [BHW.toDiffFlat, BHW.flattenCfg]
  simp only [finProdFinEquiv.symm_apply_apply]
  have hflat :
      BHW.flattenCfg 2 d (BHW.diffCoordEquiv 2 d z) (finProdFinEquiv (i, μ)) =
        BHW.diffCoordEquiv 2 d z i μ := by
    simp [BHW.flattenCfg]
  by_cases hμ : μ = 0
  ·
    subst hμ
    by_cases hi : i = ⟨1, by omega⟩
    ·
      subst hi
      simp [Function.update, BHW.diffCoordEquiv_apply, xiShift]
      ring
    ·
      have hneq :
          finProdFinEquiv (i, (0 : Fin (d + 1))) ≠
            finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))) := by
        intro h
        apply hi
        exact congrArg Prod.fst (finProdFinEquiv.injective h)
      fin_cases i
      ·
        simpa [Function.update, BHW.diffCoordEquiv_apply, xiShift] using hflat.symm
      ·
        exact False.elim (hi rfl)
  ·
    have hneq :
        finProdFinEquiv (i, μ) ≠ finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))) := by
      intro h
      exact hμ (congrArg Prod.snd (finProdFinEquiv.injective h))
    fin_cases i
    ·
      simpa [Function.update, BHW.diffCoordEquiv_apply, xiShift, hμ] using hflat.symm
    ·
      simpa [Function.update, BHW.diffCoordEquiv_apply, xiShift, hμ] using hflat.symm

/-- The fixed-time flat-update kernel on center/difference coordinates. This is
the exact kernel surface behind the `k = 2` Input A witness package. -/
def twoPointFixedTimeCenterDiffKernel_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ) : NPointDomain d 2 → ℂ :=
  fun z =>
    G (Function.update
      (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
      (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
      (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
        (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + t))

/-- The concrete `xiShift` kernel attached to `Ψ = G ∘ toDiffFlat` is exactly
the fixed-time flat-update kernel on center/difference coordinates. -/
theorem twoPointXiShiftKernel_eq_twoPointFixedTimeCenterDiffKernel_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℝ) :
    OSReconstruction.twoPointXiShiftKernel_local
        (d := d) (fun z => G (BHW.toDiffFlat 2 d z)) t =
      OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
        (d := d) G ((t : ℂ) * Complex.I) := by
  funext z
  have hbase :=
    twoPointCenterDiff_toDiffFlat_wickRotate_inputA_fixedTime_local (d := d) z
  calc
    OSReconstruction.twoPointXiShiftKernel_local
        (d := d) (fun z => G (BHW.toDiffFlat 2 d z)) t z
      = G (BHW.toDiffFlat 2 d
          (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I))) := by
              rfl
    _ = G (Function.update
          (BHW.toDiffFlat 2 d
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)))
          (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
          (BHW.toDiffFlat 2 d
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
            (t : ℂ) * Complex.I)) := by
              rw [toDiffFlat_xiShift_eq_update_fixedTime_local]
    _ = OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((t : ℂ) * Complex.I) z := by
          simp [OSReconstruction.twoPointFixedTimeCenterDiffKernel_local, hbase]

/-- The fixed-time center/difference kernel is the standard two-point fixed-time
kernel pulled back along the inverse center/difference equivalence. -/
theorem twoPointFixedTimeCenterDiffKernel_eq_twoPointFixedTimeKernel_comp_symm_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ) :
    OSReconstruction.twoPointFixedTimeCenterDiffKernel_local (d := d) G t =
      fun z => twoPointFixedTimeKernel (d := d) G t ((twoPointCenterDiffCLE d).symm z) := by
  funext z
  simp [OSReconstruction.twoPointFixedTimeCenterDiffKernel_local,
    twoPointFixedTimeKernel]

/-- Continuity of the standard fixed-time kernel transports immediately to the
center/difference fixed-time kernel. -/
theorem continuous_twoPointFixedTimeCenterDiffKernel_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hcont : Continuous (twoPointFixedTimeKernel (d := d) G t)) :
    Continuous (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local (d := d) G t) := by
  rw [twoPointFixedTimeCenterDiffKernel_eq_twoPointFixedTimeKernel_comp_symm_local
    (d := d) G t]
  exact hcont.comp (twoPointCenterDiffCLE d).symm.continuous

/-- A.e. strong measurability of the standard fixed-time kernel transports
through the center/difference equivalence. -/
theorem aestronglyMeasurable_twoPointFixedTimeCenterDiffKernel_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hK_meas : AEStronglyMeasurable (twoPointFixedTimeKernel (d := d) G t) volume) :
    AEStronglyMeasurable
      (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local (d := d) G t) volume := by
  let e : NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
    (twoPointCenterDiffCLE d).toHomeomorph.toMeasurableEquiv
  have he : MeasureTheory.MeasurePreserving e volume volume := by
    simpa [e] using twoPointCenterDiff_measurePreserving (d := d)
  rw [twoPointFixedTimeCenterDiffKernel_eq_twoPointFixedTimeKernel_comp_symm_local
    (d := d) G t]
  simpa [e] using hK_meas.comp_measurePreserving he.symm

/-- A uniform a.e. constant bound on the standard fixed-time kernel transports
unchanged to the center/difference fixed-time kernel. -/
theorem ae_norm_twoPointFixedTimeCenterDiffKernel_le_of_ae_norm_twoPointFixedTimeKernel_le_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (C_bd : ℝ)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd) :
    ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖OSReconstruction.twoPointFixedTimeCenterDiffKernel_local (d := d) G t x‖ ≤ C_bd := by
  let e : NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
    (twoPointCenterDiffCLE d).toHomeomorph.toMeasurableEquiv
  have he : MeasureTheory.MeasurePreserving e volume volume := by
    simpa [e] using twoPointCenterDiff_measurePreserving (d := d)
  rw [twoPointFixedTimeCenterDiffKernel_eq_twoPointFixedTimeKernel_comp_symm_local
    (d := d) G t]
  simpa [e] using (he.symm.quasiMeasurePreserving.tendsto_ae.eventually hK_bound)

/-- Constant-bound package for the fixed-time center/difference kernel,
transported from the standard fixed-time kernel. -/
theorem exists_constBound_package_twoPointFixedTimeCenterDiffKernel_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hcont : Continuous (twoPointFixedTimeKernel (d := d) G t))
    (hK_meas : AEStronglyMeasurable (twoPointFixedTimeKernel (d := d) G t) volume)
    (C_bd : ℝ)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd) :
    Continuous (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local (d := d) G t) ∧
      AEStronglyMeasurable
        (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local (d := d) G t) volume ∧
      (∀ᵐ x : NPointDomain d 2 ∂volume,
        ‖OSReconstruction.twoPointFixedTimeCenterDiffKernel_local (d := d) G t x‖ ≤ C_bd) := by
  refine ⟨continuous_twoPointFixedTimeCenterDiffKernel_local (d := d) G t hcont, ?_, ?_⟩
  · exact aestronglyMeasurable_twoPointFixedTimeCenterDiffKernel_local (d := d) G t hK_meas
  · exact
      ae_norm_twoPointFixedTimeCenterDiffKernel_le_of_ae_norm_twoPointFixedTimeKernel_le_local
        (d := d) G t C_bd hK_bound

/-- A constant-bound package for the standard fixed-time kernel immediately gives
the polynomial-growth package needed for the fixed-time center/difference kernel. -/
theorem exists_polyBound_package_twoPointFixedTimeCenterDiffKernel_of_constBound_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hcont : Continuous (twoPointFixedTimeKernel (d := d) G t))
    (hK_meas : AEStronglyMeasurable (twoPointFixedTimeKernel (d := d) G t) volume)
    (C_bd : ℝ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd) :
    let K₂ := OSReconstruction.twoPointFixedTimeCenterDiffKernel_local (d := d) G t
    Continuous K₂ ∧
      ∃ (C_poly : ℝ) (N : ℕ),
        ∃ hC_poly : 0 < C_poly,
          ∃ hK₂_meas : AEStronglyMeasurable K₂ volume,
            ∀ᵐ x : NPointDomain d 2 ∂volume,
              ‖K₂ x‖ ≤ C_poly * (1 + ‖x‖) ^ N := by
  dsimp
  obtain ⟨hK₂_cont, hK₂_meas, hK₂_const⟩ :=
    exists_constBound_package_twoPointFixedTimeCenterDiffKernel_local
      (d := d) G t hcont hK_meas C_bd hK_bound
  refine ⟨hK₂_cont, |C_bd| + 1, 0, by positivity, hK₂_meas, ?_⟩
  exact OSReconstruction.ae_const_bound_to_poly_bound (d := d)
    (OSReconstruction.twoPointFixedTimeCenterDiffKernel_local (d := d) G t)
    C_bd hK₂_const

/-- The fixed-time center/difference kernel is the direct positive-support
difference-shell representative of the Schwinger time-shifted test. -/
theorem schwinger_twoPointDifferenceLift_timeShift_eq_fixedTimeCenterDiffKernel_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (χ h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ (SCV.translateSchwartz (- timeShiftVec d t) h))) =
      ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((t : ℂ) * Complex.I) z *
          (χ (z 0) * h (z 1)) := by
  simpa [OSReconstruction.twoPointFixedTimeCenterDiffKernel_local] using
    schwinger_twoPointDifferenceLift_timeShift_eq_flatUpdate_of_positiveSupport_local
      (d := d) OS G hG_euclid χ h hh_pos t ht

/-- For fixed positive-support difference test `h`, the fixed-time
center/difference kernel already collapses the center slot to multiplication by
`∫ χ`. -/
theorem schwinger_twoPoint_fixedTimeCenterDiffKernel_exists_const_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ c : ℂ, ∀ χ : SchwartzSpacetime d,
      ∫ z : NPointDomain d 2,
        OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((t : ℂ) * Complex.I) z *
          (χ (z 0) * h (z 1)) =
        c * ∫ y : SpacetimeDim d, χ y := by
  simpa [OSReconstruction.twoPointFixedTimeCenterDiffKernel_local] using
    schwinger_twoPoint_flatUpdateWitness_exists_const_local
      (d := d) OS G hG_euclid h hh_pos t ht

/-- Witness-exposed fixed-time product-shell package for the Input A common
kernel route. This is the same content as the existing `xiShift` witness
package, but expressed directly through the fixed-time center/difference
kernel. -/
theorem exists_common_fixed_strip_fixedTimeCenterDiff_productShell_pairing_with_witness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
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
                reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1))) := by
  obtain ⟨G, hG_holo, hG_euclid, hprod⟩ :=
    OSReconstruction.exists_common_fixed_strip_xiShift_productShell_pairing_with_witness_local
      (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg t ht
  refine ⟨G, hG_holo, hG_euclid, ?_⟩
  intro n
  calc
    osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS)) t (0 : Fin d → ℝ)
      = ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointXiShiftKernel_local
              (d := d) (fun z => G (BHW.toDiffFlat 2 d z)) t z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1)) := hprod n
    _ = ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
              (d := d) G ((t : ℂ) * Complex.I) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (φ_seq n) (z 0 + z 1)) := by
            refine integral_congr_ae ?_
            filter_upwards with z
            rw [twoPointXiShiftKernel_eq_twoPointFixedTimeCenterDiffKernel_local
              (d := d) G t]

end OSReconstruction
