import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputA
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAHeadBlockTransport

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private def commonCenterTimeSlot_local : Fin (2 * (d + 1)) :=
  finProdFinEquiv (⟨0, by omega⟩, (0 : Fin (d + 1)))

private def commonDiffTimeSlot_local : Fin (2 * (d + 1)) :=
  finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))

private def commonDiffSlot_local (μ : Fin (d + 1)) : Fin (2 * (d + 1)) :=
  finProdFinEquiv (⟨1, by omega⟩, μ)

private theorem commonCenterTimeSlot_ne_commonDiffTimeSlot_local :
    commonCenterTimeSlot_local (d := d) ≠ commonDiffTimeSlot_local (d := d) := by
  intro h
  have := congrArg Fin.val h
  simp [commonCenterTimeSlot_local, commonDiffTimeSlot_local] at this

private theorem commonCenterTimeSlot_ne_commonDiffSlot_local
    (μ : Fin (d + 1)) :
    commonCenterTimeSlot_local (d := d) ≠ commonDiffSlot_local (d := d) μ := by
  intro h
  have := congrArg Prod.fst (finProdFinEquiv.injective h)
  simp [commonCenterTimeSlot_local, commonDiffSlot_local] at this

private def commonLiftedDifferenceSliceArg_local
    (s : ℝ) (ξ : SpacetimeDim d) : Fin (2 * (d + 1)) → ℂ :=
  Function.update
    (Function.update
      (BHW.flattenCfg 2 d (fun i => wickRotatePoint (![(0 : SpacetimeDim d), ξ] i)))
      (commonDiffTimeSlot_local (d := d))
      ((BHW.flattenCfg 2 d (fun i => wickRotatePoint (![(0 : SpacetimeDim d), ξ] i)))
        (commonDiffTimeSlot_local (d := d)) + (((s + s) : ℂ) * Complex.I)))
    (commonCenterTimeSlot_local (d := d))
    Complex.I

/-- The interior slice of the common witness obtained by lifting the center-time
slot to `Im = 1` while keeping the difference slot at strip time `s+s`. -/
def commonLiftedDifferenceSliceKernel_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (s : ℝ) : SpacetimeDim d → ℂ :=
  fun ξ => G (commonLiftedDifferenceSliceArg_local (d := d) s ξ)

private theorem continuous_commonLiftedDifferenceSliceArg_local
    (s : ℝ) :
    Continuous (commonLiftedDifferenceSliceArg_local (d := d) s) := by
  refine continuous_pi ?_
  intro p
  by_cases hp0 : p = commonCenterTimeSlot_local (d := d)
  · subst hp0
    simpa [commonLiftedDifferenceSliceArg_local] using continuous_const
  · by_cases hp1 : p = commonDiffTimeSlot_local (d := d)
    · subst hp1
      have hslots :
          commonCenterTimeSlot_local (d := d) ≠ commonDiffTimeSlot_local (d := d) :=
        commonCenterTimeSlot_ne_commonDiffTimeSlot_local (d := d)
      have htime :
          Continuous fun ξ : SpacetimeDim d =>
            (Complex.I * (ξ 0 : ℂ) + (((s + s) : ℂ) * Complex.I)) := by
        exact
          continuous_const.mul
            (Complex.continuous_ofReal.comp (continuous_apply (0 : Fin (d + 1)))) |>.add
              continuous_const
      simpa [commonLiftedDifferenceSliceArg_local, commonDiffTimeSlot_local,
        commonCenterTimeSlot_local, BHW.flattenCfg, wickRotatePoint, hslots] using htime
    · have hbase :
        Continuous
          (fun ξ : SpacetimeDim d =>
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (![(0 : SpacetimeDim d), ξ] i))) p) := by
        obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
        rcases q with ⟨i, μ⟩
        fin_cases i
        · by_cases hμ : μ = 0
          · exfalso
            apply hp0
            subst hμ
            simp [commonCenterTimeSlot_local]
          · simpa [BHW.flattenCfg, wickRotatePoint, hμ] using
              (continuous_const : Continuous fun _ : SpacetimeDim d => (0 : ℂ))
        · by_cases hμ : μ = 0
          · exfalso
            apply hp1
            subst hμ
            simp [commonDiffTimeSlot_local]
          · simpa [BHW.flattenCfg, wickRotatePoint, hμ] using
              (Complex.continuous_ofReal.comp (continuous_apply μ))
      simpa [commonLiftedDifferenceSliceArg_local, hp0, hp1] using hbase

private theorem mapsTo_commonLiftedDifferenceSliceArg_tube_local
    (s : ℝ)
    {ξ : SpacetimeDim d}
    (hξ : -(s + s) < ξ 0) :
    commonLiftedDifferenceSliceArg_local (d := d) s ξ ∈
      SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d) := by
  rw [mem_tubeDomain_flatPositiveTimeDiffReal_iff]
  intro i
  fin_cases i
  · simp [commonLiftedDifferenceSliceArg_local, commonCenterTimeSlot_local]
  · simp [commonLiftedDifferenceSliceArg_local, commonDiffTimeSlot_local, BHW.flattenCfg,
      commonCenterTimeSlot_local, wickRotatePoint]
    have hξ' : 0 < ξ 0 + (s + s) := by linarith
    simpa using hξ'

/-- The lifted common slice is continuous on the strip purely from the tube
continuity of the common holomorphic witness. -/
theorem commonLiftedDifferenceSliceKernel_continuousOn_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (s : ℝ) :
    ContinuousOn
      (commonLiftedDifferenceSliceKernel_local (d := d) G s)
      {ξ : SpacetimeDim d | -(s + s) < ξ 0} := by
  rcases hG_holo with ⟨hG_cont, _⟩
  refine hG_cont.comp
    (continuous_commonLiftedDifferenceSliceArg_local (d := d) s).continuousOn ?_
  intro ξ hξ
  exact mapsTo_commonLiftedDifferenceSliceArg_tube_local (d := d) s hξ

/-- Generic difference-only shell identity for a fixed-strip kernel `K_s`. -/
theorem differenceOnlyKernel_productShell_to_same_center_of_package_local
    (K_s : SpacetimeDim d → ℂ)
    (hK_meas : AEStronglyMeasurable
      (fun z : NPointDomain d 2 => K_s (z 1)) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ z : NPointDomain d 2 ∂volume,
      ‖K_s (z 1)‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (χ : SchwartzSpacetime d)
    (hχ : ∫ u : SpacetimeDim d, χ u = 1)
    (g : SchwartzSpacetime d) :
    ∫ z : NPointDomain d 2,
      K_s (z 1) * (χ (z 0) * g (z 0 + z 1)) =
    ∫ z : NPointDomain d 2,
      K_s (z 1) * (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := by
  let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    twoPointFlatKernelCLM
      (d := d) (fun z : NPointDomain d 2 => K_s (z 1)) hK_meas C_bd N hC hK_bound
  have hT :
      IsHeadBlockTranslationInvariantSchwartzCLM (m := d + 1) (n := d + 1) T := by
    apply twoPointFlatKernelCLM_headBlockInvariant_of_pointwise_local
      (d := d)
      (K := fun z : NPointDomain d 2 => K_s (z 1))
      hK_meas C_bd N hC hK_bound
    intro a z
    simp [twoPointHeadBlockTranslate_local_one]
  have hmap :
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
      map_twoPointProductShell_eq_canonicalDifferenceLift_of_headBlockTranslationInvariant
        (d := d) T hT χ hχ g
  calc
    ∫ z : NPointDomain d 2,
        K_s (z 1) * (χ (z 0) * g (z 0 + z 1))
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
              (K := fun z : NPointDomain d 2 => K_s (z 1))
              hK_meas C_bd N hC hK_bound
              (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))
    _ =
    T (reindexSchwartzFin
        (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
        (flattenSchwartzNPoint (d := d)
          (twoPointCenterDiffSchwartzCLM (d := d)
            (twoPointDifferenceLift χ
              (twoPointCenterShearDescent (d := d) χ g))))) := hmap
    _ =
    ∫ z : NPointDomain d 2,
        K_s (z 1) *
          (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := by
            simpa [T, twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift] using
              (twoPointFlatKernelCLM_apply_reindex_flatten
                (d := d)
                (K := fun z : NPointDomain d 2 => K_s (z 1))
                hK_meas C_bd N hC hK_bound
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ (twoPointCenterShearDescent (d := d) χ g))))

/-- Measurability of the lifted common slice is automatic after extending it by
`0` off the strip. -/
theorem aestronglyMeasurable_piecewise_commonLiftedDifferenceSliceKernel_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (s : ℝ) :
    AEStronglyMeasurable
      (fun z : NPointDomain d 2 =>
        if -(s + s) < z 1 0 then
          commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)
        else 0)
      volume := by
  let S : Set (SpacetimeDim d) := {ξ : SpacetimeDim d | -(s + s) < ξ 0}
  have hS_meas : MeasurableSet S := by
    have hS_open : IsOpen S := by
      simpa [S] using
        isOpen_lt
          (continuous_const : Continuous fun _ : SpacetimeDim d => -(s + s))
          (continuous_apply (0 : Fin (d + 1)))
    exact hS_open.measurableSet
  have hK_strip :
      ContinuousOn (commonLiftedDifferenceSliceKernel_local (d := d) G s) S := by
    simpa [S] using
      commonLiftedDifferenceSliceKernel_continuousOn_local
        (d := d) G hG_holo s
  have hK_meas :
      Measurable (S.piecewise
        (commonLiftedDifferenceSliceKernel_local (d := d) G s)
        (fun _ : SpacetimeDim d => (0 : ℂ))) := by
    exact hK_strip.measurable_piecewise continuous_zero.continuousOn hS_meas
  have hcomp :
      Measurable
        (fun z : NPointDomain d 2 =>
          S.piecewise
            (commonLiftedDifferenceSliceKernel_local (d := d) G s)
            (fun _ : SpacetimeDim d => (0 : ℂ)) (z 1)) := by
    exact Measurable.comp hK_meas (continuous_apply (1 : Fin 2)).measurable
  simpa [S, Set.piecewise] using hcomp.aestronglyMeasurable

/-- Pointwise equality of the common fixed-time kernel with the lifted common
slice on the positive strip is enough to identify their reflected product-shell
pairings for any compact negative-time probe. -/
theorem commonLiftedDifferenceSlice_productShell_pairing_of_boundary_eq_local
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (s : ℝ)
    (hboundary :
      ∀ z : NPointDomain d 2, 0 < z 1 0 →
        twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z =
        commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)) :
    ∫ z : NPointDomain d 2,
      twoPointFixedTimeCenterDiffKernel_local
        (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
        (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
    ∫ z : NPointDomain d 2,
      commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
        (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) := by
  have hsupp_pos :
      Function.support
        (fun z : NPointDomain d 2 =>
          φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1))
      ⊆ {z : NPointDomain d 2 | 0 < z 1 0} := by
    exact
      (reflected_productShell_compactSupport_support_subset_positiveStrip_local
        (d := d) φ hφ_compact hφ_neg).2
  refine integral_congr_ae ?_
  filter_upwards with z
  by_cases hz :
      φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1) = 0
  · rw [hz]
    simp
  · have hz_mem :
        z ∈ Function.support
          (fun z : NPointDomain d 2 =>
            φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) := by
        exact Function.mem_support.mpr hz
    have hz_pos : 0 < z 1 0 := hsupp_pos hz_mem
    rw [hboundary z hz_pos]

/-- If the common witness `G` depends only on the full diff block in
center/difference coordinates, then the common fixed-time kernel is already the
lifted common slice pointwise. This isolates the precise structural invariance
needed behind the recent center-independence discussion. -/
theorem twoPointFixedTimeCenterDiffKernel_eq_commonLiftedDifferenceSlice_of_diffBlockDependence_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (commonDiffSlot_local (d := d) μ) = v (commonDiffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ)
    (z : NPointDomain d 2) :
    twoPointFixedTimeCenterDiffKernel_local
      (d := d) G ((((s + s) : ℂ) * Complex.I)) z =
    commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) := by
  change
    G (Function.update
      (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
      (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
      (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
        (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
        (((s + s) : ℂ) * Complex.I))) =
    G (Function.update
      (Function.update
        (BHW.flattenCfg 2 d (fun i => wickRotatePoint (![(0 : SpacetimeDim d), z 1] i)))
        (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
        ((BHW.flattenCfg 2 d (fun i => wickRotatePoint (![(0 : SpacetimeDim d), z 1] i)))
          (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + (((s + s) : ℂ) * Complex.I)))
      (finProdFinEquiv (⟨0, by omega⟩, (0 : Fin (d + 1))))
      Complex.I)
  apply hG_diff
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [commonDiffSlot_local, commonCenterTimeSlot_local, BHW.flattenCfg, wickRotatePoint,
      Function.update, commonCenterTimeSlot_ne_commonDiffSlot_local]
  · simp [twoPointFixedTimeCenterDiffKernel_local, commonLiftedDifferenceSliceKernel_local,
      commonDiffSlot_local, commonCenterTimeSlot_local, BHW.flattenCfg, wickRotatePoint,
      Function.update, hμ]

/-- Under full diff-block dependence of `G`, the reflected product-shell
pairing of the common fixed-time kernel already agrees with the pairing against
the lifted common slice. -/
theorem commonLiftedDifferenceSlice_productShell_pairing_of_diffBlockDependence_local
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (commonDiffSlot_local (d := d) μ) = v (commonDiffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ) :
    ∫ z : NPointDomain d 2,
      twoPointFixedTimeCenterDiffKernel_local
        (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
        (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
    ∫ z : NPointDomain d 2,
      commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
        (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) := by
  apply commonLiftedDifferenceSlice_productShell_pairing_of_boundary_eq_local
    (d := d) φ hφ_compact hφ_neg G s
  intro z _hz
  exact
    twoPointFixedTimeCenterDiffKernel_eq_commonLiftedDifferenceSlice_of_diffBlockDependence_local
      (d := d) G hG_diff s z

/-- Product-shell-only common-boundary route for the VI.1 diagonal-limit proof. -/
theorem exists_fixed_strip_diagonal_limit_of_common_boundary_difference_package_of_productShell_pairing_eq_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (s : ℝ)
    (hs : 0 < s)
    (K_s : SpacetimeDim d → ℂ)
    (hK_strip : ContinuousOn K_s {ξ : SpacetimeDim d | -(s + s) < ξ 0})
    (hK_meas : AEStronglyMeasurable
      (fun z : NPointDomain d 2 => K_s (z 1)) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ z : NPointDomain d 2 ∂volume,
      ‖K_s (z 1)‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (hprod_pair : ∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        K_s (z 1) *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) :
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
  have hpair :
      ∀ n,
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
            twoPointDifferenceKernel (d := d) K_s x *
              (twoPointDifferenceLift χ₀
                (twoPointCenterShearDescent (d := d) (φ_seq n)
                  (reflectedSchwartzSpacetime (d := d) (φ_seq n))) x) := by
    intro n
    let xφ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
          OSHilbertSpace OS))
    let hdesc_n : SchwartzSpacetime d :=
      twoPointCenterShearDescent (d := d) (φ_seq n)
        (reflectedSchwartzSpacetime (d := d) (φ_seq n))
    have hprod :
        osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
          ∫ z : NPointDomain d 2,
            twoPointFixedTimeCenterDiffKernel_local
              (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
              ((φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
      simpa [xφ] using
        fixedTimeCenterDiff_productShell_pairing_eq_matrixElement_of_euclid_local
          (d := d) OS lgc G hG_euclid
          (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n) (s + s) (add_pos hs hs)
    have hsame_center :
        ∫ z : NPointDomain d 2,
          K_s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          K_s (z 1) * ((φ_seq n) (z 0) * hdesc_n (z 1)) := by
      simpa [hdesc_n] using
        differenceOnlyKernel_productShell_to_same_center_of_package_local
          (d := d) K_s hK_meas C_bd N hC hK_bound (φ_seq n) (hφ_int n)
          (reflectedSchwartzSpacetime (d := d) (φ_seq n))
    have hfactor :
        ∫ z : NPointDomain d 2,
          K_s (z 1) * ((φ_seq n) (z 0) * hdesc_n (z 1)) =
        ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            twoPointDifferenceLift χ₀ hdesc_n x := by
      calc
        ∫ z : NPointDomain d 2,
            K_s (z 1) * ((φ_seq n) (z 0) * hdesc_n (z 1))
          = (∫ u : SpacetimeDim d, φ_seq n u) *
              ∫ ξ : SpacetimeDim d, K_s ξ * hdesc_n ξ := by
                simpa using
                  integral_centerDiff_differenceOnly_kernel_factorizes
                    (d := d) K_s (φ_seq n) hdesc_n
        _ = (∫ u : SpacetimeDim d, χ₀ u) *
              ∫ ξ : SpacetimeDim d, K_s ξ * hdesc_n ξ := by
                rw [hφ_int n, hχ₀]
        _ =
            ∫ x : NPointDomain d 2,
              twoPointDifferenceKernel (d := d) K_s x *
                twoPointDifferenceLift χ₀ hdesc_n x := by
              symm
              exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
                (d := d) K_s χ₀ hdesc_n
    calc
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ)
        = ∫ z : NPointDomain d 2,
            twoPointFixedTimeCenterDiffKernel_local
              (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
              ((φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hprod
      _ =
        ∫ z : NPointDomain d 2,
            K_s (z 1) *
              ((φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hprod_pair n
      _ =
        ∫ z : NPointDomain d 2,
            K_s (z 1) * ((φ_seq n) (z 0) * hdesc_n (z 1)) := hsame_center
      _ =
        ∫ x : NPointDomain d 2,
            twoPointDifferenceKernel (d := d) K_s x *
              twoPointDifferenceLift χ₀ hdesc_n x := hfactor
  exact exists_fixed_strip_diagonal_limit_of_difference_kernel_pairing_on_fixedStrip_local
    (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
    hφ_ball s hs K_s hK_strip hpair

/-- Common-witness diagonal-limit route using the lifted common slice, extended
by `0` off the strip, plus only product-shell pairing equality. -/
theorem exists_fixed_strip_diagonal_limit_of_common_lifted_difference_slice_piecewise_of_productShell_pairing_eq_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (s : ℝ)
    (hs : 0 < s)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
      ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
        C_bd * (1 + ‖z‖) ^ N)
    (hprod_pair : ∀ n,
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
          ((φ_seq n) (z 0) *
            reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))) :
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
  let S : Set (SpacetimeDim d) := {ξ : SpacetimeDim d | -(s + s) < ξ 0}
  let K_s : SpacetimeDim d → ℂ := S.piecewise
    (commonLiftedDifferenceSliceKernel_local (d := d) G s)
    (fun _ => 0)
  have hK_strip :
      ContinuousOn K_s S := by
    refine (commonLiftedDifferenceSliceKernel_continuousOn_local
      (d := d) G hG_holo s).congr ?_
    intro ξ hξ
    show S.piecewise (commonLiftedDifferenceSliceKernel_local (d := d) G s) (fun x => 0) ξ =
      commonLiftedDifferenceSliceKernel_local (d := d) G s ξ
    simpa using
      (Set.piecewise_eq_of_mem (s := S)
        (f := commonLiftedDifferenceSliceKernel_local (d := d) G s)
        (g := fun x => (0 : ℂ)) hξ)
  have hK_meas :
      AEStronglyMeasurable (fun z : NPointDomain d 2 => K_s (z 1)) volume := by
    simpa [K_s, S] using
      aestronglyMeasurable_piecewise_commonLiftedDifferenceSliceKernel_local
        (d := d) G hG_holo s
  have hK_bound_ae :
      ∀ᵐ z : NPointDomain d 2 ∂volume,
        ‖K_s (z 1)‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    refine Filter.Eventually.of_forall ?_
    intro z
    by_cases hz : -(s + s) < z 1 0
    · have hzS : z 1 ∈ S := hz
      simpa [K_s, hzS] using hK_bound z hz
    · have hnonneg : 0 ≤ C_bd * (1 + ‖z‖) ^ N := by positivity
      have hzS : z 1 ∉ S := hz
      simp [K_s, hzS, hnonneg]
  have hprod_pair' :
      ∀ n,
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
        ∫ z : NPointDomain d 2,
          K_s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
    intro n
    calc
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local
            (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1))
        =
      ∫ z : NPointDomain d 2,
          commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := hprod_pair n
      _ =
      ∫ z : NPointDomain d 2,
          K_s (z 1) *
            ((φ_seq n) (z 0) *
              reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
            refine integral_congr_ae ?_
            filter_upwards with z
            by_cases hz :
                (φ_seq n) (z 0) *
                  reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1) = 0
            · rw [hz]
              simp
            · have hz_mem :
                  z ∈ Function.support
                    (fun z : NPointDomain d 2 =>
                      (φ_seq n) (z 0) *
                        reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) := by
                  exact Function.mem_support.mpr hz
              have hz_pos :
                  0 < z 1 0 := by
                exact
                  (reflected_productShell_compactSupport_support_subset_positiveStrip_local
                    (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)).2 hz_mem
              have hzS : z 1 ∈ S := by
                change -(s + s) < z 1 0
                linarith
              simp [K_s, hzS]
  simpa [K_s, S] using
    exists_fixed_strip_diagonal_limit_of_common_boundary_difference_package_of_productShell_pairing_eq_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_ball hφ_compact
      hφ_neg G hG_euclid s hs K_s hK_strip hK_meas C_bd N hC hK_bound_ae hprod_pair'

/-- Final packaged common-`G` repair surface for the VI.1 diagonal-limit step. -/
theorem exists_fixed_strip_diagonal_limit_of_common_lifted_difference_slice_productShell_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (s : ℝ)
    (hs : 0 < s)
    (hpkg :
      ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) (C_bd : ℝ) (N : ℕ),
        IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
        (∀ (f : ZeroDiagonalSchwartz d 2),
          OS.S 2 f = ∫ x : NPointDomain d 2,
            G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
        0 < C_bd ∧
        (∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
          ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
            C_bd * (1 + ‖z‖) ^ N) ∧
        (∀ n,
          ∫ z : NPointDomain d 2,
            twoPointFixedTimeCenterDiffKernel_local
              (d := d) G ((((s + s) : ℂ) * Complex.I)) z *
              ((φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)) =
          ∫ z : NPointDomain d 2,
            commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1) *
              ((φ_seq n) (z 0) *
                reflectedSchwartzSpacetime (d := d) (φ_seq n) (z 0 + z 1)))) :
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
  rcases hpkg with ⟨G, C_bd, N, hG_holo, hG_euclid, hC, hK_bound, hprod_pair⟩
  exact
    exists_fixed_strip_diagonal_limit_of_common_lifted_difference_slice_piecewise_of_productShell_pairing_eq_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_ball hφ_compact
      hφ_neg G hG_holo hG_euclid s hs C_bd N hC hK_bound hprod_pair

/-- Exact production route under the structural hypothesis that the common
witness depends only on the full diff block. This packages the common-`G`
repair as a clean fallback route for the VI.1 diagonal-limit theorem. -/
theorem exists_fixed_strip_diagonal_limit_of_common_lifted_difference_slice_piecewise_of_diffBlockDependence_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff :
      ∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (commonDiffSlot_local (d := d) μ) = v (commonDiffSlot_local (d := d) μ)) →
        G u = G v)
    (s : ℝ)
    (hs : 0 < s)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ z : NPointDomain d 2, -(s + s) < z 1 0 →
      ‖commonLiftedDifferenceSliceKernel_local (d := d) G s (z 1)‖ ≤
        C_bd * (1 + ‖z‖) ^ N) :
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
  refine
    exists_fixed_strip_diagonal_limit_of_common_lifted_difference_slice_piecewise_of_productShell_pairing_eq_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_ball hφ_compact
      hφ_neg G hG_holo hG_euclid s hs C_bd N hC hK_bound ?_
  intro n
  exact
    commonLiftedDifferenceSlice_productShell_pairing_of_diffBlockDependence_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n) G hG_diff s

end OSReconstruction
