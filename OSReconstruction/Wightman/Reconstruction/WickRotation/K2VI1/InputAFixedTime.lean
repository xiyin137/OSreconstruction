import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAWitness
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFlatUpdate

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private theorem continuous_timeReflection_inputA_fixedTime_local :
    Continuous (timeReflection d : SpacetimeDim d → SpacetimeDim d) := by
  refine continuous_pi ?_
  intro i
  by_cases hi : i = 0
  · subst hi
    simpa [timeReflection] using (continuous_apply (0 : Fin (d + 1))).neg
  · simpa [timeReflection, hi] using continuous_apply i

private theorem exists_negative_time_gap_of_compact_negative_support_inputA_fixedTime_local
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ ε : ℝ, 0 < ε ∧
      tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < -ε} := by
  by_cases hne : (tsupport (φ : SpacetimeDim d → ℂ)).Nonempty
  · obtain ⟨x0, hx0_mem, hx0_max⟩ :=
      hφ_compact.isCompact.exists_isMaxOn hne (continuous_apply 0).continuousOn
    have hx0_neg : x0 0 < 0 := hφ_neg hx0_mem
    refine ⟨-(x0 0) / 2, by linarith, ?_⟩
    intro x hx
    have hx_le : x 0 ≤ x0 0 := hx0_max hx
    have hx_lt : x 0 < x0 0 / 2 := by
      linarith
    have hhalf : -(-(x0 0) / 2) = x0 0 / 2 := by ring
    rw [hhalf]
    exact hx_lt
  · refine ⟨1, by positivity, ?_⟩
    intro x hx
    have hempty : tsupport (φ : SpacetimeDim d → ℂ) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    simp [hempty] at hx

private theorem splitLast_castFinCLE_succ_add_symm_cons_inputA_fixedTime_local
    {m n : ℕ} (t : ℝ) (x : Fin (m + n) → ℝ) :
    splitLast (m + 1) n ((castFinCLE (Nat.succ_add m n)).symm (Fin.cons t x)) =
      splitLast m n x := by
  ext j
  have hcast :
      Fin.cast (Nat.succ_add m n) (Fin.natAdd (m + 1) j) = (Fin.natAdd m j).succ := by
    apply Fin.ext
    simp
    omega
  simp [splitLast, hcast]

private theorem splitLast_castFinCLE_zero_add_symm_inputA_fixedTime_local
    {n : ℕ} (x : Fin n → ℝ) :
    splitLast 0 n ((castFinCLE (Nat.zero_add n)).symm x) = x := by
  ext j
  simp [splitLast]

private theorem integrateHeadBlock_eq_zero_of_vanish_on_tail_inputA_fixedTime_local :
    {m n : ℕ} →
      (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) →
      (y : Fin n → ℝ) →
      (∀ x : Fin (m + n) → ℝ, splitLast m n x = y → F x = 0) →
      integrateHeadBlock (m := m) (n := n) F y = 0
  | 0, n, F, y, hF => by
      rw [integrateHeadBlock, reindexSchwartzFin_apply]
      exact hF ((castFinCLE (Nat.zero_add n)).symm y)
        (splitLast_castFinCLE_zero_add_symm_inputA_fixedTime_local y)
  | m + 1, n, F, y, hF => by
      let F' : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ :=
        reindexSchwartzFin (Nat.succ_add m n) F
      have hslice :
          ∀ x : Fin (m + n) → ℝ, splitLast m n x = y → sliceIntegral F' x = 0 := by
        intro x hx
        rw [sliceIntegral_apply, sliceIntegralRaw]
        have hzero :
            ∀ t : ℝ, F' (Fin.cons t x) = 0 := by
          intro t
          have htail :
              splitLast (m + 1) n
                  ((castFinCLE (Nat.succ_add m n)).symm (Fin.cons t x)) = y := by
            rw [splitLast_castFinCLE_succ_add_symm_cons_inputA_fixedTime_local]
            exact hx
          exact hF _ htail
        have hzero_ae :
            ∀ᵐ t : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
              F' (Fin.cons t x) = 0 := by
          exact Filter.Eventually.of_forall hzero
        simpa using MeasureTheory.integral_eq_zero_of_ae hzero_ae
      simpa [integrateHeadBlock, F'] using
        integrateHeadBlock_eq_zero_of_vanish_on_tail_inputA_fixedTime_local
          (m := m) (n := n) (F := sliceIntegral F') y hslice

private theorem twoPointCenterShearDescent_eq_zero_of_time_lt_two_mul_gap_inputA_fixedTime_local
    (χ g : SchwartzSpacetime d)
    {ε : ℝ}
    (hχ_gap : tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < -ε})
    (hg_gap : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | ε < x 0})
    {ξ : SpacetimeDim d}
    (hξ : ξ 0 < 2 * ε) :
    twoPointCenterShearDescent (d := d) χ g ξ = 0 := by
  let F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    reindexSchwartzFin (by ring)
      (flattenSchwartzNPoint (d := d)
        (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))
  have hvanish :
      ∀ x : Fin ((d + 1) + (d + 1)) → ℝ,
        splitLast (d + 1) (d + 1) x = ξ → F x = 0 := by
    intro x hx
    rw [reindex_flatten_twoPointProductShell_apply]
    let u : SpacetimeDim d := splitFirst (d + 1) (d + 1) x
    let v : SpacetimeDim d := splitLast (d + 1) (d + 1) x
    by_cases hχu : χ u = 0
    · have hχu' : χ (splitFirst (d + 1) (d + 1) x) = 0 := by
        simpa [u] using hχu
      rw [hχu']
      simp
    · by_cases hguv : g (u + v) = 0
      · have hguv' :
          g (splitFirst (d + 1) (d + 1) x + splitLast (d + 1) (d + 1) x) = 0 := by
          simpa [u, v] using hguv
        rw [hguv']
        simp
      · exfalso
        have hu_mem : u ∈ tsupport (χ : SpacetimeDim d → ℂ) :=
          subset_tsupport _ (Function.mem_support.mpr hχu)
        have huv_mem : u + v ∈ tsupport (g : SpacetimeDim d → ℂ) :=
          subset_tsupport _ (Function.mem_support.mpr hguv)
        have hu_lt : u 0 < -ε := hχ_gap hu_mem
        have huv_gt : ε < (u + v) 0 := hg_gap huv_mem
        have hv_eq : v = ξ := hx
        have huv_time : (u + v) 0 = u 0 + ξ 0 := by
          simp [v, hv_eq]
        linarith
  simpa [twoPointCenterShearDescent_eq, twoPointCenterDescent, F] using
    integrateHeadBlock_eq_zero_of_vanish_on_tail_inputA_fixedTime_local
      (m := d + 1) (n := d + 1) F ξ hvanish

private theorem reflectedSchwartzSpacetime_tsupport_gap_inputA_fixedTime_local
    (φ : SchwartzSpacetime d)
    {ε : ℝ}
    (hφ_gap : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < -ε}) :
    tsupport (reflectedSchwartzSpacetime φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | ε < x 0} := by
  intro x hx
  have hx' : timeReflection d x ∈ tsupport (φ : SpacetimeDim d → ℂ) := by
    exact tsupport_comp_subset_preimage (φ : SpacetimeDim d → ℂ)
      (f := timeReflection d)
      (continuous_timeReflection_inputA_fixedTime_local (d := d)) hx
  have hneg := hφ_gap hx'
  simpa [timeReflection] using hneg

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

/-- The descended center-shear shell attached to a compact negative-time probe
and its reflected companion is itself strictly positive-time supported. This is
the admissibility input needed to apply the fixed-time center-value theorem to
the descended VI.1 shell. -/
theorem twoPointCenterShearDescent_reflected_tsupport_pos_local
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    tsupport ((twoPointCenterShearDescent (d := d) φ
      (reflectedSchwartzSpacetime φ) : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
  obtain ⟨ε, hε_pos, hφ_gap⟩ :=
    exists_negative_time_gap_of_compact_negative_support_inputA_fixedTime_local
      (d := d) φ hφ_compact hφ_neg
  have hψ_gap :
      tsupport (reflectedSchwartzSpacetime φ : SpacetimeDim d → ℂ) ⊆
        {x : SpacetimeDim d | ε < x 0} :=
    reflectedSchwartzSpacetime_tsupport_gap_inputA_fixedTime_local
      (d := d) φ hφ_gap
  intro ξ hξ
  by_contra hnot
  have hnonpos : ξ 0 ≤ 0 := le_of_not_gt hnot
  have hUopen : IsOpen {y : SpacetimeDim d | y 0 < 2 * ε} := by
    exact (continuous_apply 0).isOpen_preimage _ isOpen_Iio
  have hξU : ξ ∈ {y : SpacetimeDim d | y 0 < 2 * ε} := by
    have htwo : 0 < 2 * ε := by positivity
    show ξ 0 < 2 * ε
    linarith
  have hnot_supp :
      ξ ∉ tsupport ((twoPointCenterShearDescent (d := d) φ
        (reflectedSchwartzSpacetime φ) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    refine Filter.mem_of_superset (hUopen.mem_nhds hξU) ?_
    intro y hy
    exact twoPointCenterShearDescent_eq_zero_of_time_lt_two_mul_gap_inputA_fixedTime_local
      (d := d) φ (reflectedSchwartzSpacetime φ) hφ_gap hψ_gap hy
  exact hnot_supp hξ

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
