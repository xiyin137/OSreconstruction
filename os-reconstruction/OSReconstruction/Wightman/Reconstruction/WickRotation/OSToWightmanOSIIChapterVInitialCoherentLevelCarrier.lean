/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialUniformTimeCarrier
import OSReconstruction.SCV.SchwartzComplete
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

theorem unitBallBumpSchwartzPi_tsupport_eq_closedBall (m : ℕ) :
    tsupport
        (((unitBallBumpSchwartzPi m : SchwartzMap (Fin m → ℝ) ℂ) :
          (Fin m → ℝ) → ℂ)) =
      Metric.closedBall (0 : Fin m → ℝ) 2 := by
  let b : ContDiffBump (0 : Fin m → ℝ) :=
    ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hfun :
      (((unitBallBumpSchwartzPi m : SchwartzMap (Fin m → ℝ) ℂ) :
        (Fin m → ℝ) → ℂ)) = f := by
    funext x
    change (hf_compact.toSchwartzMap hf_smooth) x = f x
    exact HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x
  rw [hfun]
  have hsupport : Function.support f = Function.support b := by
    ext x
    simp [Function.mem_support, f]
  rw [tsupport, hsupport]
  exact b.tsupport_eq

theorem unitBallBumpSchwartzPiRadius_tsupport_subset_closedBall_two_mul
    {m : ℕ} (R : ℝ) (hR : 0 < R) :
    tsupport
        (((unitBallBumpSchwartzPiRadius m R hR :
          SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ)) ⊆
      Metric.closedBall (0 : Fin m → ℝ) (2 * R) := by
  rw [tsupport]
  apply closure_minimal
  · intro x hx
    have hscaled_support :
        R⁻¹ • x ∈
          Function.support
            (((unitBallBumpSchwartzPi m :
              SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ)) := by
      simpa [Function.mem_support,
        unitBallBumpSchwartzPiRadius_apply] using hx
    have hscaled :
        R⁻¹ • x ∈ Metric.closedBall (0 : Fin m → ℝ) 2 := by
      rw [← unitBallBumpSchwartzPi_tsupport_eq_closedBall]
      exact subset_tsupport _ hscaled_support
    rw [Metric.mem_closedBall, dist_eq_norm] at hscaled ⊢
    simp only [sub_zero] at hscaled ⊢
    have hRinv_nonneg : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
    rw [norm_smul, Real.norm_of_nonneg hRinv_nonneg] at hscaled
    rw [inv_mul_le_iff₀ hR] at hscaled
    simpa [mul_comm] using hscaled
  · exact Metric.isClosed_closedBall

namespace InitialBaseTimePartitionData

variable {φ : SchwartzMap (Fin k → ℝ) ℂ}

theorem headCoordProjectorCLM_eq_initialPureTimeProjection
    (y : SpacetimeDim d) :
    headCoordProjectorCLM d y = initialPureTimeProjection d y := by
  ext μ
  refine Fin.cases ?_ (fun j => ?_) μ
  · simp [headCoordProjectorCLM_apply, initialPureTimeProjection,
      initialPureTimePoint, Pi.single_apply]
  · simp [headCoordProjectorCLM_apply, initialPureTimeProjection,
      initialPureTimePoint, Pi.single_apply]

/-- Pull the fixed time guard back along the pure-time projection. -/
def levelCarrierTimeMultiplier
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (i : Fin (k + 1)) :
    SpacetimeDim d → ℂ :=
  fun y =>
    (D.levelCarrierTimeGuardData a hφ_compact).guard.factors i
      (headCoordProjectorCLM d y)

theorem levelCarrierTimeMultiplier_hasTemperateGrowth
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (i : Fin (k + 1)) :
    Function.HasTemperateGrowth
      (D.levelCarrierTimeMultiplier a hφ_compact i) := by
  unfold levelCarrierTimeMultiplier
  exact
    ((D.levelCarrierTimeGuardData a hφ_compact).guard.factors i).hasTemperateGrowth.comp
      (headCoordProjectorCLM d).hasTemperateGrowth

/-- The coherent carrier factor at level `N`: fixed in time, expanding only
through the standard radial cutoff. -/
noncomputable def coherentLevelCarrierFactor
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i : Fin (k + 1)) :
    SchwartzSpacetime d :=
  SchwartzMap.smulLeftCLM ℂ
    (D.levelCarrierTimeMultiplier a hφ_compact i)
    (unitBallBumpSchwartzPiRadius (d + 1)
      (D.levelCarrierInnerNormRadius a hφ_compact N)
      (D.levelCarrierInnerNormRadius_pos a hφ_compact N))

@[simp] theorem coherentLevelCarrierFactor_apply
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i : Fin (k + 1))
    (y : SpacetimeDim d) :
    D.coherentLevelCarrierFactor a hφ_compact N i y =
      D.levelCarrierTimeMultiplier a hφ_compact i y *
        unitBallBumpSchwartzPiRadius (d + 1)
          (D.levelCarrierInnerNormRadius a hφ_compact N)
          (D.levelCarrierInnerNormRadius_pos a hφ_compact N) y := by
  simpa [coherentLevelCarrierFactor, smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply
      (D.levelCarrierTimeMultiplier_hasTemperateGrowth
        a hφ_compact i)
      (unitBallBumpSchwartzPiRadius (d + 1)
        (D.levelCarrierInnerNormRadius a hφ_compact N)
        (D.levelCarrierInnerNormRadius_pos a hφ_compact N))
      y

theorem coherentLevelCarrierFactor_one_on_carrier
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ D.levelPieceOnePointCarrierSet a N i) :
    D.coherentLevelCarrierFactor a hφ_compact N i y = 1 := by
  rw [coherentLevelCarrierFactor_apply]
  have hpure :=
    D.levelPieceOnePointCarrierSet_pureTime_mem a N i hy
  have htime :
      D.levelCarrierTimeMultiplier a hφ_compact i y = 1 := by
    unfold levelCarrierTimeMultiplier
    rw [headCoordProjectorCLM_eq_initialPureTimeProjection]
    exact
      (D.levelCarrierTimeGuardData a hφ_compact).guard_one i
        (initialPureTimeProjection d y) hpure
  have hradial :
      unitBallBumpSchwartzPiRadius (d + 1)
          (D.levelCarrierInnerNormRadius a hφ_compact N)
          (D.levelCarrierInnerNormRadius_pos a hφ_compact N) y = 1 := by
    apply unitBallBumpSchwartzPiRadius_one_of_mem_closedBall
    simpa [Metric.mem_closedBall, dist_zero_right] using
      (D.levelPieceOnePointCarrierSet_inner_norm_bound
        a hφ_compact N i hy).le
  rw [htime, hradial, one_mul]

theorem coherentLevelCarrierFactor_tsupport_subset_radial
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i : Fin (k + 1)) :
    tsupport
        ((D.coherentLevelCarrierFactor a hφ_compact N i :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
      tsupport
        (((unitBallBumpSchwartzPiRadius (d + 1)
          (D.levelCarrierInnerNormRadius a hφ_compact N)
          (D.levelCarrierInnerNormRadius_pos a hφ_compact N) :
            SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
  intro y hy
  exact
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (D.levelCarrierTimeMultiplier a hφ_compact i)
      (unitBallBumpSchwartzPiRadius (d + 1)
        (D.levelCarrierInnerNormRadius a hφ_compact N)
        (D.levelCarrierInnerNormRadius_pos a hφ_compact N))
      hy).1

theorem coherentLevelCarrierFactor_hasCompactSupport
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i : Fin (k + 1)) :
    HasCompactSupport
      ((D.coherentLevelCarrierFactor a hφ_compact N i :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_unitBallBumpSchwartzPiRadius (d + 1)
      (D.levelCarrierInnerNormRadius a hφ_compact N)
      (D.levelCarrierInnerNormRadius_pos a hφ_compact N)).isCompact ?_
  intro y hy
  exact D.coherentLevelCarrierFactor_tsupport_subset_radial
    a hφ_compact N i (subset_tsupport _ hy)

theorem coherentLevelCarrierFactor_tsupport_norm_bound
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ tsupport
      ((D.coherentLevelCarrierFactor a hφ_compact N i :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    ‖y‖ < D.levelCarrierNormRadius a hφ_compact N := by
  have hradial :=
    unitBallBumpSchwartzPiRadius_tsupport_subset_closedBall_two_mul
      (D.levelCarrierInnerNormRadius a hφ_compact N)
      (D.levelCarrierInnerNormRadius_pos a hφ_compact N)
      (D.coherentLevelCarrierFactor_tsupport_subset_radial
        a hφ_compact N i hy)
  have hbound :
      ‖y‖ ≤ 2 * D.levelCarrierInnerNormRadius a hφ_compact N := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hradial
  have hstrict :
      2 * D.levelCarrierInnerNormRadius a hφ_compact N <
        D.levelCarrierNormRadius a hφ_compact N := by
    dsimp [levelCarrierNormRadius]
    linarith
  exact hbound.trans_lt hstrict

theorem coherentLevelCarrierFactor_projection_mem_timeGuard_tsupport
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ tsupport
      ((D.coherentLevelCarrierFactor a hφ_compact N i :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    initialPureTimeProjection d y ∈
      tsupport
        (((D.levelCarrierTimeGuardData a hφ_compact).guard.factors i :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
  have htime :
      y ∈ tsupport (D.levelCarrierTimeMultiplier a hφ_compact i) :=
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (D.levelCarrierTimeMultiplier a hφ_compact i)
      (unitBallBumpSchwartzPiRadius (d + 1)
        (D.levelCarrierInnerNormRadius a hφ_compact N)
        (D.levelCarrierInnerNormRadius_pos a hφ_compact N))
      hy).2
  have hprojected :
      headCoordProjectorCLM d y ∈
        tsupport
          (((D.levelCarrierTimeGuardData a hφ_compact).guard.factors i :
            SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
    exact
      (tsupport_comp_subset_preimage
        (((D.levelCarrierTimeGuardData a hφ_compact).guard.factors i :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ)
        (headCoordProjectorCLM d).continuous htime)
  rw [headCoordProjectorCLM_eq_initialPureTimeProjection] at hprojected
  exact hprojected

/-- Explicit coherent chronological carrier factors for one fixed-time
partition piece and one spatial level. -/
noncomputable def coherentLevelCarrierFactors
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    OSIIChronologicalCompactFactors d k where
  factors := D.coherentLevelCarrierFactor a hφ_compact N
  factor_compact :=
    D.coherentLevelCarrierFactor_hasCompactSupport a hφ_compact N
  ordered_support := by
    intro i j hij y hy z hz
    have hguard :=
      (D.levelCarrierTimeGuardData a hφ_compact).guard.ordered_support
        i j hij
        (initialPureTimeProjection d y)
        (D.coherentLevelCarrierFactor_projection_mem_timeGuard_tsupport
          a hφ_compact N i hy)
        (initialPureTimeProjection d z)
        (D.coherentLevelCarrierFactor_projection_mem_timeGuard_tsupport
          a hφ_compact N j hz)
    simpa using hguard

/-- The coherent product carrier fixes every source in the corresponding
fixed-time piece exactly. -/
theorem coherentLevelCarrierFactors_fix
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap.smulLeftCLM ℂ
        (SchwartzMap.productTensor
          (D.coherentLevelCarrierFactors a hφ_compact N).factors)
        (D.levelPiece a N χ) =
      D.levelPiece a N χ := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (SchwartzMap.productTensor
      (D.coherentLevelCarrierFactors a hφ_compact N).factors
      ).hasTemperateGrowth]
  by_cases hx :
      x ∈ tsupport
        ((D.levelPiece a N χ : SchwartzNPoint d (k + 1)) :
          NPointDomain d (k + 1) → ℂ)
  · have hxcarrier :=
      D.levelPiece_support_subset_configurationCarrierSet a N χ hx
    have hproduct :
        (SchwartzMap.productTensor
          (D.coherentLevelCarrierFactors a hφ_compact N).factors :
            SchwartzNPoint d (k + 1)) x = 1 := by
      rw [SchwartzMap.productTensor_apply]
      apply Finset.prod_eq_one
      intro i _hi
      exact D.coherentLevelCarrierFactor_one_on_carrier
        a hφ_compact N i ⟨x, hxcarrier, rfl⟩
    simp [hproduct, smul_eq_mul]
  · have hzero :
        ((D.levelPiece a N χ : SchwartzNPoint d (k + 1)) :
          NPointDomain d (k + 1) → ℂ) x = 0 :=
      image_eq_zero_of_notMem_tsupport hx
    change
      (SchwartzMap.productTensor
          (D.coherentLevelCarrierFactors a hφ_compact N).factors x) *
          (((D.levelPiece a N χ : SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ) x) =
        (((D.levelPiece a N χ : SchwartzNPoint d (k + 1)) :
          NPointDomain d (k + 1) → ℂ) x)
    rw [hzero, mul_zero]

/-- Coherent carrier support remains in the fixed time slab selected before
the spatial exhaustion begins. -/
theorem coherentLevelCarrierFactors_time_bound
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ tsupport
      (((D.coherentLevelCarrierFactors a hφ_compact N).factors i :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    |y 0| < D.levelCarrierTimeRadius a hφ_compact := by
  exact
    (D.levelCarrierTimeGuardData a hφ_compact).guard_time_bound
      i (initialPureTimeProjection d y)
      (D.coherentLevelCarrierFactor_projection_mem_timeGuard_tsupport
        a hφ_compact N i hy)

/-- The coherent factors retain the fixed chronological margin of the time
guard, independently of the spatial level. -/
theorem coherentLevelCarrierFactors_time_gap
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (i j : Fin (k + 1))
    (hij : i < j)
    {y z : SpacetimeDim d}
    (hy : y ∈ tsupport
      (((D.coherentLevelCarrierFactors a hφ_compact N).factors i :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ))
    (hz : z ∈ tsupport
      (((D.coherentLevelCarrierFactors a hφ_compact N).factors j :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    D.levelCarrierTimeGap a hφ_compact ≤ z 0 - y 0 := by
  exact
    (D.levelCarrierTimeGuardData a hφ_compact).timeGap_le
      i j hij
      (initialPureTimeProjection d y)
      (D.coherentLevelCarrierFactor_projection_mem_timeGuard_tsupport
        a hφ_compact N i hy)
      (initialPureTimeProjection d z)
      (D.coherentLevelCarrierFactor_projection_mem_timeGuard_tsupport
        a hφ_compact N j hz)

set_option maxHeartbeats 800000 in
/-- Multiplying a fixed Schwartz source by the coherent carrier factor is
uniformly bounded in every Schwartz seminorm as the spatial level grows. -/
theorem coherentLevelCarrierFactor_smul_uniform_seminorm_bound
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (i : Fin (k + 1))
    (f : SchwartzSpacetime d)
    (p q : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      (SchwartzMap.seminorm ℝ p q)
        (SchwartzMap.smulLeftCLM ℂ
          (D.coherentLevelCarrierFactor a hφ_compact N i) f) ≤ M := by
  let g : SchwartzSpacetime d :=
    SchwartzMap.smulLeftCLM ℂ
      (D.levelCarrierTimeMultiplier a hφ_compact i) f
  obtain ⟨M₀, hM₀, hcompl⟩ :=
    smulLeftCLM_cutoff_compl_uniform_seminorm_bound g p q
  let M : ℝ := (SchwartzMap.seminorm ℝ p q) g + M₀
  refine ⟨M, add_nonneg (apply_nonneg _ _) hM₀, ?_⟩
  intro N
  let R := D.levelCarrierRadialNormRadius a hφ_compact N
  have hR : 0 < R :=
    D.levelCarrierRadialNormRadius_pos a hφ_compact N
  have hR_add_one :
      R + 1 = D.levelCarrierInnerNormRadius a hφ_compact N := by
    dsimp [R, levelCarrierRadialNormRadius]
    ring
  let cutoff : SchwartzSpacetime d :=
    SchwartzMap.smulLeftCLM ℂ
      (unitBallBumpSchwartzPiRadius (d + 1)
        (D.levelCarrierInnerNormRadius a hφ_compact N)
        (D.levelCarrierInnerNormRadius_pos a hφ_compact N)) g
  have hfactor_eq :
      SchwartzMap.smulLeftCLM ℂ
          (D.coherentLevelCarrierFactor a hφ_compact N i) f =
        cutoff := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (D.coherentLevelCarrierFactor a hφ_compact N i).hasTemperateGrowth]
    rw [show cutoff y =
        unitBallBumpSchwartzPiRadius (d + 1)
            (D.levelCarrierInnerNormRadius a hφ_compact N)
            (D.levelCarrierInnerNormRadius_pos a hφ_compact N) y *
          g y by
        exact SchwartzMap.smulLeftCLM_apply_apply
          (unitBallBumpSchwartzPiRadius (d + 1)
            (D.levelCarrierInnerNormRadius a hφ_compact N)
            (D.levelCarrierInnerNormRadius_pos a hφ_compact N)
            ).hasTemperateGrowth g y]
    rw [coherentLevelCarrierFactor_apply]
    rw [show g y =
        D.levelCarrierTimeMultiplier a hφ_compact i y * f y by
      exact SchwartzMap.smulLeftCLM_apply_apply
        (D.levelCarrierTimeMultiplier_hasTemperateGrowth
          a hφ_compact i) f y]
    simp only [smul_eq_mul]
    ring
  have hcompl_N :
      (SchwartzMap.seminorm ℝ p q) (g - cutoff) ≤ M₀ := by
    have h :=
      hcompl R hR
    simpa [cutoff, hR_add_one] using h
  rw [hfactor_eq]
  have hcutoff :
      cutoff = g - (g - cutoff) := by
    abel
  rw [hcutoff]
  calc
    (SchwartzMap.seminorm ℝ p q) (g - (g - cutoff)) ≤
        (SchwartzMap.seminorm ℝ p q) g +
          (SchwartzMap.seminorm ℝ p q) (g - cutoff) :=
      map_sub_le_add _ _ _
    _ ≤ (SchwartzMap.seminorm ℝ p q) g + M₀ :=
      add_le_add_right hcompl_N _
    _ = M := rfl

/-- Explicit quantitative level cover used by the fixed-time packet route.
No cutoff is selected existentially at the spatial levels. -/
noncomputable def coherentUniformTimeQuantitativeLevelCover
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    D.UniformTimeQuantitativeLevelCover hφ_compact N where
  carrier := fun a =>
    D.coherentLevelCarrierFactors a hφ_compact N
  carrier_fix := fun a χ =>
    D.coherentLevelCarrierFactors_fix a hφ_compact N χ
  carrier_time_bound := fun a i y hy =>
    D.coherentLevelCarrierFactors_time_bound
      a hφ_compact N i hy
  carrier_norm_bound := fun a i y hy =>
    D.coherentLevelCarrierFactor_tsupport_norm_bound
      a hφ_compact N i hy
  carrier_time_gap := fun a i j hij y hy z hz =>
    D.coherentLevelCarrierFactors_time_gap
      a hφ_compact N i j hij hy hz

end InitialBaseTimePartitionData
end OSIIChapterV
end OSReconstruction
