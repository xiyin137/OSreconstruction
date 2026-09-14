/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialCoherentLevelCarrier
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialFactorStabilization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketCenteredGrowth















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

namespace InitialBaseTimePartitionData

variable {φ : SchwartzMap (Fin k → ℝ) ℂ}

namespace InitialSpatialFactorPacketData

/-- Two original-OS packet choices for the same factorwise truncation level
agree on their common narrow carrier. -/
theorem narrowDistributionOfOS_eqOn_sameLevel
    {N : ℕ}
    (P Q : InitialSpatialFactorPacketData (d := d) φ N)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    Set.EqOn
      (fun ζ => P.narrowDistributionOfOS OS η hηsum ζ χ)
      (fun ζ => Q.narrowDistributionOfOS OS η hηsum ζ χ)
      (osiiNarrowTimeCarrier (k := k) η) := by
  let U := osiiNarrowTimeCarrier (k := k) η
  let F : OSIITimeGapSpace k → ℂ :=
    fun ζ =>
      P.narrowDistributionOfOS OS η hηsum ζ χ -
        Q.narrowDistributionOfOS OS η hηsum ζ χ
  have hF : DifferentiableOn ℂ F U :=
    (P.narrowDistributionOfOS_weaklyHolomorphic OS η hηsum χ).sub
      (Q.narrowDistributionOfOS_weaklyHolomorphic OS η hηsum χ)
  have hreal :
      ∀ τ ∈ section43TimeStrictPositiveRegion k,
        P.narrowDistributionOfOS OS η hηsum
            (osiiPositiveRealTimeEmbed τ) χ =
          Q.narrowDistributionOfOS OS η hηsum
            (osiiPositiveRealTimeEmbed τ) χ := by
    intro τ hτ
    rw [P.narrowDistributionOfOS_realEdge OS η hη hηsum τ hτ χ,
      Q.narrowDistributionOfOS_realEdge OS η hη hηsum τ hτ χ]
    apply congrArg (OS.S (k + 1))
    apply SetCoe.ext
    rw [P.cover.localizedTranslatedZeroSum_coe,
      Q.cover.localizedTranslatedZeroSum_coe,
      initialReducedSpatialFactorCompactSourceCLM_apply,
      translate_initialReducedSpatialFullSource_narrow
        P.slope (lt_trans zero_lt_one P.slope_gt_one) τ hτ φ
          (initialSpatialFactorTruncationCLM d k N χ),
      translate_initialReducedSpatialFullSource_narrow
        Q.slope (lt_trans zero_lt_one Q.slope_gt_one) τ hτ φ
          (initialSpatialFactorTruncationCLM d k N χ)]
  have hpositive_nonempty :
      (section43TimeStrictPositiveRegion k).Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    intro i
    simp
  have hpositive_sub :
      ∀ τ ∈ section43TimeStrictPositiveRegion k,
        SCV.realToComplex τ ∈ U := by
    intro τ hτ
    simpa [U, SCV.realToComplex, osiiPositiveRealTimeEmbed] using
      osiiPositiveRealTimeEmbed_mem_osiiNarrowTimeCarrier
        η hη τ hτ
  have hF_zero :
      ∀ τ ∈ section43TimeStrictPositiveRegion k,
        F (SCV.realToComplex τ) = 0 := by
    intro τ hτ
    simpa [F, osiiPositiveRealTimeEmbed] using
      sub_eq_zero.mpr (hreal τ hτ)
  intro ζ hζ
  have hz :
      F ζ = 0 :=
    SCV.identity_theorem_totally_real
      (isOpen_osiiNarrowTimeCarrier η)
      (isConnected_osiiNarrowTimeCarrier η hη)
      hF
      (isOpen_section43TimeStrictPositiveRegion k)
      hpositive_nonempty
      hpositive_sub
      hF_zero
      ζ hζ
  exact sub_eq_zero.mp hz

end InitialSpatialFactorPacketData

/-- A level cover of the fixed time partition is a spatial chronological
compact cover of the canonical factorwise source map. -/
noncomputable def LevelCover.toSpatialChronologicalCompactCoverData
    (D : InitialBaseTimePartitionData (d := d) φ)
    {N : ℕ}
    (C : D.LevelCover N) :
    SpatialChronologicalCompactCoverData
      (initialReducedSpatialFactorCompactSourceCLM (d := d) φ N) where
  index := D.index
  indexFintype := D.indexFintype
  piece := fun a => D.levelPiece a N
  carrier := C.carrier
  sum_eq := (D.sum_levelPiece_eq N).symm
  carrier_fix := C.carrier_fix

/-- Explicit common packet slope. The first summand gives a uniform strict
margin, the second orders every fixed-time carrier, and the third makes the
slope dominate the common carrier norm radius. -/
noncomputable def quantitativeFixedTimePacketSlope
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    ℝ :=
  2 +
    D.commonLevelCarrierAxisPairSlope hφ_compact N +
    D.commonLevelCarrierNormRadius hφ_compact N

theorem quantitativeFixedTimePacketSlope_gt_one
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    1 < D.quantitativeFixedTimePacketSlope hφ_compact N := by
  have hS :
      0 ≤ D.commonLevelCarrierAxisPairSlope hφ_compact N := by
    dsimp [commonLevelCarrierAxisPairSlope]
    exact Finset.sum_nonneg fun a _ha =>
      le_trans zero_le_one
        (D.levelCarrierAxisPairSlope_gt_one a hφ_compact N).le
  have hR :
      0 ≤ D.commonLevelCarrierNormRadius hφ_compact N := by
    dsimp [commonLevelCarrierNormRadius]
    exact Finset.sum_nonneg fun a _ha =>
      (D.levelCarrierNormRadius_pos a hφ_compact N).le
  dsimp [quantitativeFixedTimePacketSlope]
  linarith

theorem commonLevelCarrierNormRadius_le_quantitativeFixedTimePacketSlope
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    D.commonLevelCarrierNormRadius hφ_compact N ≤
      D.quantitativeFixedTimePacketSlope hφ_compact N := by
  have hS :
      0 ≤ D.commonLevelCarrierAxisPairSlope hφ_compact N := by
    dsimp [commonLevelCarrierAxisPairSlope]
    exact Finset.sum_nonneg fun a _ha =>
      le_trans zero_le_one
        (D.levelCarrierAxisPairSlope_gt_one a hφ_compact N).le
  dsimp [quantitativeFixedTimePacketSlope]
  linarith

theorem UniformTimeQuantitativeLevelCover.axisPairOrderedAt_packetSlope
    {D : InitialBaseTimePartitionData (d := d) φ}
    {hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ)}
    {N : ℕ}
    (C : D.UniformTimeQuantitativeLevelCover hφ_compact N) :
    ((C.toQuantitativeLevelCover.toLevelCover
        ).toSpatialChronologicalCompactCoverData D
      ).AxisPairOrderedAt
        (D.quantitativeFixedTimePacketSlope hφ_compact N) := by
  have hR :
      0 ≤ D.commonLevelCarrierNormRadius hφ_compact N := by
    dsimp [commonLevelCarrierNormRadius]
    exact Finset.sum_nonneg fun a _ha =>
      (D.levelCarrierNormRadius_pos a hφ_compact N).le
  have hslope :
      D.commonLevelCarrierAxisPairSlope hφ_compact N ≤
        D.quantitativeFixedTimePacketSlope hφ_compact N := by
    dsimp [quantitativeFixedTimePacketSlope]
    linarith
  intro a
  exact
    axisPairOrdered_mono (C.carrier a) hslope
      (C.axisPairOrderedAt_commonSlope a)

/-- The fixed time partition, its level-dependent carriers, and one slope
valid for all pieces at a given spatial truncation level. -/
structure FixedTimePacketData
    (D : InitialBaseTimePartitionData (d := d) φ)
    (N : ℕ) where
  levelCover : D.LevelCover N
  slope : ℝ
  slope_gt_one : 1 < slope
  ordered :
    (levelCover.toSpatialChronologicalCompactCoverData D
      ).AxisPairOrderedAt slope

/-- Fixed-time packet data retaining the quantitative carrier bounds used to
construct its level cover. -/
structure QuantitativeFixedTimePacketData
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) where
  quantitativeLevelCover : D.QuantitativeLevelCover hφ_compact N
  slope : ℝ
  slope_gt_one : 1 < slope
  ordered :
    ((quantitativeLevelCover.toLevelCover
        ).toSpatialChronologicalCompactCoverData D
      ).AxisPairOrderedAt slope
  slope_ge_normRadius :
    D.commonLevelCarrierNormRadius hφ_compact N ≤ slope
  slope_eq_quantitativeFixedTimePacketSlope :
    slope = D.quantitativeFixedTimePacketSlope hφ_compact N

/-- Forget the quantitative carrier bounds while preserving the selected
carriers and slope definitionally. -/
def QuantitativeFixedTimePacketData.toFixedTimePacketData
    {D : InitialBaseTimePartitionData (d := d) φ}
    {hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ)}
    {N : ℕ}
    (P : D.QuantitativeFixedTimePacketData hφ_compact N) :
    D.FixedTimePacketData N where
  levelCover := P.quantitativeLevelCover.toLevelCover
  slope := P.slope
  slope_gt_one := P.slope_gt_one
  ordered := P.ordered

namespace QuantitativeFixedTimePacketData

/-- Once the selected slope dominates the level carrier radius, every
axis-pair rotated support time is bounded by the fixed time-partition radius
plus one. In particular, this bound is independent of the spatial truncation
level. -/
theorem abs_rotated_factor_time_le
    {D : InitialBaseTimePartitionData (d := d) φ}
    {hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ)}
    {N : ℕ}
    (P : D.QuantitativeFixedTimePacketData hφ_compact N)
    (a : D.index)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy :
      y ∈ tsupport
        (((P.quantitativeLevelCover.carrier a).factors i :
            SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
    (b : osiiAxisPairIndex d) :
    |((osiiAxisPairRotationData P.slope b).matrix.mulVec y) 0| ≤
      D.commonLevelCarrierTimeRadius hφ_compact + 1 := by
  let H := D.commonLevelCarrierTimeRadius hφ_compact
  let r := osiiAxisPairRadius P.slope
  have hT_pos : 0 < P.slope :=
    lt_trans zero_lt_one P.slope_gt_one
  have hr_pos : 0 < r := by
    exact osiiAxisPairRadius_pos P.slope
  have hr_sq : r ^ 2 = P.slope ^ 2 + 1 := by
    dsimp [r, osiiAxisPairRadius]
    exact Real.sq_sqrt (by positivity)
  have hT_le_r : P.slope ≤ r := by
    have hr_nonneg : 0 ≤ r := hr_pos.le
    nlinarith
  have htime :
      |y 0| ≤ H := by
    exact
      (P.quantitativeLevelCover.carrier_time_bound a i y hy).le.trans
        (D.levelCarrierTimeRadius_le_common a hφ_compact)
  have hcoord :
      |y (Fin.succ b.1)| ≤ ‖y‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_le_pi_norm y (Fin.succ b.1))
  have hnorm :
      ‖y‖ ≤ P.slope := by
    exact
      (P.quantitativeLevelCover.carrier_norm_bound a i y hy).le.trans
        ((D.levelCarrierNormRadius_le_common a hφ_compact N).trans
          P.slope_ge_normRadius)
  have hspace :
      |y (Fin.succ b.1)| ≤ P.slope :=
    hcoord.trans hnorm
  have hsigned :
      |(if b.2 then y (Fin.succ b.1) else -y (Fin.succ b.1))| =
        |y (Fin.succ b.1)| := by
    split <;> simp
  have hH_nonneg : 0 ≤ H := by
    exact le_trans (D.levelCarrierTimeRadius_pos a hφ_compact).le
      (D.levelCarrierTimeRadius_le_common a hφ_compact)
  have hnum :
      |P.slope * y 0 +
          (if b.2 then y (Fin.succ b.1) else -y (Fin.succ b.1))| ≤
        (H + 1) * r := by
    calc
      |P.slope * y 0 +
          (if b.2 then y (Fin.succ b.1) else -y (Fin.succ b.1))|
          ≤ |P.slope * y 0| +
              |(if b.2 then y (Fin.succ b.1)
                else -y (Fin.succ b.1))| :=
            abs_add_le _ _
      _ = P.slope * |y 0| + |y (Fin.succ b.1)| := by
            rw [abs_mul, abs_of_pos hT_pos, hsigned]
      _ ≤ P.slope * H + P.slope := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left htime hT_pos.le)
              hspace
      _ = P.slope * (H + 1) := by ring
      _ ≤ r * (H + 1) :=
            mul_le_mul_of_nonneg_right hT_le_r (by linarith)
      _ = (H + 1) * r := by ring
  rw [(osiiAxisPairRotationData P.slope b).mulVec_time]
  have habs :
      |r⁻¹ *
          (P.slope * y 0 +
            (if b.2 then y (Fin.succ b.1) else
              -y (Fin.succ b.1)))| =
        |P.slope * y 0 +
            (if b.2 then y (Fin.succ b.1) else
              -y (Fin.succ b.1))| / r := by
    rw [abs_mul, abs_inv, abs_of_pos hr_pos]
    ring
  change
    |r⁻¹ *
        (P.slope * y 0 +
          (if b.2 then y (Fin.succ b.1) else
            -y (Fin.succ b.1)))| ≤ H + 1
  rw [habs, div_le_iff₀ hr_pos]
  exact hnum

/-- The actual center selected by every sourcewise-localized packet piece has
a fixed affine offset bound independent of the spatial cutoff level and of
the source tuple. -/
theorem sourcewiseLocalized_norm_packetCenterOffsetVector_le
    {D : InitialBaseTimePartitionData (d := d) φ}
    {hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ)}
    {N : ℕ}
    (P : D.QuantitativeFixedTimePacketData hφ_compact N)
    (a : D.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    ‖((P.quantitativeLevelCover.carrier a
        ).sourcewiseLocalizedFactors fs
      ).packetCenterOffsetVector P.slope
        ((P.quantitativeLevelCover.carrier a
          ).sourcewiseLocalizedFactors_axisPairOrdered
            P.slope (P.ordered a) fs) q‖ ≤
      2 * (D.commonLevelCarrierTimeRadius hφ_compact + 1) + 1 := by
  let B := D.commonLevelCarrierTimeRadius hφ_compact + 1
  have hB : 0 ≤ B := by
    have htime :
        0 ≤ D.commonLevelCarrierTimeRadius hφ_compact := by
      exact le_trans (D.levelCarrierTimeRadius_pos a hφ_compact).le
        (D.levelCarrierTimeRadius_le_common a hφ_compact)
    dsimp [B]
    linarith
  apply
    (P.quantitativeLevelCover.carrier a
      ).sourcewiseLocalizedFactors fs
      |>.norm_packetCenterOffsetVector_le_of_factor_bound
        P.slope
        ((P.quantitativeLevelCover.carrier a
          ).sourcewiseLocalizedFactors_axisPairOrdered
            P.slope (P.ordered a) fs)
        q B hB
  intro i y hy
  apply P.abs_rotated_factor_time_le a i _ q.2
  exact
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g :=
        (((P.quantitativeLevelCover.carrier a).factors i :
            SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))
      (f := fs i) hy).2

end QuantitativeFixedTimePacketData

/-- The fixed-time packet selection built from the explicit coherent carrier
family.  Its time guard is independent of the spatial level, while its radial
cutoff expands through the standard uniformly controlled family. -/
noncomputable def quantitativeFixedTimePacketData
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    D.QuantitativeFixedTimePacketData hφ_compact N :=
  let C := D.coherentUniformTimeQuantitativeLevelCover hφ_compact N
  {
    quantitativeLevelCover := C.toQuantitativeLevelCover
    slope := D.quantitativeFixedTimePacketSlope hφ_compact N
    slope_gt_one :=
      D.quantitativeFixedTimePacketSlope_gt_one hφ_compact N
    ordered := C.axisPairOrderedAt_packetSlope
    slope_ge_normRadius :=
      D.commonLevelCarrierNormRadius_le_quantitativeFixedTimePacketSlope
        hφ_compact N
    slope_eq_quantitativeFixedTimePacketSlope := rfl }

@[simp] theorem quantitativeFixedTimePacketData_carrier
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (a : D.index) :
    (D.quantitativeFixedTimePacketData hφ_compact N
      ).quantitativeLevelCover.carrier a =
        D.coherentLevelCarrierFactors a hφ_compact N := by
  rfl

/-- Every selected one-point carrier multiplier is uniformly bounded on a
fixed Schwartz source as the spatial exhaustion level grows. -/
theorem quantitativeFixedTimePacketData_factor_smul_uniform_seminorm_bound
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (i : Fin (k + 1))
    (f : SchwartzSpacetime d)
    (p q : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      (SchwartzMap.seminorm ℝ p q)
        (SchwartzMap.smulLeftCLM ℂ
          (((D.quantitativeFixedTimePacketData hφ_compact N
            ).quantitativeLevelCover.carrier a).factors i)
          f) ≤ M := by
  simpa using
    D.coherentLevelCarrierFactor_smul_uniform_seminorm_bound
      a hφ_compact i f p q

/-- A fixed noncomputable selection of coherent packet data at every
factorwise truncation level. -/
noncomputable def fixedTimePacketData
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    D.FixedTimePacketData N :=
  (D.quantitativeFixedTimePacketData hφ_compact N
    ).toFixedTimePacketData

namespace FixedTimePacketData

/-- Forgetting how the finite cover was constructed gives the packet-data
type used by the existing factorwise stabilization theorem. -/
noncomputable def toInitialSpatialFactorPacketData
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N) :
    InitialSpatialFactorPacketData (d := d) φ N where
  cover := P.levelCover.toSpatialChronologicalCompactCoverData D
  slope := P.slope
  slope_gt_one := P.slope_gt_one
  ordered := P.ordered

/-- The sourcewise MZ packet attached to one member of the fixed time
partition.  Its damping rate is inherited from the common slope-independent
packet rate. -/
noncomputable def pieceSourcewisePacketData
    {D : InitialBaseTimePartitionData (d := d) φ}
    {N : ℕ}
    (P : D.FixedTimePacketData N)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (a : D.index) :
    OSIIChronologicalSourcewisePacketData d (k + 1) k OS lgc :=
  (P.levelCover.carrier a).toSourcewisePacketDataAtSlope
    OS lgc P.slope P.slope_gt_one (P.ordered a)

end FixedTimePacketData

end InitialBaseTimePartitionData

end OSIIChapterV
end OSReconstruction
