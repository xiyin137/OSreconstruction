/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketApproximation














noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- Specialize the fixed common carrier partition to an arbitrary reduced-time
test supported in that carrier. -/
noncomputable def partitionForTest
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ A.carrierData.carrier) :
    InitialBaseTimePartitionData (d := d) ψ :=
  A.partition.toInitialBaseTimePartitionData ψ hψ

/-- Every reduced-time test supported in the common carrier is compactly
supported. -/
theorem test_compact_of_tsupport_subset_carrier
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ A.carrierData.carrier) :
    HasCompactSupport (ψ : (Fin k → ℝ) → ℂ) :=
  HasCompactSupport.of_support_subset_isCompact
    A.carrierData.carrier_compact fun x hx => hψ (subset_tsupport ψ hx)

/-- Pure-time points occurring in one member of the common carrier
partition. This set is selected before choosing a shrinking time test. -/
def commonPiecePureTimeCarrierSet
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (i : Fin (k + 1)) :
    Set (SpacetimeDim d) :=
  (fun p : InitialBaseTimeSpace d k =>
      InitialBaseTimePartitionData.initialPureTimePoint d
        (initialBaseTimeConfigurationCLM d k p i 0)) ''
    (initialBaseTimeCarrierFootprint
        (d := d) A.carrierData.carrier ∩
      tsupport
        (A.partition.cutoff a : InitialBaseTimeSpace d k → ℂ))

theorem isCompact_commonPiecePureTimeCarrierSet
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (i : Fin (k + 1)) :
    IsCompact (A.commonPiecePureTimeCarrierSet a i) := by
  apply IsCompact.image
  · exact
      ((BHW.normalizedCutoffOfBump_hasCompactSupport d).isCompact.prod
          A.carrierData.carrier_compact).inter
        (A.partition.cutoff_compact a).isCompact
  · change Continuous (fun p =>
      (Fin.cons (initialBaseTimeConfigurationCLM d k p i 0)
        (0 : Fin d → ℝ) : SpacetimeDim d))
    apply continuous_pi
    intro μ
    refine Fin.cases ?_ (fun _ => ?_) μ
    · change Continuous (fun p => initialBaseTimeConfigurationCLM d k p i 0)
      exact
        (continuous_apply 0).comp
          ((continuous_apply i).comp
            (initialBaseTimeConfigurationCLM d k).continuous)
    · change Continuous (fun _ : InitialBaseTimeSpace d k => (0 : ℝ))
      exact continuous_const

theorem commonPiecePureTimeCarrierSet_subset_cell
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (i : Fin (k + 1)) :
    A.commonPiecePureTimeCarrierSet a i ⊆
      (naturalChronologicalProductNeighborhood
        (initialBaseTimeConfigurationCLM d k (A.partition.center a))
        (A.partition.center_ordered a)).cell i := by
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  have hpure := A.partition.cutoff_support a hp.2 i
  exact
    (InitialBaseTimePartitionData.mem_naturalChronologicalProductNeighborhood_cell_iff_of_time_eq
        (d := d) (k := k)
        (initialBaseTimeConfigurationCLM d k (A.partition.center a))
        (A.partition.center_ordered a) i
        (initialBaseTimeConfigurationCLM d k p i)
        (InitialBaseTimePartitionData.initialPureTimePoint d
          (initialBaseTimeConfigurationCLM d k p i 0))
        rfl).mp hpure

theorem commonPiecePureTimeCarrierSet_time_bound
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ A.commonPiecePureTimeCarrierSet a i) :
    |y 0| <
      (A.partitionAt 0).levelCarrierTimeRadius
        a (A.timeTest_compact 0) := by
  rcases hy with ⟨p, hp, rfl⟩
  let R :=
    InitialBaseTimePartitionData.schwartzCutoffRadiusData
      (A.partition.cutoff a) (A.partition.cutoff_compact a)
  have hp_bound : ‖p‖ ≤ R.radius :=
    R.bound p hp.2
  calc
    |initialBaseTimeConfigurationCLM d k p i 0| =
        ‖initialBaseTimeConfigurationCLM d k p i 0‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ‖initialBaseTimeConfigurationCLM d k p i‖ :=
      norm_le_pi_norm _ 0
    _ ≤ ‖initialBaseTimeConfigurationCLM d k p‖ :=
      norm_le_pi_norm _ i
    _ ≤ ‖initialBaseTimeConfigurationCLM d k‖ * ‖p‖ :=
      ContinuousLinearMap.le_opNorm
        (initialBaseTimeConfigurationCLM d k) p
    _ ≤ ‖initialBaseTimeConfigurationCLM d k‖ * R.radius := by
      gcongr
    _ < ‖initialBaseTimeConfigurationCLM d k‖ * R.radius + 1 := by
      linarith
    _ =
        (A.partitionAt 0).levelCarrierTimeRadius
          a (A.timeTest_compact 0) := by
      rfl

/-- One pure-time guard chosen from the common carrier partition, together
with its positive chronological gap. -/
structure CommonTimeGuardData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index) where
  guard : OSIIChronologicalCompactFactors d k
  guard_one :
    ∀ i y, y ∈ A.commonPiecePureTimeCarrierSet a i →
      guard.factors i y = 1
  guard_time_bound :
    ∀ i y,
      y ∈ tsupport
          ((guard.factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) →
        |y 0| <
          (A.partitionAt 0).levelCarrierTimeRadius
            a (A.timeTest_compact 0)
  timeGap : ℝ
  timeGap_pos : 0 < timeGap
  timeGap_le :
    ∀ i j : Fin (k + 1), i < j →
      ∀ y ∈ tsupport
          ((guard.factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ),
        ∀ z ∈ tsupport
            ((guard.factors j : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          timeGap ≤ z 0 - y 0

theorem nonempty_commonTimeGuardData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index) :
    Nonempty (A.CommonTimeGuardData a) := by
  let P :=
    naturalChronologicalProductNeighborhood
      (initialBaseTimeConfigurationCLM d k (A.partition.center a))
      (A.partition.center_ordered a)
  let K : Fin (k + 1) → Set (SpacetimeDim d) :=
    A.commonPiecePureTimeCarrierSet a
  let U : Fin (k + 1) → Set (SpacetimeDim d) := fun i =>
    P.cell i ∩
      {y |
        |y 0| <
          (A.partitionAt 0).levelCarrierTimeRadius
            a (A.timeTest_compact 0)}
  have hK_compact : ∀ i, IsCompact (K i) :=
    fun i => A.isCompact_commonPiecePureTimeCarrierSet a i
  have hU_open : ∀ i, IsOpen (U i) := by
    intro i
    exact (P.cell_open i).inter
      (isOpen_lt
        (continuous_abs.comp (continuous_apply 0))
        continuous_const)
  have hK_sub : ∀ i, K i ⊆ U i := by
    intro i y hy
    exact
      ⟨A.commonPiecePureTimeCarrierSet_subset_cell a i hy,
        A.commonPiecePureTimeCarrierSet_time_bound a i hy⟩
  have hcutoff :
      ∀ i : Fin (k + 1), ∃ χ : SchwartzSpacetime d,
        (∀ y ∈ K i, χ y = 1) ∧
        tsupport
            ((χ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          U i ∧
        HasCompactSupport
          ((χ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
    intro i
    exact
      exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open
        (m := d + 1) (hK_compact i) (hU_open i) (hK_sub i)
  choose χ hχ_one hχ_support hχ_compact using hcutoff
  let G : OSIIChronologicalCompactFactors d k :=
    { factors := χ
      factor_compact := hχ_compact
      ordered_support := by
        intro i j hij y hy z hz
        have hlt :=
          osiiOrderedTimeCell_lt
            (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
            (fun q =>
              initialBaseTimeConfigurationCLM d k
                (A.partition.center a) q 0)
            (A.partition.center_ordered a i j hij)
            (hχ_support i hy).1
            (hχ_support j hz).1
        simpa [P, naturalChronologicalProductNeighborhood,
          osiiRotatedTime] using hlt }
  obtain ⟨δ, hδ, hgap⟩ := G.exists_uniform_time_gap
  exact
    ⟨{
      guard := G
      guard_one := hχ_one
      guard_time_bound := fun i y hy => (hχ_support i hy).2
      timeGap := δ
      timeGap_pos := hδ
      timeGap_le := hgap }⟩

/-- Fixed selection of the common pure-time guard. -/
noncomputable def commonTimeGuardData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index) :
    A.CommonTimeGuardData a :=
  Classical.choice (A.nonempty_commonTimeGuardData a)

/-- Pull the common pure-time guard back along the time projection. -/
def commonTimeMultiplier
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (i : Fin (k + 1)) :
    SpacetimeDim d → ℂ :=
  fun y =>
    (A.commonTimeGuardData a).guard.factors i
      (headCoordProjectorCLM d y)

theorem commonTimeMultiplier_hasTemperateGrowth
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (i : Fin (k + 1)) :
    Function.HasTemperateGrowth (A.commonTimeMultiplier a i) := by
  convert
    ((A.commonTimeGuardData a).guard.factors i).hasTemperateGrowth.comp
      (headCoordProjectorCLM d).hasTemperateGrowth using 1
  ext y
  rfl

/-- A level carrier with a common pure-time guard and the existing expanding
radial cutoff. It is independent of the shrinking time scale. -/
noncomputable def commonCoherentLevelFactor
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (level : ℕ)
    (i : Fin (k + 1)) :
    SchwartzSpacetime d :=
  SchwartzMap.smulLeftCLM ℂ
    (A.commonTimeMultiplier a i)
    (unitBallBumpSchwartzPiRadius (d + 1)
      ((A.partitionAt 0).levelCarrierInnerNormRadius
        a (A.timeTest_compact 0) level)
      ((A.partitionAt 0).levelCarrierInnerNormRadius_pos
        a (A.timeTest_compact 0) level))

@[simp] theorem commonCoherentLevelFactor_apply
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (level : ℕ)
    (i : Fin (k + 1))
    (y : SpacetimeDim d) :
    A.commonCoherentLevelFactor a level i y =
      A.commonTimeMultiplier a i y *
        unitBallBumpSchwartzPiRadius (d + 1)
          ((A.partitionAt 0).levelCarrierInnerNormRadius
            a (A.timeTest_compact 0) level)
          ((A.partitionAt 0).levelCarrierInnerNormRadius_pos
            a (A.timeTest_compact 0) level) y := by
  simpa [commonCoherentLevelFactor, smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply
      (A.commonTimeMultiplier_hasTemperateGrowth a i)
      (unitBallBumpSchwartzPiRadius (d + 1)
        ((A.partitionAt 0).levelCarrierInnerNormRadius
          a (A.timeTest_compact 0) level)
        ((A.partitionAt 0).levelCarrierInnerNormRadius_pos
          a (A.timeTest_compact 0) level))
      y

theorem levelPieceOnePointCarrierSet_pureTime_mem_common
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (timeScale level : ℕ)
    (a : A.partition.index)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy :
      y ∈
        (A.partitionAt timeScale
          ).levelPieceOnePointCarrierSet a level i) :
    InitialBaseTimePartitionData.initialPureTimeProjection d y ∈
      A.commonPiecePureTimeCarrierSet a i := by
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with ⟨p, hp, rfl⟩
  refine ⟨p.1, ?_, ?_⟩
  · exact
      ⟨⟨hp.1.1.1,
          A.carrierData.translated_support timeScale hp.1.1.2⟩,
        hp.1.2⟩
  · ext μ
    refine Fin.cases ?_ (fun _ => ?_) μ
    · simpa using
        (initialFullConfigurationFromBaseTimeSpatialCLM_time
          (d := d) (k := k) p.1 p.2 i).symm
    · rfl

/-- The pure-time projection of every level piece specialized from the common
carrier partition lies in the fixed pure-time carrier. -/
theorem
    levelPieceOnePointCarrierSet_pureTime_mem_common_forTest
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ A.carrierData.carrier)
    (level : ℕ)
    (a : A.partition.index)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy :
      y ∈
        (A.partitionForTest ψ hψ
          ).levelPieceOnePointCarrierSet a level i) :
    InitialBaseTimePartitionData.initialPureTimeProjection d y ∈
      A.commonPiecePureTimeCarrierSet a i := by
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with ⟨p, hp, rfl⟩
  refine ⟨p.1, ?_, ?_⟩
  · exact ⟨⟨hp.1.1.1, hψ hp.1.1.2⟩, hp.1.2⟩
  · ext μ
    refine Fin.cases ?_ (fun _ => ?_) μ
    · simpa using
        (initialFullConfigurationFromBaseTimeSpatialCLM_time
          (d := d) (k := k) p.1 p.2 i).symm
    · rfl

theorem commonCoherentLevelFactor_one_on_carrier
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (timeScale level : ℕ)
    (a : A.partition.index)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy :
      y ∈
        (A.partitionAt timeScale
          ).levelPieceOnePointCarrierSet a level i) :
    A.commonCoherentLevelFactor a level i y = 1 := by
  rw [commonCoherentLevelFactor_apply]
  have hpure :=
    A.levelPieceOnePointCarrierSet_pureTime_mem_common
      timeScale level a i hy
  have htime :
      A.commonTimeMultiplier a i y = 1 := by
    unfold commonTimeMultiplier
    rw [InitialBaseTimePartitionData.headCoordProjectorCLM_eq_initialPureTimeProjection]
    exact
      (A.commonTimeGuardData a).guard_one i
        (InitialBaseTimePartitionData.initialPureTimeProjection d y)
        hpure
  have hradial :
      unitBallBumpSchwartzPiRadius (d + 1)
          ((A.partitionAt 0).levelCarrierInnerNormRadius
            a (A.timeTest_compact 0) level)
          ((A.partitionAt 0).levelCarrierInnerNormRadius_pos
            a (A.timeTest_compact 0) level) y = 1 := by
    apply unitBallBumpSchwartzPiRadius_one_of_mem_closedBall
    have hbound :=
      (A.partitionAt timeScale
        ).levelPieceOnePointCarrierSet_inner_norm_bound
          a (A.timeTest_compact timeScale) level i hy
    have hradius :
        (A.partitionAt 0).levelCarrierInnerNormRadius
            a (A.timeTest_compact 0) level =
          (A.partitionAt timeScale).levelCarrierInnerNormRadius
            a (A.timeTest_compact timeScale) level := by
      have hbase :
          ((A.partitionAt 0).levelCarrierBaseRadiusData
              a (A.timeTest_compact 0)).radius =
            ((A.partitionAt timeScale).levelCarrierBaseRadiusData
              a (A.timeTest_compact timeScale)).radius := by
        change
          (InitialBaseTimePartitionData.schwartzCutoffRadiusData
              (A.partition.cutoff a) _).radius =
            (InitialBaseTimePartitionData.schwartzCutoffRadiusData
              (A.partition.cutoff a) _).radius
        rfl
      unfold InitialBaseTimePartitionData.levelCarrierInnerNormRadius
      rw [hbase]
    rw [hradius]
    simpa [Metric.mem_closedBall, dist_zero_right] using hbound.le
  rw [htime, hradial, one_mul]

/-- The common coherent factor equals one on every level carrier obtained by
specializing the fixed partition to a test supported in the common carrier. -/
theorem commonCoherentLevelFactor_one_on_carrier_forTest
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ A.carrierData.carrier)
    (level : ℕ)
    (a : A.partition.index)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy :
      y ∈
        (A.partitionForTest ψ hψ
          ).levelPieceOnePointCarrierSet a level i) :
    A.commonCoherentLevelFactor a level i y = 1 := by
  rw [commonCoherentLevelFactor_apply]
  have hpure :=
    A.levelPieceOnePointCarrierSet_pureTime_mem_common_forTest
      ψ hψ level a i hy
  have htime :
      A.commonTimeMultiplier a i y = 1 := by
    unfold commonTimeMultiplier
    rw [InitialBaseTimePartitionData.headCoordProjectorCLM_eq_initialPureTimeProjection]
    exact
      (A.commonTimeGuardData a).guard_one i
        (InitialBaseTimePartitionData.initialPureTimeProjection d y)
        hpure
  have hradial :
      unitBallBumpSchwartzPiRadius (d + 1)
          ((A.partitionAt 0).levelCarrierInnerNormRadius
            a (A.timeTest_compact 0) level)
          ((A.partitionAt 0).levelCarrierInnerNormRadius_pos
            a (A.timeTest_compact 0) level) y = 1 := by
    apply unitBallBumpSchwartzPiRadius_one_of_mem_closedBall
    have hbound :=
      (A.partitionForTest ψ hψ
        ).levelPieceOnePointCarrierSet_inner_norm_bound
          a (A.test_compact_of_tsupport_subset_carrier ψ hψ) level i hy
    have hradius :
        (A.partitionAt 0).levelCarrierInnerNormRadius
            a (A.timeTest_compact 0) level =
          (A.partitionForTest ψ hψ).levelCarrierInnerNormRadius
            a (A.test_compact_of_tsupport_subset_carrier ψ hψ) level := by
      have hbase :
          ((A.partitionAt 0).levelCarrierBaseRadiusData
              a (A.timeTest_compact 0)).radius =
            ((A.partitionForTest ψ hψ).levelCarrierBaseRadiusData
              a (A.test_compact_of_tsupport_subset_carrier ψ hψ)).radius := by
        change
          (InitialBaseTimePartitionData.schwartzCutoffRadiusData
              (A.partition.cutoff a) _).radius =
            (InitialBaseTimePartitionData.schwartzCutoffRadiusData
              (A.partition.cutoff a) _).radius
        rfl
      unfold InitialBaseTimePartitionData.levelCarrierInnerNormRadius
      rw [hbase]
    rw [hradius]
    simpa [Metric.mem_closedBall, dist_zero_right] using hbound.le
  rw [htime, hradial, one_mul]

theorem commonCoherentLevelFactor_tsupport_subset_radial
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (level : ℕ)
    (i : Fin (k + 1)) :
    tsupport
        ((A.commonCoherentLevelFactor a level i :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
      tsupport
        (((unitBallBumpSchwartzPiRadius (d + 1)
          ((A.partitionAt 0).levelCarrierInnerNormRadius
            a (A.timeTest_compact 0) level)
          ((A.partitionAt 0).levelCarrierInnerNormRadius_pos
            a (A.timeTest_compact 0) level) :
              SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
  intro y hy
  exact
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (A.commonTimeMultiplier a i)
      (unitBallBumpSchwartzPiRadius (d + 1)
        ((A.partitionAt 0).levelCarrierInnerNormRadius
          a (A.timeTest_compact 0) level)
        ((A.partitionAt 0).levelCarrierInnerNormRadius_pos
          a (A.timeTest_compact 0) level))
      hy).1

theorem commonCoherentLevelFactor_hasCompactSupport
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (level : ℕ)
    (i : Fin (k + 1)) :
    HasCompactSupport
      ((A.commonCoherentLevelFactor a level i :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_unitBallBumpSchwartzPiRadius (d + 1)
      ((A.partitionAt 0).levelCarrierInnerNormRadius
        a (A.timeTest_compact 0) level)
      ((A.partitionAt 0).levelCarrierInnerNormRadius_pos
        a (A.timeTest_compact 0) level)).isCompact ?_
  intro y hy
  exact A.commonCoherentLevelFactor_tsupport_subset_radial
    a level i (subset_tsupport _ hy)

theorem commonCoherentLevelFactor_tsupport_norm_bound
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (level : ℕ)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ tsupport
      ((A.commonCoherentLevelFactor a level i :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    ‖y‖ <
      (A.partitionAt 0).levelCarrierNormRadius
        a (A.timeTest_compact 0) level := by
  have hradial :=
    unitBallBumpSchwartzPiRadius_tsupport_subset_closedBall_two_mul
      ((A.partitionAt 0).levelCarrierInnerNormRadius
        a (A.timeTest_compact 0) level)
      ((A.partitionAt 0).levelCarrierInnerNormRadius_pos
        a (A.timeTest_compact 0) level)
      (A.commonCoherentLevelFactor_tsupport_subset_radial
        a level i hy)
  have hbound :
      ‖y‖ ≤
        2 *
          (A.partitionAt 0).levelCarrierInnerNormRadius
            a (A.timeTest_compact 0) level := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hradial
  have hstrict :
      2 *
          (A.partitionAt 0).levelCarrierInnerNormRadius
            a (A.timeTest_compact 0) level <
        (A.partitionAt 0).levelCarrierNormRadius
          a (A.timeTest_compact 0) level := by
    dsimp [InitialBaseTimePartitionData.levelCarrierNormRadius]
    linarith
  exact hbound.trans_lt hstrict

theorem commonCoherentLevelFactor_projection_mem_guard_tsupport
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (level : ℕ)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ tsupport
      ((A.commonCoherentLevelFactor a level i :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    InitialBaseTimePartitionData.initialPureTimeProjection d y ∈
      tsupport
        (((A.commonTimeGuardData a).guard.factors i :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
  have htime :
      y ∈ tsupport (A.commonTimeMultiplier a i) :=
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (A.commonTimeMultiplier a i)
      (unitBallBumpSchwartzPiRadius (d + 1)
        ((A.partitionAt 0).levelCarrierInnerNormRadius
          a (A.timeTest_compact 0) level)
        ((A.partitionAt 0).levelCarrierInnerNormRadius_pos
          a (A.timeTest_compact 0) level))
      hy).2
  have hprojected :
      headCoordProjectorCLM d y ∈
        tsupport
          (((A.commonTimeGuardData a).guard.factors i :
            SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
    exact
      tsupport_comp_subset_preimage
        (((A.commonTimeGuardData a).guard.factors i :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ)
        (headCoordProjectorCLM d).continuous htime
  rw [InitialBaseTimePartitionData.headCoordProjectorCLM_eq_initialPureTimeProjection] at hprojected
  exact hprojected

set_option maxHeartbeats 800000 in
/-- Localizing one fixed spacetime Schwartz source by the scale-coherent
carrier is uniformly bounded in every Schwartz seminorm as the spatial level
grows. The pure-time multiplier is fixed; only the standard expanding radial
cutoff varies. -/
theorem commonCoherentLevelFactor_smul_uniform_seminorm_bound
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (i : Fin (k + 1))
    (f : SchwartzSpacetime d)
    (p q : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ level : ℕ,
      (SchwartzMap.seminorm ℝ p q)
        (SchwartzMap.smulLeftCLM ℂ
          (A.commonCoherentLevelFactor a level i) f) ≤ M := by
  let g : SchwartzSpacetime d :=
    SchwartzMap.smulLeftCLM ℂ
      (A.commonTimeMultiplier a i) f
  obtain ⟨M₀, hM₀, hcompl⟩ :=
    smulLeftCLM_cutoff_compl_uniform_seminorm_bound g p q
  let M : ℝ := (SchwartzMap.seminorm ℝ p q) g + M₀
  refine ⟨M, add_nonneg (apply_nonneg _ _) hM₀, ?_⟩
  intro level
  let D := A.partitionAt 0
  let hcompact := A.timeTest_compact 0
  let R := D.levelCarrierRadialNormRadius a hcompact level
  have hR : 0 < R :=
    D.levelCarrierRadialNormRadius_pos a hcompact level
  have hR_add_one :
      R + 1 = D.levelCarrierInnerNormRadius a hcompact level := by
    dsimp [R, InitialBaseTimePartitionData.levelCarrierRadialNormRadius]
    ring
  let cutoff : SchwartzSpacetime d :=
    SchwartzMap.smulLeftCLM ℂ
      (unitBallBumpSchwartzPiRadius (d + 1)
        (D.levelCarrierInnerNormRadius a hcompact level)
        (D.levelCarrierInnerNormRadius_pos a hcompact level)) g
  have hfactor_eq :
      SchwartzMap.smulLeftCLM ℂ
          (A.commonCoherentLevelFactor a level i) f =
        cutoff := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (A.commonCoherentLevelFactor a level i).hasTemperateGrowth]
    rw [show cutoff y =
        unitBallBumpSchwartzPiRadius (d + 1)
            (D.levelCarrierInnerNormRadius a hcompact level)
            (D.levelCarrierInnerNormRadius_pos a hcompact level) y *
          g y by
        exact SchwartzMap.smulLeftCLM_apply_apply
          (unitBallBumpSchwartzPiRadius (d + 1)
            (D.levelCarrierInnerNormRadius a hcompact level)
            (D.levelCarrierInnerNormRadius_pos a hcompact level)
            ).hasTemperateGrowth g y]
    rw [commonCoherentLevelFactor_apply]
    rw [show g y =
        A.commonTimeMultiplier a i y * f y by
      exact SchwartzMap.smulLeftCLM_apply_apply
        (A.commonTimeMultiplier_hasTemperateGrowth a i) f y]
    simp only [smul_eq_mul]
    ring
  have hcompl_level :
      (SchwartzMap.seminorm ℝ p q) (g - cutoff) ≤ M₀ := by
    have h := hcompl R hR
    simpa [cutoff, hR_add_one, D, hcompact] using h
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
      add_le_add_right hcompl_level _
    _ = M := rfl

/-- The localized coherent one-point factors form a bounded family in
spacetime Schwartz topology. -/
theorem commonCoherentLevelFactor_smul_isVonNBounded
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (i : Fin (k + 1))
    (f : SchwartzSpacetime d) :
    Bornology.IsVonNBounded ℝ
      (Set.range fun level : ℕ =>
        SchwartzMap.smulLeftCLM ℂ
          (A.commonCoherentLevelFactor a level i) f) := by
  rw [
    (schwartz_withSeminorms ℝ
      (SpacetimeDim d) ℂ).isVonNBounded_iff_seminorm_bounded]
  intro pq
  obtain ⟨M, hM, hbound⟩ :=
    A.commonCoherentLevelFactor_smul_uniform_seminorm_bound
      a i f pq.1 pq.2
  refine ⟨M + 1, by linarith, ?_⟩
  intro g hg
  rcases hg with ⟨level, rfl⟩
  exact (hbound level).trans_lt (lt_add_of_pos_right M zero_lt_one)

theorem commonCoherentLevelFactor_tsupport_time_bound
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (level : ℕ)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ tsupport
      ((A.commonCoherentLevelFactor a level i :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    |y 0| <
      (A.partitionAt 0).levelCarrierTimeRadius
        a (A.timeTest_compact 0) := by
  exact
    (A.commonTimeGuardData a).guard_time_bound
      i (InitialBaseTimePartitionData.initialPureTimeProjection d y)
      (A.commonCoherentLevelFactor_projection_mem_guard_tsupport
        a level i hy)

/-- Common chronological factors at one spatial level. -/
noncomputable def commonCoherentLevelFactors
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (level : ℕ) :
    OSIIChronologicalCompactFactors d k where
  factors := A.commonCoherentLevelFactor a level
  factor_compact :=
    A.commonCoherentLevelFactor_hasCompactSupport a level
  ordered_support := by
    intro i j hij y hy z hz
    have hguard :=
      (A.commonTimeGuardData a).guard.ordered_support
        i j hij
        (InitialBaseTimePartitionData.initialPureTimeProjection d y)
        (A.commonCoherentLevelFactor_projection_mem_guard_tsupport
          a level i hy)
        (InitialBaseTimePartitionData.initialPureTimeProjection d z)
        (A.commonCoherentLevelFactor_projection_mem_guard_tsupport
          a level j hz)
    simpa using hguard

theorem commonCoherentLevelFactors_fix
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (timeScale level : ℕ)
    (a : A.partition.index)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap.smulLeftCLM ℂ
        (SchwartzMap.productTensor
          (A.commonCoherentLevelFactors a level).factors)
        ((A.partitionAt timeScale).levelPiece a level χ) =
      (A.partitionAt timeScale).levelPiece a level χ := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (SchwartzMap.productTensor
      (A.commonCoherentLevelFactors a level).factors
      ).hasTemperateGrowth]
  by_cases hx :
      x ∈ tsupport
        ((((A.partitionAt timeScale).levelPiece a level χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ))
  · have hxcarrier :=
      (A.partitionAt timeScale
        ).levelPiece_support_subset_configurationCarrierSet
          a level χ hx
    have hproduct :
        (SchwartzMap.productTensor
          (A.commonCoherentLevelFactors a level).factors :
            SchwartzNPoint d (k + 1)) x = 1 := by
      rw [SchwartzMap.productTensor_apply]
      apply Finset.prod_eq_one
      intro i _hi
      exact A.commonCoherentLevelFactor_one_on_carrier
        timeScale level a i ⟨x, hxcarrier, rfl⟩
    simp [hproduct, smul_eq_mul]
  · have hzero :
        ((((A.partitionAt timeScale).levelPiece a level χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ) x) = 0 :=
      image_eq_zero_of_notMem_tsupport hx
    change
      (SchwartzMap.productTensor
          (A.commonCoherentLevelFactors a level).factors x) *
          ((((A.partitionAt timeScale).levelPiece a level χ :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ) x) =
        ((((A.partitionAt timeScale).levelPiece a level χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ) x)
    rw [hzero, mul_zero]

/-- The common carrier factors fix every level piece obtained from an
arbitrary test supported in the common time carrier. -/
theorem commonCoherentLevelFactors_fix_forTest
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ A.carrierData.carrier)
    (level : ℕ)
    (a : A.partition.index)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap.smulLeftCLM ℂ
        (SchwartzMap.productTensor
          (A.commonCoherentLevelFactors a level).factors)
        ((A.partitionForTest ψ hψ).levelPiece a level χ) =
      (A.partitionForTest ψ hψ).levelPiece a level χ := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (SchwartzMap.productTensor
      (A.commonCoherentLevelFactors a level).factors
      ).hasTemperateGrowth]
  by_cases hx :
      x ∈ tsupport
        ((((A.partitionForTest ψ hψ).levelPiece a level χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ))
  · have hxcarrier :=
      (A.partitionForTest ψ hψ
        ).levelPiece_support_subset_configurationCarrierSet
          a level χ hx
    have hproduct :
        (SchwartzMap.productTensor
          (A.commonCoherentLevelFactors a level).factors :
            SchwartzNPoint d (k + 1)) x = 1 := by
      rw [SchwartzMap.productTensor_apply]
      apply Finset.prod_eq_one
      intro i _hi
      exact A.commonCoherentLevelFactor_one_on_carrier_forTest
        ψ hψ level a i ⟨x, hxcarrier, rfl⟩
    simp [hproduct, smul_eq_mul]
  · have hzero :
        ((((A.partitionForTest ψ hψ).levelPiece a level χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ) x) = 0 :=
      image_eq_zero_of_notMem_tsupport hx
    change
      (SchwartzMap.productTensor
          (A.commonCoherentLevelFactors a level).factors x) *
          ((((A.partitionForTest ψ hψ).levelPiece a level χ :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ) x) =
        ((((A.partitionForTest ψ hψ).levelPiece a level χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ) x)
    rw [hzero, mul_zero]

/-- The common carrier family, viewed as a level cover for any shrinking
time scale. -/
noncomputable def commonCoherentLevelCover
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (timeScale level : ℕ) :
    (A.partitionAt timeScale).LevelCover level where
  carrier := fun a => A.commonCoherentLevelFactors a level
  carrier_fix := fun a χ =>
    A.commonCoherentLevelFactors_fix timeScale level a χ

/-- The common carrier family as a level cover for an arbitrary test
supported in the fixed time carrier. -/
noncomputable def commonCoherentLevelCoverForTest
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ A.carrierData.carrier)
    (level : ℕ) :
    (A.partitionForTest ψ hψ).LevelCover level where
  carrier := fun a => A.commonCoherentLevelFactors a level
  carrier_fix := fun a χ =>
    A.commonCoherentLevelFactors_fix_forTest ψ hψ level a χ

/-- One slope and ordering proof selected from the common level carrier. -/
structure CommonPacketSlopeData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (level : ℕ) where
  slope : ℝ
  slope_gt_one : 1 < slope
  slope_ge_normRadius :
    (A.partitionAt 0).commonLevelCarrierNormRadius
        (A.timeTest_compact 0) level ≤ slope
  ordered :
    ((A.commonCoherentLevelCover 0 level
      ).toSpatialChronologicalCompactCoverData (A.partitionAt 0)
      ).AxisPairOrderedAt slope

theorem nonempty_commonPacketSlopeData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (level : ℕ) :
    Nonempty (A.CommonPacketSlopeData level) := by
  obtain ⟨T, hT, hordered⟩ :=
    ((A.commonCoherentLevelCover 0 level
      ).toSpatialChronologicalCompactCoverData (A.partitionAt 0)
      ).exists_common_axisPairSlope
  let R :=
    (A.partitionAt 0).commonLevelCarrierNormRadius
      (A.timeTest_compact 0) level
  have hR : 0 ≤ R := by
    dsimp [R, InitialBaseTimePartitionData.commonLevelCarrierNormRadius]
    exact Finset.sum_nonneg fun a _ha =>
      ((A.partitionAt 0).levelCarrierNormRadius_pos
        a (A.timeTest_compact 0) level).le
  let S := T + R + 1
  exact
    ⟨{
      slope := S
      slope_gt_one := by
        dsimp [S]
        linarith
      slope_ge_normRadius := by
        dsimp [S, R]
        linarith
      ordered := by
        intro a
        exact
          axisPairOrdered_mono
            (A.commonCoherentLevelFactors a level)
            (show T ≤ S by
              dsimp [S]
              linarith)
            (hordered a) }⟩

noncomputable def commonPacketSlopeData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (level : ℕ) :
    A.CommonPacketSlopeData level :=
  Classical.choice (A.nonempty_commonPacketSlopeData level)

theorem commonCoherentLevelCover_ordered
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (timeScale level : ℕ) :
    ((A.commonCoherentLevelCover timeScale level
      ).toSpatialChronologicalCompactCoverData (A.partitionAt timeScale)
      ).AxisPairOrderedAt (A.commonPacketSlopeData level).slope := by
  intro a
  exact (A.commonPacketSlopeData level).ordered a

/-- The common carrier remains ordered after specializing the fixed partition
to any test supported in the common time carrier. -/
theorem commonCoherentLevelCoverForTest_ordered
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ A.carrierData.carrier)
    (level : ℕ) :
    ((A.commonCoherentLevelCoverForTest ψ hψ level
      ).toSpatialChronologicalCompactCoverData
        (A.partitionForTest ψ hψ)
      ).AxisPairOrderedAt (A.commonPacketSlopeData level).slope := by
  intro a
  exact (A.commonPacketSlopeData level).ordered a

/-- A packet selection whose carrier factors and slope are literally shared
by all shrinking time scales. -/
noncomputable def commonPacketAt
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (timeScale level : ℕ) :
    (A.partitionAt timeScale).FixedTimePacketData level where
  levelCover := A.commonCoherentLevelCover timeScale level
  slope := (A.commonPacketSlopeData level).slope
  slope_gt_one := (A.commonPacketSlopeData level).slope_gt_one
  ordered := A.commonCoherentLevelCover_ordered timeScale level

/-- The common packet specialized to an arbitrary test supported in the fixed
time carrier. -/
noncomputable def commonPacketForTest
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ A.carrierData.carrier)
    (level : ℕ) :
    (A.partitionForTest ψ hψ).FixedTimePacketData level where
  levelCover := A.commonCoherentLevelCoverForTest ψ hψ level
  slope := (A.commonPacketSlopeData level).slope
  slope_gt_one := (A.commonPacketSlopeData level).slope_gt_one
  ordered := A.commonCoherentLevelCoverForTest_ordered ψ hψ level

/-- Every axis-pair rotated support time of the coherent packet is bounded by
the common pure-time radius plus one, independently of both packet indices. -/
theorem commonPacketAt_abs_rotated_factor_time_le
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (timeScale level : ℕ)
    (a : A.partition.index)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy :
      y ∈ tsupport
        ((((A.commonPacketAt timeScale level).levelCover.carrier a
          ).factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ))
    (b : osiiAxisPairIndex d) :
    |((osiiAxisPairRotationData
        (A.commonPacketAt timeScale level).slope b).matrix.mulVec y) 0| ≤
      (A.partitionAt 0).commonLevelCarrierTimeRadius
          (A.timeTest_compact 0) + 1 := by
  let P := A.commonPacketAt timeScale level
  let H :=
    (A.partitionAt 0).commonLevelCarrierTimeRadius
      (A.timeTest_compact 0)
  let r := osiiAxisPairRadius P.slope
  have hT_pos : 0 < P.slope :=
    lt_trans zero_lt_one P.slope_gt_one
  have hr_pos : 0 < r :=
    osiiAxisPairRadius_pos P.slope
  have hr_sq : r ^ 2 = P.slope ^ 2 + 1 := by
    dsimp [r, osiiAxisPairRadius]
    exact Real.sq_sqrt (by positivity)
  have hT_le_r : P.slope ≤ r := by
    have hr_nonneg : 0 ≤ r := hr_pos.le
    nlinarith
  have htime :
      |y 0| ≤ H := by
    exact
      (A.commonCoherentLevelFactor_tsupport_time_bound
        a level i (by simpa [P, commonPacketAt,
          commonCoherentLevelCover, commonCoherentLevelFactors] using hy)
        ).le.trans
      ((A.partitionAt 0).levelCarrierTimeRadius_le_common
        a (A.timeTest_compact 0))
  have hcoord :
      |y (Fin.succ b.1)| ≤ ‖y‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_le_pi_norm y (Fin.succ b.1))
  have hnorm :
      ‖y‖ ≤ P.slope := by
    exact
      (A.commonCoherentLevelFactor_tsupport_norm_bound
        a level i (by simpa [P, commonPacketAt,
          commonCoherentLevelCover, commonCoherentLevelFactors] using hy)
        ).le.trans
      (((A.partitionAt 0).levelCarrierNormRadius_le_common
        a (A.timeTest_compact 0) level).trans
          (A.commonPacketSlopeData level).slope_ge_normRadius)
  have hspace :
      |y (Fin.succ b.1)| ≤ P.slope :=
    hcoord.trans hnorm
  have hsigned :
      |(if b.2 then y (Fin.succ b.1) else -y (Fin.succ b.1))| =
        |y (Fin.succ b.1)| := by
    split <;> simp
  have hH_nonneg : 0 ≤ H := by
    exact
      le_trans
        ((A.partitionAt 0).levelCarrierTimeRadius_pos
          a (A.timeTest_compact 0)).le
        ((A.partitionAt 0).levelCarrierTimeRadius_le_common
          a (A.timeTest_compact 0))
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

/-- Sourcewise localization of a coherent carrier retains one affine packet
center bound independent of both packet indices. -/
theorem commonPacketAt_sourcewiseLocalized_norm_packetCenterOffsetVector_le
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (timeScale level : ℕ)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    let P := A.commonPacketAt timeScale level
    let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
    let hordered :=
      (P.levelCover.carrier a).sourcewiseLocalizedFactors_axisPairOrdered
        P.slope (P.ordered a) fs
    ‖F.packetCenterOffsetVector P.slope hordered q‖ ≤
      2 * ((A.partitionAt 0).commonLevelCarrierTimeRadius
        (A.timeTest_compact 0) + 1) + 1 := by
  dsimp only
  let P := A.commonPacketAt timeScale level
  let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors_axisPairOrdered
      P.slope (P.ordered a) fs
  let B :=
    (A.partitionAt 0).commonLevelCarrierTimeRadius
      (A.timeTest_compact 0) + 1
  have hB : 0 ≤ B := by
    have htime :
        0 ≤ (A.partitionAt 0).commonLevelCarrierTimeRadius
          (A.timeTest_compact 0) :=
      ((A.partitionAt 0).commonLevelCarrierTimeRadius_pos
        a (A.timeTest_compact 0)).le
    dsimp [B]
    linarith
  apply F.norm_packetCenterOffsetVector_le_of_factor_bound
    P.slope hordered q B hB
  intro i y hy
  have hyCarrier :
      y ∈ tsupport
        (((P.levelCover.carrier a).factors i :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) :=
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := (((P.levelCover.carrier a).factors i :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ))
      (f := fs i) hy).2
  simpa [P, B] using
    A.commonPacketAt_abs_rotated_factor_time_le
      timeScale level a i hyCarrier q.2

/-- The common coherent reduced-time Schwartz distribution constructed from
the original OS axioms. -/
noncomputable def commonTimeShellDistributionOfOS
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (level : ℕ)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
  (A.commonPacketAt 0 level).timeShellDistributionOfOS
    OS η hηsum ζ χ

theorem commonPacketAt_timeShellDistributionOfOS_eq_common
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (timeScale level : ℕ)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (A.commonPacketAt timeScale level).timeShellDistributionOfOS
        OS η hηsum ζ χ =
      A.commonTimeShellDistributionOfOS
        OS η hηsum level ζ χ := by
  rfl

/-- The original-OS common shell agrees with the canonical packet
specialized to any reduced-time test supported in its carrier. -/
theorem commonTimeShellDistributionOfOS_apply_eq_commonPacketForTest
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (level : ℕ)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (hψ :
      tsupport (ψ : (Fin k → ℝ) → ℂ) ⊆ A.carrierData.carrier) :
    A.commonTimeShellDistributionOfOS
        OS η hηsum level ζ χ ψ =
      (A.commonPacketForTest ψ hψ level
        ).toInitialSpatialFactorPacketData.narrowDistributionOfOS
          OS η hηsum ζ χ := by
  rw [← InitialBaseTimePartitionData.FixedTimePacketData.timeShellDistributionOfOS_apply_canonical]
  rfl

/-- Any coherent original-OS packet has the same value as the selected
factorwise packet on the common narrow carrier. -/
theorem
    commonPacketAt_timeShellDistributionOfOS_eq_initialSpatialFactorPacketDistributionOfOS
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (timeScale level : ℕ)
    (ζ : OSIITimeGapSpace k)
    (hζ : ζ ∈ osiiNarrowTimeCarrier (k := k) η)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (A.commonPacketAt timeScale level).timeShellDistributionOfOS
        OS η hηsum ζ χ (A.timeTest timeScale) =
      initialSpatialFactorPacketDistributionOfOS
        OS (A.timeTest timeScale)
          (A.timeTest_compact timeScale)
          (A.timeTest_positive timeScale)
          η hηsum level ζ χ := by
  rw [InitialBaseTimePartitionData.FixedTimePacketData.timeShellDistributionOfOS_apply_canonical]
  exact
    (InitialBaseTimePartitionData.InitialSpatialFactorPacketData.narrowDistributionOfOS_eqOn_sameLevel
        (A.commonPacketAt timeScale level
          ).toInitialSpatialFactorPacketData
        (initialSpatialFactorPacketData
          (d := d) (A.timeTest timeScale)
          (A.timeTest_compact timeScale)
          (A.timeTest_positive timeScale) level)
        OS η hη hηsum χ) hζ

/-- Every two-scale original-OS packet approximant is the common one-index
time shell applied to the corresponding shrinking test. -/
theorem
    commonTimeShellDistributionOfOS_apply_timeTest_eq_initialSpatialFactorPacketDistributionOfOS
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (timeScale level : ℕ)
    (ζ : OSIITimeGapSpace k)
    (hζ : ζ ∈ osiiNarrowTimeCarrier (k := k) η)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    A.commonTimeShellDistributionOfOS
        OS η hηsum level ζ χ (A.timeTest timeScale) =
      initialSpatialFactorPacketDistributionOfOS
        OS (A.timeTest timeScale)
          (A.timeTest_compact timeScale)
          (A.timeTest_positive timeScale)
          η hηsum level ζ χ := by
  rw [← A.commonPacketAt_timeShellDistributionOfOS_eq_common
    OS η hηsum timeScale level ζ χ]
  exact
    A.commonPacketAt_timeShellDistributionOfOS_eq_initialSpatialFactorPacketDistributionOfOS
      OS η hη hηsum timeScale level ζ hζ χ

/-- The route-facing compact estimate is exactly uniform boundedness of the
single coherent time-shell distribution family on the shrinking anchored
tests.  In particular, the time scale is no longer part of the distribution
being estimated. -/
theorem hasUniformPacketCompactBoundOfOS_iff_commonTimeShellDistributionOfOS
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    A.HasUniformPacketCompactBoundOfOS OS η hηsum ↔
      ∀ K : Set (OSIITimeGapSpace k),
        IsCompact K →
          K ⊆ osiiNarrowTimeCarrier (k := k) η →
            ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
              ∃ C : ℝ, ∀ N level ζ, ζ ∈ K →
                ‖A.commonTimeShellDistributionOfOS
                    OS η hηsum level ζ χ (A.timeTest N)‖ ≤ C := by
  constructor
  · intro hbound K hK_compact hK_subset χ
    obtain ⟨C, hC⟩ := hbound K hK_compact hK_subset χ
    refine ⟨C, ?_⟩
    intro N level ζ hζ
    rw [
      A.commonTimeShellDistributionOfOS_apply_timeTest_eq_initialSpatialFactorPacketDistributionOfOS
        OS η hη hηsum N level ζ (hK_subset hζ) χ]
    exact hC N level ζ hζ
  · intro hbound K hK_compact hK_subset χ
    obtain ⟨C, hC⟩ := hbound K hK_compact hK_subset χ
    refine ⟨C, ?_⟩
    intro N level ζ hζ
    rw [←
      A.commonTimeShellDistributionOfOS_apply_timeTest_eq_initialSpatialFactorPacketDistributionOfOS
        OS η hη hηsum N level ζ (hK_subset hζ) χ]
    exact hC N level ζ hζ

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
