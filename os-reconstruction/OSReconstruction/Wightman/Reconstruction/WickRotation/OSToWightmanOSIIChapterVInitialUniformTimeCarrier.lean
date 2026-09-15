/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialQuantitativeLevelCarrier















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

namespace InitialBaseTimePartitionData

variable {φ : SchwartzMap (Fin k → ℝ) ℂ}

/-- Embed one Euclidean time coordinate with zero spatial part. -/
def initialPureTimePoint (d : ℕ) (t : ℝ) : SpacetimeDim d :=
  Fin.cons t 0

@[simp] theorem initialPureTimePoint_time (t : ℝ) :
    initialPureTimePoint d t 0 = t :=
  rfl

/-- Remove the spatial coordinates of a spacetime point. -/
def initialPureTimeProjection (d : ℕ) (y : SpacetimeDim d) :
    SpacetimeDim d :=
  initialPureTimePoint d (y 0)

@[simp] theorem initialPureTimeProjection_time (y : SpacetimeDim d) :
    initialPureTimeProjection d y 0 = y 0 :=
  rfl

/-- The fixed compact set of pure-time points occurring in one coordinate of
one base/time partition piece. It is independent of the spatial level. -/
def levelPiecePureTimeCarrierSet
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (i : Fin (k + 1)) :
    Set (SpacetimeDim d) :=
  (fun p : InitialBaseTimeSpace d k =>
      initialPureTimePoint d
        (initialBaseTimeConfigurationCLM d k p i 0)) ''
    (initialBaseTimeFootprint (d := d) φ ∩
      tsupport (D.cutoff a : InitialBaseTimeSpace d k → ℂ))

theorem isCompact_levelPiecePureTimeCarrierSet
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (i : Fin (k + 1)) :
    IsCompact (D.levelPiecePureTimeCarrierSet a i) := by
  apply IsCompact.image
  · exact
      (isCompact_initialBaseTimeFootprint (d := d) φ hφ_compact).inter
        (D.cutoff_compact a).isCompact
  · change Continuous (fun p =>
      (Fin.cons (initialBaseTimeConfigurationCLM d k p i 0)
        (0 : Fin d → ℝ) : SpacetimeDim d))
    apply continuous_pi
    intro μ
    refine Fin.cases ?_ (fun _ => ?_) μ
    · fun_prop
    · simpa using (continuous_const :
        Continuous (fun _ : InitialBaseTimeSpace d k => (0 : ℝ)))

theorem levelPiecePureTimeCarrierSet_subset_cell
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (i : Fin (k + 1)) :
    D.levelPiecePureTimeCarrierSet a i ⊆
      (naturalChronologicalProductNeighborhood
        (initialBaseTimeConfigurationCLM d k (D.center a))
        (D.center_ordered a)).cell i := by
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  have hpure := D.cutoff_support a hp.2 i
  exact
    (mem_naturalChronologicalProductNeighborhood_cell_iff_of_time_eq
      (d := d) (k := k)
      (initialBaseTimeConfigurationCLM d k (D.center a))
      (D.center_ordered a) i
      (initialBaseTimeConfigurationCLM d k p i)
      (initialPureTimePoint d
        (initialBaseTimeConfigurationCLM d k p i 0))
      rfl).mp hpure

theorem levelPiecePureTimeCarrierSet_time_bound
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ D.levelPiecePureTimeCarrierSet a i) :
    |y 0| < D.levelCarrierTimeRadius a hφ_compact := by
  rcases hy with ⟨p, hp, rfl⟩
  have hp_bound :=
    (D.levelCarrierBaseRadiusData a hφ_compact).bound p hp
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
    _ ≤
        ‖initialBaseTimeConfigurationCLM d k‖ *
          (D.levelCarrierBaseRadiusData a hφ_compact).radius := by
      gcongr
    _ <
        ‖initialBaseTimeConfigurationCLM d k‖ *
            (D.levelCarrierBaseRadiusData a hφ_compact).radius + 1 := by
      linarith
    _ = D.levelCarrierTimeRadius a hφ_compact := rfl

/-- Fixed compact time guards for one partition piece, together with their
positive pairwise chronological gap. -/
structure LevelCarrierTimeGuardData
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) where
  guard : OSIIChronologicalCompactFactors d k
  guard_one :
    ∀ i y, y ∈ D.levelPiecePureTimeCarrierSet a i →
      guard.factors i y = 1
  guard_time_bound :
    ∀ i y,
      y ∈ tsupport
          ((guard.factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) →
        |y 0| < D.levelCarrierTimeRadius a hφ_compact
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

theorem nonempty_levelCarrierTimeGuardData
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    Nonempty (D.LevelCarrierTimeGuardData a hφ_compact) := by
  let P :=
    naturalChronologicalProductNeighborhood
      (initialBaseTimeConfigurationCLM d k (D.center a))
      (D.center_ordered a)
  let K : Fin (k + 1) → Set (SpacetimeDim d) :=
    D.levelPiecePureTimeCarrierSet a
  let U : Fin (k + 1) → Set (SpacetimeDim d) := fun i =>
    P.cell i ∩
      {y | |y 0| < D.levelCarrierTimeRadius a hφ_compact}
  have hK_compact : ∀ i, IsCompact (K i) :=
    fun i => D.isCompact_levelPiecePureTimeCarrierSet a hφ_compact i
  have hU_open : ∀ i, IsOpen (U i) := by
    intro i
    exact (P.cell_open i).inter
      (isOpen_lt
        (continuous_abs.comp (continuous_apply 0))
        continuous_const)
  have hK_sub : ∀ i, K i ⊆ U i := by
    intro i y hy
    exact
      ⟨D.levelPiecePureTimeCarrierSet_subset_cell a i hy,
        D.levelPiecePureTimeCarrierSet_time_bound
          a hφ_compact i hy⟩
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
              initialBaseTimeConfigurationCLM d k (D.center a) q 0)
            (D.center_ordered a i j hij)
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

/-- Route-local fixed selection of the time guards for one partition piece. -/
noncomputable def levelCarrierTimeGuardData
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    D.LevelCarrierTimeGuardData a hφ_compact :=
  Classical.choice (D.nonempty_levelCarrierTimeGuardData a hφ_compact)

/-- The fixed positive chronological margin for one partition piece. -/
noncomputable def levelCarrierTimeGap
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    ℝ :=
  (D.levelCarrierTimeGuardData a hφ_compact).timeGap

theorem levelCarrierTimeGap_pos
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)) :
    0 < D.levelCarrierTimeGap a hφ_compact :=
  (D.levelCarrierTimeGuardData a hφ_compact).timeGap_pos

theorem levelPieceOnePointCarrierSet_pureTime_mem
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (N : ℕ)
    (i : Fin (k + 1))
    {y : SpacetimeDim d}
    (hy : y ∈ D.levelPieceOnePointCarrierSet a N i) :
    initialPureTimeProjection d y ∈
      D.levelPiecePureTimeCarrierSet a i := by
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with ⟨p, hp, rfl⟩
  refine ⟨p.1, hp.1, ?_⟩
  ext μ
  refine Fin.cases ?_ (fun j => ?_) μ
  · simpa using
      (initialFullConfigurationFromBaseTimeSpatialCLM_time
        (d := d) (k := k) p.1 p.2 i).symm
  · rfl

/-- Quantitative level cover with one fixed positive time gap per member of
the finite base/time partition. -/
structure UniformTimeQuantitativeLevelCover
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) where
  carrier : D.index → OSIIChronologicalCompactFactors d k
  carrier_fix :
    ∀ a χ,
      SchwartzMap.smulLeftCLM ℂ
          (SchwartzMap.productTensor (carrier a).factors)
          (D.levelPiece a N χ) =
        D.levelPiece a N χ
  carrier_time_bound :
    ∀ a i y,
      y ∈ tsupport
          (((carrier a).factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) →
        |y 0| < D.levelCarrierTimeRadius a hφ_compact
  carrier_norm_bound :
    ∀ a i y,
      y ∈ tsupport
          (((carrier a).factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) →
        ‖y‖ < D.levelCarrierNormRadius a hφ_compact N
  carrier_time_gap :
    ∀ a, ∀ i j : Fin (k + 1), i < j →
      ∀ y ∈ tsupport
          (((carrier a).factors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ),
        ∀ z ∈ tsupport
            (((carrier a).factors j : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          D.levelCarrierTimeGap a hφ_compact ≤ z 0 - y 0

def UniformTimeQuantitativeLevelCover.toQuantitativeLevelCover
    {D : InitialBaseTimePartitionData (d := d) φ}
    {hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)}
    {N : ℕ}
    (C : D.UniformTimeQuantitativeLevelCover hφ_compact N) :
    D.QuantitativeLevelCover hφ_compact N where
  carrier := C.carrier
  carrier_fix := C.carrier_fix
  carrier_time_bound := C.carrier_time_bound
  carrier_norm_bound := C.carrier_norm_bound

/-- Explicit slope making one quantitatively guarded level carrier ordered in
every signed axis-pair frame. -/
noncomputable def levelCarrierAxisPairSlope
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    ℝ :=
  2 +
    2 * D.levelCarrierNormRadius a hφ_compact N /
      D.levelCarrierTimeGap a hφ_compact

theorem levelCarrierAxisPairSlope_gt_one
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    1 < D.levelCarrierAxisPairSlope a hφ_compact N := by
  have hR :
      0 ≤ D.levelCarrierNormRadius a hφ_compact N :=
    (D.levelCarrierNormRadius_pos a hφ_compact N).le
  have hδ :
      0 < D.levelCarrierTimeGap a hφ_compact :=
    D.levelCarrierTimeGap_pos a hφ_compact
  dsimp [levelCarrierAxisPairSlope]
  have hquot :
      0 ≤
        2 * D.levelCarrierNormRadius a hφ_compact N /
          D.levelCarrierTimeGap a hφ_compact :=
    div_nonneg (mul_nonneg (by norm_num) hR) hδ.le
  linarith

/-- The explicit slope sees the fixed chronological gap despite the moving
spatial radius. -/
theorem UniformTimeQuantitativeLevelCover.axisPairOrderedAt_levelCarrierSlope
    {D : InitialBaseTimePartitionData (d := d) φ}
    {hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)}
    {N : ℕ}
    (C : D.UniformTimeQuantitativeLevelCover hφ_compact N)
    (a : D.index) :
    ∀ b : osiiAxisPairIndex d,
      ∀ i j : Fin (k + 1), i < j →
        ∀ y ∈ tsupport
            (((C.carrier a).factors i : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              (((C.carrier a).factors j : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ((osiiAxisPairRotationData
                (D.levelCarrierAxisPairSlope a hφ_compact N) b
              ).matrix.mulVec y) 0 <
              ((osiiAxisPairRotationData
                  (D.levelCarrierAxisPairSlope a hφ_compact N) b
                ).matrix.mulVec z) 0 := by
  intro b i j hij y hy z hz
  let R := D.levelCarrierNormRadius a hφ_compact N
  let δ := D.levelCarrierTimeGap a hφ_compact
  let T := D.levelCarrierAxisPairSlope a hφ_compact N
  have hR_pos : 0 < R :=
    D.levelCarrierNormRadius_pos a hφ_compact N
  have hδ_pos : 0 < δ :=
    D.levelCarrierTimeGap_pos a hφ_compact
  have hT_pos : 0 < T :=
    lt_trans zero_lt_one
      (D.levelCarrierAxisPairSlope_gt_one a hφ_compact N)
  have hgap : δ ≤ z 0 - y 0 :=
    C.carrier_time_gap a i j hij y hy z hz
  have hycoord :
      |y (Fin.succ b.1)| < R := by
    have hcoord_le :
        |y (Fin.succ b.1)| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using
        (norm_le_pi_norm y (Fin.succ b.1))
    exact hcoord_le.trans_lt
      (C.carrier_norm_bound a i y hy)
  have hzcoord :
      |z (Fin.succ b.1)| < R := by
    have hcoord_le :
        |z (Fin.succ b.1)| ≤ ‖z‖ := by
      simpa [Real.norm_eq_abs] using
        (norm_le_pi_norm z (Fin.succ b.1))
    exact hcoord_le.trans_lt
      (C.carrier_norm_bound a j z hz)
  let sy :=
    if b.2 then y (Fin.succ b.1) else -y (Fin.succ b.1)
  let sz :=
    if b.2 then z (Fin.succ b.1) else -z (Fin.succ b.1)
  have hsy : |sy| = |y (Fin.succ b.1)| := by
    dsimp [sy]
    split <;> simp
  have hsz : |sz| = |z (Fin.succ b.1)| := by
    dsimp [sz]
    split <;> simp
  have hspatial : sy - sz < 2 * R := by
    have hsy_le : sy ≤ |sy| := le_abs_self sy
    have hsz_le : -sz ≤ |sz| := neg_le_abs sz
    rw [hsy] at hsy_le
    rw [hsz] at hsz_le
    linarith
  have hTδ : 2 * R < T * δ := by
    have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
    have hformula : T * δ = 2 * δ + 2 * R := by
      change (2 + 2 * R / δ) * δ = 2 * δ + 2 * R
      rw [add_mul, div_mul_cancel₀ (2 * R) hδ_ne]
    rw [hformula]
    linarith
  have hscaledGap : T * δ ≤ T * (z 0 - y 0) :=
    mul_le_mul_of_nonneg_left hgap hT_pos.le
  rw [(osiiAxisPairRotationData T b).mulVec_time,
    (osiiAxisPairRotationData T b).mulVec_time,
    mul_lt_mul_iff_right₀
      (inv_pos.mpr (osiiAxisPairRadius_pos T))]
  change T * y 0 + sy < T * z 0 + sz
  linarith

/-- One explicit common slope for the finite fixed-time partition. -/
noncomputable def commonLevelCarrierAxisPairSlope
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    ℝ :=
  ∑ a, D.levelCarrierAxisPairSlope a hφ_compact N

theorem levelCarrierAxisPairSlope_le_common
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ) :
    D.levelCarrierAxisPairSlope a hφ_compact N ≤
      D.commonLevelCarrierAxisPairSlope hφ_compact N := by
  exact
    Finset.single_le_sum
      (fun b _hb =>
        le_trans (by norm_num)
          (D.levelCarrierAxisPairSlope_gt_one b hφ_compact N).le)
      (Finset.mem_univ a)

theorem UniformTimeQuantitativeLevelCover.axisPairOrderedAt_commonSlope
    {D : InitialBaseTimePartitionData (d := d) φ}
    {hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ)}
    {N : ℕ}
    (C : D.UniformTimeQuantitativeLevelCover hφ_compact N) :
    ∀ a : D.index,
      ∀ b : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              (((C.carrier a).factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                (((C.carrier a).factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData
                  (D.commonLevelCarrierAxisPairSlope hφ_compact N) b
                ).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData
                    (D.commonLevelCarrierAxisPairSlope hφ_compact N) b
                  ).matrix.mulVec z) 0 := by
  intro a
  exact
    axisPairOrdered_mono (C.carrier a)
      (D.levelCarrierAxisPairSlope_le_common a hφ_compact N)
      (C.axisPairOrderedAt_levelCarrierSlope a)

end InitialBaseTimePartitionData

end OSIIChapterV
end OSReconstruction
