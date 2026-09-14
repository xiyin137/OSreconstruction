/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacket
import Init
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairCompactSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialStageRealEdge
import OSReconstruction.SCV.EuclideanWeylOpen
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- The product neighborhood obtained from the ordinary Euclidean-time order
of one configuration.  Its rotation and ordering permutation are both the
identity. -/
noncomputable def naturalChronologicalProductNeighborhood
    (x : NPointDomain d (k + 1))
    (hx :
      ∀ i j : Fin (k + 1), i < j →
        x i 0 < x j 0) :
    OSIIOrderedProductNeighborhood x where
  rotation := 1
  orthogonal := by simp
  det_one := by simp
  order := 1
  cell :=
    osiiOrderedTimeCell (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (fun i => x i 0)
  cell_open :=
    isOpen_osiiOrderedTimeCell
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (fun i => x i 0)
  center_mem := by
    intro i
    exact
      mem_osiiOrderedTimeCell_self
        (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        x i (by
          intro q
          simp [osiiRotatedTime])
  ordered := by
    intro y hy i j hij
    have hlt :=
      osiiOrderedTimeCell_lt
        (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (fun q => x q 0) (hx i j hij) (hy i) (hy j)
    simpa [osiiRotatedTime] using hlt

/-- A compact source supported in one natural chronological product box
admits compact ordered factor cutoffs whose product fixes the source exactly.

The factors are carriers, not a factorization of the source.  This distinction
lets the packet construction act on arbitrary full Schwartz sources. -/
theorem exists_chronologicalCompactFactors_fix_source_of_natural_box
    (x₀ : NPointDomain d (k + 1))
    (hx₀ :
      ∀ i j : Fin (k + 1), i < j →
        x₀ i 0 < x₀ j 0)
    (f : SchwartzNPoint d (k + 1))
    (hf_compact :
      HasCompactSupport
        (f : NPointDomain d (k + 1) → ℂ))
    (hf_box :
      tsupport (f : NPointDomain d (k + 1) → ℂ) ⊆
        {x |
          ∀ i : Fin (k + 1),
            x i ∈
              (naturalChronologicalProductNeighborhood x₀ hx₀).cell i}) :
    ∃ F : OSIIChronologicalCompactFactors d k,
      SchwartzMap.smulLeftCLM ℂ
          (SchwartzMap.productTensor F.factors) f =
        f := by
  let P := naturalChronologicalProductNeighborhood x₀ hx₀
  let K : Fin (k + 1) → Set (SpacetimeDim d) := fun i =>
    (fun x : NPointDomain d (k + 1) => x i) ''
      tsupport (f : NPointDomain d (k + 1) → ℂ)
  have hK_compact : ∀ i, IsCompact (K i) := by
    intro i
    exact hf_compact.isCompact.image (continuous_apply i)
  have hK_sub : ∀ i, K i ⊆ P.cell i := by
    intro i y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hf_box hx i
  have hcutoff :
      ∀ i : Fin (k + 1), ∃ χ : SchwartzSpacetime d,
        (∀ y ∈ K i, χ y = 1) ∧
        tsupport
            ((χ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          P.cell i ∧
        HasCompactSupport
          ((χ : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
    intro i
    exact
      exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open
        (m := d + 1) (hK_compact i) (P.cell_open i) (hK_sub i)
  choose χ hχ_one hχ_support hχ_compact using hcutoff
  let F : OSIIChronologicalCompactFactors d k :=
    { factors := χ
      factor_compact := hχ_compact
      ordered_support := by
        intro i j hij y hy z hz
        have hlt :=
          osiiOrderedTimeCell_lt
            (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
            (fun q => x₀ q 0) (hx₀ i j hij)
            (hχ_support i hy) (hχ_support j hz)
        simpa [P, naturalChronologicalProductNeighborhood,
          osiiRotatedTime] using hlt }
  refine ⟨F, ?_⟩
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (SchwartzMap.productTensor F.factors).hasTemperateGrowth]
  by_cases hx : x ∈ tsupport
      (f : NPointDomain d (k + 1) → ℂ)
  · have hcarrier :
        (SchwartzMap.productTensor F.factors :
          SchwartzNPoint d (k + 1)) x = 1 := by
      rw [SchwartzMap.productTensor_apply]
      apply Finset.prod_eq_one
      intro i _hi
      exact hχ_one i (x i) ⟨x, hx, rfl⟩
    simp [hcarrier, smul_eq_mul]
  · have hzero : f x = 0 :=
      image_eq_zero_of_notMem_tsupport hx
    simp [hzero, smul_eq_mul]

/-- A finite exact chronological decomposition of an entire spatial source
map. The partition and carriers are fixed for all spatial tests, so every
piece remains continuous and linear in the spatial source. -/
structure SpatialChronologicalCompactCoverData
    (L :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzNPoint d (k + 1)) where
  index : Type
  indexFintype : Fintype index
  piece :
    index →
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzNPoint d (k + 1)
  carrier : index → OSIIChronologicalCompactFactors d k
  sum_eq :
    L =
      (@Finset.univ index indexFintype).sum piece
  carrier_fix :
    ∀ a χ,
      SchwartzMap.smulLeftCLM ℂ
          (SchwartzMap.productTensor (carrier a).factors)
          (piece a χ) =
        piece a χ

/-- Once a slope sees a compact chronological carrier in every signed
axis-pair frame, every larger slope does as well. -/
theorem axisPairOrdered_mono
    (F : OSIIChronologicalCompactFactors d k)
    {T T' : ℝ}
    (hTT' : T ≤ T')
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0) :
    ∀ a : osiiAxisPairIndex d,
      ∀ i j : Fin (k + 1), i < j →
        ∀ y ∈ tsupport
            ((F.factors i : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          ∀ z ∈ tsupport
              ((F.factors j : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ((osiiAxisPairRotationData T' a).matrix.mulVec y) 0 <
              ((osiiAxisPairRotationData T' a).matrix.mulVec z) 0 := by
  intro a i j hij y hy z hz
  have hbase := hordered a i j hij y hy z hz
  have htime : y 0 < z 0 :=
    F.ordered_support i j hij y hy z hz
  rw [(osiiAxisPairRotationData T a).mulVec_time,
    (osiiAxisPairRotationData T a).mulVec_time] at hbase
  rw [(osiiAxisPairRotationData T' a).mulVec_time,
    (osiiAxisPairRotationData T' a).mulVec_time]
  have hscaled :
      T * y 0 +
          (if a.2 then y (Fin.succ a.1) else -y (Fin.succ a.1)) <
        T * z 0 +
          (if a.2 then z (Fin.succ a.1) else -z (Fin.succ a.1)) := by
    exact
      (mul_lt_mul_iff_right₀
        (inv_pos.mpr (osiiAxisPairRadius_pos T))).mp hbase
  rw [mul_lt_mul_iff_right₀
    (inv_pos.mpr (osiiAxisPairRadius_pos T'))]
  have hTdiff : 0 ≤ T' - T :=
    sub_nonneg.mpr hTT'
  have htimeDiff : 0 ≤ z 0 - y 0 :=
    sub_nonneg.mpr htime.le
  have hincrement :
      0 ≤ (T' - T) * (z 0 - y 0) :=
    mul_nonneg hTdiff htimeDiff
  have hdecomp :
      (T' * z 0 +
            (if a.2 then z (Fin.succ a.1) else -z (Fin.succ a.1))) -
          (T' * y 0 +
            (if a.2 then y (Fin.succ a.1) else -y (Fin.succ a.1))) =
        ((T * z 0 +
              (if a.2 then z (Fin.succ a.1) else -z (Fin.succ a.1))) -
            (T * y 0 +
              (if a.2 then y (Fin.succ a.1) else -y (Fin.succ a.1)))) +
          (T' - T) * (z 0 - y 0) := by
    ring
  linarith

/-- The finitely many fixed carriers in a spatial source-map cover admit one
common slope and one common axis-pair chart. -/
theorem SpatialChronologicalCompactCoverData.exists_common_axisPairSlope
    {L :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzNPoint d (k + 1)}
    (D : SpatialChronologicalCompactCoverData L) :
    ∃ T : ℝ, 1 < T ∧
      ∀ a : D.index,
        ∀ b : osiiAxisPairIndex d,
          ∀ i j : Fin (k + 1), i < j →
            ∀ y ∈ tsupport
                (((D.carrier a).factors i : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ∀ z ∈ tsupport
                  (((D.carrier a).factors j : SchwartzSpacetime d) :
                    SpacetimeDim d → ℂ),
                ((osiiAxisPairRotationData T b).matrix.mulVec y) 0 <
                  ((osiiAxisPairRotationData T b).matrix.mulVec z) 0 := by
  letI : Fintype D.index := D.indexFintype
  by_cases hindex : Nonempty D.index
  · have hslope :
        ∀ a : D.index, ∃ T : ℝ, 1 < T ∧
          ∀ b : osiiAxisPairIndex d,
            ∀ i j : Fin (k + 1), i < j →
              ∀ y ∈ tsupport
                  (((D.carrier a).factors i : SchwartzSpacetime d) :
                    SpacetimeDim d → ℂ),
                ∀ z ∈ tsupport
                    (((D.carrier a).factors j : SchwartzSpacetime d) :
                      SpacetimeDim d → ℂ),
                  ((osiiAxisPairRotationData T b).matrix.mulVec y) 0 <
                    ((osiiAxisPairRotationData T b).matrix.mulVec z) 0 :=
      fun a => (D.carrier a).exists_axisPairSlope_pairwise_ordered
    choose T hT hordered using hslope
    let Tcommon : ℝ := ∑ a : D.index, T a
    have hT_nonneg : ∀ a : D.index, 0 ≤ T a :=
      fun a => le_of_lt (lt_trans zero_lt_one (hT a))
    obtain ⟨a₀⟩ := hindex
    have hTa₀_le : T a₀ ≤ Tcommon := by
      exact
        Finset.single_le_sum
          (fun a _ha => hT_nonneg a) (Finset.mem_univ a₀)
    have hTcommon : 1 < Tcommon :=
      (hT a₀).trans_le hTa₀_le
    refine ⟨Tcommon, hTcommon, ?_⟩
    intro a
    have hTa_le : T a ≤ Tcommon := by
      exact
        Finset.single_le_sum
          (fun q _hq => hT_nonneg q) (Finset.mem_univ a)
    exact
      axisPairOrdered_mono (D.carrier a)
        hTa_le (hordered a)
  · refine ⟨2, by norm_num, ?_⟩
    intro a
    exact False.elim (hindex ⟨a⟩)

/-- A compact set with strict Euclidean-time order which uniformly carries a
continuous spatial source map admits one finite exact chronological
decomposition, fixed for every spatial test. -/
theorem nonempty_spatialChronologicalCompactCoverData
    (L :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzNPoint d (k + 1))
    (K : Set (NPointDomain d (k + 1)))
    (hK_compact : IsCompact K)
    (hL_support :
      ∀ χ,
        tsupport
            ((L χ : SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ) ⊆
          K)
    (hK_ordered :
      ∀ x ∈ K,
        ∀ i j : Fin (k + 1), i < j →
          x i 0 < x j 0) :
    Nonempty (SpatialChronologicalCompactCoverData L) := by
  obtain ⟨R, hKR⟩ :=
    hK_compact.isBounded.subset_closedBall
      (0 : NPointDomain d (k + 1))
  let B : ℝ := max R 0 + 1
  have hB_pos : 0 < B := by
    dsimp [B]
    linarith [le_max_right R 0]
  let orderedAt :
      ∀ y : K, ∀ i j : Fin (k + 1), i < j →
        y.1 i 0 < y.1 j 0 :=
    fun y => hK_ordered y.1 y.2
  let P : ∀ y : K, OSIIOrderedProductNeighborhood y.1 :=
    fun y =>
      naturalChronologicalProductNeighborhood y.1 (orderedAt y)
  let Vβ : K → Set (NPointDomain d (k + 1)) := fun y =>
    {z | ∀ i : Fin (k + 1), z i ∈ (P y).cell i} ∩
      Metric.ball 0 B
  have hVβ_open : ∀ y : K, IsOpen (Vβ y) := by
    intro y
    apply IsOpen.inter
    · change IsOpen
        {z : NPointDomain d (k + 1) |
          ∀ i : Fin (k + 1), z i ∈ (P y).cell i}
      have hopen :
          IsOpen
            (⋂ i : Fin (k + 1),
              {z : NPointDomain d (k + 1) | z i ∈ (P y).cell i}) :=
        isOpen_iInter_of_finite fun i =>
          (P y).cell_open i |>.preimage (continuous_apply i)
      convert hopen using 1
      ext z
      simp
    · exact Metric.isOpen_ball
  have hK_cover : K ⊆ ⋃ y : K, Vβ y := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    constructor
    · exact (P ⟨x, hx⟩).center_mem
    · have hxR : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hKR hx
      have hxB : ‖x‖ < B := by
        dsimp [B]
        linarith [le_max_left R 0]
      simpa [Metric.mem_ball, dist_zero_right] using hxB
  obtain ⟨s, hscover⟩ :=
    hK_compact.elim_finite_subcover Vβ hVβ_open hK_cover
  let α := {y : K // y ∈ s}
  let V : α → Set (NPointDomain d (k + 1)) := fun a => Vβ a.1
  let Q : α → NPointDomain d (k + 1) := fun a => a.1.1
  let hQ :
      ∀ a : α, ∀ i j : Fin (k + 1), i < j →
        Q a i 0 < Q a j 0 :=
    fun a => orderedAt a.1
  letI : Fintype α := Fintype.ofFinite α
  have hV_open : ∀ a : α, IsOpen (V a) := by
    intro a
    exact hVβ_open a.1
  have hV_relcompact :
      ∀ a : α, ∃ c r,
        V a ⊆ Metric.closedBall c r := by
    intro a
    refine ⟨0, B, ?_⟩
    intro x hx
    exact Metric.ball_subset_closedBall hx.2
  have hcover : K ⊆ ⋃ a : α, V a := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hscover hx) with ⟨y, hys, hxy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hys⟩, hxy⟩
  obtain ⟨θ, hθ_compact, hθ_support, hθ_sum⟩ :=
    SCV.exists_finite_schwartz_partitionOfUnity_on_compact
      hK_compact hV_open hV_relcompact hcover
  let piece :
      α →
        SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
          SchwartzNPoint d (k + 1) := fun a =>
    (SchwartzMap.smulLeftCLM ℂ
      (θ a : NPointDomain d (k + 1) → ℂ)).comp L
  have hpiece_sum :
      L = ∑ a : α, piece a := by
    apply ContinuousLinearMap.ext
    intro χ
    simpa [piece] using
      SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset α) θ (L χ)
        (by
          intro x hx
          exact hθ_sum x (hL_support χ hx))
  have hcarrier :
      ∀ a : α, ∃ F : OSIIChronologicalCompactFactors d k,
        SchwartzMap.smulLeftCLM ℂ
            (SchwartzMap.productTensor F.factors)
            (θ a) =
          θ a := by
    intro a
    apply
      exists_chronologicalCompactFactors_fix_source_of_natural_box
        (Q a) (hQ a) (θ a) (hθ_compact a)
    intro x hx i
    exact (hθ_support a hx).1 i
  choose carrier hcarrier_fix using hcarrier
  have hcarrier_piece :
      ∀ a χ,
        SchwartzMap.smulLeftCLM ℂ
            (SchwartzMap.productTensor (carrier a).factors)
            (piece a χ) =
          piece a χ := by
    intro a χ
    ext x
    have hfixpoint :
        SchwartzMap.productTensor (carrier a).factors x *
            θ a x =
          θ a x := by
      have hx :=
        congrArg
          (fun g : SchwartzNPoint d (k + 1) => g x)
          (hcarrier_fix a)
      change
        (SchwartzMap.smulLeftCLM ℂ
            (SchwartzMap.productTensor (carrier a).factors)
            (θ a)) x =
          (θ a) x at hx
      rw [SchwartzMap.smulLeftCLM_apply_apply
        (SchwartzMap.productTensor (carrier a).factors).hasTemperateGrowth]
        at hx
      simpa only [smul_eq_mul] using hx
    simp only [piece, ContinuousLinearMap.comp_apply]
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (SchwartzMap.productTensor (carrier a).factors).hasTemperateGrowth]
    rw [SchwartzMap.smulLeftCLM_apply_apply (θ a).hasTemperateGrowth]
    simpa only [smul_eq_mul, mul_assoc] using
      congrArg (fun z : ℂ => z * (L χ) x) hfixpoint
  exact
    ⟨{
      index := α
      indexFintype := inferInstance
      piece := piece
      carrier := carrier
      sum_eq := hpiece_sum
      carrier_fix := hcarrier_piece }⟩

end OSIIChapterV
end OSReconstruction
