/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialBaseTimeFootprint
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVChronologicalCompactCover











noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- The compact base/time footprint associated to an explicit reduced-time
carrier.  Unlike `initialBaseTimeFootprint`, this set is independent of a
particular Schwartz time test. -/
def initialBaseTimeCarrierFootprint
    (timeCarrier : Set (Fin k → ℝ)) :
    Set (InitialBaseTimeSpace d k) :=
  tsupport
      ((BHW.normalizedCutoffOfBump d).toSchwartz :
        SpacetimeDim d → ℂ) ×ˢ
    timeCarrier

/-- A finite chronological partition chosen for one explicit compact
reduced-time carrier.

This is the scale-coherent form of the initial partition.  Every Schwartz
time test supported in `timeCarrier` inherits the same index set, centers,
and cutoffs. -/
structure InitialBaseTimeCarrierPartitionData
    (timeCarrier : Set (Fin k → ℝ)) where
  index : Type
  indexFintype : Fintype index
  center : index → InitialBaseTimeSpace d k
  center_ordered :
    ∀ a, ∀ i j : Fin (k + 1), i < j →
      initialBaseTimeConfigurationCLM d k (center a) i 0 <
        initialBaseTimeConfigurationCLM d k (center a) j 0
  cutoff : index → SchwartzMap (InitialBaseTimeSpace d k) ℂ
  cutoff_compact :
    ∀ a, HasCompactSupport
      (cutoff a : InitialBaseTimeSpace d k → ℂ)
  cutoff_support :
    ∀ a,
      tsupport (cutoff a : InitialBaseTimeSpace d k → ℂ) ⊆
        {p |
          ∀ i : Fin (k + 1),
            initialBaseTimeConfigurationCLM d k p i ∈
              (naturalChronologicalProductNeighborhood
                (initialBaseTimeConfigurationCLM d k (center a))
                (center_ordered a)).cell i}
  cutoff_sum :
    ∀ p ∈ initialBaseTimeCarrierFootprint (d := d) timeCarrier,
      ∑ a, cutoff a p = 1

/-- A finite Schwartz partition of the compact basepoint/time-gap footprint,
with every piece supported in one natural chronological product box after
pure-time reconstruction. -/
structure InitialBaseTimePartitionData
    (φ : SchwartzMap (Fin k → ℝ) ℂ) where
  index : Type
  indexFintype : Fintype index
  center : index → InitialBaseTimeSpace d k
  center_ordered :
    ∀ a, ∀ i j : Fin (k + 1), i < j →
      initialBaseTimeConfigurationCLM d k (center a) i 0 <
        initialBaseTimeConfigurationCLM d k (center a) j 0
  cutoff : index → SchwartzMap (InitialBaseTimeSpace d k) ℂ
  cutoff_compact :
    ∀ a, HasCompactSupport
      (cutoff a : InitialBaseTimeSpace d k → ℂ)
  cutoff_support :
    ∀ a,
      tsupport (cutoff a : InitialBaseTimeSpace d k → ℂ) ⊆
        {p |
          ∀ i : Fin (k + 1),
            initialBaseTimeConfigurationCLM d k p i ∈
              (naturalChronologicalProductNeighborhood
                (initialBaseTimeConfigurationCLM d k (center a))
                (center_ordered a)).cell i}
  cutoff_sum :
    ∀ p ∈ initialBaseTimeFootprint (d := d) φ,
      ∑ a, cutoff a p = 1

namespace InitialBaseTimePartitionData

variable {φ : SchwartzMap (Fin k → ℝ) ℂ}

instance (D : InitialBaseTimePartitionData (d := d) φ) :
    Fintype D.index :=
  D.indexFintype

/-- Pull one fixed base/time cutoff back to full absolute configuration
space. -/
def weight
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index) :
    NPointDomain d (k + 1) → ℂ :=
  fun x => D.cutoff a (initialBaseTimeProjectionCLM d k x)

theorem weight_hasTemperateGrowth
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index) :
    Function.HasTemperateGrowth (D.weight a) := by
  change Function.HasTemperateGrowth
    ((D.cutoff a : InitialBaseTimeSpace d k → ℂ) ∘
      initialBaseTimeProjectionCLM d k)
  exact
    (D.cutoff a).hasTemperateGrowth.comp
      (initialBaseTimeProjectionCLM d k).hasTemperateGrowth

/-- The source-map piece obtained from one fixed base/time cutoff. -/
noncomputable def piece
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1) :=
  (SchwartzMap.smulLeftCLM ℂ (D.weight a)).comp
    (initialReducedSpatialFullSourceCLM (d := d) φ)

@[simp] theorem piece_apply_point
    (D : InitialBaseTimePartitionData (d := d) φ)
    (a : D.index)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (x : NPointDomain d (k + 1)) :
    D.piece a χ x =
      D.cutoff a (initialBaseTimeProjectionCLM d k x) *
        initialReducedSpatialFullSourceCLM (d := d) φ χ x := by
  rw [piece, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (D.weight_hasTemperateGrowth a)]
  rfl

/-- The fixed pieces sum exactly to the canonical initial spatial source map.
-/
theorem sum_piece_eq
    (D : InitialBaseTimePartitionData (d := d) φ) :
    ∑ a, D.piece a =
      initialReducedSpatialFullSourceCLM (d := d) φ := by
  apply ContinuousLinearMap.ext
  intro χ
  ext x
  let ev : SchwartzNPoint d (k + 1) →+ ℂ :=
    { toFun := fun f => f x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hterm :
      (∑ a : D.index, D.piece a χ) x =
        ∑ a : D.index,
          D.cutoff a (initialBaseTimeProjectionCLM d k x) *
            initialReducedSpatialFullSourceCLM (d := d) φ χ x := by
    calc
      (∑ a : D.index, D.piece a χ) x =
          ev (∑ a : D.index, D.piece a χ) := rfl
      _ = ∑ a : D.index, ev (D.piece a χ) := by
        rw [map_sum]
      _ = ∑ a : D.index,
          D.cutoff a (initialBaseTimeProjectionCLM d k x) *
            initialReducedSpatialFullSourceCLM (d := d) φ χ x := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact D.piece_apply_point a χ x
  by_cases hx :
      x ∈ tsupport
        ((initialReducedSpatialFullSourceCLM (d := d) φ χ :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ)
  · have hfootprint :
        initialBaseTimeProjectionCLM d k x ∈
          initialBaseTimeFootprint (d := d) φ :=
      initialBaseTimeProjection_mem_footprint_of_mem_source
        φ χ x hx
    rw [ContinuousLinearMap.sum_apply]
    rw [hterm]
    rw [← Finset.sum_mul]
    rw [D.cutoff_sum _ hfootprint]
    simp
  · have hzero :
        initialReducedSpatialFullSourceCLM (d := d) φ χ x = 0 :=
      image_eq_zero_of_notMem_tsupport hx
    rw [ContinuousLinearMap.sum_apply]
    rw [hterm]
    rw [hzero]
    simp

end InitialBaseTimePartitionData

namespace InitialBaseTimeCarrierPartitionData

variable {timeCarrier : Set (Fin k → ℝ)}

instance (D :
    InitialBaseTimeCarrierPartitionData (d := d) timeCarrier) :
    Fintype D.index :=
  D.indexFintype

/-- A carrier partition specializes to every reduced-time Schwartz test whose
topological support lies in the chosen carrier.  The finite partition data are
retained definitionally. -/
noncomputable def toInitialBaseTimePartitionData
    (D : InitialBaseTimeCarrierPartitionData (d := d) timeCarrier)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ : tsupport (φ : (Fin k → ℝ) → ℂ) ⊆ timeCarrier) :
    InitialBaseTimePartitionData (d := d) φ where
  index := D.index
  indexFintype := D.indexFintype
  center := D.center
  center_ordered := D.center_ordered
  cutoff := D.cutoff
  cutoff_compact := D.cutoff_compact
  cutoff_support := D.cutoff_support
  cutoff_sum := by
    intro p hp
    exact D.cutoff_sum p ⟨hp.1, hφ hp.2⟩

@[simp] theorem toInitialBaseTimePartitionData_index
    (D : InitialBaseTimeCarrierPartitionData (d := d) timeCarrier)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ : tsupport (φ : (Fin k → ℝ) → ℂ) ⊆ timeCarrier) :
    (D.toInitialBaseTimePartitionData φ hφ).index = D.index :=
  rfl

@[simp] theorem toInitialBaseTimePartitionData_center
    (D : InitialBaseTimeCarrierPartitionData (d := d) timeCarrier)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ : tsupport (φ : (Fin k → ℝ) → ℂ) ⊆ timeCarrier)
    (a : D.index) :
    (D.toInitialBaseTimePartitionData φ hφ).center a = D.center a :=
  rfl

@[simp] theorem toInitialBaseTimePartitionData_cutoff
    (D : InitialBaseTimeCarrierPartitionData (d := d) timeCarrier)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ : tsupport (φ : (Fin k → ℝ) → ℂ) ⊆ timeCarrier)
    (a : D.index) :
    (D.toInitialBaseTimePartitionData φ hφ).cutoff a = D.cutoff a :=
  rfl

end InitialBaseTimeCarrierPartitionData

/-- Every compact strict-positive reduced-time carrier admits one finite
base/time chronological partition which can then be reused for all time tests
supported in that carrier. -/
theorem nonempty_initialBaseTimeCarrierPartitionData
    (timeCarrier : Set (Fin k → ℝ))
    (hcompact : IsCompact timeCarrier)
    (hpositive :
      timeCarrier ⊆ section43TimeStrictPositiveRegion k) :
    Nonempty
      (InitialBaseTimeCarrierPartitionData
        (d := d) timeCarrier) := by
  let K : Set (InitialBaseTimeSpace d k) :=
    initialBaseTimeCarrierFootprint (d := d) timeCarrier
  have hK_compact : IsCompact K :=
    (BHW.normalizedCutoffOfBump_hasCompactSupport d).isCompact.prod
      hcompact
  obtain ⟨R, hKR⟩ :=
    hK_compact.isBounded.subset_closedBall
      (0 : InitialBaseTimeSpace d k)
  let B : ℝ := max R 0 + 1
  have hB_pos : 0 < B := by
    dsimp [B]
    linarith [le_max_right R 0]
  let orderedAt :
      ∀ y : K, ∀ i j : Fin (k + 1), i < j →
        initialBaseTimeConfigurationCLM d k y.1 i 0 <
          initialBaseTimeConfigurationCLM d k y.1 j 0 :=
    fun y =>
      initialBaseTimeConfiguration_strictMono
        (d := d) y.1 (hpositive y.2.2)
  let P :
      ∀ y : K,
        OSIIOrderedProductNeighborhood
          (initialBaseTimeConfigurationCLM d k y.1) :=
    fun y =>
      naturalChronologicalProductNeighborhood
        (initialBaseTimeConfigurationCLM d k y.1) (orderedAt y)
  let Vβ : K → Set (InitialBaseTimeSpace d k) := fun y =>
    {p |
      ∀ i : Fin (k + 1),
        initialBaseTimeConfigurationCLM d k p i ∈ (P y).cell i} ∩
      Metric.ball 0 B
  have hVβ_open : ∀ y : K, IsOpen (Vβ y) := by
    intro y
    apply IsOpen.inter
    · have hopen :
          IsOpen
            {x : NPointDomain d (k + 1) |
              ∀ i : Fin (k + 1), x i ∈ (P y).cell i} := by
          have hi :
              IsOpen
                (⋂ i : Fin (k + 1),
                  {x : NPointDomain d (k + 1) |
                    x i ∈ (P y).cell i}) :=
            isOpen_iInter_of_finite fun i =>
              (P y).cell_open i |>.preimage (continuous_apply i)
          convert hi using 1
          ext x
          simp
      exact hopen.preimage
        (initialBaseTimeConfigurationCLM d k).continuous
    · exact Metric.isOpen_ball
  have hK_cover : K ⊆ ⋃ y : K, Vβ y := by
    intro p hp
    refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    constructor
    · exact (P ⟨p, hp⟩).center_mem
    · have hpR : ‖p‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hKR hp
      have hpB : ‖p‖ < B := by
        dsimp [B]
        linarith [le_max_left R 0]
      simpa [Metric.mem_ball, dist_zero_right] using hpB
  obtain ⟨s, hscover⟩ :=
    hK_compact.elim_finite_subcover Vβ hVβ_open hK_cover
  let α := {y : K // y ∈ s}
  let V : α → Set (InitialBaseTimeSpace d k) := fun a => Vβ a.1
  letI : Fintype α := Fintype.ofFinite α
  have hV_open : ∀ a : α, IsOpen (V a) := by
    intro a
    exact hVβ_open a.1
  have hV_relcompact :
      ∀ a : α, ∃ c r, V a ⊆ Metric.closedBall c r := by
    intro a
    refine ⟨0, B, ?_⟩
    intro p hp
    exact Metric.ball_subset_closedBall hp.2
  have hcover : K ⊆ ⋃ a : α, V a := by
    intro p hp
    rcases Set.mem_iUnion₂.mp (hscover hp) with ⟨y, hys, hpy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hys⟩, hpy⟩
  obtain ⟨θ, hθ_compact, hθ_support, hθ_sum⟩ :=
    SCV.exists_finite_schwartz_partitionOfUnity_on_compact
      hK_compact hV_open hV_relcompact hcover
  exact
    ⟨{
      index := α
      indexFintype := inferInstance
      center := fun a => a.1.1
      center_ordered := fun a => orderedAt a.1
      cutoff := θ
      cutoff_compact := hθ_compact
      cutoff_support := by
        intro a p hp
        exact (hθ_support a hp).1
      cutoff_sum := hθ_sum }⟩

end OSIIChapterV
end OSReconstruction
