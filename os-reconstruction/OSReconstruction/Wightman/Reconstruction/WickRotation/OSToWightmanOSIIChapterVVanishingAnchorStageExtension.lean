/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAngleExhaustion
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageAffineTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageConvexAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicArgumentDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageExtension
import OSReconstruction.SCV.DistributionalRepresentationUniqueness
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.SCV.LocallyUniformDistributionRepresentation
import OSReconstruction.SCV.EuclideanWeylFrechet
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredOrderedTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdgeUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVExhaustingCarrierNormalFamily

















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A relatively compact open convex core inside `U` containing two
prescribed points. -/
structure RelativelyCompactConvexCoreData
    {k : ℕ}
    (U : Set (OSIITimeGapSpace k))
    (x y : OSIITimeGapSpace k) where
  carrier : Set (OSIITimeGapSpace k)
  carrier_open : IsOpen carrier
  carrier_convex : Convex ℝ carrier
  carrier_closure_compact : IsCompact (closure carrier)
  carrier_closure_subset : closure carrier ⊆ U
  left_mem : x ∈ carrier
  right_mem : y ∈ carrier

namespace RelativelyCompactConvexCoreData

/-- A compact segment contained in an open finite-dimensional domain admits a
relatively compact open convex thickening inside that domain. -/
theorem nonempty_of_segment_subset_open
    {k : ℕ}
    {U : Set (OSIITimeGapSpace k)}
    {x y : OSIITimeGapSpace k}
    (hU_open : IsOpen U)
    (hsegment : segment ℝ x y ⊆ U) :
    Nonempty (RelativelyCompactConvexCoreData U x y) := by
  let K : Set (OSIITimeGapSpace k) := segment ℝ x y
  have hK_compact : IsCompact K := by
    dsimp [K]
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨r, hr_pos, hr_subset⟩ :=
    hK_compact.exists_cthickening_subset_open
      hU_open hsegment
  let s : ℝ := r / 2
  have hs_pos : 0 < s := half_pos hr_pos
  have hs_le : s ≤ r := by
    dsimp [s]
    linarith
  refine
    ⟨{
      carrier := Metric.thickening s K
      carrier_open := Metric.isOpen_thickening
      carrier_convex := (convex_segment x y).thickening s
      carrier_closure_compact := ?_
      carrier_closure_subset := ?_
      left_mem :=
        Metric.self_subset_thickening hs_pos K
          (left_mem_segment ℝ x y)
      right_mem :=
        Metric.self_subset_thickening hs_pos K
          (right_mem_segment ℝ x y) }⟩
  · exact
      IsCompact.of_isClosed_subset
        (hK_compact.cthickening)
        isClosed_closure
        (Metric.closure_thickening_subset_cthickening s K)
  · exact
      (Metric.closure_thickening_subset_cthickening s K).trans
        ((Metric.cthickening_mono hs_le K).trans hr_subset)

/-- Select a relatively compact convex core from a segment inclusion in an
open ambient domain. -/
noncomputable def selectedOfSegmentSubsetOpen
    {k : ℕ}
    {U : Set (OSIITimeGapSpace k)}
    {x y : OSIITimeGapSpace k}
    (hU_open : IsOpen U)
    (hsegment : segment ℝ x y ⊆ U) :
    RelativelyCompactConvexCoreData U x y :=
  Classical.choice
    (nonempty_of_segment_subset_open hU_open hsegment)

end RelativelyCompactConvexCoreData

namespace GeneratorStageExtensionData

variable {d k : ℕ}
  {A : OSIITimeContinuationStage d k}

end GeneratorStageExtensionData

namespace VanishingAnchorCenteredExtensionChartData

variable {d k : ℕ}
  {predecessor : OSIITimeContinuationStage d k}

end VanishingAnchorCenteredExtensionChartData

namespace GeneratorStageExtensionNormalFamilyAtlasData

variable {d k : ℕ} [NeZero d]
  {ι : Type*}

end GeneratorStageExtensionNormalFamilyAtlasData

end OSIIChapterV
end OSReconstruction
