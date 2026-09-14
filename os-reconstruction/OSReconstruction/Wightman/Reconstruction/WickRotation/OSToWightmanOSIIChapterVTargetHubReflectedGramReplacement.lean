/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTargetHubAnchoredAtlas
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRealization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTargetAdaptedMovingSliceCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniversalCompactCarrierAnchoredAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain











noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

namespace TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData

variable
  {C : Type*}
  [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {depth q : ℕ}
  {K : Set (Fin ((q + 1) + 1) → ℝ)}
  {anchor hub : Fin ((q + 1) + 1) → ℝ}
  {z : Fin (q + 1) → ℂ}

end TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData

/-- One universal atlas adapted to two target-and-hub requests over the same
compact source carrier. -/
structure PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
    {q : ℕ}
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (K : Set (Fin ((q + 1) + 1) → ℝ))
    (anchor₁ hub₁ : Fin ((q + 1) + 1) → ℝ)
    (z₁ : Fin (q + 1) → ℂ)
    (anchor₂ hub₂ : Fin ((q + 1) + 1) → ℝ)
    (z₂ : Fin (q + 1) → ℂ) where
  atlas : UniversalCompactCarrierAnchoredAtlasData L OS K
  firstRegion :
    TailAnchorTargetHubBoxTimeRegionData
      (L.reflectedPairStage (q := q)) anchor₁ hub₁ z₁
      (reflectedChronologicalGapCarrier (q + 1) K)
  secondRegion :
    TailAnchorTargetHubBoxTimeRegionData
      (L.reflectedPairStage (q := q)) anchor₂ hub₂ z₂
      (reflectedChronologicalGapCarrier (q + 1) K)
  cutoff_support_first :
    tsupport
        (atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ) ⊆
      firstRegion.region
  cutoff_support_second :
    tsupport
        (atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ) ⊆
      secondRegion.region

namespace PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData

variable
  {q : ℕ}
  {L : SimultaneousTimeContinuationStageLevel d}
  {K : Set (Fin ((q + 1) + 1) → ℝ)}
  {anchor₁ hub₁ : Fin ((q + 1) + 1) → ℝ}
  {z₁ : Fin (q + 1) → ℂ}
  {anchor₂ hub₂ : Fin ((q + 1) + 1) → ℝ}
  {z₂ : Fin (q + 1) → ℂ}

/-- View the common atlas through its first target-and-hub request. -/
noncomputable def first
    (D :
      PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor₁ hub₁ z₁ anchor₂ hub₂ z₂) :
    TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      L OS K anchor₁ hub₁ z₁ where
  atlas := D.atlas
  boxRegion := D.firstRegion
  cutoff_support_region := D.cutoff_support_first

/-- View the common atlas through its second target-and-hub request. -/
noncomputable def second
    (D :
      PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
        L OS K anchor₁ hub₁ z₁ anchor₂ hub₂ z₂) :
    TargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData
      L OS K anchor₂ hub₂ z₂ where
  atlas := D.atlas
  boxRegion := D.secondRegion
  cutoff_support_region := D.cutoff_support_second

end PairTargetHubAdaptedUniversalCompactCarrierAnchoredAtlasData

namespace StageWideGeneratedMixedReflectedGramData

variable
  {C : Type*}
  [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {depth : ℕ}

end StageWideGeneratedMixedReflectedGramData

end OSIIChapterV
end OSReconstruction
