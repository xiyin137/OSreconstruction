/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumTailField










noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace PositiveHeadUniversalAnchoredAtlasData

variable {d q : ℕ} [NeZero d]
variable
  {I : Section43ProductTimeApproximateIdentity (q + 1)}
  {anchor : Fin (q + 1) → ℝ}
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}

/-- The vacuum-tail limit stage has its represented limiting orbit on the
common real germ. -/
theorem vacuumTailLimitStage_hasPositiveRealEdge
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) :
    D.vacuumTailLimitStage.HasPositiveRealEdge
      (fun u =>
        D.vacuumTailLimitSpatialDistribution (SCV.realToComplex u))
      (D.vacuumTailRealRegion C) := by
  intro u hu
  constructor
  · change SCV.realToComplex u ∈ D.spatialLinearDomain
    exact D.initialGramPolydisc_subset_spatialLinearDomain hu.1.1.2
  · rfl

end PositiveHeadUniversalAnchoredAtlasData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
