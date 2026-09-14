/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedScalarSeeds
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubDirectExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVPointedStageLevel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumTailTargetHubPointedExtension

















noncomputable section

open Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]

/-- A simultaneous successor which retains its predecessor and realizes the
complete primitive scalar seed base at one target depth. -/
structure GeneratedScalarSeedStageLevelSuccessorData
    (current : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (depth : Nat) where
  next : SimultaneousTimeContinuationStageLevel d
  carrier_subset :
    forall k, (current.stage k).carrier <= (next.stage k).carrier
  extendsOld :
    forall k,
      Set.EqOn
        (next.stage k).distribution
        (current.stage k).distribution
        (current.stage k).carrier
  canonicalEdges :
    next.HasCanonicalReducedCompactEdges OS
  scalarSeedMem :
    forall (k : Nat) (x : Fin k -> Real),
      OSIIGeneratedScalarSeed k depth x ->
      osiiTimeArgumentCarrier ({x} : Set (Fin k -> Real)) <=
        (next.stage k).carrier

namespace GeneratedScalarSeedStageLevelSuccessorData

variable
  {current : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {depth : Nat}

end GeneratedScalarSeedStageLevelSuccessorData

end OSIIChapterV
end OSReconstruction
