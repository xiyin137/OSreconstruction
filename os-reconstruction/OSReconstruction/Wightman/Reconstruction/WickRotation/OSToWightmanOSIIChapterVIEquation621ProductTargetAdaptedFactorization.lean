/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetAdaptedFieldComparison
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialSmoothingVitali
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedSourceIntegral












noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k depth : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}

/-- The left reflected field parameter read from the target generator point. -/
def equation621TargetLeftParameter
    (i : GeneratorIndex k) (zeta : OSIITimeGapSpace k) :
    Fin (i.n - 1) -> Complex :=
  fun u => -star ((generatorChronologicalParameterComplexCLE i zeta)
    (i.leftGlobalIndex u))

/-- The right reflected field parameter read from the target generator point. -/
def equation621TargetRightParameter
    (i : GeneratorIndex k) (zeta : OSIITimeGapSpace k) :
    Fin (i.m - 1) -> Complex :=
  fun u => (generatorChronologicalParameterComplexCLE i zeta)
    (i.rightGlobalIndex u)

/-- The left parameter used by equation `(6.21)` is the canonical rooted
left block target. -/
@[simp] theorem equation621TargetLeftParameter_eq_rootedLeftBlockTarget
    (i : GeneratorIndex k) (zeta : OSIITimeGapSpace k) :
    equation621TargetLeftParameter i zeta =
      rootedLeftBlockTarget i zeta := by
  ext u
  simp [equation621TargetLeftParameter, rootedLeftBlockTarget]

/-- The right parameter used by equation `(6.21)` is the canonical rooted
right block target. -/
@[simp] theorem equation621TargetRightParameter_eq_rootedRightBlockTarget
    (i : GeneratorIndex k) (zeta : OSIITimeGapSpace k) :
    equation621TargetRightParameter i zeta =
      rootedRightBlockTarget i zeta := by
  ext u
  simp [equation621TargetRightParameter, rootedRightBlockTarget]

/-- The physical lower-stage point associated with the left reflected row. -/
def equation621TargetLeftTimePoint
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) (zeta : OSIITimeGapSpace k) :
    OSIITimeGapSpace ((i.n - 1) + ((i.n - 1) + 1)) :=
  equation621ReflectedMovingSlicePoint
    (reflectedCauchyCenter (equation621TargetLeftParameter i zeta))
    (osiiMixedBlockGlobalReducedTime (i.n - 1)
      (Fin.append (A.rootedLeftBlockAnchor i)
        (A.rootedLeftBlockAnchor i)))

/-- The physical lower-stage point associated with the right reflected row. -/
def equation621TargetRightTimePoint
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) (zeta : OSIITimeGapSpace k) :
    OSIITimeGapSpace ((i.m - 1) + ((i.m - 1) + 1)) :=
  equation621ReflectedMovingSlicePoint
    (reflectedCauchyCenter (equation621TargetRightParameter i zeta))
    (osiiMixedBlockGlobalReducedTime (i.m - 1)
      (Fin.append (A.rootedRightBlockAnchor i)
        (A.rootedRightBlockAnchor i)))

open OSIITimeContinuationLadderRealEdgeDensityGrowthData
open OSIITimeContinuationLadderRealEdgeDensityGrowthData.OSIIEquation621WeightedPositiveRealEdgeData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
