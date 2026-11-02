/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import Init
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation629Majorant
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeometry
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarPhysicalCharts
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction

@[expose] public section

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

namespace StrictGeneratedScalarRankPointedInductionData

variable {depth rank : Nat}

end StrictGeneratedScalarRankPointedInductionData

namespace StrictGeneratedScalarDepthPointedData

variable {depth : Nat}

/-- The finite target-rank induction stage used by the quantitative sector
argument. -/
noncomputable def recursiveSectorRankInduction
    (D : StrictGeneratedScalarDepthPointedData OS depth)
    (lgc : OSLinearGrowthCondition d OS)
    (rank : Nat) :
    StrictGeneratedScalarRankPointedInductionData OS depth rank :=
  D.pointed.scalarRankInduction
    depth D.strictGeneratedCarrier_subset lgc rank

end StrictGeneratedScalarDepthPointedData

end OSIIChapterV
end OSReconstruction
