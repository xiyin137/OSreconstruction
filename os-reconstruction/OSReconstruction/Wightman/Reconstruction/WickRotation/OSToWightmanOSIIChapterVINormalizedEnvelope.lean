/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621NormalizedFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarPhysicalCharts
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]

/-- A stage-wide bounded realization of the normalized equation-`(6.21)`
family at one fixed positive shift.  The bound may depend on both arity and
the spatial Schwartz test; this dependence is essential for the later
finite-seminorm estimate. -/
structure VI2NormalizedEnvelopeFamilyData
    (S : SimultaneousTimeContinuationStageLevel d)
    (t : Nat) (epsilon : Real)
    (bound : forall k,
      SchwartzMap (Section43SpatialSpace d k) Complex -> Real) where
  epsilon_pos : 0 < epsilon
  realization : forall k chi,
    BoundedScalarPhysicalRealizationData
      ((S.stage k).vi2NormalizedStage t epsilon)
      chi (bound k chi)

namespace VI2NormalizedEnvelopeFamilyData

variable
  {S : SimultaneousTimeContinuationStageLevel d}
  {t : Nat} {epsilon : Real}
  {bound : forall k,
    SchwartzMap (Section43SpatialSpace d k) Complex -> Real}

end VI2NormalizedEnvelopeFamilyData

/-- Coverage of a specified logarithmic target family by one normalized
envelope.  The target is deliberately external: rank stages, depth stages,
and the final recursive sectors have different geometric roles. -/
structure VI2NormalizedEnvelopeCoverageData
    {S : SimultaneousTimeContinuationStageLevel d}
    {t : Nat} {epsilon : Real}
    {bound : forall k,
      SchwartzMap (Section43SpatialSpace d k) Complex -> Real}
    (D : VI2NormalizedEnvelopeFamilyData S t epsilon bound)
    (target : forall k, Set (Fin k -> Complex)) : Prop where
  target_subset : forall k chi,
    target k ⊆ (D.realization k chi).continuation.carrier

namespace VI2NormalizedEnvelopeStageCoverageData

variable
  {S : SimultaneousTimeContinuationStageLevel d}
  {t : Nat} {epsilon : Real}
  {bound : forall k,
    SchwartzMap (Section43SpatialSpace d k) Complex -> Real}
  {D : VI2NormalizedEnvelopeFamilyData S t epsilon bound}

end VI2NormalizedEnvelopeStageCoverageData

namespace VI2NormalizedEnvelopeCoverageData

variable
  {S : SimultaneousTimeContinuationStageLevel d}
  {t : Nat} {epsilon : Real}
  {bound : forall k,
    SchwartzMap (Section43SpatialSpace d k) Complex -> Real}
  {D : VI2NormalizedEnvelopeFamilyData S t epsilon bound}
  {target : forall k, Set (Fin k -> Complex)}

end VI2NormalizedEnvelopeCoverageData

namespace StrictGeneratedScalarDepthPointedData

variable {OS : OsterwalderSchraderAxioms d}
variable {depth : Nat}

end StrictGeneratedScalarDepthPointedData

end OSIIChapterV
end OSReconstruction
