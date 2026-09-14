/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicStagePushforward
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientAmbientFullTube
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILocalTimeStageGluing



















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace CanonicalReducedCompactStageEdgeData

variable
  {d k : Nat} [NeZero d]
  {OS : OsterwalderSchraderAxioms d}
  {A B : OSIITimeContinuationStage d k}
  {compactCarrier : Set (Fin k -> Real)}

/-- Canonical compact-edge data transfers across an arbitrary honest stage
extension. -/
noncomputable def ofEqOnExtension
    (E :
      CanonicalReducedCompactStageEdgeData
        OS A compactCarrier)
    (hcarrier : A.carrier ⊆ B.carrier)
    (hextends :
      Set.EqOn B.distribution A.distribution A.carrier) :
    CanonicalReducedCompactStageEdgeData
      OS B compactCarrier where
  cutoff := E.cutoff
  cutoff_support := E.cutoff_support
  cutoff_compact := E.cutoff_compact
  realRegion := E.realRegion
  realRegion_open := E.realRegion_open
  compactCarrier_subset := E.compactCarrier_subset
  cutoff_one_on := E.cutoff_one_on
  edge := E.edge.ofEqOnExtension hcarrier hextends

end CanonicalReducedCompactStageEdgeData

/-- The canonical compact-edge invariant transfers across an arbitrary honest
stage extension. -/
theorem hasCanonicalReducedCompactStageEdges_of_eqOn_extension
    {d k : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {A B : OSIITimeContinuationStage d k}
    (H : HasCanonicalReducedCompactStageEdges OS A)
    (hcarrier : A.carrier ⊆ B.carrier)
    (hextends :
      Set.EqOn B.distribution A.distribution A.carrier) :
    HasCanonicalReducedCompactStageEdges OS B := by
  intro compactCarrier hcompact hpositive
  obtain ⟨E⟩ := H compactCarrier hcompact hpositive
  exact
    ⟨E.ofEqOnExtension hcarrier hextends⟩

namespace StrictScalarTargetAmbientLogarithmicStageLevelSuccessorData

variable
  {d : Nat} [NeZero d]
  {current : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {depth : Nat}
  {D :
    GeneratedScalarSeedStageLevelSuccessorData
      current OS depth}

end StrictScalarTargetAmbientLogarithmicStageLevelSuccessorData

namespace StrictGeneratedScalarStageLevelSuccessorData

variable
  {d : Nat} [NeZero d]
  {current : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {depth : Nat}

end StrictGeneratedScalarStageLevelSuccessorData

end OSIIChapterV
end OSReconstruction
