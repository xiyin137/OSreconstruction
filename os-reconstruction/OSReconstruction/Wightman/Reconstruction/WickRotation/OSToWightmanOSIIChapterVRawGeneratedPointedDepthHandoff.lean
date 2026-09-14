/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRawGeneratedRecursiveAngleDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction












noncomputable section

open Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

namespace StrictGeneratedScalarDepthPointedData

variable {depth : Nat}

/-- A pointed legacy depth stage realizes the raw scalar
carrier at the same depth. -/
theorem rawStrictGeneratedScalarCarrier_subset_stage
    (D : StrictGeneratedScalarDepthPointedData OS depth)
    (arity : Nat) :
    osiiTimeArgumentCarrier
        (osiiRawStrictGeneratedLogarithmicBase arity depth) ⊆
      (D.pointed.stageLevel.stage arity).carrier := by
  intro z hz
  exact
    D.strictGeneratedCarrier_subset arity
      ⟨hz.1,
        rawStrictGeneratedScalarBase_subset_strictGenerated
          arity depth hz.2⟩

end StrictGeneratedScalarDepthPointedData

end OSIIChapterV
end OSReconstruction
