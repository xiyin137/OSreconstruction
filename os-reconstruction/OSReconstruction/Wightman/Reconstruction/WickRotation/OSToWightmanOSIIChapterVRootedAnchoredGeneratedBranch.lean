/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredSpatialSmearing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedTwoScaleFamily
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTwoScaleAssembly
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBranchGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedLogarithmicDomains














noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}

omit [NeZero k] in
/-- The reflected-left block of a chronological generator target lies in the
principal-argument fiber prescribed by the generated mixed vector. -/
theorem star_generatorChronological_split_left_mem_argumentCarrier
    (i : GeneratorIndex k)
    (left : Fin i.n → ℝ)
    (θ : ℝ)
    (right : Fin i.m → ℝ)
    {w : OSIITimeGapSpace k}
    (hw :
      w ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left θ right} :
          Set (Fin k → ℝ))) :
    star
        (i.splitCoordinatesCLM
          (generatorChronologicalParameterComplexCLE i w)).2.1 ∈
      osiiTimeArgumentCarrier
        ({osiiMixedArgumentTail left} :
          Set (Fin (i.n - 1) → ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro a
    change
      0 <
        (star
          ((i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i w)).2.1 a)).re
    rw [generatorChronological_split_left]
    simpa using hw.1 (i.leftGlobalIndex a)
  · rw [Set.mem_singleton_iff]
    funext a
    change
      Complex.arg
          (star
            ((i.splitCoordinatesCLM
              (generatorChronologicalParameterComplexCLE i w)).2.1 a)) =
        osiiMixedArgumentTail left a
    rw [generatorChronological_split_left]
    change
      Complex.arg ((starRingEnd ℂ) (w (i.leftGlobalIndex a))) =
        osiiMixedArgumentTail left a
    rw [Complex.arg_conj, if_neg]
    · have harg := congrFun
          (Set.mem_singleton_iff.mp hw.2) (i.leftGlobalIndex a)
      change
        Complex.arg (w (i.leftGlobalIndex a)) =
          osiiArgumentGeneratorPoint i left θ right
            (i.leftGlobalIndex a) at harg
      rw [osiiArgumentGeneratorPoint_left] at harg
      linarith
    · intro hpi
      have hneg := (Complex.arg_eq_pi_iff.mp hpi).1
      linarith [hw.1 (i.leftGlobalIndex a)]

omit [NeZero k] in
/-- The right block of a chronological generator target lies in the
principal-argument fiber prescribed by the generated mixed vector. -/
theorem generatorChronological_split_right_mem_argumentCarrier
    (i : GeneratorIndex k)
    (left : Fin i.n → ℝ)
    (θ : ℝ)
    (right : Fin i.m → ℝ)
    {w : OSIITimeGapSpace k}
    (hw :
      w ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left θ right} :
          Set (Fin k → ℝ))) :
    (i.splitCoordinatesCLM
        (generatorChronologicalParameterComplexCLE i w)).2.2 ∈
      osiiTimeArgumentCarrier
        ({osiiMixedArgumentTail right} :
          Set (Fin (i.m - 1) → ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro b
    rw [generatorChronological_split_right]
    exact hw.1 (i.rightGlobalIndex b)
  · rw [Set.mem_singleton_iff]
    funext b
    change
      Complex.arg
          ((i.splitCoordinatesCLM
            (generatorChronologicalParameterComplexCLE i w)).2.2 b) =
        osiiMixedArgumentTail right b
    rw [generatorChronological_split_right]
    have harg := congrFun
      (Set.mem_singleton_iff.mp hw.2) (i.rightGlobalIndex b)
    change
      Complex.arg (w (i.rightGlobalIndex b)) =
        osiiArgumentGeneratorPoint i left θ right
          (i.rightGlobalIndex b) at harg
    simpa using harg

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
