/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedBridgeBlocks
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketA0FieldBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairCompactSupport



















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

/-- Internal chronological translations of the exact rooted left block. The
shrinking root coordinate remains the distinguished head. -/
noncomputable def rootedLeftBlockTranslatedSpatialSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (x : Fin (i.n - 1) → ℝ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) ((i.n - 1) + 1) :=
  localPositiveTimeParameterTranslate
    (A.rootedLeftBlockSpatialSource R i N χ)
    (fun a : Fin (i.n - 1) =>
      chronologicalTimeSourceDirection (d := d) a)
    x

@[simp]
theorem rootedLeftBlockTranslatedSpatialSource_zero
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :
    A.rootedLeftBlockTranslatedSpatialSource R i N 0 χ =
      A.rootedLeftBlockSpatialSource R i N χ := by
  simp [rootedLeftBlockTranslatedSpatialSource]

/-- Internal chronological translations of the exact rooted right block. -/
noncomputable def rootedRightBlockTranslatedSpatialSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (x : Fin (i.m - 1) → ℝ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) ((i.m - 1) + 1) :=
  localPositiveTimeParameterTranslate
    (A.rootedRightBlockSpatialSource R i N χ)
    (fun a : Fin (i.m - 1) =>
      chronologicalTimeSourceDirection (d := d) a)
    x

@[simp]
theorem rootedRightBlockTranslatedSpatialSource_zero
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :
    A.rootedRightBlockTranslatedSpatialSource R i N 0 χ =
      A.rootedRightBlockSpatialSource R i N χ := by
  simp [rootedRightBlockTranslatedSpatialSource]

namespace RootedA0BlockRealTraceGramKernelData

end RootedA0BlockRealTraceGramKernelData

/-- Continuous translated fields obtained from the exact rooted Gram
representations. -/
structure RootedA0BlockContinuousTranslationData
    (OS : OsterwalderSchraderAxioms d)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I) where
  leftTailStart : GeneratorIndex k → ℕ
  rightTailStart : GeneratorIndex k → ℕ
  left :
    ∀ i,
      LocalReflectedA0ContinuousTranslationFieldData
        OS ((i.n - 1) + 1) (i.n - 1)
        (fun N x χ =>
          A.rootedLeftBlockTranslatedSpatialSource R i
            (N + leftTailStart i) x χ)
  right :
    ∀ i,
      LocalReflectedA0ContinuousTranslationFieldData
        OS ((i.m - 1) + 1) (i.m - 1)
        (fun N x χ =>
          A.rootedRightBlockTranslatedSpatialSource R i
            (N + rightTailStart i) x χ)

namespace RootedA0BlockContinuousTranslationRepresentationData

end RootedA0BlockContinuousTranslationRepresentationData

namespace RootedA0BlockRealTraceGramLimitData

end RootedA0BlockRealTraceGramLimitData

namespace RootedA0BlockRealTraceCauchyData

end RootedA0BlockRealTraceCauchyData

namespace RootedA0BlockContinuousTranslationData

end RootedA0BlockContinuousTranslationData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
