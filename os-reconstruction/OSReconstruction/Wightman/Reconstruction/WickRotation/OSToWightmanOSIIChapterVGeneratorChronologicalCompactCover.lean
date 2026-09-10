/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorGlobalProfile
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairCompactSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.SCV.SchwartzFiniteSeminormBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVChronologicalCompactCover















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : Nat} [NeZero d] [NeZero k]

/-- A finite exact chronological decomposition of a continuous linear source
map from an arbitrary topological complex module.  This is the domain-agnostic
form of the older reduced-spatial cover data. -/
structure SourceChronologicalCompactCoverData
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module Complex E]
    (L : E →L[Complex] SchwartzNPoint d (k + 1)) where
  index : Type
  indexFintype : Fintype index
  piece : index -> E →L[Complex] SchwartzNPoint d (k + 1)
  carrier : index -> OSIIChronologicalCompactFactors d k
  sum_eq :
    L =
      (@Finset.univ index indexFintype).sum piece
  carrier_fix :
    ∀ a χ,
      SchwartzMap.smulLeftCLM Complex
          (SchwartzMap.productTensor (carrier a).factors)
          (piece a χ) =
        piece a χ

namespace SourceChronologicalCompactCoverData

variable
  {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module Complex E]
  {L : E →L[Complex] SchwartzNPoint d (k + 1)}

/-- One slope orders every carrier in a source-map cover in every signed
axis-pair frame. -/
def AxisPairOrderedAt
    (D : SourceChronologicalCompactCoverData L)
    (T : Real) : Prop :=
  ∀ a : D.index,
    ∀ b : osiiAxisPairIndex d,
      ∀ i j : Fin (k + 1), i < j ->
        ∀ y ∈ tsupport
            (((D.carrier a).factors i : SchwartzSpacetime d) :
              SpacetimeDim d -> Complex),
          ∀ z ∈ tsupport
              (((D.carrier a).factors j : SchwartzSpacetime d) :
                SpacetimeDim d -> Complex),
            ((osiiAxisPairRotationData T b).matrix.mulVec y) 0 <
              ((osiiAxisPairRotationData T b).matrix.mulVec z) 0

end SourceChronologicalCompactCoverData

namespace GeneratorHermiteHilbertFieldFamilyData

variable {OS : OsterwalderSchraderAxioms d}

end GeneratorHermiteHilbertFieldFamilyData
end OSIIChapterV
end OSReconstruction
