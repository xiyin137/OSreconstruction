/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniversalCompactCarrierAnchoredAtlas











noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace UniformCompactTimeMixedHilbertGramFamilyData

variable {d q : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {K : Set (Fin ((q + 1) + 1) -> Real)}

/-- A prescribed diagonal scalar bound controls the squared norm of the
production globally anchored Hilbert field at that point. -/
theorem norm_anchoredAtlasField_sq_le_of_scalar_diagonal_bound
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (B : Real)
    (a : AnchoredSourceIndex d q K)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ)
    (hdiagonal :
      norm ((G.cauchy a a).scalar
        (reflectedCauchyCenter z)) <= B) :
    norm (G.anchoredAtlasField stage germ a z) ^ 2 <= B := by
  rw [G.anchoredAtlasField_norm_sq_eq_scalar_re
    stage germ a z hz]
  exact (Complex.re_le_norm _).trans hdiagonal

end UniformCompactTimeMixedHilbertGramFamilyData

namespace UniversalCompactCarrierAnchoredAtlasData

variable {d q : Nat} [NeZero d]
variable {L : SimultaneousTimeContinuationStageLevel d}
variable {OS : OsterwalderSchraderAxioms d}
variable {K : Set (Fin ((q + 1) + 1) -> Real)}

/-- A diagonal scalar bound controls the squared norm of the concrete
source-linear spatial field with the same numerical constant. -/
theorem norm_spatialFieldCLM_sq_le_of_scalar_diagonal_bound
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (sourceCLM :
      Nat ->
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) Complex →L[Complex]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (scale : Nat)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ D.spatialLinearDomain)
    (test : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (B : Real)
    (hdiagonal :
      norm ((D.gram.cauchy
        (sourceCLM scale test)
        (sourceCLM scale test)).scalar
          (reflectedCauchyCenter z)) <= B) :
    norm (D.spatialFieldCLM sourceCLM scale z hz test) ^ 2 <= B := by
  rw [D.spatialFieldCLM_apply]
  exact
    D.gram.norm_anchoredAtlasField_sq_le_of_scalar_diagonal_bound
      D.sourceStage.stage D.sourceStage.germ B
      (sourceCLM scale test) z hz.1 hdiagonal

end UniversalCompactCarrierAnchoredAtlasData
end OSIIChapterV
end OSReconstruction
