/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import Init
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOpenFieldRealEdge
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVProductBasepointMixedDeltaProducer
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSimultaneousStageLevel
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapDistributionHolomorphy
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketGeneratorBridge
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSimultaneousStageLevel
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialGrowth
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredGeneratedSpatialGrowth
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCoordinates
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOpenFieldScales
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTwoScaleAssembly

@[expose] public section

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

/-- The selected holomorphic packet-scale limit of one anchored spatial
Hilbert field. -/
noncomputable def fixedHeadAnchoredSpatialHilbertFieldLimit
    {q : ℕ}
    {J : Section43ProductTimeApproximateIdentity (q + 1)}
    {base : Fin (q + 1) → ℝ}
    {L : SimultaneousTimeContinuationStageLevel d}
    {B : AnchoredPacketTimeShellFamilyData (d := d) J base}
    (D : PositiveHeadUniversalAnchoredAtlasData L OS B)
    (χ : SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    (Fin (q + 1) → ℂ) → OSHilbertSpace OS :=
  Classical.choose
    ((D.toLocallyUniformPairwiseInnerLimitData_anchoredSpatial χ
      ).exists_holomorphicField
        (fun scale =>
          (D.generatedSpatialField_holomorphic scale χ).mono
            (fun _ hz => hz.1))
        D.spatialLinearDomain_open)

theorem fixedHeadAnchoredSpatialHilbertFieldLimit_locallyUniform
    {q : ℕ}
    {J : Section43ProductTimeApproximateIdentity (q + 1)}
    {base : Fin (q + 1) → ℝ}
    {L : SimultaneousTimeContinuationStageLevel d}
    {B : AnchoredPacketTimeShellFamilyData (d := d) J base}
    (D : PositiveHeadUniversalAnchoredAtlasData L OS B)
    (χ : SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    TendstoLocallyUniformlyOn
      (fun scale z =>
        D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (B.positiveHeadSpatialAnchoredSourceCLM scale χ) z)
      (fixedHeadAnchoredSpatialHilbertFieldLimit D χ)
      atTop
      D.spatialLinearDomain :=
  (Classical.choose_spec
    ((D.toLocallyUniformPairwiseInnerLimitData_anchoredSpatial χ
      ).exists_holomorphicField
        (fun scale =>
          (D.generatedSpatialField_holomorphic scale χ).mono
            (fun _ hz => hz.1))
        D.spatialLinearDomain_open)).1

theorem fixedHeadAnchoredSpatialHilbertFieldLimit_holomorphic
    {q : ℕ}
    {J : Section43ProductTimeApproximateIdentity (q + 1)}
    {base : Fin (q + 1) → ℝ}
    {L : SimultaneousTimeContinuationStageLevel d}
    {B : AnchoredPacketTimeShellFamilyData (d := d) J base}
    (D : PositiveHeadUniversalAnchoredAtlasData L OS B)
    (χ : SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    DifferentiableOn ℂ
      (fixedHeadAnchoredSpatialHilbertFieldLimit D χ)
      D.spatialLinearDomain :=
  (Classical.choose_spec
    ((D.toLocallyUniformPairwiseInnerLimitData_anchoredSpatial χ
      ).exists_holomorphicField
        (fun scale =>
          (D.generatedSpatialField_holomorphic scale χ).mono
            (fun _ hz => hz.1))
        D.spatialLinearDomain_open)).2

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
