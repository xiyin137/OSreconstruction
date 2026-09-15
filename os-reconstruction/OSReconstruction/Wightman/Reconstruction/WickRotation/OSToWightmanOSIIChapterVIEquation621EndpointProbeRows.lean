/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedSourceAnchorCutoff
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialSmoothingVitali
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetAdaptedFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621EndpointRootedSourceIntegral











noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace OneParticleTranslatedMixedDeltaPredecessorData

variable {d : Nat} [NeZero d]
variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity 1}
  {tau : Fin 1 -> Real}
  {htau : tau ∈ section43TimeStrictPositiveRegion 1}

/-- The one-particle predecessor cutoff is one at the reflected pair of its
packet anchor. -/
theorem cutoff_eq_one_at_translatedSourceAnchor
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I tau htau) :
    D.germ.η
        (osiiMixedBlockGlobalReducedTime 0 (Fin.append tau tau)) = 1 := by
  exact
    UniformCompactTimeMixedReflectedSourceFamilyData.cutoff_eq_one_at_translatedSourceAnchor
      (r := 0)
      (f := fun p : Nat × SchwartzMap (Section43SpatialSpace d 1) Complex =>
        I.translatedPositiveTimeSpatialSource
          tau htau p.2 (p.1 + D.tailStart))
      D.germ I tau htau (fun scale chi => (scale, chi)) D.tailStart
      (by
        intro scale chi
        rfl)

/-- A cofinal diagonal of the one-particle pairwise Gram family converges to
the common moving-kernel center. -/
theorem tendsto_inner_field_add_to_centerValue
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I tau htau)
    (chi : SchwartzMap (Section43SpatialSpace d 1) Complex)
    (tail : Nat) :
    Tendsto
      (fun N => @inner Complex (OSHilbertSpace OS) _
        (D.field chi (N + tail) 0) (D.field chi (N + tail) 0))
      atTop (nhds (D.centerValue chi 0)) := by
  let G :=
    (D.toLocallyCompactTensorPairGramRepresentationData chi
      ).toLocallyUniformPairwiseInnerLimitData
  obtain ⟨V, hV, hinner⟩ := G.locallyUniform 0 (Set.mem_univ 0)
  have hzero : (0 : Fin 0 -> Complex) ∈ V :=
    mem_of_mem_nhdsWithin (Set.mem_univ 0) hV
  have hpair := hinner.tendsto_at hzero
  have hcofinal : Tendsto (fun N : Nat => (N + tail, N + tail))
      atTop atTop :=
    tendsto_atTop_diagonal.comp (tendsto_add_atTop_nat tail)
  convert hpair.comp hcofinal using 1 <;> rfl

/-- The one-particle moving-kernel center is the represented stage evaluated
at the physical reflected anchor and the exact mixed spatial marginal. -/
theorem centerValue_eq_distribution_at_anchor
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I tau htau)
    (chi : SchwartzMap (Section43SpatialSpace d 1) Complex) :
    D.centerValue chi 0 =
      (L.stage 1).distribution
        (equation621ReflectedMovingSlicePoint
          (0 : Fin (0 + 0) -> Complex)
          (osiiMixedBlockGlobalReducedTime 0 (Fin.append tau tau)))
        (osiiMixedSpatialHeadMarginal chi chi) := by
  let sigma := osiiMixedBlockGlobalReducedTime 0 (Fin.append tau tau)
  have hcutoff : D.germ.η sigma = 1 := by
    simpa only [sigma] using D.cutoff_eq_one_at_translatedSourceAnchor
  have hsigma_support : sigma ∈
      tsupport (D.germ.η : (Fin 1 -> Real) -> Complex) := by
    apply subset_tsupport
    change D.germ.η sigma ≠ 0
    rw [hcutoff]
    exact one_ne_zero
  have hsigma_region : sigma ∈ D.realRegion :=
    D.cutoff_support hsigma_support
  have hedge := (D.edge.stageEdge sigma hsigma_region).2
  rw [D.centerValue_eq_centerA0Value]
  change D.germ.η sigma *
      D.edge.orbit sigma (osiiMixedSpatialHeadMarginal chi chi) = _
  rw [hcutoff, one_mul, ← hedge]
  simp [sigma, equation621ReflectedMovingSlicePoint]

/-- The cofinal one-particle diagonal row converges directly to the represented
arity-one lower stage. -/
theorem tendsto_inner_field_add_to_distribution_at_anchor
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I tau htau)
    (chi : SchwartzMap (Section43SpatialSpace d 1) Complex)
    (tail : Nat) :
    Tendsto
      (fun N => @inner Complex (OSHilbertSpace OS) _
        (D.field chi (N + tail) 0) (D.field chi (N + tail) 0))
      atTop
      (nhds ((L.stage 1).distribution
        (equation621ReflectedMovingSlicePoint
          (0 : Fin (0 + 0) -> Complex)
          (osiiMixedBlockGlobalReducedTime 0 (Fin.append tau tau)))
        (osiiMixedSpatialHeadMarginal chi chi))) := by
  rw [← D.centerValue_eq_distribution_at_anchor chi]
  exact D.tendsto_inner_field_add_to_centerValue chi tail

end OneParticleTranslatedMixedDeltaPredecessorData

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedA0BlockContinuousTranslationData

variable {d k : Nat} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
