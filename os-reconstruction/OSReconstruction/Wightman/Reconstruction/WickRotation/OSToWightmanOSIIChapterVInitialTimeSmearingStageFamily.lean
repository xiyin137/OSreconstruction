/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalStageEdgeInvariant
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTimeSmearingRealEdge
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialFixedTimePacketCenteredMZ
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialFixedTimePacket
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialFactorExhaustion
import OSReconstruction.SCV.SchwartzComplete
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapFullSourceRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanE0FiniteSeminorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialStageRealEdge















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- A common-carrier family of initial stages indexed by shrinking
time-smearing scale. -/
structure InitialTimeSmearingStageFamilyData
    (OS : OsterwalderSchraderAxioms d)
    (I : Section43ProductTimeApproximateIdentity k)
    {compactCarrier : Set (Fin k → ℝ)}
    (C : CanonicalReducedCompactCutoffData compactCarrier)
    (realRegion : Set (Fin k → ℝ))
    (tailStart : ℕ)
    (η : ℝ) where
  realCompact : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  compactCarrier_subset_realRegion : compactCarrier ⊆ realRegion
  realRegion_subset_cutoffRegion : realRegion ⊆ C.realRegion
  realRegion_subset_realCompact : realRegion ⊆ realCompact
  realCompact_compact : IsCompact realCompact
  realCompact_positive :
    realCompact ⊆ section43TimeStrictPositiveRegion k
  stage : ℕ → OSIITimeContinuationStage d k
  carrier :
    ∀ N, (stage N).carrier = osiiNarrowTimeCarrier (k := k) η
  locallyPointwiseBounded :
    ∀ N,
      OSIIComplexTimeSpatialLocallyPointwiseBoundedOn
        (stage N).distribution
        (osiiNarrowTimeCarrier (k := k) η)
  edge :
    ∀ N,
      (stage N).HasPositiveRealEdge
        (fun τ =>
          osiiTranslatedTimeSmearedSpatialDistribution
            (orderedTransportDistribution
              (canonicalReducedTimeCutoffSchwingerCLM
                OS C.cutoff C.cutoff_support))
            (I.test (N + tailStart)) τ)
        realRegion

namespace InitialTimeSmearingStageFamilyData

variable
  {OS : OsterwalderSchraderAxioms d}
  {lgc : OSLinearGrowthCondition d OS}
  {I : Section43ProductTimeApproximateIdentity k}
  {compactCarrier : Set (Fin k → ℝ)}
  {C : CanonicalReducedCompactCutoffData compactCarrier}
  {realRegion : Set (Fin k → ℝ)}
  {tailStart : ℕ}
  {η : ℝ}
  {hη : 0 < η}
  {hηsum :
    (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
        Real.arctan η < Real.pi / 2}

/-- The exact normal-family estimate still needed to pass from the
fixed-smearing stages to one unsmeared holomorphic stage. -/
def ScaleUniformLocallyPointwiseBounded
    (F : InitialTimeSmearingStageFamilyData
      OS I C realRegion tailStart η) : Prop :=
  ∀ K : Set (OSIITimeGapSpace k),
    IsCompact K →
      K ⊆ osiiNarrowTimeCarrier (k := k) η →
        ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
          ∃ M : ℝ, ∀ N ζ, ζ ∈ K →
            ‖(F.stage N).distribution ζ χ‖ ≤ M

/-- Finite packet approximants for all smearing scales, together with one
compact bound uniform in both the packet level and the smearing scale. -/
structure ScaleUniformApproximationData
    (F : InitialTimeSmearingStageFamilyData
      OS I C realRegion tailStart η) where
  approximation :
    ℕ → ℕ → OSIITimeGapSpace k → OSIISpatialDistribution d k
  tendsto_stage :
    ∀ N ζ,
      ζ ∈ osiiNarrowTimeCarrier (k := k) η →
        ∀ χ,
          Tendsto
            (fun level => approximation N level ζ χ)
            atTop
            (nhds ((F.stage N).distribution ζ χ))
  compact_bound :
    ∀ K : Set (OSIITimeGapSpace k),
      IsCompact K →
        K ⊆ osiiNarrowTimeCarrier (k := k) η →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            ∃ M : ℝ, ∀ N level ζ, ζ ∈ K →
              ‖approximation N level ζ χ‖ ≤ M

namespace CanonicalPacketApproximationData

namespace ScaleUniformKernelRepresentationData

end ScaleUniformKernelRepresentationData

end CanonicalPacketApproximationData

namespace ScaleUniformApproximationData

/-- A bound uniform before taking the spatial packet limit remains uniform
after taking that limit at every time-smearing scale. -/
theorem scaleUniformLocallyPointwiseBounded
    {F : InitialTimeSmearingStageFamilyData
      OS I C realRegion tailStart η}
    (A : ScaleUniformApproximationData F) :
    F.ScaleUniformLocallyPointwiseBounded := by
  intro K hK_compact hK_subset χ
  obtain ⟨M, hM⟩ :=
    A.compact_bound K hK_compact hK_subset χ
  refine ⟨M, ?_⟩
  intro N ζ hζ
  have hnorm :
      Tendsto
        (fun level => ‖A.approximation N level ζ χ‖)
        atTop
        (nhds ‖(F.stage N).distribution ζ χ‖) := by
    simpa using
      Tendsto.norm (A.tendsto_stage N ζ (hK_subset hζ) χ)
  exact le_of_tendsto hnorm
    (Filter.Eventually.of_forall fun level => hM N level ζ hζ)

end ScaleUniformApproximationData

namespace CanonicalPacketApproximationData

end CanonicalPacketApproximationData

end InitialTimeSmearingStageFamilyData

end OSIIChapterV
end OSReconstruction
