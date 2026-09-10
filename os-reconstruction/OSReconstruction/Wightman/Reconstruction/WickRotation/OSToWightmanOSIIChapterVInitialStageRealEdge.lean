/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingSliceBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapTimeStage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeSpatialCurrying
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- The spatial-distribution-valued real orbit obtained by localizing the
canonical reduced-spatial source and evaluating the OS Schwinger functional. -/
noncomputable def initialLocalizedSpatialOrbit
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    OSIISpatialDistribution d k :=
  ((OsterwalderSchraderAxioms.schwingerCLM
      (d := d) OS (k + 1)).comp
    (F.sourcewiseLocalizedTranslatedFullZeroCLM
      T hT hordered x)).comp
    (initialReducedSpatialFullSourceCLM (d := d) φ)

@[simp] theorem initialLocalizedSpatialOrbit_apply
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    initialLocalizedSpatialOrbit F OS T hT hordered φ x χ =
      OS.S (k + 1)
        (F.sourcewiseLocalizedTranslatedFullZeroCLM
          T hT hordered x
          (initialReducedSpatialFullSourceCLM (d := d) φ χ)) :=
  rfl

/-- The translated time-smearing of the ordered canonical reduced
distribution is the absolute Schwinger value of the corresponding normalized
basepoint lift whenever the canonical time cutoff fixes that lift. -/
theorem canonicalTranslatedTimeSmearedSpatialDistribution_apply_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (η : SchwartzMap (Fin k → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k)
    (τ : Fin k → ℝ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hzero :
      VanishesToInfiniteOrderOnCoincidence
        (initialReducedSpatialFullSourceCLM (d := d)
          (SCV.translateSchwartz (-τ) φ) χ))
    (hcutoff :
      SchwartzMap.smulLeftCLM ℂ
          (reducedTimeCutoffWeight (d := d) η)
          (initialReducedSpatialFullSourceCLM (d := d)
            (SCV.translateSchwartz (-τ) φ) χ) =
        initialReducedSpatialFullSourceCLM (d := d)
          (SCV.translateSchwartz (-τ) φ) χ) :
    osiiTranslatedTimeSmearedSpatialDistribution
        (orderedTransportDistribution
          (canonicalReducedTimeCutoffSchwingerCLM OS η hη))
        φ τ χ =
      OS.S (k + 1)
        ⟨initialReducedSpatialFullSourceCLM (d := d)
            (SCV.translateSchwartz (-τ) φ) χ,
          hzero⟩ := by
  rw [osiiTranslatedTimeSmearedSpatialDistribution_apply]
  change
    orderedTransportDistribution
        (canonicalReducedTimeCutoffSchwingerCLM OS η hη)
        (section43OrderedPullbackTimeSpatialTensorCLM d k χ
          (SCV.translateSchwartz (-τ) φ)) =
      _
  rw [orderedTransportDistribution_orderedPullbackTimeSpatialTensor]
  rw [←
    canonicalReducedTimeCutoffSchwingerCLM_apply_diffVarReduction_eq_of_cutoff
      OS η hη
        (initialReducedSpatialFullSourceCLM (d := d)
          (SCV.translateSchwartz (-τ) φ) χ)
        hzero hcutoff]
  apply congrArg
    (canonicalReducedTimeCutoffSchwingerCLM OS η hη)
  simpa [initialReducedSpatialFullSourceCLM] using
    (diffVarReduction_reducedTestLift
      (BHW.normalizedCutoffOfBump d)
      (section43NPointTimeSpatialTensor d k
        (SCV.translateSchwartz (-τ) φ) χ)).symm

end OSIIChapterV
end OSReconstruction
