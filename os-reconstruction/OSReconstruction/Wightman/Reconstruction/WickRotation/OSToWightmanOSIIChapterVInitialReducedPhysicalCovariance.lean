/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapPhysicalDistribution
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapFullSourceRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialCompactStage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalStageEdgeInvariant














noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

namespace CanonicalReducedCompactCutoffData

end CanonicalReducedCompactCutoffData

/-- Reduced-time support of the translated chronological carrier itself.

This differs from `chronologicalCarrierReducedTimeFootprint`, which records
the untranslated source point seen underneath the translated carrier.  The
covariance theorem needs the reduced time of the translated source point. -/
def chronologicalTranslatedCarrierReducedTimeSupport
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    Set (Fin k → ℝ) :=
  reducedTimeProjectionCLM d k ''
    tsupport
      ((F.chronologicalTranslatedCarrier T x :
        SchwartzNPoint d (k + 1)) :
          NPointDomain d (k + 1) → ℂ)

namespace SpatialChronologicalCompactCoverData

variable
  {L :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1)}

end SpatialChronologicalCompactCoverData

/-- Support of a translated normalized lift projects into support of the
correspondingly translated reduced test. -/
theorem reducedDiff_mem_tsupport_translate_of_mem_translate_reducedTestLift
    (a : NPointDomain d (k + 1))
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d k)
    (x : NPointDomain d (k + 1))
    (hx :
      x ∈ tsupport
        ((translateSchwartzConfiguration a
            (BHW.reducedTestLift k d χ φ) :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ)) :
    BHW.reducedDiffMapRealCLM (k + 1) d x ∈
      tsupport
        ((translateSchwartzConfiguration
            (reducedConfigurationDisplacement a) φ :
          SchwartzNPoint d k) :
            NPointDomain d k → ℂ) := by
  let L : NPointDomain d (k + 1) →L[ℝ] NPointDomain d k :=
    BHW.reducedDiffMapRealCLM (k + 1) d
  rw [tsupport_translateSchwartzConfiguration_eq_preimage] at hx ⊢
  have hdiff :=
    reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
      χ φ hx
  change L (x + a) ∈ tsupport (φ : NPointDomain d k → ℂ) at hdiff
  change
    L x + reducedConfigurationDisplacement a ∈
      tsupport (φ : NPointDomain d k → ℂ)
  rw [← show L a = reducedConfigurationDisplacement a by
    rfl, ← L.map_add]
  exact hdiff

/-- A compact reduced-time carrier for the translated reduced probe controls
the reduced-time support of its translated normalized full lift. -/
theorem translatedReducedTestLift_reducedTimeSupport
    (a : NPointDomain d (k + 1))
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d k)
    {compactCarrier : Set (Fin k → ℝ)}
    (hcarrier :
      ∀ ξ ∈ tsupport
          ((translateSchwartzConfiguration
              (reducedConfigurationDisplacement a) φ :
            SchwartzNPoint d k) :
              NPointDomain d k → ℂ),
        section43QTime (d := d) (n := k) ξ ∈ compactCarrier) :
    ∀ x ∈ tsupport
        ((translateSchwartzConfiguration a
            (BHW.reducedTestLift k d χ φ) :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ),
      reducedTimeProjectionCLM d k x ∈ compactCarrier := by
  intro x hx
  have hdiff :=
    reducedDiff_mem_tsupport_translate_of_mem_translate_reducedTestLift
      a χ φ x hx
  exact hcarrier _ hdiff

namespace SpatialChronologicalCompactCoverData

variable
  {L :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1)}

end SpatialChronologicalCompactCoverData

end OSIIChapterV
end OSReconstruction
