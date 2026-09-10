import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedTransport

/-!
# Anchored ordered transport

This small foundational module records the translation of a reduced
difference-coordinate current to the ordered spacetime distribution centered
at a packet anchor.
-/

noncomputable section

open Complex

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

/-- The ordered distribution whose fixed-spatial time pairing is the common
chronological trace translated by the packet anchor. -/
noncomputable def anchoredOrderedTransportDistribution
    (L : SchwartzNPoint d k →L[ℂ] ℂ)
    (anchor : Fin k → ℝ) :
    SchwartzNPoint d k →L[ℂ] ℂ :=
  orderedTransportDistribution
    (L.comp
      (translateSchwartzConfigurationCLM
        (osiiDifferenceTimeTranslation (d := d) (-anchor))))

@[simp]
theorem anchoredOrderedTransportDistribution_orderedPullbackTimeSpatialTensor
    (L : SchwartzNPoint d k →L[ℂ] ℂ)
    (anchor : Fin k → ℝ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ) :
    anchoredOrderedTransportDistribution L anchor
        (section43OrderedPullbackTimeSpatialTensorCLM d k χ φ) =
      L (section43NPointTimeSpatialTensor d k
        (SCV.translateSchwartz (-anchor) φ) χ) := by
  rw [anchoredOrderedTransportDistribution,
    orderedTransportDistribution_orderedPullbackTimeSpatialTensor]
  change
    L (translateSchwartzConfiguration
      (osiiDifferenceTimeTranslation (d := d) (-anchor))
      (section43NPointTimeSpatialTensor d k φ χ)) =
      L (section43NPointTimeSpatialTensor d k
        (SCV.translateSchwartz (-anchor) φ) χ)
  apply congrArg L
  ext x
  have hspatial :
      section43QSpatial d k
          (x + osiiDifferenceTimeTranslation (d := d) (-anchor)) =
        section43QSpatial d k x := by
    change
      (nPointTimeSpatialCLE (d := d) k
        (x + osiiDifferenceTimeTranslation (d := d) (-anchor))).2 =
        (nPointTimeSpatialCLE (d := d) k x).2
    rw [map_add, nPointTimeSpatialCLE_osiiDifferenceTimeTranslation]
    simp
  simp [translateSchwartzConfiguration_apply,
    section43NPointTimeSpatialTensor_apply,
    SCV.translateSchwartz_apply,
    section43QTime_add_osiiDifferenceTimeTranslation, hspatial]

end OSIIChapterV
end OSReconstruction
