/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapDistributionHolomorphy
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairPhysicalBlockPatch
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge





















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

variable {d n r k : ℕ} [NeZero d]

/-- A holomorphic map from one Chapter V complex time carrier into the
simultaneous multi-gap logarithmic carrier. -/
structure OSIIMultiGapTimeStageChart (d r k : ℕ) [NeZero d] where
  carrier : Set (OSIITimeGapSpace k)
  carrier_open : IsOpen carrier
  coordinate :
    OSIITimeGapSpace k → Fin r → osiiAxisPairIndex d → ℂ
  coordinate_differentiable :
    DifferentiableOn ℂ coordinate carrier
  coordinate_mapsTo :
    Set.MapsTo coordinate carrier
      (osiiAxisPairMultiGapLogDomain d r)

namespace OSIIAxisPairPhysicalBlockPatch

variable {r : ℕ}

end OSIIAxisPairPhysicalBlockPatch

namespace OSIIAxisPairMultiGapSourcewiseMZFamily
namespace SchwartzDistributionFamily

variable
  {P : OSIIAxisPairMultiGapSourcewiseMZFamily d n r}

/-- Totalize the canonical full distribution family by zero outside its
multi-gap logarithmic carrier. -/
noncomputable def totalDistribution
    (A : P.SchwartzDistributionFamily)
    (z : Fin r → osiiAxisPairIndex d → ℂ) :
    SchwartzNPoint d n →L[ℂ] ℂ :=
  if hz : z ∈ osiiAxisPairMultiGapLogDomain d r then
    A.distribution ⟨z, hz⟩
  else
    0

/-- The totalized distribution has exactly the previously defined totalized
scalar pairing. -/
@[simp] theorem totalDistribution_apply
    (A : P.SchwartzDistributionFamily)
    (z : Fin r → osiiAxisPairIndex d → ℂ)
    (f : SchwartzNPoint d n) :
    A.totalDistribution z f = A.pairing f z := by
  by_cases hz : z ∈ osiiAxisPairMultiGapLogDomain d r
  · simp [totalDistribution, pairing, hz]
  · simp [totalDistribution, pairing, hz]

/-- Pull a full multi-gap distribution family through a holomorphic
time-coordinate chart and curry it by a continuous spatial-source map. -/
noncomputable def timeStageDistribution
    (A : P.SchwartzDistributionFamily)
    (C : OSIIMultiGapTimeStageChart d r k)
    (source :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzNPoint d n)
    (ζ : OSIITimeGapSpace k) :
    OSIISpatialDistribution d k :=
  (A.totalDistribution (C.coordinate ζ)).comp source

@[simp] theorem timeStageDistribution_apply
    (A : P.SchwartzDistributionFamily)
    (C : OSIIMultiGapTimeStageChart d r k)
    (source :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzNPoint d n)
    (ζ : OSIITimeGapSpace k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    A.timeStageDistribution C source ζ χ =
      A.pairing (source χ) (C.coordinate ζ) := by
  simp [timeStageDistribution]

/-- Unconditional full-test holomorphy of the multi-gap distribution family
passes through every holomorphic time chart and continuous spatial currying
map. -/
theorem timeStageDistribution_weaklyHolomorphic
    (A : P.SchwartzDistributionFamily)
    (hn : 0 < n)
    (C : OSIIMultiGapTimeStageChart d r k)
    (source :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzNPoint d n) :
    OSIIWeaklyHolomorphicOn
      (A.timeStageDistribution C source) C.carrier := by
  intro χ
  have hdiff :
      DifferentiableOn ℂ
        (fun ζ => A.pairing (source χ) (C.coordinate ζ))
        C.carrier :=
    (A.differentiableOn_pairing_of_productTensor_holomorphic
      hn (source χ)).comp
        C.coordinate_differentiable C.coordinate_mapsTo
  exact hdiff.congr fun ζ _hζ =>
    A.timeStageDistribution_apply C source ζ χ

namespace TimeStageRealEdgeData

end TimeStageRealEdgeData

end SchwartzDistributionFamily
end OSIIAxisPairMultiGapSourcewiseMZFamily

namespace OSIIChronologicalCompactFactors

variable [NeZero k]

section OriginalOSTimeContinuation

variable (F : OSIIChronologicalCompactFactors d k)
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

end OriginalOSTimeContinuation

end OSIIChronologicalCompactFactors

end OSReconstruction
