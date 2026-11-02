/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import Init
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizationRadius
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Pi
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIComplexMeanValue
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import OSReconstruction.SCV.EuclideanWeylPairing
public import OSReconstruction.SCV.SchwartzFiniteSeminormBound
public import OSReconstruction.Wightman.SchwartzTensorProduct
public import OSReconstruction.SCV.DistributionalRepresentationUniqueness
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizedLadderGrowth

@[expose] public section

noncomputable section

open Complex MeasureTheory Set
open scoped Classical

namespace OSReconstruction

/-- The VI.1 growth estimate on the positive real edge of the exhausted
Chapter V continuation. -/
structure OSIITimeContinuationLadderRealEdgeGrowthData
    {d k : ℕ}
    (L : OSIITimeContinuationLadder d k) where
  spatialSeminorms : Finset (ℕ × ℕ)
  constant : ℝ
  polynomialDegree : ℕ
  boundaryDegree : ℕ
  constant_pos : 0 < constant
  bound :
    ∀ τ : Fin k → ℝ,
      τ ∈ section43TimeStrictPositiveRegion k →
        ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
          ‖L.fullDistribution (osiiPositiveRealTimeEmbed τ) χ‖ ≤
            constant *
              (1 + ‖osiiPositiveRealTimeEmbed τ‖) ^ polynomialDegree *
              (1 +
                (osiiTimeBoundaryDistance k
                  (osiiPositiveRealTimeEmbed τ))⁻¹) ^ boundaryDegree *
              spatialSeminorms.sup
                (schwartzSeminormFamily ℂ
                  (Section43SpatialSpace d k) ℂ) χ

/-- A regularized VI.1 representation of the positive real edge. The
mean-value identity is kept independent of the later orbit estimate. -/
structure OSIITimeContinuationLadderRealEdgeRegularizedMeanValueData
    {d k : ℕ}
    (L : OSIITimeContinuationLadder d k) where
  arity_pos : 0 < k
  regularizerMeasure :
    (Fin k → ℝ) → Measure (OSIIStep4FullComplexSpace d k)
  regularizerSupport :
    (Fin k → ℝ) → Set (OSIIStep4FullComplexSpace d k)
  regularizer_isProbability :
    ∀ τ,
      τ ∈ section43TimeStrictPositiveRegion k →
        IsProbabilityMeasure (regularizerMeasure τ)
  regularizer_support_ae :
    ∀ τ,
      τ ∈ section43TimeStrictPositiveRegion k →
        ∀ᵐ y ∂regularizerMeasure τ,
          y ∈ regularizerSupport τ
  regularizedOrbit :
    (Fin k → ℝ) →
      SchwartzMap (Section43SpatialSpace d k) ℂ →
        OSIIStep4FullComplexSpace d k → ℂ
  orbit_integrable :
    ∀ τ,
      τ ∈ section43TimeStrictPositiveRegion k →
        ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
          Integrable (regularizedOrbit τ χ) (regularizerMeasure τ)
  meanValue :
    ∀ τ,
      τ ∈ section43TimeStrictPositiveRegion k →
        ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
          L.fullDistribution (osiiPositiveRealTimeEmbed τ) χ =
            ∫ y, regularizedOrbit τ χ y ∂regularizerMeasure τ

namespace OSIITimeContinuationLadderRealEdgeRegularizedMeanValueData

variable {d k : ℕ}
variable {L : OSIITimeContinuationLadder d k}

end OSIITimeContinuationLadderRealEdgeRegularizedMeanValueData

namespace OSIITimeContinuationLadderRealEdgeRadialComparisonData

variable {d k : ℕ}
variable {L : OSIITimeContinuationLadder d k}

end OSIITimeContinuationLadderRealEdgeRadialComparisonData

namespace OSIITimeContinuationLadderRealEdgeRegularizedOrbitGrowthData

variable {d k : ℕ}
variable {L : OSIITimeContinuationLadder d k}
variable {R : OSIITimeContinuationLadderRealEdgeRegularizedMeanValueData L}

end OSIITimeContinuationLadderRealEdgeRegularizedOrbitGrowthData

namespace OSIITimeContinuationLadderVI2PropagationData

variable {d k : ℕ}
variable {L : OSIITimeContinuationLadder d k}
variable {E : OSIITimeContinuationLadderRealEdgeGrowthData L}

end OSIITimeContinuationLadderVI2PropagationData

namespace OSIITimeContinuationLadderVladimirovGrowthData

variable {d k : ℕ}
variable {L : OSIITimeContinuationLadder d k}

end OSIITimeContinuationLadderVladimirovGrowthData

end OSReconstruction
