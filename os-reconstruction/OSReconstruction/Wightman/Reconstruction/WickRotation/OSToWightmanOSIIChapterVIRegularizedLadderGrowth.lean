/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.LocalProductDescent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVILadderGrowthHandoff
import Init
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIComplexMeanValue





















noncomputable section

open Complex MeasureTheory Set
open scoped Classical

namespace OSReconstruction

namespace OSIITimeContinuationLadderVladimirovGrowthData

/-- At arity zero, every stage value is the same continuous spatial
functional, so a finite Schwartz-seminorm bound gives uniform ladder growth
without a regularization argument. -/
noncomputable def ofZeroArity
    {d : ℕ}
    (L : OSIITimeContinuationLadder d 0) :
    OSIITimeContinuationLadderVladimirovGrowthData L := by
  let T : SchwartzMap (Section43SpatialSpace d 0) ℂ →L[ℂ] ℂ :=
    L.toFullTimeContinuationStage.distribution (0 : Fin 0 → ℂ)
  let hboundData :=
    SCV.exists_schwartzFunctional_finsetSeminormBound T
  let s := hboundData.choose
  let C := hboundData.choose_spec.choose
  have hC : 0 ≤ C := hboundData.choose_spec.choose_spec.1
  have hbound :
      ∀ φ : SchwartzMap (Section43SpatialSpace d 0) ℂ,
        ‖T φ‖ ≤ C *
          s.sup
            (schwartzSeminormFamily ℂ
              (Section43SpatialSpace d 0) ℂ) φ :=
    hboundData.choose_spec.choose_spec.2
  refine
    { spatialSeminorms := s
      constant := C + 1
      polynomialDegree := 0
      boundaryDegree := 0
      constant_pos := by linarith
      bound := ?_ }
  intro stageIndex ζ hζ _hphysical χ
  have hstage :
      (L.stage stageIndex).distribution ζ χ = T χ := by
    rw [← L.toFullTimeContinuationStage_extends_stage stageIndex hζ]
    have hζ_zero : ζ = (0 : Fin 0 → ℂ) := Subsingleton.elim _ _
    simp [T, hζ_zero]
  rw [hstage]
  simp only [pow_zero, mul_one]
  exact
    (hbound χ).trans
      (mul_le_mul_of_nonneg_right (by linarith)
        (apply_nonneg
          (s.sup
            (schwartzSeminormFamily ℂ
              (Section43SpatialSpace d 0) ℂ)) χ))

end OSIITimeContinuationLadderVladimirovGrowthData

/-- A direct positive-arity Step-4 input above every stage of an exhausting
Chapter V ladder.

`regularizedOrbit` is the genuine auxiliary analytic object of Chapter VI,
not merely the convolution of an already chosen boundary distribution.  Its
parameter has `k * (d + 1)` complex coordinates, as in equation (6.6), rather
than only one real coordinate per time gap.  The concrete regularizer measure
and its support are retained explicitly because proving that measure is a
holomorphic mean-value kernel is part of the mathematics.

`meanValue` is the unregularization identity.  The quantitative orbit bound is
packaged separately below so the two mathematical steps can be proved and
audited independently. -/
structure OSIITimeContinuationLadderRegularizedMeanValueData
    {d k : ℕ}
    (L : OSIITimeContinuationLadder d k) where
  arity_pos : 0 < k
  regularizerMeasure :
    (Fin k → ℂ) → Measure (OSIIStep4FullComplexSpace d k)
  regularizerSupport :
    (Fin k → ℂ) → Set (OSIIStep4FullComplexSpace d k)
  regularizer_isProbability :
    ∀ ζ,
      ζ ∈ osiiTimeRightHalfPlane k →
        IsProbabilityMeasure (regularizerMeasure ζ)
  regularizer_support_ae :
    ∀ ζ,
      ζ ∈ osiiTimeRightHalfPlane k →
        ∀ᵐ y ∂regularizerMeasure ζ,
          y ∈ regularizerSupport ζ
  regularizedOrbit :
    ℕ → (Fin k → ℂ) →
      SchwartzMap (Section43SpatialSpace d k) ℂ →
        OSIIStep4FullComplexSpace d k → ℂ
  orbit_integrable :
    ∀ stageIndex ζ,
      ζ ∈ (L.stage stageIndex).carrier →
        ∀ _hζ : ζ ∈ osiiTimeRightHalfPlane k,
        ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
          Integrable (regularizedOrbit stageIndex ζ χ)
            (regularizerMeasure ζ)
  meanValue :
    ∀ stageIndex ζ,
      ζ ∈ (L.stage stageIndex).carrier →
      ∀ _hζ : ζ ∈ osiiTimeRightHalfPlane k,
        ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
          (L.stage stageIndex).distribution ζ χ =
            ∫ y,
              regularizedOrbit stageIndex ζ χ y
                ∂regularizerMeasure ζ

namespace OSIITimeContinuationLadderRegularizedMeanValueData

variable {d k : ℕ}
variable {L : OSIITimeContinuationLadder d k}

end OSIITimeContinuationLadderRegularizedMeanValueData

namespace OSIITimeContinuationLadderRegularizedOrbitGrowthData

variable {d k : ℕ}
variable {L : OSIITimeContinuationLadder d k}
variable {R : OSIITimeContinuationLadderRegularizedMeanValueData L}

end OSIITimeContinuationLadderRegularizedOrbitGrowthData

end OSReconstruction
