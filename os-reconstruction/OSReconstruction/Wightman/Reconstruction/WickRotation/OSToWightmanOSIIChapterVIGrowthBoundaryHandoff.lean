/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIReducedForwardTubePaleyWiener



















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction



/-- The strict positive orthant for the `k` relative time variables. -/
def osiiTimePositiveCone (k : ℕ) : Set (Fin k → ℝ) :=
  section43TimeStrictPositiveRegion k

theorem osiiTimePositiveCone_open (k : ℕ) :
    IsOpen (osiiTimePositiveCone k) := by
  simpa [osiiTimePositiveCone] using
    isOpen_section43TimeStrictPositiveRegion k

theorem osiiTimePositiveCone_convex (k : ℕ) :
    Convex ℝ (osiiTimePositiveCone k) := by
  intro x hx y hy a b ha hb hab i
  have hxi : 0 < x i := hx i
  have hyi : 0 < y i := hy i
  change 0 < a * x i + b * y i
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    simpa [hb1] using hyi
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    exact add_pos_of_pos_of_nonneg
      (mul_pos ha_pos hxi)
      (mul_nonneg hb (le_of_lt hyi))

theorem osiiTimePositiveCone_isCone (k : ℕ) :
    IsCone (osiiTimePositiveCone k) := by
  intro y hy t ht i
  change 0 < t * y i
  exact mul_pos ht (hy i)

theorem osiiTimePositiveCone_nonempty (k : ℕ) :
    (osiiTimePositiveCone k).Nonempty := by
  refine ⟨fun _ => 1, ?_⟩
  intro i
  exact zero_lt_one

/-- Rotate the positive-orthant tube to the Chapter V right half-plane. -/
def osiiTubeToRightHalfPlane (k : ℕ) :
    (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) :=
  (ContinuousLinearMap.lsmul ℂ ℂ) (-I)

theorem osiiTubeToRightHalfPlane_differentiable (k : ℕ) :
    Differentiable ℂ (osiiTubeToRightHalfPlane k) := by
  exact (osiiTubeToRightHalfPlane k).differentiable

@[simp] theorem osiiTubeToRightHalfPlane_re
    (w : Fin k → ℂ) (i : Fin k) :
    ((osiiTubeToRightHalfPlane k w) i).re = (w i).im := by
  simp [osiiTubeToRightHalfPlane, ContinuousLinearMap.lsmul_apply]

@[simp] theorem osiiTubeToRightHalfPlane_norm
    (w : Fin k → ℂ) :
    ‖osiiTubeToRightHalfPlane k w‖ = ‖w‖ := by
  change ‖(-I) • w‖ = ‖w‖
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]

theorem osiiTubeToRightHalfPlane_mem_iff
    (w : Fin k → ℂ) :
    osiiTubeToRightHalfPlane k w ∈ osiiTimeRightHalfPlane k ↔
      w ∈ SCV.TubeDomain (osiiTimePositiveCone k) := by
  simp [osiiTubeToRightHalfPlane, osiiTimeRightHalfPlane,
    osiiTimePositiveCone, section43TimeStrictPositiveRegion,
    SCV.TubeDomain]

namespace OSIITimeContinuationStage

/-- The scalar positive-orthant tube function obtained by fixing a spatial
Schwartz test in a Chapter V continuation stage. -/
def rotatedTubeScalar
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (Fin k → ℂ) → ℂ :=
  fun w => A.distribution (osiiTubeToRightHalfPlane k w) χ

/-- A full Chapter V stage is holomorphic after rotation to the ordinary
positive-orthant tube. -/
theorem rotatedTubeScalar_differentiableOn
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k)
    (hfull : A.carrier = osiiTimeRightHalfPlane k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    DifferentiableOn ℂ (A.rotatedTubeScalar χ)
      (SCV.TubeDomain (osiiTimePositiveCone k)) := by
  refine (A.weaklyHolomorphic χ).comp
    (osiiTubeToRightHalfPlane_differentiable k).differentiableOn ?_
  intro w hw
  rw [hfull]
  exact (osiiTubeToRightHalfPlane_mem_iff w).2 hw

end OSIITimeContinuationStage



/-- Distance of the real time-gap vector from the boundary of the positive
orthant. -/
def osiiTimeBoundaryDistance (k : ℕ) (ζ : Fin k → ℂ) : ℝ :=
  Metric.infDist (fun i => (ζ i).re) (osiiTimePositiveCone k)ᶜ

/-- The Chapter VI growth data needed after a full Chapter V continuation.

The spatial dependence is controlled by one finite supremum of Schwartz
seminorms.  The time dependence has global polynomial growth and a separate
power of the inverse distance to the boundary of the right half-plane. -/
structure OSIIFullTimeStageVladimirovGrowthData
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k) where
  fullCarrier : A.carrier = osiiTimeRightHalfPlane k
  spatialSeminorms : Finset (ℕ × ℕ)
  constant : ℝ
  polynomialDegree : ℕ
  boundaryDegree : ℕ
  constant_pos : 0 < constant
  bound :
    ∀ ζ ∈ osiiTimeRightHalfPlane k,
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ‖A.distribution ζ χ‖ ≤
          constant * (1 + ‖ζ‖) ^ polynomialDegree *
            (1 + (osiiTimeBoundaryDistance k ζ)⁻¹) ^ boundaryDegree *
              spatialSeminorms.sup
                (schwartzSeminormFamily ℂ (Section43SpatialSpace d k) ℂ) χ

namespace OSIIFullTimeStageVladimirovGrowthData

variable {d k : ℕ}
variable {A : OSIITimeContinuationStage d k}

theorem rotatedScalar_differentiableOn
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    DifferentiableOn ℂ (A.rotatedTubeScalar χ)
      (SCV.TubeDomain (osiiTimePositiveCone k)) := by
  exact A.rotatedTubeScalar_differentiableOn G.fullCarrier χ

theorem rotatedScalar_vladimirov_bound
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (w : Fin k → ℂ)
    (hw : w ∈ SCV.TubeDomain (osiiTimePositiveCone k)) :
    ‖A.rotatedTubeScalar χ w‖ ≤
      G.constant * (1 + ‖w‖) ^ G.polynomialDegree *
        (1 + (Metric.infDist (fun i => (w i).im)
          (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree *
            G.spatialSeminorms.sup
              (schwartzSeminormFamily ℂ (Section43SpatialSpace d k) ℂ) χ := by
  have hmem :
      osiiTubeToRightHalfPlane k w ∈ osiiTimeRightHalfPlane k :=
    (osiiTubeToRightHalfPlane_mem_iff w).2 hw
  simpa [OSIITimeContinuationStage.rotatedTubeScalar,
    osiiTimeBoundaryDistance] using
    G.bound (osiiTubeToRightHalfPlane k w) hmem χ

theorem exists_rotatedScalar_vladimirov_bound
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ∃ Cχ : ℝ, 0 < Cχ ∧
      ∀ w ∈ SCV.TubeDomain (osiiTimePositiveCone k),
        ‖A.rotatedTubeScalar χ w‖ ≤
          Cχ * (1 + ‖w‖) ^ G.polynomialDegree *
            (1 + (Metric.infDist (fun i => (w i).im)
              (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree := by
  let p : ℝ :=
    G.spatialSeminorms.sup
      (schwartzSeminormFamily ℂ (Section43SpatialSpace d k) ℂ) χ
  refine ⟨G.constant * (1 + p), ?_, ?_⟩
  · have hp : 0 ≤ p := by
      dsimp [p]
      exact apply_nonneg _ _
    exact mul_pos G.constant_pos (by linarith)
  · intro w hw
    have hp : 0 ≤ p := by
      dsimp [p]
      exact apply_nonneg _ _
    have hp_le : p ≤ 1 + p := by linarith
    have hC : 0 ≤ G.constant := le_of_lt G.constant_pos
    have hpoly : 0 ≤ (1 + ‖w‖) ^ G.polynomialDegree := by positivity
    have hboundary :
        0 ≤ (1 + (Metric.infDist (fun i => (w i).im)
          (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree := by
      have hdist :
          0 ≤ Metric.infDist (fun i => (w i).im)
            (osiiTimePositiveCone k)ᶜ :=
        Metric.infDist_nonneg
      exact pow_nonneg (by linarith [inv_nonneg.mpr hdist]) _
    calc
      ‖A.rotatedTubeScalar χ w‖ ≤
          G.constant * (1 + ‖w‖) ^ G.polynomialDegree *
            (1 + (Metric.infDist (fun i => (w i).im)
              (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree * p := by
        simpa [p] using G.rotatedScalar_vladimirov_bound χ w hw
      _ ≤ (G.constant * (1 + p)) *
          (1 + ‖w‖) ^ G.polynomialDegree *
            (1 + (Metric.infDist (fun i => (w i).im)
              (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree := by
        have hCp :
            G.constant * p ≤ G.constant * (1 + p) :=
          mul_le_mul_of_nonneg_left hp_le hC
        calc
          G.constant * (1 + ‖w‖) ^ G.polynomialDegree *
                (1 + (Metric.infDist (fun i => (w i).im)
                  (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree * p =
              (G.constant * p) *
                ((1 + ‖w‖) ^ G.polynomialDegree *
                  (1 + (Metric.infDist (fun i => (w i).im)
                    (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree) := by
            ring
          _ ≤ (G.constant * (1 + p)) *
                ((1 + ‖w‖) ^ G.polynomialDegree *
                  (1 + (Metric.infDist (fun i => (w i).im)
                    (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree) :=
            mul_le_mul_of_nonneg_right hCp
              (mul_nonneg hpoly hboundary)
          _ = (G.constant * (1 + p)) *
                (1 + ‖w‖) ^ G.polynomialDegree *
                  (1 + (Metric.infDist (fun i => (w i).im)
                    (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree := by
            ring

end OSIIFullTimeStageVladimirovGrowthData



/-- Approach the imaginary time axis from the positive real time-gap cone.

For a forward-tube point `z = t + i epsilon eta`, the Chapter V right-half-plane
coordinate is `zeta = -i z = epsilon eta - i t`.  This sign is what makes the
resulting Minkowski boundary have positive, rather than negative, energy. -/
def osiiMinkowskiTimeApproach
    (η t : Fin k → ℝ) (ε : ℝ) :
    Fin k → ℂ :=
  fun i => (ε * η i : ℂ) - (t i : ℂ) * I

theorem osiiMinkowskiTimeApproach_mem
    {η t : Fin k → ℝ} {ε : ℝ}
    (hη : η ∈ osiiTimePositiveCone k)
    (hε : 0 < ε) :
    osiiMinkowskiTimeApproach η t ε ∈ osiiTimeRightHalfPlane k := by
  intro i
  simp only [osiiMinkowskiTimeApproach,
    Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero]
  exact mul_pos hε (hη i)

/-- Pair a positive-cone time slice of the continuation stage with a Schwartz
test in the real relative-time variables. -/
def osiiFullTimeBoundaryPairing
    {d k : ℕ} [NeZero d]
    (A : OSIITimeContinuationStage d k)
    (η : Fin k → ℝ) (ε : ℝ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) : ℂ :=
  ∫ t : Fin k → ℝ,
    A.distribution (osiiMinkowskiTimeApproach η t ε) χ * φ t

/-- A full tempered Minkowski boundary for a Chapter V time-continuation
stage.

The target is the ordered spacetime distribution because the Section 4.3
time-spatial tensor map lands in ordered coordinates.  Reduced coordinates
are recovered canonically below. -/
structure OSIIFullTimeStageTemperedBoundaryData
    {d k : ℕ} [NeZero d]
    (A : OSIITimeContinuationStage d k) where
  fullCarrier : A.carrier = osiiTimeRightHalfPlane k
  orderedBoundary : SchwartzNPoint d k →L[ℂ] ℂ
  slice_integrable :
    ∀ η ∈ osiiTimePositiveCone k,
      ∀ ε > 0,
        ∀ φ : SchwartzMap (Fin k → ℝ) ℂ,
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            Integrable (fun t : Fin k → ℝ =>
              A.distribution (osiiMinkowskiTimeApproach η t ε) χ * φ t)
  boundaryValue :
    ∀ η ∈ osiiTimePositiveCone k,
      ∀ φ : SchwartzMap (Fin k → ℝ) ℂ,
        ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
          Tendsto
            (fun ε : ℝ => osiiFullTimeBoundaryPairing A η ε φ χ)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (orderedBoundary
              (section43OrderedPullbackTimeSpatialTensorCLM d k χ φ)))

namespace OSIIFullTimeStageTemperedBoundaryData

variable {d k : ℕ} [NeZero d]
variable {A : OSIITimeContinuationStage d k}

/-- The canonical reduced-coordinate form of the ordered Minkowski boundary. -/
def reducedBoundary
    (B : OSIIFullTimeStageTemperedBoundaryData A) :
    SchwartzNPoint d k →L[ℂ] ℂ :=
  OSIIChapterV.reducedTransportDistribution B.orderedBoundary

@[simp] theorem orderedTransportDistribution_reducedBoundary
    (B : OSIIFullTimeStageTemperedBoundaryData A) :
    OSIIChapterV.orderedTransportDistribution B.reducedBoundary =
      B.orderedBoundary := by
  exact OSIIChapterV.orderedTransportDistribution_reducedTransportDistribution
    B.orderedBoundary

/-- Add the separate spectral-support obligation to obtain the canonical
reduced forward-tube boundary package. -/
def toReducedForwardTubeBoundarySpectralData
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (hsupport :
      HasFourierSupportInDualCone (osiiReducedForwardFlatCone d k)
        (osiiCanonicalFrequencyDistribution B.reducedBoundary)) :
    OSIIReducedForwardTubeBoundarySpectralData d k where
  boundaryDistribution := B.reducedBoundary
  support := hsupport

@[simp] theorem toReducedForwardTubeBoundarySpectralData_boundaryDistribution
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (hsupport :
      HasFourierSupportInDualCone (osiiReducedForwardFlatCone d k)
        (osiiCanonicalFrequencyDistribution B.reducedBoundary)) :
    (B.toReducedForwardTubeBoundarySpectralData hsupport).boundaryDistribution =
      B.reducedBoundary := rfl

end OSIIFullTimeStageTemperedBoundaryData

end OSReconstruction
