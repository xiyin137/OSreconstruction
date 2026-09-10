/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITestedTimeBoundary
















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]
variable {A : OSIITimeContinuationStage d k}

omit [NeZero d] in
private theorem rotatedTubeScalar_slice_eq_minkowskiTimeApproach
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (eta t : Fin k -> Real) (epsilon : Real) :
    A.rotatedTubeScalar chi
        (fun i => (t i : Complex) +
          (((epsilon • eta) i : Real) : Complex) * I) =
      A.distribution (osiiMinkowskiTimeApproach eta t epsilon) chi := by
  apply congrArg (fun z => A.distribution z chi)
  ext i
  simp [osiiTubeToRightHalfPlane, ContinuousLinearMap.lsmul_apply,
    osiiMinkowskiTimeApproach, Pi.smul_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem tubeSlice_eq_osiiFullTimeBoundaryPairing
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (eta : Fin k -> Real)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (epsilon : Real) :
    tubeSlice (A.rotatedTubeScalar chi) (epsilon • eta)
        phi =
      osiiFullTimeBoundaryPairing A eta epsilon phi chi := by
  rw [tubeSlice]
  apply integral_congr_ae
  filter_upwards with t
  rw [rotatedTubeScalar_slice_eq_minkowskiTimeApproach]

namespace OSIIFullTimeStageVladimirovGrowthData

/-- The tested time derivative at positive height, with the Fourier sign
fixed by the existing Minkowski approach convention. -/
theorem hasDerivAt_positiveSlicePairing
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (t : Real) (ht : 0 < t)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    HasDerivAt (fun u => osiiFullTimeBoundaryPairing A eta u phi chi)
      (-I * osiiFullTimeBoundaryPairing A eta t
        (directionalDerivSchwartz eta phi) chi) t := by
  obtain ⟨Cchi, hCchi, hbound⟩ := G.exists_rotatedScalar_vladimirov_bound chi
  simpa only [tubeSlice_eq_osiiFullTimeBoundaryPairing] using
    osiiTimeTube_hasDerivAt_ray_of_vladimirovGrowth
      (G.rotatedScalar_differentiableOn chi) hCchi hbound eta heta t ht phi

/-- Fixing a spatial Schwartz test in a full Chapter V stage with the Chapter
VI Vladimirov bound produces a tempered distribution in the real Minkowski
time gaps.

The sign in `osiiMinkowskiTimeApproach` implements the convention
`zeta = -I * z` directly, so no reflection of the boundary distribution is
introduced. -/
theorem exists_timeBoundary
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ∃ Wtime : SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex,
      ∀ eta : Fin k -> Real, eta ∈ osiiTimePositiveCone k ->
        ∀ phi : SchwartzMap (Fin k -> Real) Complex,
          Tendsto
            (fun epsilon : Real =>
              osiiFullTimeBoundaryPairing A eta epsilon phi chi)
            (nhdsWithin 0 (Ioi 0))
            (nhds (Wtime phi)) := by
  obtain ⟨Cchi, hCchi, hbound⟩ :=
    G.exists_rotatedScalar_vladimirov_bound chi
  obtain ⟨Wraw, hWraw⟩ :=
    osiiTimeTube_boundaryValue_of_vladimirovGrowth
      (G.rotatedScalar_differentiableOn chi) hCchi hbound
  refine ⟨Wraw, ?_⟩
  intro eta heta phi
  have hraw := hWraw phi eta heta
  have heq :
      (fun epsilon : Real =>
        tubeSlice (A.rotatedTubeScalar chi) (epsilon • eta)
          phi) =
        fun epsilon : Real =>
          osiiFullTimeBoundaryPairing A eta epsilon phi chi := by
    funext epsilon
    exact tubeSlice_eq_osiiFullTimeBoundaryPairing
      chi eta phi epsilon
  rw [← heq]
  exact hraw

/-- The selected tempered time boundary for one fixed spatial Schwartz test. -/
noncomputable def timeBoundary
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex :=
  Classical.choose (G.exists_timeBoundary chi)

/-- The selected time boundary is the distributional Minkowski limit along
every positive time-gap direction. -/
theorem timeBoundary_boundaryValue
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (eta : Fin k -> Real)
    (heta : eta ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    Tendsto
      (fun epsilon : Real =>
        osiiFullTimeBoundaryPairing A eta epsilon phi chi)
      (nhdsWithin 0 (Ioi 0))
      (nhds (G.timeBoundary chi phi)) :=
  Classical.choose_spec (G.exists_timeBoundary chi) eta heta phi

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
