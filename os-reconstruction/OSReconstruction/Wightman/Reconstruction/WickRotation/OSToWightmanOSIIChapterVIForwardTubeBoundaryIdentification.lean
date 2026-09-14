/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeSmearing
import OSReconstruction.SCV.DistributionalUniqueness










noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d] {A : OSIITimeContinuationStage d k}

omit [NeZero d] in
private theorem rotate_timeSlice (eta t : Fin k -> Real) (epsilon : Real) :
    osiiTubeToRightHalfPlane k
        (fun j => (t j : Complex) + (epsilon : Complex) * (eta j : Complex) * I) =
      osiiMinkowskiTimeApproach eta t epsilon := by
  ext j
  simp [osiiTubeToRightHalfPlane, ContinuousLinearMap.lsmul_apply,
    osiiMinkowskiTimeApproach]
  ring_nf
  rw [Complex.I_sq]
  ring

namespace OSIIFullTimeStageTemperedBoundaryData

private theorem reducedBoundary_tensor_eq
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    B.reducedBoundary (section43NPointTimeSpatialTensor d k phi chi) =
      B.orderedBoundary (section43OrderedPullbackTimeSpatialTensorCLM d k chi phi) := by
  rw [← section43TimeSpatialTensorCLM_apply,
    ← OSIIChapterV.orderedTransportDistribution_orderedPullbackTimeSpatialTensor,
    B.orderedTransportDistribution_reducedBoundary]

theorem rotatedTubeScalar_slice_integrable
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    Integrable (fun t => A.rotatedTubeScalar chi
      (fun j => (t j : Complex) + (epsilon : Complex) * (eta j : Complex) * I) * phi t) := by
  simpa only [OSIITimeContinuationStage.rotatedTubeScalar, rotate_timeSlice] using
    B.slice_integrable eta heta epsilon hepsilon phi chi

theorem rotatedTubeScalar_boundaryValue
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex) :
    Tendsto (fun epsilon : Real => ∫ t : Fin k -> Real,
      A.rotatedTubeScalar chi
        (fun j => (t j : Complex) + (epsilon : Complex) * (eta j : Complex) * I) * phi t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (B.reducedBoundary (section43NPointTimeSpatialTensor d k phi chi))) := by
  simpa only [OSIITimeContinuationStage.rotatedTubeScalar, rotate_timeSlice,
    reducedBoundary_tensor_eq, osiiFullTimeBoundaryPairing] using
      B.boundaryValue eta heta phi chi

/-- A physical tube with the native boundary agrees, after spatial smearing,
with the original time continuation. This includes zero gap arity. -/
theorem spatialSmearing_eq_rotatedTubeScalar
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (H : OSIIReducedForwardTubeBoundaryData B.reducedBoundary)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (z : Fin k -> Complex) (hz : z ∈ SCV.TubeDomain (osiiTimePositiveCone k)) :
    H.spatialSmearing chi z = A.rotatedTubeScalar chi z := by
  let F := fun w => H.spatialSmearing chi w - A.rotatedTubeScalar chi w
  have hFholo : DifferentiableOn Complex F (SCV.TubeDomain (osiiTimePositiveCone k)) :=
    (H.spatialSmearing_differentiableOn chi).sub
      (A.rotatedTubeScalar_differentiableOn B.fullCarrier chi)
  have hHint (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
      (epsilon : Real) (hepsilon : 0 < epsilon)
      (phi : SchwartzMap (Fin k -> Real) Complex) :
      Integrable (fun t => H.spatialSmearing chi
        (fun j => (t j : Complex) + (epsilon : Complex) * (eta j : Complex) * I) * phi t) := by
    simpa only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul] using
      H.spatialSmearing_slice_integrable chi (epsilon • eta)
        (osiiTimePositiveCone_isCone k eta heta epsilon hepsilon) phi
  have hFint (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k)
      (phi : SchwartzMap (Fin k -> Real) Complex) :
      Integrable (fun t => F
        (fun j => (t j : Complex) + (y j : Complex) * I) * phi t) := by
    simpa only [F, sub_mul, Complex.ofReal_one, one_mul] using
      (hHint y hy 1 zero_lt_one phi).sub
        (B.rotatedTubeScalar_slice_integrable chi y hy 1 zero_lt_one phi)
  have hFbv (phi : SchwartzMap (Fin k -> Real) Complex)
      (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k) :
      Tendsto (fun epsilon : Real => ∫ t : Fin k -> Real,
        F (fun j => (t j : Complex) + (epsilon : Complex) * (eta j : Complex) * I) * phi t)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hlim : Tendsto (fun epsilon : Real =>
        (∫ t : Fin k -> Real, H.spatialSmearing chi
          (fun j => (t j : Complex) + (epsilon : Complex) * (eta j : Complex) * I) * phi t) -
        (∫ t : Fin k -> Real, A.rotatedTubeScalar chi
          (fun j => (t j : Complex) + (epsilon : Complex) * (eta j : Complex) * I) * phi t))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using (H.spatialSmearing_boundaryValue chi eta heta phi).sub
        (B.rotatedTubeScalar_boundaryValue chi eta heta phi)
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    simp only [F, sub_mul]
    exact (integral_sub (hHint eta heta epsilon hepsilon phi)
      (B.rotatedTubeScalar_slice_integrable chi eta heta epsilon hepsilon phi)).symm
  exact sub_eq_zero.mp (SCV.distributional_uniqueness_tube_of_zero_bv
    (osiiTimePositiveCone_open k) (osiiTimePositiveCone_convex k)
    (osiiTimePositiveCone_nonempty k)
    (fun epsilon hepsilon eta heta => osiiTimePositiveCone_isCone k eta heta epsilon hepsilon)
    hFholo hFint hFbv z hz)

/-- Populate the existing interior-realization interface from equality of
the native boundaries, rather than assume the interior comparison. -/
def toForwardTubeTimeSliceRealizationData
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (H : OSIIReducedForwardTubeBoundaryData B.reducedBoundary) :
    OSIIReducedForwardTubeTimeSliceRealizationData (A := A) H where
  spatialSlice := by
    intro eta heta epsilon hepsilon t chi
    rw [← H.spatialSmearing_eq_pureTimeSpatialPairing chi eta t epsilon,
      B.spatialSmearing_eq_rotatedTubeScalar H chi _ (by
        change (fun j => _) ∈ osiiTimePositiveCone k
        simpa using osiiTimePositiveCone_isCone k eta heta epsilon hepsilon),
      OSIITimeContinuationStage.rotatedTubeScalar, rotate_timeSlice]

end OSIIFullTimeStageTemperedBoundaryData

end OSReconstruction
