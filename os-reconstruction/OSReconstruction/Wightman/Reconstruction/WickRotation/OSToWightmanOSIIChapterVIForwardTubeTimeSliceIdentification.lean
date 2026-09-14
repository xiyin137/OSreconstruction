/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43WickRotateFourierLaplaceBridge













noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

/-- A positive time-gap direction embedded as a purely temporal reduced
spacetime direction. -/
def osiiPureTimeReducedDirection
    (d k : Nat) (eta : Fin k -> Real) :
    NPointDomain d k :=
  fun i mu => if mu = 0 then eta i else 0

omit [NeZero d] in
@[simp] theorem osiiPureTimeReducedDirection_time
    (eta : Fin k -> Real) (i : Fin k) :
    osiiPureTimeReducedDirection d k eta i 0 = eta i :=
  rfl

omit [NeZero d] in
@[simp] theorem osiiPureTimeReducedDirection_space
    (eta : Fin k -> Real) (i : Fin k) (mu : Fin d) :
    osiiPureTimeReducedDirection d k eta i mu.succ = 0 :=
  rfl

omit [NeZero d] in
theorem osiiPureTimeReducedDirection_mem_productForwardCone
    (eta : Fin k -> Real)
    (heta : eta ∈ osiiTimePositiveCone k) :
    osiiPureTimeReducedDirection d k eta ∈
      BHW.ProductForwardConeReal d k := by
  intro i
  constructor
  · simpa [osiiPureTimeReducedDirection] using heta i
  · rw [BHW.minkowski_sum_decomp]
    simp [osiiPureTimeReducedDirection]
    nlinarith [heta i]

/-- The spatial slice of a reduced forward-tube kernel at a pure-time
interior point. -/
def osiiReducedForwardTubePureTimeSpatialPairing
    {W : SchwartzNPoint d k →L[Complex] Complex}
    (H : OSIIReducedForwardTubeBoundaryData W)
    (eta : Fin k -> Real) (epsilon : Real)
    (t : Fin k -> Real)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) : Complex :=
  ∫ x : Section43SpatialSpace d k,
    H.kernel (fun j mu =>
      (((section43NPointTimeSpatialMeasurableEquiv d k).symm (t, x)) j mu :
          Complex) +
        (epsilon : Complex) *
          (osiiPureTimeReducedDirection d k eta j mu : Complex) * I) *
      chi x

/-- The genuine identification datum between a reduced forward-tube kernel
and a completed Chapter V time stage.  It is stated before taking either
boundary value: integrate only the spatial variables at a positive pure-time
interior point and recover the stage distribution at that time point. -/
structure OSIIReducedForwardTubeTimeSliceRealizationData
    {A : OSIITimeContinuationStage d k}
    {W : SchwartzNPoint d k →L[Complex] Complex}
    (H : OSIIReducedForwardTubeBoundaryData W) where
  spatialSlice :
    forall (eta : Fin k -> Real),
      eta ∈ osiiTimePositiveCone k ->
        forall (epsilon : Real), 0 < epsilon ->
          forall (t : Fin k -> Real),
            forall chi : SchwartzMap (Section43SpatialSpace d k) Complex,
              osiiReducedForwardTubePureTimeSpatialPairing
                  H eta epsilon t chi =
                A.distribution
                  (osiiMinkowskiTimeApproach eta t epsilon) chi

namespace OSIIReducedForwardTubeBoundaryData

variable {W : SchwartzNPoint d k →L[Complex] Complex}

/-- Fubini for the physical tube, before any identification with the time
stage. This direction is also needed to prove that identification. -/
theorem boundaryPairing_eq_spatialPairing
    (H : OSIIReducedForwardTubeBoundaryData W)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    (∫ q : NPointDomain d k,
      H.kernel (fun j mu =>
        (q j mu : Complex) +
          (epsilon : Complex) *
            (osiiPureTimeReducedDirection d k eta j mu : Complex) * I) *
        section43NPointTimeSpatialTensor d k phi chi q) =
      ∫ t : Fin k -> Real,
        osiiReducedForwardTubePureTimeSpatialPairing H eta epsilon t chi * phi t := by
  let etaFull := osiiPureTimeReducedDirection d k eta
  let test := section43NPointTimeSpatialTensor d k phi chi
  let f : NPointDomain d k -> Complex := fun q =>
    H.kernel (fun j mu =>
      (q j mu : Complex) +
        (epsilon : Complex) * (etaFull j mu : Complex) * I) *
      test q
  let eTS := section43NPointTimeSpatialMeasurableEquiv d k
  have hetaFull : etaFull ∈ BHW.ProductForwardConeReal d k :=
    osiiPureTimeReducedDirection_mem_productForwardCone eta heta
  have hf : Integrable f := by
    simpa [f, test, etaFull] using
      H.boundarySlice_integrable etaFull hetaFull epsilon hepsilon test
  have hTSsymm : MeasurePreserving eTS.symm volume volume :=
    MeasurePreserving.symm eTS (by
      simpa [eTS] using
        section43NPointTimeSpatialCLE_measurePreserving d k)
  have hsplit : Integrable (fun p => f (eTS.symm p)) :=
    hTSsymm.integrable_comp_of_integrable hf
  have htensor : forall
      (t : Fin k -> Real) (x : Section43SpatialSpace d k),
      test (eTS.symm (t, x)) = phi t * chi x := by
    intro t x
    have hp :
        nPointTimeSpatialCLE (d := d) k (eTS.symm (t, x)) = (t, x) := by
      rw [← section43NPointTimeSpatialMeasurableEquiv_apply]
      exact eTS.apply_symm_apply (t, x)
    have ht :
        section43QTime (d := d) (n := k) (eTS.symm (t, x)) = t := by
      simpa [section43QTime] using congrArg Prod.fst hp
    have hx :
        section43QSpatial (d := d) (n := k) (eTS.symm (t, x)) = x := by
      simpa [section43QSpatial] using congrArg Prod.snd hp
    simp [test, ht, hx]
  calc
    (∫ q : NPointDomain d k,
        H.kernel (fun j mu =>
          (q j mu : Complex) +
            (epsilon : Complex) *
              (osiiPureTimeReducedDirection d k eta j mu : Complex) * I) *
          section43NPointTimeSpatialTensor d k phi chi q) =
        ∫ q : NPointDomain d k, f q := by rfl
    _ = ∫ p : (Fin k -> Real) × Section43SpatialSpace d k,
          f (eTS.symm p) := by
      exact (hTSsymm.integral_comp' (g := f)).symm
    _ = ∫ t : Fin k -> Real,
          ∫ x : Section43SpatialSpace d k,
            f (eTS.symm (t, x)) := by
      exact integral_prod (fun p => f (eTS.symm p)) hsplit
    _ = ∫ t : Fin k -> Real,
          osiiReducedForwardTubePureTimeSpatialPairing
              H eta epsilon t chi * phi t := by
      apply integral_congr_ae
      filter_upwards with t
      let g : Section43SpatialSpace d k -> Complex := fun x =>
        H.kernel (fun j mu =>
          ((eTS.symm (t, x)) j mu : Complex) +
            (epsilon : Complex) * (etaFull j mu : Complex) * I) *
          chi x
      change
        (∫ x : Section43SpatialSpace d k, f (eTS.symm (t, x))) =
          (∫ x : Section43SpatialSpace d k, g x) * phi t
      calc
        (∫ x : Section43SpatialSpace d k,
            f (eTS.symm (t, x))) =
            ∫ x : Section43SpatialSpace d k, g x * phi t := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [f]
          rw [htensor t x]
          simp only [g, etaFull]
          ring
        _ = (∫ x : Section43SpatialSpace d k, g x) * phi t := by
          exact MeasureTheory.integral_mul_const (phi t) g

end OSIIReducedForwardTubeBoundaryData

namespace OSIIReducedForwardTubeTimeSliceRealizationData

variable {A : OSIITimeContinuationStage d k}
variable {W : SchwartzNPoint d k →L[Complex] Complex}
variable {H : OSIIReducedForwardTubeBoundaryData W}

end OSIIReducedForwardTubeTimeSliceRealizationData

end OSReconstruction
