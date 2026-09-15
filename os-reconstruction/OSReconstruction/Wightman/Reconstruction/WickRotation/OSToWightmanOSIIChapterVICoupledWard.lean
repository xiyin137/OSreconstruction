import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledBoostSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIWickWardRestriction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledTimeBoundary
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeDomainGeometry

/-!
# The coupled Ward identity and its native boundary

The actual original-E1 identity gives the exact regulator term on a positive
Wick slice. Continuity supplies full-source density before the existing
tempered boundary removes that regulator term.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical LineDeriv

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction
namespace OSIIFullTimeStageVladimirovGrowthData

open OSIIChapterV OSIIChapterVI

variable {d k : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d} {A : OSIITimeContinuationStage d k}

private theorem wickWard_algebra (P Q x y : Complex) :
    I * (P + (y - x * I) * Q) = I * P + x * Q + I * y * Q := by
  calc
    _ = I * P + I * y * Q - (I * I) * (x * Q) := by ring
    _ = _ := by rw [I_mul_I]; ring

set_option maxHeartbeats 600000 in
theorem coupledTimeSlice_boost_tensor_compact
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (H : HasCanonicalReducedCompactStageEdges OS A)
    (a : Fin d) (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (hphi : HasCompactSupport (phi : (Fin k -> Real) -> Complex)) :
    osiiCoupledTimeSlice A y
        (osiiCoupledBoostDeriv d k a (section43TimeSpatialTensor d k phi chi)) =
      (-I) * osiiCoupledTimeSlice A y
        (osiiCoupledSpatialDeriv d k (osiiSpatialAxisCLM d k a y)
          (section43TimeSpatialTensor d k phi chi)) := by
  let J := G.coupledTimeSliceCLM y hy
  let z := fun x => osiiMinkowskiTimeApproach y x 1
  let P (j : Fin k) (x : Fin k -> Real) :=
    timePairingPartial A (spatialCoordinateMultiplier j a chi) j (z x) * phi x
  let Q (j : Fin k) (x : Fin k -> Real) :=
    A.distribution (z x) (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi) * phi x
  let R (j : Fin k) (x : Fin k -> Real) := (x j : Complex) * Q j x
  have hsource : SCV.SupportsInOpen (phi : (Fin k -> Real) -> Complex) Set.univ :=
    ⟨hphi, Set.subset_univ _⟩
  have hP (j : Fin k) : Integrable (P j) :=
    SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen isOpen_univ
      (continuous_wickRestriction G.fullCarrier
        (differentiableOn_timePairingPartial A _ j).continuousOn y hy).continuousOn hsource
  have hQ (j : Fin k) : Integrable (Q j) :=
    SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen isOpen_univ
      (continuous_wickRestriction G.fullCarrier (A.weaklyHolomorphic _).continuousOn
        y hy).continuousOn hsource
  have hR (j : Fin k) : Integrable (R j) := by
    have h := SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen isOpen_univ
      (((Complex.continuous_ofReal.comp (continuous_apply j)).mul
        (continuous_wickRestriction G.fullCarrier (A.weaklyHolomorphic
          (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi)).continuousOn
            y hy)).continuousOn) hsource
    simpa only [R, Q, z, Function.comp_apply, Pi.mul_apply, mul_assoc] using h
  have hpoint (x : Fin k -> Real) :
      (∑ j : Fin k, (I * P j x + R j x + I * (y j : Complex) * Q j x)) = 0 := by
    have hz : z x ∈ A.carrier := by
      rw [G.fullCarrier]
      exact osiiMinkowskiTimeApproach_mem hy zero_lt_one
    have hw := timeWardDefect_eq_zero H
      (by rw [G.fullCarrier]; exact isConnected_osiiTimeRightHalfPlane k) a chi (z x) hz
    calc
      _ = ∑ j : Fin k, I * (P j x + ((y j : Complex) - (x j : Complex) * I) * Q j x) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (wickWard_algebra (P j x) (Q j x) (x j) (y j)).symm
      _ = I * timeWardDefect A a chi (z x) * phi x := by
        rw [timeWardDefect, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        simp only [P, Q, z, osiiMinkowskiTimeApproach, Complex.ofReal_one, one_mul]
        ring
      _ = 0 := by rw [hw]; simp
  have hint : (∑ j : Fin k,
      (I * (∫ x, P j x) + (∫ x, R j x) + I * (y j : Complex) * (∫ x, Q j x))) = 0 := by
    calc
      _ = ∑ j : Fin k, ∫ x, (I * P j x + R j x + I * (y j : Complex) * Q j x) := by
        apply Finset.sum_congr rfl
        intro j _
        have hsum := integral_add (((hP j).const_mul I).add (hR j))
          ((hQ j).const_mul (I * (y j : Complex)))
        have hfirst := integral_add ((hP j).const_mul I) (hR j)
        change (∫ x, I * P j x + R j x + I * (y j : Complex) * Q j x) =
          (∫ x, I * P j x + R j x) + (∫ x, I * (y j : Complex) * Q j x) at hsum
        change (∫ x, I * P j x + R j x) =
          (∫ x, I * P j x) + (∫ x, R j x) at hfirst
        rw [hfirst, integral_const_mul, integral_const_mul] at hsum
        exact hsum.symm
      _ = ∫ x, ∑ j : Fin k, (I * P j x + R j x + I * (y j : Complex) * Q j x) :=
        (integral_finset_sum _ (fun j _ =>
          (((hP j).const_mul I).add (hR j)).add
            ((hQ j).const_mul (I * (y j : Complex))))).symm
      _ = 0 := by simp only [hpoint, integral_zero]
  have hJ (psi : SchwartzMap (Fin k -> Real) Complex)
      (kappa : SchwartzMap (Section43SpatialSpace d k) Complex) :
      J (section43TimeSpatialTensor d k psi kappa) =
        ∫ x, A.distribution (z x) kappa * psi x := by
    simpa only [J, z, one_smul, osiiFullTimeBoundaryPairing,
      coupledTimeSliceCLM_apply] using
      osiiCoupledTimeSlice_tensor A y 1 psi kappa
  have hJx (j : Fin k) :
      J (section43TimeSpatialTensor d k
        (∂_{(Pi.single j (1 : Real) : Fin k -> Real)} phi)
        (spatialCoordinateMultiplier j a chi)) = I * (∫ x, P j x) := by
    rw [hJ]
    exact integral_wickTrace_mul_lineDeriv G.fullCarrier
      (spatialCoordinateMultiplier j a chi) y hy j phi hphi
  have hJt (j : Fin k) :
      J (section43TimeSpatialTensor d k (timeCoordinateMultiplier j phi)
        (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi)) = ∫ x, R j x := by
    rw [hJ]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [timeCoordinateMultiplier_apply, R, Q]
      ring
  have hJq (j : Fin k) :
      J (section43TimeSpatialTensor d k phi
        (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi)) = ∫ x, Q j x := hJ _ _
  change J (osiiCoupledBoostDeriv d k a (section43TimeSpatialTensor d k phi chi)) =
    (-I) * J (osiiCoupledSpatialDeriv d k (osiiSpatialAxisCLM d k a y)
      (section43TimeSpatialTensor d k phi chi))
  rw [osiiCoupledBoostDeriv_tensor, osiiCoupledSpatialDeriv_axis_tensor,
    map_sum, map_sum]
  simp only [map_add, map_smul, smul_eq_mul]
  simp_rw [hJx, hJt, hJq]
  rw [Finset.sum_add_distrib] at hint
  have hlast : (∑ j : Fin k, I * (y j : Complex) * (∫ x, Q j x)) =
      I * ∑ j : Fin k, (y j : Complex) * (∫ x, Q j x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hlast] at hint
  linear_combination hint

/-- Compact temporal tests are dense before full time/spatial tensor
density is used. Both sides are continuous functionals throughout. -/
theorem coupledTimeSlice_boost_tensor
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (H : HasCanonicalReducedCompactStageEdges OS A)
    (a : Fin d) (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    osiiCoupledTimeSlice A y
        (osiiCoupledBoostDeriv d k a (section43TimeSpatialTensor d k phi chi)) =
      (-I) * osiiCoupledTimeSlice A y
        (osiiCoupledSpatialDeriv d k (osiiSpatialAxisCLM d k a y)
          (section43TimeSpatialTensor d k phi chi)) := by
  let J := G.coupledTimeSliceCLM y hy
  have hT : Continuous (fun psi : SchwartzMap (Fin k -> Real) Complex =>
      section43TimeSpatialTensor d k psi chi) := by
    have h := (nPointTimeSpatialSchwartzCLE (d := d) (n := k)).continuous.comp
      (section43TimeSpatialTensorCLM d k chi).continuous
    rw [show (fun psi : SchwartzMap (Fin k -> Real) Complex =>
        section43TimeSpatialTensor d k psi chi) =
        (nPointTimeSpatialSchwartzCLE (d := d) (n := k)) ∘
          (section43TimeSpatialTensorCLM d k chi) by
      funext psi
      simp only [Function.comp_apply, section43TimeSpatialTensorCLM_apply,
        section43NPointTimeSpatialTensor, ContinuousLinearEquiv.apply_symm_apply]]
    exact h
  refine (SchwartzMap.dense_hasCompactSupport (m := k)).induction
    (fun psi hpsi => G.coupledTimeSlice_boost_tensor_compact H a y hy psi chi hpsi)
    (isClosed_eq
      ((J.continuous.comp (osiiCoupledBoostDeriv d k a).continuous).comp hT)
      (continuous_const.mul ((J.continuous.comp
        (osiiCoupledSpatialDeriv d k (osiiSpatialAxisCLM d k a y)).continuous).comp hT))) phi

/-- The exact original-source Ward identity on every coupled Schwartz
source at positive height. The regulator term is retained explicitly. -/
theorem coupledTimeSlice_boost_eq
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (H : HasCanonicalReducedCompactStageEdges OS A)
    (a : Fin d) (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    osiiCoupledTimeSlice A y (osiiCoupledBoostDeriv d k a Phi) =
      (-I) * osiiCoupledTimeSlice A y
        (osiiCoupledSpatialDeriv d k (osiiSpatialAxisCLM d k a y) Phi) := by
  let J := G.coupledTimeSliceCLM y hy
  have heq : J.comp (osiiCoupledBoostDeriv d k a) =
      (-I) • J.comp (osiiCoupledSpatialDeriv d k (osiiSpatialAxisCLM d k a y)) := by
    apply section43TimeSpatial_clm_eq_of_eq_on_timeSpatialTensor
    intro phi chi
    exact G.coupledTimeSlice_boost_tensor H a y hy phi chi
  exact congrArg (fun T => T Phi) heq

/-- The already constructed native boundary annihilates the actual boost
generator. The spatial regulator contribution vanishes by its own boundary
limit, not by pointwise deletion of an imaginary coordinate. -/
theorem timeSpatialBoundary_boostDeriv_eq_zero
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (H : HasCanonicalReducedCompactStageEdges OS A)
    (a : Fin d) (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    B.timeSpatialBoundary (osiiCoupledBoostDeriv d k a Phi) = 0 := by
  let Psi := osiiCoupledSpatialDeriv d k (osiiSpatialAxisCLM d k a eta) Phi
  have hleft := G.tendsto_coupledTimeBoundary B eta heta (osiiCoupledBoostDeriv d k a Phi)
  have hright : Tendsto
      (fun u : Real => (-I) * (u : Complex) * osiiCoupledTimeSlice A (u • eta) Psi)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hu : Tendsto (fun u : Real => (u : Complex))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hc : Tendsto (fun _ : Real => (-I)) (nhdsWithin 0 (Ioi 0)) (nhds (-I)) :=
      tendsto_const_nhds
    simpa only [mul_zero, zero_mul] using (hc.mul hu).mul
      (G.tendsto_coupledTimeBoundary B eta heta Psi)
  have heq : (fun u : Real => (-I) * (u : Complex) *
      osiiCoupledTimeSlice A (u • eta) Psi) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun u => osiiCoupledTimeSlice A (u • eta) (osiiCoupledBoostDeriv d k a Phi)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have h := G.coupledTimeSlice_boost_eq H a (u • eta)
      (osiiTimePositiveCone_isCone k eta heta u hu) Phi
    rw [map_smul, osiiCoupledSpatialDeriv_smul] at h
    have hsmul : osiiCoupledTimeSlice A (u • eta) ((u : Complex) • Psi) =
        (u : Complex) * osiiCoupledTimeSlice A (u • eta) Psi :=
      (G.coupledTimeSliceCLM (u • eta)
        (osiiTimePositiveCone_isCone k eta heta u hu)).map_smul _ _
    change osiiCoupledTimeSlice A (u • eta) (osiiCoupledBoostDeriv d k a Phi) =
      (-I) * osiiCoupledTimeSlice A (u • eta) ((u : Complex) • Psi) at h
    rw [hsmul] at h
    simpa only [mul_assoc] using h.symm
  exact tendsto_nhds_unique hleft (hright.congr' heq)

end OSIIFullTimeStageVladimirovGrowthData
end OSReconstruction
