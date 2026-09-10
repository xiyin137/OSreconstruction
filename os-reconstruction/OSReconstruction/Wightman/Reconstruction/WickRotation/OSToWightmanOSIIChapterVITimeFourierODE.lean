/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledTimeBoundary
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform

set_option backward.isDefEq.respectTransparency false











noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical LineDeriv

namespace OSReconstruction

/-- The real-linear momentum pairing, valued in `Complex` so that it can be
used by the compact exponential test construction. -/
def osiiTimeMomentumLinearForm {k : Nat} (eta : Fin k -> Real) :
    (Fin k -> Real) →L[Real] Complex :=
  Complex.ofRealCLM.comp (∑ i : Fin k, eta i •
    ContinuousLinearMap.proj (R := Real) (ι := Fin k) (φ := fun _ => Real) i)

@[simp] theorem osiiTimeMomentumLinearForm_apply {k : Nat}
    (eta p : Fin k -> Real) :
    osiiTimeMomentumLinearForm eta p =
      ∑ i : Fin k, (eta i : Complex) * (p i : Complex) := by
  simp [osiiTimeMomentumLinearForm]

@[simp] theorem osiiTimeMomentumLinearForm_re {k : Nat}
    (eta p : Fin k -> Real) :
    (osiiTimeMomentumLinearForm eta p).re = ∑ i : Fin k, eta i * p i := by
  simp [osiiTimeMomentumLinearForm]

/-- Multiplication by the ordinary coordinate pairing with a time direction. -/
def osiiTimeMomentumMultiplier {k : Nat} (eta : Fin k -> Real) :
    SchwartzMap (Fin k -> Real) Complex →L[Complex]
      SchwartzMap (Fin k -> Real) Complex :=
  SchwartzMap.smulLeftCLM Complex
    (fun p : Fin k -> Real => ∑ i : Fin k, (eta i : Complex) * (p i : Complex))

theorem osiiTimeMomentumMultiplier_eq_smulLeftCLM {k : Nat}
    (eta : Fin k -> Real) :
    osiiTimeMomentumMultiplier eta =
      SchwartzMap.smulLeftCLM Complex (osiiTimeMomentumLinearForm eta) := by
  unfold osiiTimeMomentumMultiplier
  congr 1
  funext p
  exact (osiiTimeMomentumLinearForm_apply eta p).symm

/-- This sign is forced by the inverse of the existing positive-phase Fourier
transform; no alternative Fourier convention is introduced. -/
theorem directionalDerivSchwartz_physicsFourierFlatInvCLM {k : Nat}
    (eta : Fin k -> Real) (psi : SchwartzMap (Fin k -> Real) Complex) :
    directionalDerivSchwartz eta (physicsFourierFlatInvCLM psi) =
      (-I) • physicsFourierFlatInvCLM (osiiTimeMomentumMultiplier eta psi) := by
  have hinj : Function.Injective
      (physicsFourierFlatCLM : SchwartzMap (Fin k -> Real) Complex ->
        SchwartzMap (Fin k -> Real) Complex) := by
    intro phi theta h
    simpa only [physicsFourierFlatInvCLM_left] using
      congrArg physicsFourierFlatInvCLM h
  apply hinj
  change physicsFourierFlatCLM (∂_{eta} (physicsFourierFlatInvCLM psi)) = _
  rw [physicsFourierFlatCLM_lineDeriv_eq_pairingMultiplier,
    physicsFourierFlatCLM_inv_right, map_smul, physicsFourierFlatCLM_inv_right]
  rfl

/-- The actual time-frequency pairing before taking a boundary limit. -/
def osiiFullTimeFrequencyPairing {d k : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d k) (eta : Fin k -> Real) (t : Real)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) : Complex :=
  osiiFullTimeBoundaryPairing A eta t (physicsFourierFlatInvCLM psi) chi

private theorem osiiFullTimeBoundaryPairing_smul {d k : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d k) (eta : Fin k -> Real) (t : Real)
    (c : Complex) (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    osiiFullTimeBoundaryPairing A eta t (c • phi) chi =
      c * osiiFullTimeBoundaryPairing A eta t phi chi := by
  simp only [osiiFullTimeBoundaryPairing, SchwartzMap.smul_apply, smul_eq_mul,
    mul_left_comm _ c]
  exact MeasureTheory.integral_const_mul c _

private def timeFrequencyTensorCLM (d k : Nat) [NeZero d]
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    SchwartzMap (Fin k -> Real) Complex →L[Complex]
      SchwartzMap (Section43TimeSpatialSpace d k) Complex :=
  (nPointTimeSpatialSchwartzCLE (d := d) (n := k)).toContinuousLinearMap.comp
    ((section43TimeSpatialTensorCLM d k chi).comp physicsFourierFlatInvCLM)

private theorem timeFrequencyTensorCLM_apply {d k : Nat} [NeZero d]
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex) :
    timeFrequencyTensorCLM d k chi psi =
      section43TimeSpatialTensor d k (physicsFourierFlatInvCLM psi) chi := by
  simp [timeFrequencyTensorCLM, section43NPointTimeSpatialTensor]

namespace OSIIFullTimeStageVladimirovGrowthData

variable {d k : Nat} [NeZero d]
variable {A : OSIITimeContinuationStage d k}

/-- The actual horizontal frequency distribution at a positive height. -/
def timeFrequencySliceCLM
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k) :
    SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex :=
  (G.coupledTimeSliceCLM y hy).comp (timeFrequencyTensorCLM d k chi)

@[simp] theorem timeFrequencySliceCLM_smul_apply
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (t : Real) (ht : 0 < t) (psi : SchwartzMap (Fin k -> Real) Complex) :
    G.timeFrequencySliceCLM chi (t • eta)
        (osiiTimePositiveCone_isCone k eta heta t ht) psi =
      osiiFullTimeFrequencyPairing A eta t psi chi := by
  rw [timeFrequencySliceCLM, ContinuousLinearMap.comp_apply,
    coupledTimeSliceCLM_apply, timeFrequencyTensorCLM_apply,
    osiiCoupledTimeSlice_tensor]
  rfl

omit [NeZero d] in
/-- Global growth, unlike compact-height growth, bounds every large height on
one positive ray by the same polynomial. -/
theorem coupledSliceConstant_largeHeight_le
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) {t : Real} (ht : 1 <= t) :
    G.coupledSliceConstant (t • eta) <=
      G.coupledSliceConstant eta * t ^ G.polynomialDegree := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hcone : IsCone (osiiTimePositiveCone k)ᶜ := by
    intro y hy u hu huy
    apply hy
    intro i
    exact (mul_pos_iff_of_pos_left hu).1 (huy i)
  have hnorm : 1 + ‖t • eta‖ <= t * (1 + ‖eta‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    nlinarith
  have hwall :
      1 + (Metric.infDist (t • eta) (osiiTimePositiveCone k)ᶜ)⁻¹ <=
        1 + (Metric.infDist eta (osiiTimePositiveCone k)ᶜ)⁻¹ := by
    rw [infDist_smul_cone hcone htpos, mul_inv_rev]
    have hdelta : 0 <= (Metric.infDist eta (osiiTimePositiveCone k)ᶜ)⁻¹ :=
      inv_nonneg.mpr Metric.infDist_nonneg
    nlinarith [inv_le_one_of_one_le₀ ht]
  have hdelta : 0 <= (Metric.infDist (t • eta) (osiiTimePositiveCone k)ᶜ)⁻¹ :=
    inv_nonneg.mpr Metric.infDist_nonneg
  unfold coupledSliceConstant
  calc
    _ <= G.constant * (t * (1 + ‖eta‖)) ^ G.polynomialDegree *
        (1 + (Metric.infDist eta (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hnorm _) G.constant_pos.le)
        (pow_le_pow_left₀ (by positivity) hwall _) (by positivity)
        (mul_nonneg G.constant_pos.le (pow_nonneg (by positivity) _))
    _ = _ := by rw [mul_pow]; ring

/-- A single finite momentum seminorm controls the entire large-height ray.
This is the polynomial estimate required to kill a compact negative-energy
test after exponential damping. -/
theorem exists_positiveFrequencyPairing_largeHeight_bound
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    exists s : Finset (Nat × Nat), exists C : Real, 0 < C ∧
      forall t : Real, 1 <= t ->
      forall psi : SchwartzMap (Fin k -> Real) Complex,
        ‖osiiFullTimeFrequencyPairing A eta t psi chi‖ <=
          C * t ^ G.polynomialDegree *
            s.sup (schwartzSeminormFamily Complex (Fin k -> Real) Complex) psi := by
  let T := timeFrequencyTensorCLM d k chi
  let q : Seminorm Complex (SchwartzMap (Fin k -> Real) Complex) :=
    (G.coupledSourceIndices.sup
      (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex)).comp
        T.toLinearMap
  have hq : Continuous q :=
    (((schwartz_withSeminorms Complex (Section43TimeSpatialSpace d k) Complex
      ).finset_sups).continuous_seminorm G.coupledSourceIndices).comp T.continuous
  obtain ⟨s, D, _, hD⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms Complex (Fin k -> Real) Complex) q hq
  let C := G.coupledSliceConstant eta * G.coupledSourceConstant * (D : Real)
  have hC : 0 <= C :=
    mul_nonneg (mul_nonneg (G.coupledSliceConstant_pos eta).le
      G.coupledSourceConstant_nonneg) D.coe_nonneg
  refine ⟨s, C + 1, by linarith, ?_⟩
  intro t ht psi
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hsource : G.coupledSourceIndices.sup
      (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex)
        (T psi) <=
      (D : Real) * s.sup
        (schwartzSeminormFamily Complex (Fin k -> Real) Complex) psi := by
    simpa only [q, Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def,
      smul_eq_mul] using hD psi
  have hslice := G.norm_coupledTimeSlice_le
    (osiiTimePositiveCone_isCone k eta heta t htpos) (T psi)
  rw [show T psi = section43TimeSpatialTensor d k
    (physicsFourierFlatInvCLM psi) chi from timeFrequencyTensorCLM_apply chi psi,
    osiiCoupledTimeSlice_tensor] at hslice
  change ‖osiiFullTimeFrequencyPairing A eta t psi chi‖ <= _ at hslice
  have hbase := G.coupledSliceConstant_largeHeight_le eta ht
  have hp : 0 <= s.sup
      (schwartzSeminormFamily Complex (Fin k -> Real) Complex) psi := apply_nonneg _ _
  calc
    _ <= (G.coupledSliceConstant eta * t ^ G.polynomialDegree) *
        G.coupledSourceConstant *
        ((D : Real) * s.sup
          (schwartzSeminormFamily Complex (Fin k -> Real) Complex) psi) := by
      exact hslice.trans (mul_le_mul
        (mul_le_mul_of_nonneg_right hbase G.coupledSourceConstant_nonneg)
        hsource (apply_nonneg _ _)
        (mul_nonneg (mul_nonneg (G.coupledSliceConstant_pos eta).le
          (pow_nonneg htpos.le _)) G.coupledSourceConstant_nonneg))
    _ = C * t ^ G.polynomialDegree * s.sup
        (schwartzSeminormFamily Complex (Fin k -> Real) Complex) psi := by
      dsimp [C]
      ring
    _ <= _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C <= C + 1) (by positivity)) hp

/-- The frequency-side Cauchy-Riemann equation at every positive height. -/
theorem hasDerivAt_positiveFrequencyPairing
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (t : Real) (ht : 0 < t)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    HasDerivAt (fun u => osiiFullTimeFrequencyPairing A eta u psi chi)
      (-osiiFullTimeFrequencyPairing A eta t (osiiTimeMomentumMultiplier eta psi) chi) t := by
  have h := G.hasDerivAt_positiveSlicePairing eta heta t ht
    (physicsFourierFlatInvCLM psi) chi
  rw [directionalDerivSchwartz_physicsFourierFlatInvCLM,
    osiiFullTimeBoundaryPairing_smul] at h
  have hsign (z : Complex) : -I * (-I * z) = -z := by
    calc
      -I * (-I * z) = I ^ 2 * z := by ring
      _ = -z := by simp
  simpa only [hsign, osiiFullTimeFrequencyPairing] using h

/-- The same frequency slices tend to the Fourier transform of the already
constructed native time boundary. -/
theorem tendsto_positiveFrequencyPairing
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    Tendsto (fun t => osiiFullTimeFrequencyPairing A eta t psi chi)
      (nhdsWithin 0 (Ioi 0))
      (nhds ((G.timeBoundary chi).comp physicsFourierFlatInvCLM psi)) :=
  G.timeBoundary_boundaryValue chi eta heta (physicsFourierFlatInvCLM psi)

end OSIIFullTimeStageVladimirovGrowthData
end OSReconstruction
