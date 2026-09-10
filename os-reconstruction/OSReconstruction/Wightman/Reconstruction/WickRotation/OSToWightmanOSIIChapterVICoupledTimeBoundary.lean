/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledTimeDerivative
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISingularTaylorBoundary
import OSReconstruction.SCV.ConeCutoffSchwartz
import Mathlib.Topology.Algebra.Module.StrongTopology










noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical Interval

namespace OSReconstruction

private theorem osiiTimePositiveCone_compl_isCone (k : Nat) :
    IsCone (osiiTimePositiveCone k)ᶜ := by
  intro y hy t ht hty
  apply hy
  intro i
  exact (mul_pos_iff_of_pos_left ht).1 (hty i)

namespace OSIIFullTimeStageTemperedBoundaryData

/-- The existing ordered boundary in the mixed difference-time/spatial
coordinates used by the genuine horizontal integral. -/
def timeSpatialBoundary {d k : Nat} [NeZero d]
    {A : OSIITimeContinuationStage d k}
    (B : OSIIFullTimeStageTemperedBoundaryData A) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex] Complex :=
  B.reducedBoundary.comp
    (nPointTimeSpatialSchwartzCLE (d := d) (n := k)).symm.toContinuousLinearMap

@[simp] theorem timeSpatialBoundary_tensor {d k : Nat} [NeZero d]
    {A : OSIITimeContinuationStage d k}
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    B.timeSpatialBoundary (section43TimeSpatialTensor d k phi chi) =
      B.orderedBoundary (section43OrderedPullbackTimeSpatialTensorCLM d k chi phi) := rfl

end OSIIFullTimeStageTemperedBoundaryData

namespace OSIIFullTimeStageVladimirovGrowthData

variable {d k : Nat}
variable {A : OSIITimeContinuationStage d k}

theorem coupledSliceConstant_smul_le
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) {u : Real} (hu : u ∈ Ioc (0 : Real) 1) :
    G.coupledSliceConstant (u • eta) <=
      G.coupledSliceConstant eta * u ^ (-(G.boundaryDegree : Real)) := by
  have hnorm : ‖u • eta‖ <= ‖eta‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hu.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hu.2
  have huinv : 1 <= u⁻¹ := (one_le_inv₀ hu.1).2 hu.2
  have hdist : 0 <= (Metric.infDist eta (osiiTimePositiveCone k)ᶜ)⁻¹ :=
    inv_nonneg.mpr Metric.infDist_nonneg
  have hscaledDist : 0 <= (Metric.infDist (u • eta) (osiiTimePositiveCone k)ᶜ)⁻¹ :=
    inv_nonneg.mpr Metric.infDist_nonneg
  have hC := G.constant_pos.le
  have hwall : 1 + (Metric.infDist (u • eta) (osiiTimePositiveCone k)ᶜ)⁻¹ <=
      u⁻¹ * (1 + (Metric.infDist eta (osiiTimePositiveCone k)ᶜ)⁻¹) := by
    rw [infDist_smul_cone (osiiTimePositiveCone_compl_isCone k) hu.1, mul_inv_rev]
    nlinarith
  unfold coupledSliceConstant
  calc
    _ <= G.constant * (1 + ‖eta‖) ^ G.polynomialDegree *
        (u⁻¹ * (1 + (Metric.infDist eta (osiiTimePositiveCone k)ᶜ)⁻¹)) ^
          G.boundaryDegree := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) hnorm) _) hC)
        (pow_le_pow_left₀ (by positivity) hwall _) (by positivity) (by positivity)
    _ = _ := by
      rw [mul_pow, Real.rpow_neg hu.1.le, Real.rpow_natCast, inv_pow]
      ring

/-- One fixed full-source rectangle controls every tested jet needed at the
boundary. Both orders are explicit. -/
def coupledBoundaryIndices (G : OSIIFullTimeStageVladimirovGrowthData A) :
    Finset (Nat × Nat) :=
  Finset.Iic
    (G.polynomialDegree + (k + 1) + G.spatialSeminorms.sup Prod.fst,
      G.spatialSeminorms.sup Prod.snd + G.boundaryDegree + 1)

def coupledBoundaryConstant (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) : Real :=
  G.coupledSliceConstant eta * G.coupledSourceConstant *
    (max 1 ‖eta‖) ^ (G.boundaryDegree + 1)

theorem coupledBoundaryConstant_nonneg
    (G : OSIIFullTimeStageVladimirovGrowthData A) (eta : Fin k -> Real) :
    0 <= G.coupledBoundaryConstant eta :=
  mul_nonneg (mul_nonneg (G.coupledSliceConstant_pos eta).le
    G.coupledSourceConstant_nonneg) (by positivity)

private def coupledTimeJet (A : OSIITimeContinuationStage d k)
    (eta : Fin k -> Real)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (j : Nat) (u : Real) : Complex :=
  (-I) ^ j * osiiCoupledTimeSlice A (u • eta)
    (((osiiCoupledTimeDeriv d k eta) ^ j) Phi)

private theorem coupledTimeJet_zero (A : OSIITimeContinuationStage d k)
    (eta : Fin k -> Real)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) (u : Real) :
    coupledTimeJet A eta Phi 0 u = osiiCoupledTimeSlice A (u • eta) Phi := by
  simp [coupledTimeJet]

private theorem hasDerivAt_coupledTimeJet [NeZero d] [NeZero k]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (j : Nat) (u : Real) (hu : 0 < u) :
    HasDerivAt (coupledTimeJet A eta Phi j) (coupledTimeJet A eta Phi (j + 1) u) u := by
  let D := osiiCoupledTimeDeriv d k eta
  have hD : D ((D ^ j) Phi) = (D ^ (j + 1)) Phi := by
    rw [pow_succ', ContinuousLinearMap.mul_apply]
  have h := (G.hasDerivAt_coupledTimeSlice_ray eta heta u hu ((D ^ j) Phi)).const_mul
    ((-I : Complex) ^ j)
  change HasDerivAt
    (fun v => (-I) ^ j * osiiCoupledTimeSlice A (v • eta) ((D ^ j) Phi))
    ((-I) ^ (j + 1) * osiiCoupledTimeSlice A (u • eta) ((D ^ (j + 1)) Phi)) u
  rw [pow_succ, ← hD]
  simpa only [mul_assoc] using h

private theorem sourceSeminorm_directionalPow_le
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (j : Nat) (hj : j <= G.boundaryDegree + 1) :
    G.coupledSourceIndices.sup
        (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex)
        (((osiiCoupledTimeDeriv d k eta) ^ j) Phi) <=
      (max 1 ‖eta‖) ^ (G.boundaryDegree + 1) *
        G.coupledBoundaryIndices.sup
          (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi := by
  let p := G.polynomialDegree + (k + 1) + G.spatialSeminorms.sup Prod.fst
  let l := G.spatialSeminorms.sup Prod.snd
  have hderiv := OSIIChapterVI.schwartz_rectangle_directionalPow_le Phi
    (eta, (0 : Section43SpatialSpace d k)) p l j
  have hdir : ‖eta‖ ^ j <= (max 1 ‖eta‖) ^ (G.boundaryDegree + 1) :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ (le_max_left _ _) hj)
  have hindices :
      (Finset.Iic (p, l + j)).sup
          (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi <=
        G.coupledBoundaryIndices.sup
          (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi := by
    apply Seminorm.finset_sup_apply_le
    · exact apply_nonneg _ _
    intro a ha
    apply Seminorm.le_finset_sup_apply
    have ha' : a.1 <= p ∧ a.2 <= l + j := Finset.mem_Iic.mp ha
    exact Finset.mem_Iic.mpr ⟨ha'.1, by dsimp [l] at *; omega⟩
  have hderiv' : G.coupledSourceIndices.sup
      (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex)
      (((osiiCoupledTimeDeriv d k eta) ^ j) Phi) <=
      ‖eta‖ ^ j * (Finset.Iic (p, l + j)).sup
        (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi := by
    simpa [coupledSourceIndices, OSIIChapterVI.coupledSourceSeminorms,
      osiiCoupledTimeDeriv, Prod.norm_def, p, l] using hderiv
  exact hderiv'.trans (mul_le_mul hdir hindices (apply_nonneg _ _) (by positivity))

private theorem norm_coupledTimeJet_le
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (j : Nat) (hj : j <= G.boundaryDegree + 1)
    (u : Real) (hu : u ∈ Ioc (0 : Real) 1) :
    ‖coupledTimeJet A eta Phi j u‖ <=
      (G.coupledBoundaryConstant eta * G.coupledBoundaryIndices.sup
        (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi) *
        u ^ (-(G.boundaryDegree : Real)) := by
  have hsource := sourceSeminorm_directionalPow_le G eta Phi j hj
  have htime := G.coupledSliceConstant_smul_le eta hu
  have hslice := G.norm_coupledTimeSlice_le
    (osiiTimePositiveCone_isCone k eta heta u hu.1)
    (((osiiCoupledTimeDeriv d k eta) ^ j) Phi)
  have hnorm : ‖coupledTimeJet A eta Phi j u‖ =
      ‖osiiCoupledTimeSlice A (u • eta) (((osiiCoupledTimeDeriv d k eta) ^ j) Phi)‖ := by
    simp [coupledTimeJet, norm_pow]
  rw [hnorm]
  calc
    _ <= (G.coupledSliceConstant eta * u ^ (-(G.boundaryDegree : Real))) *
        G.coupledSourceConstant *
        ((max 1 ‖eta‖) ^ (G.boundaryDegree + 1) *
          G.coupledBoundaryIndices.sup
            (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi) := by
      exact hslice.trans (mul_le_mul
        (mul_le_mul_of_nonneg_right htime G.coupledSourceConstant_nonneg)
        hsource (apply_nonneg _ _)
        (mul_nonneg (mul_nonneg (G.coupledSliceConstant_pos eta).le
          (Real.rpow_nonneg hu.1.le _))
          G.coupledSourceConstant_nonneg))
    _ = _ := by unfold coupledBoundaryConstant; ring

private def coupledBoundaryValue (A : OSIITimeContinuationStage d k)
    (eta : Fin k -> Real)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) : Complex :=
  OSIIChapterVI.singularTaylorBoundaryValue (coupledTimeJet A eta Phi)

private theorem tendsto_coupledBoundaryValue [NeZero d] [NeZero k]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    Tendsto (fun u : Real => osiiCoupledTimeSlice A (u • eta) Phi)
      (nhdsWithin 0 (Ioi 0)) (nhds (coupledBoundaryValue A eta Phi)) := by
  have h := OSIIChapterVI.tendsto_singularTaylorBoundaryValue
      (coupledTimeJet A eta Phi) G.boundaryDegree
      (mul_nonneg (G.coupledBoundaryConstant_nonneg eta) (apply_nonneg _ _))
      (hasDerivAt_coupledTimeJet G eta heta Phi)
      (norm_coupledTimeJet_le G eta heta Phi)
  change Tendsto (fun u => coupledTimeJet A eta Phi 0 u)
    (nhdsWithin 0 (Ioi 0)) (nhds (coupledBoundaryValue A eta Phi)) at h
  simpa only [coupledTimeJet_zero] using h

private theorem norm_coupledBoundaryValue_le [NeZero d] [NeZero k]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    ‖coupledBoundaryValue A eta Phi‖ <=
      (G.coupledBoundaryConstant eta * (2 * G.boundaryDegree + 2 : Nat)) *
        G.coupledBoundaryIndices.sup
          (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi := by
  have h := OSIIChapterVI.norm_singularTaylorBoundaryValue_le
    (coupledTimeJet A eta Phi) G.boundaryDegree
    (mul_nonneg (G.coupledBoundaryConstant_nonneg eta) (apply_nonneg _ _))
    (hasDerivAt_coupledTimeJet G eta heta Phi)
    (norm_coupledTimeJet_le G eta heta Phi)
  simpa only [coupledBoundaryValue, mul_assoc, mul_left_comm, mul_comm] using h

private theorem exists_coupledBoundaryCLM [NeZero d] [NeZero k]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k) :
    exists W : SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex] Complex,
      forall Phi, W Phi = coupledBoundaryValue A eta Phi := by
  let T : Real -> SchwartzMap (Section43TimeSpatialSpace d k) Complex
      →L[Complex] Complex := fun u =>
    if hu : 0 < u then
      G.coupledTimeSliceCLM (u • eta) (osiiTimePositiveCone_isCone k eta heta u hu)
    else 0
  have hpointwise : forall Phi,
      Tendsto (fun u : Real => T u Phi) (nhdsWithin 0 (Ioi 0))
        (nhds (coupledBoundaryValue A eta Phi)) := by
    intro Phi
    apply (tendsto_coupledBoundaryValue G eta heta Phi).congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : 0 < u := hu
    simp only [T, dif_pos hu', coupledTimeSliceCLM_apply]
  have hadd : forall Phi Psi,
      coupledBoundaryValue A eta (Phi + Psi) =
        coupledBoundaryValue A eta Phi + coupledBoundaryValue A eta Psi := by
    intro Phi Psi
    apply tendsto_nhds_unique (hpointwise (Phi + Psi))
    simpa only [map_add] using (hpointwise Phi).add (hpointwise Psi)
  have hsmul : forall (c : Complex) Phi,
      coupledBoundaryValue A eta (c • Phi) = c • coupledBoundaryValue A eta Phi := by
    intro c Phi
    apply tendsto_nhds_unique (hpointwise (c • Phi))
    simpa only [map_smul] using tendsto_const_nhds.smul (hpointwise Phi)
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (𝕜 := Complex)
    (coupledBoundaryValue A eta) hadd hsmul ?_, fun _ => rfl⟩
  exact ⟨G.coupledBoundaryIndices,
    G.coupledBoundaryConstant eta * (2 * G.boundaryDegree + 2 : Nat),
    mul_nonneg (G.coupledBoundaryConstant_nonneg eta) (by positivity),
    norm_coupledBoundaryValue_le G eta heta⟩

private theorem coupledBoundaryValue_eq_native_of_pos [NeZero d] [NeZero k]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    coupledBoundaryValue A eta Phi = B.timeSpatialBoundary Phi := by
  obtain ⟨W, hW⟩ := exists_coupledBoundaryCLM G eta heta
  have heq : W = B.timeSpatialBoundary := by
    apply section43TimeSpatial_clm_eq_of_eq_on_timeSpatialTensor
    intro phi chi
    rw [hW, OSIIFullTimeStageTemperedBoundaryData.timeSpatialBoundary_tensor]
    apply tendsto_nhds_unique
      (l := nhdsWithin (0 : Real) (Ioi 0))
      (f := fun u : Real => osiiFullTimeBoundaryPairing A eta u phi chi)
    · simpa only [osiiCoupledTimeSlice_tensor] using
        tendsto_coupledBoundaryValue G eta heta (section43TimeSpatialTensor d k phi chi)
    · exact B.boundaryValue eta heta phi chi
  exact (hW Phi).symm.trans (congrArg (fun L => L Phi) heq)

theorem tendsto_coupledTimeBoundary_of_pos [NeZero d] [NeZero k]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    Tendsto (fun u : Real => osiiCoupledTimeSlice A (u • eta) Phi)
      (nhdsWithin 0 (Ioi 0)) (nhds (B.timeSpatialBoundary Phi)) := by
  rw [← coupledBoundaryValue_eq_native_of_pos G B eta heta Phi]
  exact tendsto_coupledBoundaryValue G eta heta Phi

theorem norm_timeSpatialBoundary_le_of_pos [NeZero d] [NeZero k]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    ‖B.timeSpatialBoundary Phi‖ <=
      (G.coupledBoundaryConstant eta * (2 * G.boundaryDegree + 2 : Nat)) *
        G.coupledBoundaryIndices.sup
          (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi := by
  rw [← coupledBoundaryValue_eq_native_of_pos G B eta heta Phi]
  exact norm_coupledBoundaryValue_le G eta heta Phi

/-- At arity zero every height is the same point. Tensor uniqueness identifies
the constant full-source slice with any native boundary of that stage. -/
theorem coupledTimeSlice_eq_native_zero {d : Nat} [NeZero d]
    {A : OSIITimeContinuationStage d 0}
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (y : Fin 0 -> Real)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d 0) Complex) :
    osiiCoupledTimeSlice A y Phi = B.timeSpatialBoundary Phi := by
  have hy : y ∈ osiiTimePositiveCone 0 := fun i => Fin.elim0 i
  have heq : G.coupledTimeSliceCLM y hy = B.timeSpatialBoundary := by
    apply section43TimeSpatial_clm_eq_of_eq_on_timeSpatialTensor
    intro phi chi
    rw [coupledTimeSliceCLM_apply,
      OSIIFullTimeStageTemperedBoundaryData.timeSpatialBoundary_tensor]
    have h := B.boundaryValue y hy phi chi
    have hfun : (fun u : Real => osiiFullTimeBoundaryPairing A y u phi chi) =
        fun _ : Real => osiiCoupledTimeSlice A y (section43TimeSpatialTensor d 0 phi chi) := by
      funext u
      rw [← osiiCoupledTimeSlice_tensor]
      exact congrArg (fun v => osiiCoupledTimeSlice A v
        (section43TimeSpatialTensor d 0 phi chi)) (Subsingleton.elim _ _)
    rw [hfun] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  exact congrArg (fun L => L Phi) heq

theorem tendsto_coupledTimeBoundary [NeZero d]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    Tendsto (fun u : Real => osiiCoupledTimeSlice A (u • eta) Phi)
      (nhdsWithin 0 (Ioi 0)) (nhds (B.timeSpatialBoundary Phi)) := by
  by_cases hk : k = 0
  · subst k
    simpa only [G.coupledTimeSlice_eq_native_zero B] using
      (tendsto_const_nhds : Tendsto (fun _ : Real => B.timeSpatialBoundary Phi)
        (nhdsWithin 0 (Ioi 0)) (nhds (B.timeSpatialBoundary Phi)))
  · letI : NeZero k := ⟨hk⟩
    exact G.tendsto_coupledTimeBoundary_of_pos B eta heta Phi

theorem norm_timeSpatialBoundary_le [NeZero d]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (B : OSIIFullTimeStageTemperedBoundaryData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    ‖B.timeSpatialBoundary Phi‖ <=
      (G.coupledBoundaryConstant eta * (2 * G.boundaryDegree + 2 : Nat)) *
        G.coupledBoundaryIndices.sup
          (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi := by
  by_cases hk : k = 0
  · subst k
    rw [← G.coupledTimeSlice_eq_native_zero B eta Phi]
    have hsource := sourceSeminorm_directionalPow_le G eta Phi 0 (by omega)
    simp only [pow_zero, ContinuousLinearMap.one_apply] at hsource
    have hbase := (G.norm_coupledTimeSlice_le heta Phi).trans
      (mul_le_mul_of_nonneg_left hsource
        (mul_nonneg (G.coupledSliceConstant_pos eta).le G.coupledSourceConstant_nonneg))
    have hfactor : (1 : Real) <= ((2 * G.boundaryDegree + 2 : Nat) : Real) := by
      exact_mod_cast (show 1 <= 2 * G.boundaryDegree + 2 by omega)
    calc
      _ <= G.coupledBoundaryConstant eta *
          G.coupledBoundaryIndices.sup
            (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d 0) Complex) Phi := by
        simpa only [coupledBoundaryConstant, mul_assoc] using hbase
      _ <= _ := by
        apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
        simpa using mul_le_mul_of_nonneg_left hfactor (G.coupledBoundaryConstant_nonneg eta)
  · letI : NeZero k := ⟨hk⟩
    exact G.norm_timeSpatialBoundary_le_of_pos B eta heta Phi

end OSIIFullTimeStageVladimirovGrowthData
end OSReconstruction
