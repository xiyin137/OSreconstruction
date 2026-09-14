import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledSourceDecay
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITimeBoundary

/-!
# Actual coupled-source time slices

These are the horizontal integrals of the same distribution-valued Chapter V
continuation. No spatial complexification, separated-source restriction, or
new boundary distribution is used.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat}
variable {A : OSIITimeContinuationStage d k}

/-- Pair the continued spatial distribution with a genuinely coupled
time/spatial Schwartz source at positive imaginary height `y`. -/
def osiiCoupledTimeSlice
    (A : OSIITimeContinuationStage d k) (y : Fin k -> Real)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) : Complex :=
  OSIIChapterVI.coupledSourceIntegral
    (fun x => A.distribution (osiiMinkowskiTimeApproach y x 1)) Phi

@[simp] theorem osiiCoupledTimeSlice_tensor [NeZero d]
    (A : OSIITimeContinuationStage d k) (eta : Fin k -> Real) (t : Real)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    osiiCoupledTimeSlice A (t • eta) (section43TimeSpatialTensor d k phi chi) =
      osiiFullTimeBoundaryPairing A eta t phi chi := by
  apply integral_congr_ae
  filter_upwards with x
  have hslice : SCV.schwartzPartialEval₁
      (section43TimeSpatialTensor d k phi chi) x = phi x • chi := by
    ext v
    simp [smul_eq_mul]
  rw [hslice, map_smul]
  have hpoint : osiiMinkowskiTimeApproach (t • eta) x 1 =
      osiiMinkowskiTimeApproach eta x t := by
    ext i
    simp [osiiMinkowskiTimeApproach]
  rw [hpoint]
  exact mul_comm _ _

namespace OSIIFullTimeStageVladimirovGrowthData

def coupledSliceConstant (G : OSIIFullTimeStageVladimirovGrowthData A)
    (y : Fin k -> Real) : Real :=
  G.constant * (1 + ‖y‖) ^ G.polynomialDegree *
    (1 + (Metric.infDist y (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree

theorem coupledSliceConstant_pos (G : OSIIFullTimeStageVladimirovGrowthData A)
    (y : Fin k -> Real) : 0 < G.coupledSliceConstant y := by
  unfold coupledSliceConstant
  have hdist : 0 <= (Metric.infDist y (osiiTimePositiveCone k)ᶜ)⁻¹ :=
    inv_nonneg.mpr Metric.infDist_nonneg
  have hC := G.constant_pos
  positivity

theorem continuousAt_coupledSliceConstant
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k) :
    ContinuousAt G.coupledSliceConstant y := by
  have hinv := Metric.continuousAt_inv_infDist_pt
    (s := (osiiTimePositiveCone k)ᶜ)
    (x := y) (by simpa [(osiiTimePositiveCone_open k).isClosed_compl.closure_eq] using hy)
  exact (continuousAt_const.mul
    ((continuousAt_const.add continuous_norm.continuousAt).pow _)).mul
      ((continuousAt_const.add hinv).pow _)

theorem continuous_horizontalSpatialPairing
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    Continuous (fun x => A.distribution (osiiMinkowskiTimeApproach y x 1) chi) := by
  apply (A.weaklyHolomorphic chi).continuousOn.comp_continuous
  · unfold osiiMinkowskiTimeApproach
    fun_prop
  · intro x
    rw [G.fullCarrier]
    exact osiiMinkowskiTimeApproach_mem hy zero_lt_one

theorem norm_horizontalSpatialPairing_le
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k)
    (x : Fin k -> Real)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    ‖A.distribution (osiiMinkowskiTimeApproach y x 1) chi‖ <=
      G.coupledSliceConstant y * (1 + ‖x‖) ^ G.polynomialDegree *
        G.spatialSeminorms.sup
          (schwartzSeminormFamily Complex (Section43SpatialSpace d k) Complex) chi := by
  have hnorm : ‖osiiMinkowskiTimeApproach y x 1‖ <= ‖y‖ + ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    calc
      ‖osiiMinkowskiTimeApproach y x 1 i‖ <= ‖(y i : Complex)‖ +
          ‖(x i : Complex) * I‖ := by
        simpa [osiiMinkowskiTimeApproach] using
          norm_sub_le (y i : Complex) ((x i : Complex) * I)
      _ = ‖y i‖ + ‖x i‖ := by simp
      _ <= ‖y‖ + ‖x‖ := add_le_add (norm_le_pi_norm y i) (norm_le_pi_norm x i)
  have hbase : 1 + ‖osiiMinkowskiTimeApproach y x 1‖ <=
      (1 + ‖y‖) * (1 + ‖x‖) := by
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hgrowth := G.bound (osiiMinkowskiTimeApproach y x 1)
    (osiiMinkowskiTimeApproach_mem hy zero_lt_one) chi
  have hdist : 0 <= (Metric.infDist y (osiiTimePositiveCone k)ᶜ)⁻¹ :=
    inv_nonneg.mpr Metric.infDist_nonneg
  have hp := pow_le_pow_left₀ (by positivity) hbase G.polynomialDegree
  calc
    ‖A.distribution (osiiMinkowskiTimeApproach y x 1) chi‖ <=
        G.constant * (1 + ‖osiiMinkowskiTimeApproach y x 1‖) ^ G.polynomialDegree *
          (1 + (Metric.infDist y (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree *
            G.spatialSeminorms.sup
              (schwartzSeminormFamily Complex (Section43SpatialSpace d k) Complex) chi := by
      simpa [osiiTimeBoundaryDistance, osiiMinkowskiTimeApproach] using hgrowth
    _ <= G.constant * ((1 + ‖y‖) * (1 + ‖x‖)) ^ G.polynomialDegree *
          (1 + (Metric.infDist y (osiiTimePositiveCone k)ᶜ)⁻¹) ^ G.boundaryDegree *
            G.spatialSeminorms.sup
              (schwartzSeminormFamily Complex (Section43SpatialSpace d k) Complex) chi := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp G.constant_pos.le) (by positivity))
        (apply_nonneg _ _)
    _ = _ := by unfold coupledSliceConstant; rw [mul_pow]; ring

def coupledSourceIndices (G : OSIIFullTimeStageVladimirovGrowthData A) :
    Finset (Nat × Nat) :=
  OSIIChapterVI.coupledSourceSeminorms G.spatialSeminorms
    (G.polynomialDegree + (k + 1))

def coupledSourceConstant (G : OSIIFullTimeStageVladimirovGrowthData A) : Real :=
  2 ^ (G.polynomialDegree + (k + 1) + G.spatialSeminorms.sup Prod.fst) *
    OSIIChapterVI.timeDecayIntegral k

theorem coupledSourceConstant_nonneg (G : OSIIFullTimeStageVladimirovGrowthData A) :
    0 <= G.coupledSourceConstant :=
  mul_nonneg (by positivity) (OSIIChapterVI.timeDecayIntegral_nonneg k)

theorem integrable_coupledTimeSlice
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    Integrable (fun x : Fin k -> Real =>
      A.distribution (osiiMinkowskiTimeApproach y x 1)
        (SCV.schwartzPartialEval₁ Phi x)) :=
  OSIIChapterVI.integrable_coupledSourcePairing _
    (G.continuous_horizontalSpatialPairing hy) G.spatialSeminorms
    (G.coupledSliceConstant y) G.polynomialDegree (G.coupledSliceConstant_pos y)
    (G.norm_horizontalSpatialPairing_le hy) Phi

theorem norm_coupledTimeSlice_le
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    {y : Fin k -> Real} (hy : y ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    ‖osiiCoupledTimeSlice A y Phi‖ <=
      G.coupledSliceConstant y * G.coupledSourceConstant *
        G.coupledSourceIndices.sup
          (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi := by
  simpa [osiiCoupledTimeSlice, coupledSourceIndices, coupledSourceConstant, mul_assoc] using
    OSIIChapterVI.norm_coupledSourceIntegral_le _ G.spatialSeminorms
      (G.coupledSliceConstant y) G.polynomialDegree (G.coupledSliceConstant_pos y).le
      (G.norm_horizontalSpatialPairing_le hy) Phi

/-- The genuine coupled horizontal integral, as a Schwartz functional. -/
def coupledTimeSliceCLM
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex] Complex :=
  OSIIChapterVI.coupledSourceIntegralCLM _
    (G.continuous_horizontalSpatialPairing hy) G.spatialSeminorms
    (G.coupledSliceConstant y) G.polynomialDegree (G.coupledSliceConstant_pos y)
    (G.norm_horizontalSpatialPairing_le hy)

@[simp] theorem coupledTimeSliceCLM_apply
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    G.coupledTimeSliceCLM y hy Phi = osiiCoupledTimeSlice A y Phi := rfl

theorem continuousOn_coupledTimeSlice
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    ContinuousOn (fun y => osiiCoupledTimeSlice A y Phi)
      (osiiTimePositiveCone k) := by
  intro y hy
  let B := G.coupledSliceConstant y + 1
  have hB : 0 < B := by dsimp [B]; linarith [G.coupledSliceConstant_pos y]
  have hnear : ∀ᶠ v in nhdsWithin y (osiiTimePositiveCone k),
      G.coupledSliceConstant v <= B := by
    have h := ((G.continuousAt_coupledSliceConstant hy).tendsto.mono_left
      (nhdsWithin_le_nhds (s := osiiTimePositiveCone k))).eventually
        (Iio_mem_nhds (show G.coupledSliceConstant y < B by dsimp [B]; linarith))
    filter_upwards [h] with v hv
    exact hv.le
  let P := G.coupledSourceIndices.sup
    (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi
  let Q := G.polynomialDegree + (k + 1) + G.spatialSeminorms.sup Prod.fst
  change Tendsto
    (fun v => ∫ x : Fin k -> Real,
      A.distribution (osiiMinkowskiTimeApproach v x 1)
        (SCV.schwartzPartialEval₁ Phi x)) _
    (nhds (∫ x : Fin k -> Real,
      A.distribution (osiiMinkowskiTimeApproach y x 1)
        (SCV.schwartzPartialEval₁ Phi x)))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : Fin k -> Real =>
      (1 + ‖x‖) ^ (-((k + 1 : Nat) : Real)) * (B * 2 ^ Q * P))
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact (G.integrable_coupledTimeSlice hv Phi).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, hnear] with v hv hvB
    have hbound : forall x chi,
        ‖A.distribution (osiiMinkowskiTimeApproach v x 1) chi‖ <=
          B * (1 + ‖x‖) ^ G.polynomialDegree *
            G.spatialSeminorms.sup
              (schwartzSeminormFamily Complex
                (Section43SpatialSpace d k) Complex) chi := by
      intro x chi
      exact (G.norm_horizontalSpatialPairing_le hv x chi).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hvB (by positivity)) (apply_nonneg _ _))
    filter_upwards with x
    exact OSIIChapterVI.norm_coupledSourcePairing_le _ G.spatialSeminorms
      B G.polynomialDegree hB.le hbound Phi x
  · exact (OSIIChapterVI.integrable_timeDecay k).mul_const _
  · filter_upwards with x
    have hpath : Continuous
        (fun v : Fin k -> Real => osiiMinkowskiTimeApproach v x 1) := by
      unfold osiiMinkowskiTimeApproach
      fun_prop
    exact ((A.weaklyHolomorphic (SCV.schwartzPartialEval₁ Phi x)).continuousOn.comp
      hpath.continuousOn (by
        intro v hv
        rw [G.fullCarrier]
        exact osiiMinkowskiTimeApproach_mem hv zero_lt_one)) y hy

end OSIIFullTimeStageVladimirovGrowthData
end OSReconstruction
