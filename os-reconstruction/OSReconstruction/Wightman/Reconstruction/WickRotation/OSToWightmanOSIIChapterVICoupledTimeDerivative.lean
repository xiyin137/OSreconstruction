import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledTimeSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFullBoundary

/-!
# Tested time derivatives on coupled sources

The scalar Cauchy--Riemann identity first gives an integrated identity on
time/spatial tensors. Uniform full-source slice bounds make both sides
continuous Schwartz functionals, so tensor density proves the same identity
for every coupled source. The fundamental theorem of calculus then supplies
the actual derivative.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical Interval

namespace OSReconstruction

private def schwartzIntervalIntegralCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (L : Real -> SchwartzMap E Complex →L[Complex] Complex)
    (a b : Real)
    (hcont : forall Phi, ContinuousOn (fun u => L u Phi) (uIcc a b))
    (s : Finset (Nat × Nat)) (C : Real) (hC : 0 <= C)
    (hbound : forall u, u ∈ uIcc a b -> forall Phi,
      ‖L u Phi‖ <= C * s.sup (schwartzSeminormFamily Complex E Complex) Phi) :
    SchwartzMap E Complex →L[Complex] Complex :=
  SchwartzMap.mkCLMtoNormedSpace (𝕜 := Complex)
    (fun Phi => ∫ u in a..b, L u Phi)
    (fun Phi Psi => by
      simp only [map_add]
      exact intervalIntegral.integral_add
        (hcont Phi).intervalIntegrable (hcont Psi).intervalIntegrable)
    (fun c Phi => by
      simp only [map_smul]
      exact intervalIntegral.integral_smul c _)
    (by
      refine ⟨s, C * |b - a|, mul_nonneg hC (abs_nonneg _), ?_⟩
      intro Phi
      exact (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun u hu => hbound u (uIoc_subset_uIcc hu) Phi)).trans_eq (by ring))

/-- Time differentiation on the complete mixed Schwartz source. -/
def osiiCoupledTimeDeriv (d k : Nat) (eta : Fin k -> Real) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex]
      SchwartzMap (Section43TimeSpatialSpace d k) Complex :=
  LineDeriv.lineDerivOpCLM Complex
    (SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (eta, (0 : Section43SpatialSpace d k))

@[simp] theorem osiiCoupledTimeDeriv_tensor
    (d k : Nat) (eta : Fin k -> Real)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    osiiCoupledTimeDeriv d k eta (section43TimeSpatialTensor d k phi chi) =
      section43TimeSpatialTensor d k (directionalDerivSchwartz eta phi) chi := by
  ext p
  rcases p with ⟨x, v⟩
  have hfun : (section43TimeSpatialTensor d k phi chi :
      Section43TimeSpatialSpace d k -> Complex) =
      fun p => phi p.1 * chi p.2 := by
    funext p
    exact section43TimeSpatialTensor_apply d k phi chi p.1 p.2
  have hphi := (phi.hasFDerivAt x).comp (x, v)
    (ContinuousLinearMap.fst Real (Fin k -> Real)
      (Section43SpatialSpace d k)).hasFDerivAt
  have hchi := (chi.hasFDerivAt v).comp (x, v)
    (ContinuousLinearMap.snd Real (Fin k -> Real)
      (Section43SpatialSpace d k)).hasFDerivAt
  rw [section43TimeSpatialTensor_apply]
  change fderiv Real (section43TimeSpatialTensor d k phi chi :
      Section43TimeSpatialSpace d k -> Complex) (x, v) (eta, 0) =
    (directionalDerivSchwartz eta phi) x * chi v
  have hd := (hphi.mul hchi).fderiv
  change fderiv Real (fun p : Section43TimeSpatialSpace d k => phi p.1 * chi p.2)
    (x, v) = _ at hd
  rw [hfun, hd]
  change phi x * (fderiv Real (chi : Section43SpatialSpace d k -> Complex) v) 0 +
      chi v * (fderiv Real (phi : (Fin k -> Real) -> Complex) x) eta =
    (fderiv Real (phi : (Fin k -> Real) -> Complex) x) eta * chi v
  simp [mul_comm]

namespace OSIIFullTimeStageVladimirovGrowthData

variable {d k : Nat}
variable {A : OSIITimeContinuationStage d k}

theorem continuousOn_coupledTimeSlice_ray
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    ContinuousOn (fun u : Real => osiiCoupledTimeSlice A (u • eta) Phi) (Ioi 0) :=
  (G.continuousOn_coupledTimeSlice Phi).comp
    (continuous_id.smul continuous_const).continuousOn
    (fun u hu => osiiTimePositiveCone_isCone k eta heta u hu)

private theorem positive_of_mem_uIcc {a b u : Real}
    (ha : 0 < a) (hb : 0 < b) (hu : u ∈ uIcc a b) : 0 < u :=
  (lt_min ha hb).trans_le hu.1

/-- Integrating the genuine coupled slices over a compact positive ray
interval is a continuous full-source functional. -/
theorem exists_coupledTimeRayIntegralCLM
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    exists L : SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex] Complex,
      forall Phi, L Phi = ∫ u in a..b, osiiCoupledTimeSlice A (u • eta) Phi := by
  let T : Real -> SchwartzMap (Section43TimeSpatialSpace d k) Complex
      →L[Complex] Complex := fun u =>
    if hu : 0 < u then
      G.coupledTimeSliceCLM (u • eta) (osiiTimePositiveCone_isCone k eta heta u hu)
    else 0
  have hT (u : Real) (hu : 0 < u) (Phi) :
      T u Phi = osiiCoupledTimeSlice A (u • eta) Phi := by simp [T, hu]
  have hcont : forall Phi, ContinuousOn (fun u => T u Phi) (uIcc a b) := by
    intro Phi
    apply ((G.continuousOn_coupledTimeSlice_ray eta heta Phi).mono
      (fun u hu => positive_of_mem_uIcc ha hb hu)).congr
    intro u hu
    exact hT u (positive_of_mem_uIcc ha hb hu) Phi
  have hconstant : ContinuousOn (fun u : Real => G.coupledSliceConstant (u • eta))
      (uIcc a b) := by
    intro u hu
    have hpath : Continuous (fun v : Real => v • eta) :=
      continuous_id.smul continuous_const
    have hout := (G.continuousAt_coupledSliceConstant
      (osiiTimePositiveCone_isCone k eta heta u (positive_of_mem_uIcc ha hb hu))).tendsto
    have hcomp : Tendsto (fun v : Real => G.coupledSliceConstant (v • eta))
        (nhds u) (nhds (G.coupledSliceConstant (u • eta))) :=
      hout.comp (hpath.tendsto u)
    exact hcomp.mono_left nhdsWithin_le_nhds
  obtain ⟨B, hB⟩ := isCompact_uIcc.bddAbove_image hconstant
  let C := max B 0 * G.coupledSourceConstant
  have hC : 0 <= C := mul_nonneg (le_max_right _ _) G.coupledSourceConstant_nonneg
  have hbound : forall u, u ∈ uIcc a b -> forall Phi,
      ‖T u Phi‖ <= C * G.coupledSourceIndices.sup
        (schwartzSeminormFamily Complex (Section43TimeSpatialSpace d k) Complex) Phi := by
    intro u hu Phi
    rw [hT u (positive_of_mem_uIcc ha hb hu)]
    have huB : G.coupledSliceConstant (u • eta) <= max B 0 :=
      (hB (mem_image_of_mem _ hu)).trans (le_max_left _ _)
    exact (G.norm_coupledTimeSlice_le
      (osiiTimePositiveCone_isCone k eta heta u (positive_of_mem_uIcc ha hb hu)) Phi).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right huB G.coupledSourceConstant_nonneg)
          (apply_nonneg _ _))
  refine ⟨schwartzIntervalIntegralCLM T a b hcont G.coupledSourceIndices C hC hbound, ?_⟩
  intro Phi
  change (∫ u in a..b, T u Phi) = _
  exact intervalIntegral.integral_congr
    (fun u hu => hT u (positive_of_mem_uIcc ha hb hu) Phi)

/-- The integrated Cauchy--Riemann identity on the entire coupled Schwartz
space. Density is used only after both sides are continuous functionals. -/
theorem coupledTimeSlice_sub_eq_integral [NeZero d] [NeZero k]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    osiiCoupledTimeSlice A (b • eta) Phi - osiiCoupledTimeSlice A (a • eta) Phi =
      -I * ∫ u in a..b,
        osiiCoupledTimeSlice A (u • eta) (osiiCoupledTimeDeriv d k eta Phi) := by
  obtain ⟨L, hL⟩ := G.exists_coupledTimeRayIntegralCLM eta heta a b ha hb
  let W := G.coupledTimeSliceCLM (b • eta)
      (osiiTimePositiveCone_isCone k eta heta b hb) -
    G.coupledTimeSliceCLM (a • eta)
      (osiiTimePositiveCone_isCone k eta heta a ha)
  let U := (-I : Complex) • (L.comp (osiiCoupledTimeDeriv d k eta))
  have heq : W = U := by
    apply section43TimeSpatial_clm_eq_of_eq_on_timeSpatialTensor
    intro phi chi
    change osiiCoupledTimeSlice A (b • eta) (section43TimeSpatialTensor d k phi chi) -
        osiiCoupledTimeSlice A (a • eta) (section43TimeSpatialTensor d k phi chi) =
      -I * L (osiiCoupledTimeDeriv d k eta (section43TimeSpatialTensor d k phi chi))
    rw [osiiCoupledTimeDeriv_tensor, hL]
    simp_rw [osiiCoupledTimeSlice_tensor]
    have hderiv : forall u, u ∈ uIcc a b ->
        HasDerivAt (fun v => osiiFullTimeBoundaryPairing A eta v phi chi)
          (-I * osiiFullTimeBoundaryPairing A eta u
            (directionalDerivSchwartz eta phi) chi) u := by
      intro u hu
      exact G.hasDerivAt_positiveSlicePairing eta heta u
        (positive_of_mem_uIcc ha hb hu) phi chi
    have hcont : ContinuousOn
        (fun u => osiiFullTimeBoundaryPairing A eta u
          (directionalDerivSchwartz eta phi) chi) (uIcc a b) := by
      intro u hu
      exact (G.hasDerivAt_positiveSlicePairing eta heta u
        (positive_of_mem_uIcc ha hb hu)
        (directionalDerivSchwartz eta phi) chi).continuousAt.continuousWithinAt
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((continuousOn_const.mul hcont).intervalIntegrable)
    exact hftc.symm.trans (intervalIntegral.integral_const_mul (-I : Complex) _)
  have h := congrArg (fun T => T Phi) heq
  change osiiCoupledTimeSlice A (b • eta) Phi -
      osiiCoupledTimeSlice A (a • eta) Phi =
    -I * L (osiiCoupledTimeDeriv d k eta Phi) at h
  rwa [hL] at h

/-- The actual tested derivative of a positive-height coupled source. -/
theorem hasDerivAt_coupledTimeSlice_ray [NeZero d] [NeZero k]
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (t : Real) (ht : 0 < t)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    HasDerivAt (fun u => osiiCoupledTimeSlice A (u • eta) Phi)
      (-I * osiiCoupledTimeSlice A (t • eta) (osiiCoupledTimeDeriv d k eta Phi)) t := by
  let D := osiiCoupledTimeDeriv d k eta
  have hcont := G.continuousOn_coupledTimeSlice_ray eta heta (D Phi)
  have hmeas := ContinuousOn.stronglyMeasurableAtFilter (μ := volume)
    isOpen_Ioi hcont t ht
  have hpoint := (hcont t ht).continuousAt (isOpen_Ioi.mem_nhds ht)
  have hftc := intervalIntegral.integral_hasDerivAt_right
    (a := t) (b := t) IntervalIntegrable.refl hmeas hpoint
  have hderiv := (hftc.const_mul (-I)).const_add
    (osiiCoupledTimeSlice A (t • eta) Phi)
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  have h := G.coupledTimeSlice_sub_eq_integral eta heta t u ht hu Phi
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

end OSIIFullTimeStageVladimirovGrowthData
end OSReconstruction
