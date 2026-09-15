import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeTimeSliceIdentification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalMovingSliceCutoff
import OSReconstruction.SCV.EuclideanWeylOpen

/-!
# Chapter VI flat-Wick moving-slice bridge

A reduced forward-tube realization is compared with the Chapter V time stage
on pure-time spatial slices. At a Euclidean reduced point, the Wick-rotated
configuration is exactly such a pure-time interior slice: its imaginary time
direction is the Euclidean time-gap vector and its real part is the spatial
block.

Fubini therefore turns the pure-time slice identity into a sourcewise
flat-Wick identity. This is the non-vacuous spatial handoff needed by the
ordered-product E-to-R endpoint.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

omit [NeZero d] in
/-- Wick rotation of a real reduced configuration is continuous. This local
form keeps the Chapter VI bridge independent of theorem-2 locality modules. -/
theorem continuous_osiiReducedWickRotateConfig :
    Continuous
      (fun q : NPointDomain d k => fun j => wickRotatePoint (q j)) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro mu
  by_cases hmu : mu = 0
  · subst mu
    continuity
  · simp only [wickRotatePoint, hmu, ↓reduceIte]
    continuity

/-- Positive Euclidean reduced times send the literal Wick slice into the
reduced forward tube.  This is the domain-local fact needed whenever a
forward-tube branch is compared with a larger MZ continuation only on their
common carrier. -/
theorem osiiReducedWickRotateConfig_mem_productForwardTube_of_strictPositive
    (q : NPointDomain d k)
    (hq :
      section43QTime (d := d) (n := k) q ∈
        section43TimeStrictPositiveRegion k) :
    (fun j => wickRotatePoint (q j)) ∈
      TubeDomainSetPi (BHW.ProductForwardConeReal d k) := by
  change (fun j mu => (wickRotatePoint (q j) mu).im) ∈
    BHW.ProductForwardConeReal d k
  have hpure :=
    osiiPureTimeReducedDirection_mem_productForwardCone
      (d := d) (k := k)
      (section43QTime (d := d) (n := k) q) hq
  convert hpure using 1
  ext j mu
  by_cases hmu : mu = 0
  · subst mu
    simp [wickRotatePoint, osiiPureTimeReducedDirection,
      section43QTime, nPointTimeSpatialCLE]
  · simp [wickRotatePoint, osiiPureTimeReducedDirection, hmu]

/-- In time/spatial coordinates, the flat Wick point is the pure-time
forward-tube point with Euclidean time gaps as imaginary direction. -/
theorem wickRotate_timeSpatial_eq_pureTimeShift
    (tau : Fin k -> Real)
    (x : Section43SpatialSpace d k) :
    (fun j mu =>
      wickRotatePoint
        ((section43NPointTimeSpatialMeasurableEquiv d k).symm
          (tau, x) j) mu) =
      (fun j mu =>
        (((section43NPointTimeSpatialMeasurableEquiv d k).symm
            (0, x) j mu : Complex) +
          (1 : Complex) *
            (osiiPureTimeReducedDirection d k tau j mu : Complex) * I)) := by
  let eTS := section43NPointTimeSpatialMeasurableEquiv d k
  have htau :
      nPointTimeSpatialCLE (d := d) k (eTS.symm (tau, x)) = (tau, x) := by
    rw [← section43NPointTimeSpatialMeasurableEquiv_apply]
    exact eTS.apply_symm_apply (tau, x)
  have hzero :
      nPointTimeSpatialCLE (d := d) k
          (eTS.symm ((0 : Fin k -> Real), x)) =
        ((0 : Fin k -> Real), x) := by
    rw [← section43NPointTimeSpatialMeasurableEquiv_apply]
    exact eTS.apply_symm_apply (0, x)
  ext j mu
  by_cases hmu : mu = 0
  · subst mu
    simp [wickRotatePoint, osiiPureTimeReducedDirection]
    rw [mul_comm]
  · let a : Fin d := mu.pred hmu
    have hsucc : Fin.succ a = mu := Fin.succ_pred mu hmu
    have htau_space :
        (eTS.symm (tau, x)) j mu =
          (EuclideanSpace.equiv (ι := Fin k × Fin d) (𝕜 := Real) x)
            (j, a) := by
      rw [← hsucc]
      have h := congrArg
        (fun p =>
          (EuclideanSpace.equiv (ι := Fin k × Fin d) (𝕜 := Real) p.2)
            (j, a)) htau
      simpa [nPointTimeSpatialCLE] using h
    have hzero_space :
        (eTS.symm ((0 : Fin k -> Real), x)) j mu =
          (EuclideanSpace.equiv (ι := Fin k × Fin d) (𝕜 := Real) x)
            (j, a) := by
      rw [← hsucc]
      have h := congrArg
        (fun p =>
          (EuclideanSpace.equiv (ι := Fin k × Fin d) (𝕜 := Real) p.2)
            (j, a)) hzero
      simpa [nPointTimeSpatialCLE] using h
    simp [wickRotatePoint, osiiPureTimeReducedDirection, hmu]
    exact htau_space.trans hzero_space.symm

/-- At real time zero and unit approach scale, the Minkowski time approach is
the positive-real Chapter V time coordinate. -/
theorem osiiMinkowskiTimeApproach_zero_one
    (tau : Fin k -> Real) :
    osiiMinkowskiTimeApproach tau 0 1 =
      osiiPositiveRealTimeEmbed tau := by
  ext i
  simp [osiiMinkowskiTimeApproach, osiiPositiveRealTimeEmbed]

/-- On a source supported over one compact positive-time carrier, a
pure-time forward-tube realization represents the canonical Chapter V
moving-slice distribution at the flat Wick slice. -/
theorem osiiStageMovingSliceDistribution_zero_eq_forwardTubeFlatWickIntegral
    {compactCarrier : Set (Fin k -> Real)}
    {OS : OsterwalderSchraderAxioms d}
    {stage : OSIITimeContinuationStage d k}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (C : OSIIChapterV.CanonicalReducedCompactMovingSliceCutoffData D)
    {W : SchwartzNPoint d k →L[Complex] Complex}
    (H : OSIIReducedForwardTubeBoundaryData W)
    (R : OSIIReducedForwardTubeTimeSliceRealizationData
      (A := stage) H)
    (F : SchwartzNPoint d k)
    (hF : SCV.SupportsInOpen
      (F : NPointDomain d k -> Complex)
      {q | section43QTime (d := d) (n := k) q ∈ compactCarrier}) :
    osiiStageMovingSliceDistribution stage C.cutoff C.cutoff_compact 0 F =
      ∫ q : NPointDomain d k,
        H.kernel (fun j => wickRotatePoint (q j)) * F q := by
  let U : Set (NPointDomain d k) :=
    {q | section43QTime (d := d) (n := k) q ∈ compactCarrier}
  let V : Set (NPointDomain d k) :=
    {q | section43QTime (d := d) (n := k) q ∈ D.realRegion}
  let wick : NPointDomain d k -> Fin k -> Fin (d + 1) -> Complex :=
    fun q j => wickRotatePoint (q j)
  have hF_U : SCV.SupportsInOpen (F : NPointDomain d k -> Complex) U := by
    simpa only [U] using hF
  have hF_V : SCV.SupportsInOpen (F : NPointDomain d k -> Complex) V := by
    refine ⟨hF_U.1, ?_⟩
    intro q hq
    exact D.compactCarrier_subset (hF_U.2 hq)
  have hV_open : IsOpen V := by
    exact D.realRegion_open.preimage
      (section43QTimeCLM d k).continuous
  have hwick_maps :
      Set.MapsTo wick V
        (TubeDomainSetPi (BHW.ProductForwardConeReal d k)) := by
    intro q hq
    exact
      osiiReducedWickRotateConfig_mem_productForwardTube_of_strictPositive
        q (D.realRegion_subset_strictPositive hq)
  have hwick_cont :
      ContinuousOn (fun q => H.kernel (wick q)) V := by
    exact H.holomorphic.continuousOn.comp
      (continuous_osiiReducedWickRotateConfig (d := d) (k := k)).continuousOn
      hwick_maps
  let f : NPointDomain d k -> Complex :=
    fun q => H.kernel (wick q) * F q
  have hf_int : Integrable f := by
    exact
      SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
        hV_open hwick_cont hF_V
  let eTS := section43NPointTimeSpatialMeasurableEquiv d k
  have hTSsymm : MeasurePreserving eTS.symm volume volume :=
    MeasurePreserving.symm eTS (by
      simpa [eTS] using
        section43NPointTimeSpatialCLE_measurePreserving d k)
  have hsplit : Integrable (fun p => f (eTS.symm p)) :=
    hTSsymm.integrable_comp_of_integrable hf_int
  have hpoint :
      forall (tau : Fin k -> Real) (x : Section43SpatialSpace d k),
        f (eTS.symm (tau, x)) =
          H.kernel
            (fun j mu =>
              (eTS.symm ((0 : Fin k -> Real), x) j mu : Complex) +
                (1 : Complex) *
                  (osiiPureTimeReducedDirection d k tau j mu : Complex) * I) *
            osiiFullSourceSpatialSlice F tau x := by
    intro tau x
    have heq :
        eTS.symm (tau, x) =
          (nPointTimeSpatialCLE (d := d) k).symm (tau, x) := by
      apply (nPointTimeSpatialCLE (d := d) k).injective
      rw [← section43NPointTimeSpatialMeasurableEquiv_apply]
      exact eTS.apply_symm_apply (tau, x)
    simp only [f, wick]
    rw [wickRotate_timeSpatial_eq_pureTimeShift (d := d) tau x]
    rw [osiiFullSourceSpatialSlice_apply, ← heq]
  have hinner :
      forall tau : Fin k -> Real,
        (∫ x : Section43SpatialSpace d k,
          f (eTS.symm (tau, x))) =
          C.cutoff tau *
            stage.distribution (osiiPositiveRealTimeEmbed tau)
              (osiiFullSourceSpatialSlice F tau) := by
    intro tau
    by_cases htau : tau ∈ compactCarrier
    · have hpos :
          tau ∈ osiiTimePositiveCone k := by
        exact D.realRegion_subset_strictPositive
          (D.compactCarrier_subset htau)
      have hedge :=
        R.spatialSlice tau hpos 1 zero_lt_one 0
          (osiiFullSourceSpatialSlice F tau)
      rw [osiiMinkowskiTimeApproach_zero_one] at hedge
      calc
        (∫ x : Section43SpatialSpace d k,
            f (eTS.symm (tau, x))) =
          ∫ x : Section43SpatialSpace d k,
            H.kernel
              (fun j mu =>
                (eTS.symm ((0 : Fin k -> Real), x) j mu : Complex) +
                  (1 : Complex) *
                    (osiiPureTimeReducedDirection d k tau j mu : Complex) * I) *
              osiiFullSourceSpatialSlice F tau x := by
                apply integral_congr_ae
                filter_upwards with x
                exact hpoint tau x
        _ = stage.distribution (osiiPositiveRealTimeEmbed tau)
              (osiiFullSourceSpatialSlice F tau) := hedge
        _ = C.cutoff tau *
              stage.distribution (osiiPositiveRealTimeEmbed tau)
                (osiiFullSourceSpatialSlice F tau) := by
                rw [C.cutoff_one_on tau htau]
                simp
    · have hslice_zero :
          osiiFullSourceSpatialSlice F tau = 0 := by
        ext x
        rw [osiiFullSourceSpatialSlice_apply]
        have hnot :
            (nPointTimeSpatialCLE (d := d) k).symm (tau, x) ∉
              tsupport (F : NPointDomain d k -> Complex) := by
          intro hx
          apply htau
          have hxU := hF_U.2 hx
          change
            section43QTime (d := d) (n := k)
                ((nPointTimeSpatialCLE (d := d) k).symm (tau, x)) ∈
              compactCarrier at hxU
          simpa [section43QTime] using hxU
        exact image_eq_zero_of_notMem_tsupport hnot
      calc
        (∫ x : Section43SpatialSpace d k,
            f (eTS.symm (tau, x))) =
          ∫ x : Section43SpatialSpace d k,
            H.kernel
              (fun j mu =>
                (eTS.symm ((0 : Fin k -> Real), x) j mu : Complex) +
                  (1 : Complex) *
                    (osiiPureTimeReducedDirection d k tau j mu : Complex) * I) *
              osiiFullSourceSpatialSlice F tau x := by
                apply integral_congr_ae
                filter_upwards with x
                exact hpoint tau x
        _ = C.cutoff tau *
              stage.distribution (osiiPositiveRealTimeEmbed tau)
                (osiiFullSourceSpatialSlice F tau) := by
                simp [hslice_zero]
  have hzero : 0 ∈ osiiStageMovingSliceCarrier stage C.cutoff := by
    intro tau htau
    simpa using (D.edge.stageEdge tau (C.cutoff_support htau)).1
  calc
    osiiStageMovingSliceDistribution stage C.cutoff C.cutoff_compact 0 F =
      osiiStageMovingSliceScalar stage C.cutoff F 0 := by
        rw [osiiStageMovingSliceDistribution_apply_of_mem
          stage C.cutoff C.cutoff_compact 0 hzero F]
    _ = ∫ tau : Fin k -> Real,
        C.cutoff tau *
          stage.distribution (osiiPositiveRealTimeEmbed tau)
            (osiiFullSourceSpatialSlice F tau) := by
          simp [osiiStageMovingSliceScalar,
            osiiShiftedMovingSpatialSliceIntegral_zero,
            osiiMovingSpatialSliceIntegral]
    _ = ∫ tau : Fin k -> Real,
        ∫ x : Section43SpatialSpace d k,
          f (eTS.symm (tau, x)) := by
          apply integral_congr_ae
          filter_upwards with tau
          exact (hinner tau).symm
    _ = ∫ p : (Fin k -> Real) × Section43SpatialSpace d k,
        f (eTS.symm p) := by
          exact (integral_prod (fun p => f (eTS.symm p)) hsplit).symm
    _ = ∫ q : NPointDomain d k, f q := by
          exact hTSsymm.integral_comp' (g := f)
    _ = ∫ q : NPointDomain d k,
        H.kernel (fun j => wickRotatePoint (q j)) * F q := rfl

/-- On any source neighborhood whose reduced times stay in the chosen compact
carrier, the flat-Wick slice of a pure-time forward-tube realization represents
the canonical Chapter V moving-slice distribution.  This is the
representation-level form of the preceding Fubini identity, suitable for
pointwise comparison with an independently constructed MZ density. -/
theorem forwardTubeFlatWick_represents_movingSlice
    {compactCarrier : Set (Fin k -> Real)}
    {OS : OsterwalderSchraderAxioms d}
    {stage : OSIITimeContinuationStage d k}
    (D : OSIIChapterV.CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (C : OSIIChapterV.CanonicalReducedCompactMovingSliceCutoffData D)
    {W : SchwartzNPoint d k →L[Complex] Complex}
    (H : OSIIReducedForwardTubeBoundaryData W)
    (R : OSIIReducedForwardTubeTimeSliceRealizationData
      (A := stage) H)
    (U : Set (NPointDomain d k))
    (hU : U ⊆
      {q | section43QTime (d := d) (n := k) q ∈ compactCarrier}) :
    SCV.RepresentsDistributionOn
      (osiiStageMovingSliceDistribution stage C.cutoff C.cutoff_compact 0)
      (fun q : NPointDomain d k =>
        H.kernel (fun j => wickRotatePoint (q j)))
      U := by
  intro F hF
  exact osiiStageMovingSliceDistribution_zero_eq_forwardTubeFlatWickIntegral
    D C H R F ⟨hF.1, hF.2.trans hU⟩

end OSReconstruction
