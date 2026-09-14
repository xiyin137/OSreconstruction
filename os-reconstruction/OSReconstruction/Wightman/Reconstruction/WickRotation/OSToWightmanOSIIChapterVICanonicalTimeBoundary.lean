/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFullBoundary
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledTimeBoundary










noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

private def zeroGapSpatialUnit (d : Nat) :
    SchwartzMap (Section43SpatialSpace d 0) Complex :=
  (section43SpatialFlatSchwartzCLE d 0).symm
    (unitBallBumpSchwartzPi (0 * d))

private theorem zeroGapSpatialUnit_apply (d : Nat)
    (x : Section43SpatialSpace d 0) : zeroGapSpatialUnit d x = 1 := by
  rw [zeroGapSpatialUnit, section43SpatialFlatSchwartzCLE_symm_apply]
  apply unitBallBumpSchwartzPi_one_of_mem_closedBall
  have hzero : section43SpatialFlatCLE d 0 x = 0 := by
    ext i
    have hi := i.isLt
    omega
  simp [hzero]

private theorem zeroGapSpatial_eq_smul_unit {d : Nat}
    (chi : SchwartzMap (Section43SpatialSpace d 0) Complex) :
    chi = chi 0 • zeroGapSpatialUnit d := by
  ext x
  rw [SchwartzMap.smul_apply, zeroGapSpatialUnit_apply]
  simpa [smul_eq_mul] using congrArg chi (Subsingleton.elim x 0)

private def zeroGapNPointEvalCLM (d : Nat) : SchwartzNPoint d 0 →L[Complex] Complex :=
  (BoundedContinuousFunction.evalCLM Complex (0 : NPointDomain d 0)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM Complex (NPointDomain d 0) Complex)

private theorem zeroGapBoundaryPairing
    {d : Nat} [NeZero d] (A : OSIITimeContinuationStage d 0)
    (eta : Fin 0 -> Real) (epsilon : Real)
    (phi : SchwartzMap (Fin 0 -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d 0) Complex) :
    osiiFullTimeBoundaryPairing A eta epsilon phi chi =
      A.distribution 0 (zeroGapSpatialUnit d) *
        (section43OrderedPullbackTimeSpatialTensorCLM d 0 chi phi) 0 := by
  have hvol : (volume : Measure (Fin 0 -> Real)) = Measure.dirac default := by
    simpa using (Measure.volume_pi_eq_dirac
      (ι := Fin 0) (α := fun _ => Real) (x := default))
  have hvalue : A.distribution 0 chi =
      chi 0 * A.distribution 0 (zeroGapSpatialUnit d) := by
    calc
      A.distribution 0 chi = A.distribution 0 (chi 0 • zeroGapSpatialUnit d) :=
        congrArg (A.distribution 0) (zeroGapSpatial_eq_smul_unit chi)
      _ = chi 0 * A.distribution 0 (zeroGapSpatialUnit d) := by
        rw [map_smul]
        rfl
  have htensor : (section43OrderedPullbackTimeSpatialTensorCLM d 0 chi phi) 0 =
      phi 0 * chi 0 := by
    rw [section43OrderedPullbackTimeSpatialTensorCLM_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply,
      section43NPointTimeSpatialTensor_apply]
    exact congrArg₂ (fun a b : Complex => a * b)
      (congrArg phi (Subsingleton.elim _ _))
      (congrArg chi (Subsingleton.elim _ _))
  rw [osiiFullTimeBoundaryPairing, hvol, integral_dirac,
    show osiiMinkowskiTimeApproach eta default epsilon = 0 from Subsingleton.elim _ _,
    hvalue, htensor]
  rw [show (default : Fin 0 -> Real) = 0 from Subsingleton.elim _ _]
  ring

namespace OSIIFullTimeStageVladimirovGrowthData

/-- The zero-gap boundary is the actual scalar distribution value. No
normalization of that scalar is imposed. -/
noncomputable def toZeroGapTemperedBoundaryData
    {d : Nat} [NeZero d] {A : OSIITimeContinuationStage d 0}
    (G : OSIIFullTimeStageVladimirovGrowthData A) :
    OSIIFullTimeStageTemperedBoundaryData A where
  fullCarrier := G.fullCarrier
  orderedBoundary := A.distribution 0 (zeroGapSpatialUnit d) • zeroGapNPointEvalCLM d
  slice_integrable := G.integrable_positiveSlicePairing
  boundaryValue := by
    intro eta heta phi chi
    change Tendsto (fun epsilon : Real => osiiFullTimeBoundaryPairing A eta epsilon phi chi)
      (nhdsWithin 0 (Ioi 0))
      (nhds (A.distribution 0 (zeroGapSpatialUnit d) *
        (section43OrderedPullbackTimeSpatialTensorCLM d 0 chi phi) 0))
    simpa only [zeroGapBoundaryPairing] using
      (tendsto_const_nhds : Tendsto
        (fun _ : Real => A.distribution 0 (zeroGapSpatialUnit d) *
          (section43OrderedPullbackTimeSpatialTensorCLM d 0 chi phi) 0)
        (nhdsWithin 0 (Ioi 0)) (nhds _))

/-- The existing positive-arity boundary construction, completed by its
separate zero-gap scalar case. -/
noncomputable def toTemperedBoundaryDataAllArity
    {d k : Nat} [NeZero d] {A : OSIITimeContinuationStage d k}
    (G : OSIIFullTimeStageVladimirovGrowthData A) :
    OSIIFullTimeStageTemperedBoundaryData A := by
  cases k with
  | zero => exact G.toZeroGapTemperedBoundaryData
  | succ q => exact G.toTemperedBoundaryData

end OSIIFullTimeStageVladimirovGrowthData

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

/-- The chronological full-Schwartz boundary of the actual OS-built stage,
at every arity, from precisely the corrected OS-II input. -/
noncomputable def toStrictGeneratedTemperedBoundaryDataOfOSII
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    OSIIFullTimeStageTemperedBoundaryData
      (initial.toStrictGeneratedFullTimeContinuationStage lgc k) :=
  (initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII lgc k
    ).toTemperedBoundaryDataAllArity

/-- The tested boundary of the actual OS continuation retains arity-linear
Schwartz orders. The zero-gap scalar has its separate native construction. -/
theorem strictGeneratedCoupledBoundaryIndicesOfOSII
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) [NeZero k] :
    let G := initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII lgc k
    let t := (initial.toEquation621UniformPositiveRealSeedData lgc).exponent
    let beta := osiiEquation621CanonicalSeedArityRate lgc
    G.coupledBoundaryIndices = Finset.Iic
      (k * (2 * t + 2 * beta + d + 1) + 2, k * (t + 2 * beta) + 1) := by
  obtain ⟨hN, hM, hs⟩ :=
    initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII_parameters lgc k
  dsimp only
  rw [OSIIFullTimeStageVladimirovGrowthData.coupledBoundaryIndices, hN, hM, hs]
  change Finset.Iic
      (_ + (k + 1) + schwartzSeminormWeightOrder (Finset.Iic (_, 0)),
        schwartzSeminormDerivativeOrder (Finset.Iic (_, 0)) + _ + 1) = _
  rw [schwartzSeminormWeightOrder_Iic_zero, schwartzSeminormDerivativeOrder_Iic_zero]
  congr 2 <;> ring

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
