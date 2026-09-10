/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFullEuclideanRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEuclideanHolomorphicGluing











noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIReducedForwardTubeBoundaryData

variable {d k : Nat} [NeZero d]
variable {W : SchwartzNPoint d k →L[Complex] Complex}
variable {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}

/-- Retain the physical restriction even for generic boundary data. For the
actual original-OS data this equals the coherent holomorphic chart extension. -/
def wickPairKernel (H : OSIIReducedForwardTubeBoundaryData W)
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex) : Complex :=
  if BHW.reducedDiffMap (k + 1) d z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k) then
    H.kernel (BHW.reducedDiffMap (k + 1) d z)
  else H.euclideanHolomorphicKernel z

omit [NeZero d] in
theorem wickPairKernel_eq_of_reduced_mem
    (H : OSIIReducedForwardTubeBoundaryData W)
    {z : Fin (k + 1) -> Fin (d + 1) -> Complex}
    (hz : BHW.reducedDiffMap (k + 1) d z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k)) :
    H.wickPairKernel z = H.kernel (BHW.reducedDiffMap (k + 1) d z) := by
  simp only [wickPairKernel, if_pos hz]

theorem wickPairKernel_eqOn_forwardTube
    (H : OSIIReducedForwardTubeBoundaryData W) :
    EqOn H.wickPairKernel (fun z => H.kernel (BHW.reducedDiffMap (k + 1) d z))
      (ForwardTube d (k + 1)) := by
  intro z hz
  exact H.wickPairKernel_eq_of_reduced_mem
    ((BHW.mem_forwardTube_iff_basepoint_and_reducedDiff z).mp
      (by simpa only [BHW_forwardTube_eq] using hz)).2

theorem wickPairKernel_holomorphic
    (H : OSIIReducedForwardTubeBoundaryData W) :
    DifferentiableOn Complex H.wickPairKernel (ForwardTube d (k + 1)) := by
  have hmaps : MapsTo (BHW.reducedDiffMap (k + 1) d) (ForwardTube d (k + 1))
      (TubeDomainSetPi (BHW.ProductForwardConeReal d k)) := by
    intro z hz
    exact ((BHW.mem_forwardTube_iff_basepoint_and_reducedDiff z).mp
      (by simpa only [BHW_forwardTube_eq] using hz)).2
  exact (H.holomorphic.comp (BHW.reducedDiffMap (k + 1) d).differentiable.differentiableOn
    hmaps).congr H.wickPairKernel_eqOn_forwardTube

theorem wickPairKernel_wick
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (x : NPointDomain d (k + 1)) :
    H.wickPairKernel (fun j => wickRotatePoint (x j)) = H.euclideanDensity x := by
  by_cases hx : BHW.reducedDiffMap (k + 1) d (fun j => wickRotatePoint (x j)) ∈
      TubeDomainSetPi (BHW.ProductForwardConeReal d k)
  · rw [H.wickPairKernel_eq_of_reduced_mem hx,
      ← H.euclideanHolomorphicKernel_eq_of_reduced_mem Hstage Rstage hx]
    exact H.euclideanHolomorphicKernel_wick Hstage Rstage x
  · simp only [wickPairKernel, if_neg hx]
    exact H.euclideanHolomorphicKernel_wick Hstage Rstage x

theorem wickPairKernel_eq_euclideanHolomorphicKernel
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex) :
    H.wickPairKernel z = H.euclideanHolomorphicKernel z := by
  by_cases hz : BHW.reducedDiffMap (k + 1) d z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k)
  · rw [H.wickPairKernel_eq_of_reduced_mem hz]
    exact (H.euclideanHolomorphicKernel_eq_of_reduced_mem Hstage Rstage hz).symm
  · simp only [wickPairKernel, if_neg hz]

theorem wickPairKernel_perm
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (sigma : Equiv.Perm (Fin (k + 1))) (z : Fin (k + 1) -> Fin (d + 1) -> Complex) :
    H.wickPairKernel (fun j => z (sigma j)) = H.wickPairKernel z := by
  simp_rw [H.wickPairKernel_eq_euclideanHolomorphicKernel Hstage Rstage]
  exact H.euclideanHolomorphicKernel_perm Hstage Rstage sigma z

theorem wickPairKernel_translate
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex) (a : Fin (d + 1) -> Complex) :
    H.wickPairKernel (fun j => z j + a) = H.wickPairKernel z := by
  simp_rw [H.wickPairKernel_eq_euclideanHolomorphicKernel Hstage Rstage]
  exact H.euclideanHolomorphicKernel_translate Hstage Rstage z a

theorem wickPairKernel_approach
    (H : OSIIReducedForwardTubeBoundaryData W)
    (eta : NPointDomain d (k + 1)) (heta : eta ∈ ForwardConeAbs d (k + 1))
    (epsilon : Real) (hepsilon : 0 < epsilon) (x : NPointDomain d (k + 1)) :
    H.wickPairKernel (fun j mu =>
        (x j mu : Complex) + (epsilon : Complex) * (eta j mu : Complex) * I) =
      H.kernel (fun j mu =>
        (BHW.reducedDiffMapReal (k + 1) d x j mu : Complex) +
          (epsilon : Complex) * (BHW.reducedDiffMapReal (k + 1) d eta j mu : Complex) * I) := by
  rw [wickPairKernel, reducedDiffMap_complex_approach]
  apply if_pos
  have hred := reducedDiffMapReal_mem_productForwardConeReal_of_mem_forwardConeAbs eta heta
  have hscaled : epsilon • BHW.reducedDiffMapReal (k + 1) d eta ∈
      BHW.ProductForwardConeReal d k := by
    intro j
    simpa [Pi.smul_apply] using BHW.inOpenForwardCone_smul_pos (d := d) (hred j) hepsilon
  simpa [TubeDomainSetPi, Pi.smul_apply, Complex.ofReal_mul, mul_assoc] using hscaled

theorem wickPairKernel_compactSubsetGrowth
    (H : OSIIReducedForwardTubeBoundaryData W)
    (K : Set (NPointDomain d (k + 1))) (hK : IsCompact K)
    (hKsub : K ⊆ ForwardConeAbs d (k + 1)) :
    ∃ (C : Real) (N : Nat), 0 < C ∧ ∀ (x y : NPointDomain d (k + 1)), y ∈ K ->
      ‖H.wickPairKernel (fun j mu => (x j mu : Complex) + (y j mu : Complex) * I)‖ ≤
        C * (1 + ‖x‖) ^ N := by
  let L := BHW.reducedDiffMapRealCLM (k + 1) d
  obtain ⟨C, N, hC, hbound⟩ := H.compactSubsetGrowth (L '' K) (hK.image L.continuous) (by
    rintro _ ⟨y, hy, rfl⟩
    exact reducedDiffMapReal_mem_productForwardConeReal_of_mem_forwardConeAbs y (hKsub hy))
  refine ⟨C * (1 + ‖L‖) ^ N, N, mul_pos hC (pow_pos (by positivity) _), ?_⟩
  intro x y hy
  have heq : H.wickPairKernel (fun j mu => (x j mu : Complex) + (y j mu : Complex) * I) =
      H.kernel (fun j mu => (L x j mu : Complex) + (L y j mu : Complex) * I) := by
    simpa using H.wickPairKernel_approach y (hKsub hy) 1 zero_lt_one x
  rw [heq]
  calc
    ‖H.kernel (fun j mu => (L x j mu : Complex) + (L y j mu : Complex) * I)‖
        ≤ C * (1 + ‖L x‖) ^ N := hbound (L x) (L y) ⟨y, hy, rfl⟩
    _ ≤ C * ((1 + ‖L‖) * (1 + ‖x‖)) ^ N := by
      gcongr
      nlinarith [L.le_opNorm x, norm_nonneg L, norm_nonneg x]
    _ = (C * (1 + ‖L‖) ^ N) * (1 + ‖x‖) ^ N := by rw [mul_pow]; ring

theorem wickPairKernel_boundaryValue
    (H : OSIIReducedForwardTubeBoundaryData W)
    (eta : NPointDomain d (k + 1)) (heta : eta ∈ ForwardConeAbs d (k + 1))
    (phi : SchwartzNPoint d (k + 1)) :
    Tendsto (fun epsilon : Real => ∫ x : NPointDomain d (k + 1),
      H.wickPairKernel (fun j mu =>
        (x j mu : Complex) + (epsilon : Complex) * (eta j mu : Complex) * I) * phi x)
      (nhdsWithin 0 (Ioi 0)) (nhds (W (diffVarReduction d k phi))) := by
  have h := H.boundaryValue (BHW.reducedDiffMapReal (k + 1) d eta)
    (reducedDiffMapReal_mem_productForwardConeReal_of_mem_forwardConeAbs eta heta)
    (diffVarReduction d k phi)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  simpa only [H.wickPairKernel_approach eta heta epsilon hepsilon] using
    (H.absolute_boundarySlice_integral_eq eta heta epsilon hepsilon phi).symm

end OSIIReducedForwardTubeBoundaryData

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

def strictGeneratedWickKernel
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) : (n : Nat) -> (Fin n -> Fin (d + 1) -> Complex) -> Complex
  | 0 => fun _ => 1
  | k + 1 => (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).wickPairKernel

/-- The native full-Schwartz boundary family, before the remaining Wightman
axioms are assembled. Its scalar component is the existing normalization. -/
def strictGeneratedFullBoundary
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) : (n : Nat) -> SchwartzNPoint d n →L[Complex] Complex
  | 0 => (BoundedContinuousFunction.evalCLM Complex (0 : NPointDomain d 0)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM Complex (NPointDomain d 0) Complex)
  | k + 1 => (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary.comp
      (diffVarReduction d k)

theorem strictGeneratedWickKernel_wick
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n : Nat) (x : NPointDomain d n) :
    initial.strictGeneratedWickKernel lgc n (fun j => wickRotatePoint (x j)) =
      initial.strictGeneratedEuclideanKernel lgc n x := by
  cases n with
  | zero => rfl
  | succ k =>
      exact (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).wickPairKernel_wick
        (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc k)
        (initial.toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII lgc k) x

theorem strictGeneratedWickKernel_holomorphic
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n : Nat) :
    DifferentiableOn Complex (initial.strictGeneratedWickKernel lgc n) (ForwardTube d n) := by
  cases n with
  | zero => exact differentiableOn_const _
  | succ k => exact (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).wickPairKernel_holomorphic

theorem strictGeneratedWickKernel_perm
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n : Nat)
    (sigma : Equiv.Perm (Fin n)) (z : Fin n -> Fin (d + 1) -> Complex) :
    initial.strictGeneratedWickKernel lgc n (fun j => z (sigma j)) =
      initial.strictGeneratedWickKernel lgc n z := by
  cases n with
  | zero => rfl
  | succ k =>
      exact (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).wickPairKernel_perm
        (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc k)
        (initial.toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII lgc k) sigma z

theorem strictGeneratedWickKernel_translate
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n : Nat)
    (z : Fin n -> Fin (d + 1) -> Complex) (a : Fin (d + 1) -> Complex) :
    initial.strictGeneratedWickKernel lgc n (fun j => z j + a) =
      initial.strictGeneratedWickKernel lgc n z := by
  cases n with
  | zero => rfl
  | succ k =>
      exact (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).wickPairKernel_translate
        (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc k)
        (initial.toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII lgc k) z a

theorem strictGeneratedWickKernel_boundaryValue
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n : Nat)
    (phi : SchwartzNPoint d n) (eta : NPointDomain d n) (heta : InForwardCone d n eta) :
    Tendsto (fun epsilon : Real => ∫ x : NPointDomain d n,
      initial.strictGeneratedWickKernel lgc n (fun j mu =>
        (x j mu : Complex) + (epsilon : Complex) * (eta j mu : Complex) * I) * phi x)
      (nhdsWithin 0 (Ioi 0)) (nhds (initial.strictGeneratedFullBoundary lgc n phi)) := by
  cases n with
  | zero =>
      have hvol : (volume : Measure (NPointDomain d 0)) = Measure.dirac 0 :=
        Measure.volume_pi_eq_dirac (x := 0)
      simp [strictGeneratedWickKernel, strictGeneratedFullBoundary, hvol]
  | succ k =>
      exact (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k
        ).wickPairKernel_boundaryValue eta heta phi

theorem strictGenerated_forwardTubeAnalyticityCompactSubset
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    ForwardTubeAnalyticityCompactSubset d (fun n phi => initial.strictGeneratedFullBoundary lgc n phi) := by
  intro n
  refine ⟨initial.strictGeneratedWickKernel lgc n,
    initial.strictGeneratedWickKernel_holomorphic lgc n, ?_,
    initial.strictGeneratedWickKernel_boundaryValue lgc n⟩
  intro K hK hKsub
  cases n with
  | zero => exact ⟨1, 0, zero_lt_one, by simp [strictGeneratedWickKernel]⟩
  | succ k =>
      exact (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k
        ).wickPairKernel_compactSubsetGrowth K hK hKsub

theorem strictGenerated_isWickRotationPair
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    IsWickRotationPair OS.schwinger (fun n phi => initial.strictGeneratedFullBoundary lgc n phi) := by
  intro n
  refine ⟨initial.strictGeneratedWickKernel lgc n,
    initial.strictGeneratedWickKernel_holomorphic lgc n,
    initial.strictGeneratedWickKernel_boundaryValue lgc n, ?_⟩
  intro f
  simpa only [initial.strictGeneratedWickKernel_wick] using
    initial.strictGeneratedEuclideanKernel_reproducesZeroDiagonal lgc n f

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

end OSReconstruction
