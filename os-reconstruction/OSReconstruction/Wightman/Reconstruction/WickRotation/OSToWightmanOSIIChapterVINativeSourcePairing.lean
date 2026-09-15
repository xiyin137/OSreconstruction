/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFullFrequency
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISameWitnessWickPair
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceComponentKernel










noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

private theorem fullForwardFlatCone_geometry (d n : Nat) [NeZero d] :
    let C := (flattenCLEquivReal n (d + 1)) '' ForwardConeAbs d n
    IsOpen C ∧ Convex Real C ∧ IsCone C ∧ IsSalientCone C := by
  let e := flattenCLEquivReal n (d + 1)
  refine ⟨e.toHomeomorph.isOpenMap _ (forwardConeAbs_isOpen d n),
    (forwardConeAbs_convex d n).linear_image e.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩ t ht
    exact ⟨t • y, forwardConeAbs_smul d n t ht y hy, by simp⟩
  · intro y hy hny
    rw [show closure (e '' ForwardConeAbs d n) = e '' closure (ForwardConeAbs d n) from
      (e.toHomeomorph.image_closure _).symm] at hy hny
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨x', hx', heq⟩ := hny
    have hneg : x' = -x := e.injective (by rw [heq, map_neg])
    subst x'
    rw [forwardConeAbs_salient d n x hx hx', map_zero]

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

def strictGeneratedFullFrequency
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    SchwartzMap (Fin ((k + 1) * (d + 1)) -> Real) Complex →L[Complex] Complex :=
  (initial.toStrictGeneratedForwardTubeBoundarySpectralDataOfOSII lgc k
    ).toSpectralData.fullFrequencyDistribution

theorem strictGeneratedFullFrequency_support
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    HasFourierSupportIn (section43WightmanSpectralRegion d (k + 1))
      (initial.strictGeneratedFullFrequency lgc k) :=
  (initial.toStrictGeneratedForwardTubeBoundarySpectralDataOfOSII lgc k
    ).toSpectralData.fullFrequencyDistribution_support

theorem strictGeneratedFullFrequency_physicsFourier
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat)
    (f : SchwartzNPoint d (k + 1)) :
    initial.strictGeneratedFullFrequency lgc k
        (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) f)) =
      initial.strictGeneratedFullBoundary lgc (k + 1) f := by
  let P := initial.toStrictGeneratedForwardTubeBoundarySpectralDataOfOSII lgc k
  change P.toSpectralData.fullFrequencyDistribution _ =
    P.boundaryDistribution (diffVarReduction d k f)
  have hflat : flattenSchwartzNPoint (d := d) f = _root_.flattenSchwartzNPoint (d := d) f := by
    ext x
    rfl
  calc
    _ = P.toSpectralData.fullFrequencyDistribution
        (physicsFourierFlatCLM (_root_.flattenSchwartzNPoint (d := d) f)) :=
      congrArg (fun phi => P.toSpectralData.fullFrequencyDistribution (physicsFourierFlatCLM phi)) hflat
    _ = P.toSpectralData.reducedBoundaryDistribution (diffVarReduction d k f) :=
      P.toSpectralData.fullFrequencyDistribution_physicsFourier f
    _ = _ := congrArg (fun L : SchwartzNPoint d k →L[Complex] Complex => L (diffVarReduction d k f))
      P.toSpectralData_reducedBoundaryDistribution

theorem strictGeneratedFullFrequency_fourierLaplace
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat)
    (hC_open : IsOpen ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1)))
    (hC_conv : Convex Real ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1)))
    (hC_cone : IsCone ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1)))
    (hC_salient : IsSalientCone
      ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1)))
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex)
    (hz : z ∈ TubeDomainSetPi (ForwardConeAbs d (k + 1))) :
    initial.strictGeneratedWickKernel lgc (k + 1) z =
      fourierLaplaceExtMultiDim
        ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1))
        hC_open hC_conv hC_cone hC_salient
        (initial.strictGeneratedFullFrequency lgc k)
        (flattenCLEquiv (k + 1) (d + 1) z) := by
  let H := initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k
  change H.wickPairKernel z = _
  have hz' : z ∈ ForwardTube d (k + 1) := by
    rw [forwardTube_eq_imPreimage]
    exact (show (fun k μ => (z k μ).im) ∈ ForwardConeAbs d (k + 1) from hz)
  rw [H.wickPairKernel_eqOn_forwardTube hz']
  rw [show H.kernel =
      (initial.toStrictGeneratedForwardTubeBoundarySpectralDataOfOSII lgc k).toSpectralData.kernel from
    initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII_kernel lgc k]
  exact (initial.toStrictGeneratedForwardTubeBoundarySpectralDataOfOSII lgc k
    ).toSpectralData.fullFrequencyDistribution_fourierLaplace
      hC_open hC_conv hC_cone hC_salient z hz |>.symm

private theorem strictGeneratedWickKernel_forwardTubeLift
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n m : Nat) (t : Real)
    (y : NPointDomain d (n + (m + 1))) :
    initial.strictGeneratedWickKernel lgc (n + (m + 1))
        (section43OSForwardTubeLift_succRight (d := d) t y) =
      initial.strictGeneratedWickKernel lgc (n + (m + 1))
        (xiShift ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : Complex) * I)) := by
  unfold section43OSForwardTubeLift_succRight
  rw [initial.strictGeneratedWickKernel_translate]
  unfold section43OSBorchersTimeShiftConfig_succRight
  rw [initial.strictGeneratedWickKernel_perm]
  rfl

/-- The regulated OS24 scalar is the original OS pairing for the same
native spectral functional. The left degree may be zero. -/
theorem strictGeneratedFullFrequency_sourcePairing_pos
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n m : Nat)
    (phi : SchwartzNPoint d n) (psi : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf : HasCompactSupport (f.1 : NPointDomain d n -> Complex))
    (hg : HasCompactSupport (g.1 : NPointDomain d (m + 1) -> Complex))
    (hphi : section43FourierLaplaceRepresentative d n f (section43FrequencyRepresentative d n phi))
    (hpsi : section43FourierLaplaceRepresentative d (m + 1) g
      (section43FrequencyRepresentative d (m + 1) psi))
    {t : Real} (ht : 0 < t) :
    initial.strictGeneratedFullFrequency lgc (n + m)
        (section43OS24Kernel_succRight d n m phi psi t ht) =
      OS.S (n + (m + 1)) (ZeroDiagonalSchwartz.ofClassical
        (f.1.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g.1))) := by
  obtain ⟨hopen, hconv, hcone, hsalient⟩ := fullForwardFlatCone_geometry d (n + (m + 1))
  refine (section43OS24Kernel_pairing_eq_forwardTubeLiftIntegral_succRight_of_FL
    d n m (initial.strictGeneratedWickKernel lgc (n + (m + 1)))
    hopen hconv hcone hsalient (initial.strictGeneratedFullFrequency lgc (n + m))
    (initial.strictGeneratedFullFrequency_fourierLaplace lgc (n + m)
      hopen hconv hcone hsalient)
    phi psi f g hf hg hphi hpsi ht (initial.strictGeneratedFullFrequency_support lgc (n + m))).trans ?_
  simp_rw [initial.strictGeneratedWickKernel_forwardTubeLift lgc n m t]
  apply (schwinger_simpleTensor_timeShift_eq_xiShift OS (Nat.succ_pos m)
    (initial.strictGeneratedWickKernel lgc (n + (m + 1)))
    ?_ f.1 f.2 g.1 g.2 t ht).symm
  intro h
  simpa only [initial.strictGeneratedWickKernel_wick] using
    initial.strictGeneratedEuclideanKernel_reproducesZeroDiagonal lgc (n + (m + 1)) h

/-- Remove the regulator in the existing Section 4.3 pairing, using its
proved spectral Abel limit and original E0 source continuity. -/
theorem strictGeneratedFullBoundary_sourcePairing_succRight
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n m : Nat)
    (phi : SchwartzNPoint d n) (psi : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf : HasCompactSupport (f.1 : NPointDomain d n -> Complex))
    (hg : HasCompactSupport (g.1 : NPointDomain d (m + 1) -> Complex))
    (hphi : section43FourierLaplaceRepresentative d n f (section43FrequencyRepresentative d n phi))
    (hpsi : section43FourierLaplaceRepresentative d (m + 1) g
      (section43FrequencyRepresentative d (m + 1) psi)) :
    initial.strictGeneratedFullBoundary lgc (n + (m + 1)) (phi.conjTensorProduct psi) =
      OS.S (n + (m + 1)) (ZeroDiagonalSchwartz.ofClassical (f.1.osConjTensorProduct g.1)) := by
  let T := initial.strictGeneratedFullFrequency lgc (n + m)
  have hT := initial.strictGeneratedFullFrequency_support lgc (n + m)
  have hbase : T (section43OS24FlatBaseKernel_succRight d n m phi psi) =
      initial.strictGeneratedFullBoundary lgc (n + (m + 1)) (phi.conjTensorProduct psi) := by
    refine (hasFourierSupportIn_eqOn hT (fun p hp =>
      (physicsFourierFlatCLM_flatten_conjTensorProduct_eq_OS24FlatBaseKernel_on_spectralRegion_succRight
        d n m phi psi hp).symm)).trans ?_
    exact initial.strictGeneratedFullFrequency_physicsFourier lgc (n + m) (phi.conjTensorProduct psi)
  have hlim := tendsto_Tflat_section43OS24Kernel_succRight_to_flatBase d n m phi psi T hT
  have hsource : Tendsto (fun t : Real => OS.S (n + (m + 1))
      (ZeroDiagonalSchwartz.ofClassical
        (f.1.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g.1))))
      (𝓝[>] 0) (𝓝 (T (section43OS24FlatBaseKernel_succRight d n m phi psi))) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    rw [dif_pos ht]
    exact initial.strictGeneratedFullFrequency_sourcePairing_pos lgc n m phi psi f g hf hg hphi hpsi ht
  have hcont := continuousOn_os_pairing_term_timeShift_nonneg_of_isCompactSupport
    OS f.1 g.1 f.2 g.2 hg
  have hzero := ((hcont 0 (by simp)).mono Ioi_subset_Ici_self).tendsto
  have hgzero : timeShiftSchwartzNPoint (d := d) 0 g.1 = g.1 := by
    ext x
    simp
  rw [hgzero] at hzero
  exact hbase.symm.trans (tendsto_nhds_unique hsource hzero)

/-- The source identity in the quotient form used by compact-source density. -/
theorem strictGeneratedFullBoundary_sourcePairing_succRight_of_transformComponent
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n m : Nat)
    (phi : SchwartzNPoint d n) (psi : SchwartzNPoint d (m + 1))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) (m + 1))
    (hf : HasCompactSupport (f.1 : NPointDomain d n -> Complex))
    (hg : HasCompactSupport (g.1 : NPointDomain d (m + 1) -> Complex))
    (hphi : section43FrequencyProjection d n phi =
      section43FourierLaplaceTransformComponent d n f.1 f.2 hf)
    (hpsi : section43FrequencyProjection d (m + 1) psi =
      section43FourierLaplaceTransformComponent d (m + 1) g.1 g.2 hg) :
    initial.strictGeneratedFullBoundary lgc (n + (m + 1)) (phi.conjTensorProduct psi) =
      OS.S (n + (m + 1)) (ZeroDiagonalSchwartz.ofClassical (f.1.osConjTensorProduct g.1)) := by
  obtain ⟨F, hF, hFq⟩ := section43FourierLaplaceTransformComponent_has_representative d n f.1 f.2 hf
  obtain ⟨G, hG, hGq⟩ := section43FourierLaplaceTransformComponent_has_representative
    d (m + 1) g.1 g.2 hg
  exact initial.strictGeneratedFullBoundary_sourcePairing_succRight lgc n m phi psi f g hf hg
    (section43FrequencyRepresentative_is_fourierLaplaceRepresentative_of_quotient_eq
      d n phi f F hF (hphi.trans hFq.symm))
    (section43FrequencyRepresentative_is_fourierLaplaceRepresentative_of_quotient_eq
      d (m + 1) psi g G hG (hpsi.trans hGq.symm))

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
