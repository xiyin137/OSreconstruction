import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFrequencyReduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIReducedForwardTubePaleyWiener

/-!
# The full spectral functional of the native reduced boundary

The zero-total-momentum embedding is injective, so restriction along it is
a continuous map of Schwartz spaces. Its transpose sends the actual reduced
spectral functional to the full one. The Fourier reduction identity fixes
the boundary and every normalization, including zero gap arity.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

private def prependZeroMomentumCLM (d k : Nat) :
    NPointDomain d k →L[Real] NPointDomain d (k + 1) :=
  ContinuousLinearMap.pi fun i =>
    Fin.cases 0 (fun j => ContinuousLinearMap.proj j) i

def osiiReducedToFullMomentumCLM (d k : Nat) [NeZero d] :
    (Fin (k * (d + 1)) -> Real) →L[Real]
      (Fin ((k + 1) * (d + 1)) -> Real) :=
  (section43CumulativeTailMomentumCLE d (k + 1)).symm.toContinuousLinearMap.comp
    ((prependZeroMomentumCLM d k).comp
      ((section43SpatialFourierScaleCLE d k).toContinuousLinearMap.comp
        (flattenCLEquivReal k (d + 1)).symm.toContinuousLinearMap))

@[simp] theorem osiiReducedToFullMomentumCLM_apply
    (p : Fin (k * (d + 1)) -> Real) :
    osiiReducedToFullMomentumCLM d k p =
      (section43CumulativeTailMomentumCLE d (k + 1)).symm
        (section43ReducedPhysicsFrequencyZeroHead d k p) := by
  apply congrArg (section43CumulativeTailMomentumCLE d (k + 1)).symm
  ext i mu
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

theorem osiiReducedToFullMomentumCLM_injective :
    Function.Injective (osiiReducedToFullMomentumCLM d k) := by
  intro p q hpq
  rw [osiiReducedToFullMomentumCLM_apply, osiiReducedToFullMomentumCLM_apply] at hpq
  have h := (section43CumulativeTailMomentumCLE d (k + 1)).symm.injective hpq
  apply (flattenCLEquivReal k (d + 1)).symm.injective
  apply (section43SpatialFourierScaleCLE d k).injective
  exact congrArg (fun v : NPointDomain d (k + 1) => fun j : Fin k => v j.succ) h

theorem osiiReducedToFullMomentumCLM_antilipschitz :
    ∃ K, AntilipschitzWith K (osiiReducedToFullMomentumCLM d k) := by
  obtain ⟨K, _, hK⟩ :=
    (osiiReducedToFullMomentumCLM d k).toLinearMap.injective_iff_antilipschitz.mp
      osiiReducedToFullMomentumCLM_injective
  exact ⟨K, hK⟩

def osiiFullFrequencyRestriction (d k : Nat) [NeZero d] :
    SchwartzMap (Fin ((k + 1) * (d + 1)) -> Real) Complex →L[Complex]
      SchwartzMap (Fin (k * (d + 1)) -> Real) Complex :=
  SchwartzMap.compCLMOfAntilipschitz Complex
    (osiiReducedToFullMomentumCLM d k).hasTemperateGrowth
    (Classical.choose_spec (osiiReducedToFullMomentumCLM_antilipschitz (d := d) (k := k)))

@[simp] theorem osiiFullFrequencyRestriction_apply
    (f : SchwartzMap (Fin ((k + 1) * (d + 1)) -> Real) Complex)
    (p : Fin (k * (d + 1)) -> Real) :
    osiiFullFrequencyRestriction d k f p = f (osiiReducedToFullMomentumCLM d k p) := rfl

theorem osiiReducedToFullMomentum_pairing
    (x : NPointDomain d (k + 1)) (p : Fin (k * (d + 1)) -> Real) :
    (∑ i, flattenCLEquivReal (k + 1) (d + 1) x i *
      osiiReducedToFullMomentumCLM d k p i) =
      ∑ i, flattenCLEquivReal k (d + 1)
        (BHW.reducedDiffMapReal (k + 1) d x) i * p i := by
  have hcoord :
      Fin.cons (x 0) (BHW.reducedDiffMapReal (k + 1) d x) =
        section43DiffCoordRealCLE d (k + 1) x := by
    ext i mu
    refine Fin.cases ?_ ?_ i
    · simp [section43DiffCoordRealCLE, BHW.realDiffCoordCLE_apply]
    · intro j
      change x j.succ mu - x j.castSucc mu = x j.succ mu - x j.castSucc mu
      rfl
  have h := section43ReducedPhysicsFrequencyZeroHead_pairing
    d k (x 0) (BHW.reducedDiffMapReal (k + 1) d x) p
  rw [hcoord, ContinuousLinearEquiv.symm_apply_apply] at h
  simpa only [osiiReducedToFullMomentumCLM_apply] using h

theorem osiiReducedToFullMomentum_complex_pairing
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex)
    (p : Fin (k * (d + 1)) -> Real) :
    (∑ i, flattenCLEquiv (k + 1) (d + 1) z i *
      (osiiReducedToFullMomentumCLM d k p i : Complex)) =
      ∑ i, BHW.flattenCfg k d (BHW.reducedDiffMap (k + 1) d z) i * (p i : Complex) := by
  apply Complex.ext
  · calc
      (∑ i, flattenCLEquiv (k + 1) (d + 1) z i *
          (osiiReducedToFullMomentumCLM d k p i : Complex)).re =
          ∑ i, flattenCLEquivReal (k + 1) (d + 1) (fun j mu => (z j mu).re) i *
            osiiReducedToFullMomentumCLM d k p i := by
            simp [Complex.mul_re, flattenCLEquiv_apply, flattenCLEquivReal_apply]
      _ = ∑ i, flattenCLEquivReal k (d + 1)
          (BHW.reducedDiffMapReal (k + 1) d (fun j mu => (z j mu).re)) i * p i :=
        osiiReducedToFullMomentum_pairing (fun j mu => (z j mu).re) p
      _ = (∑ i, BHW.flattenCfg k d (BHW.reducedDiffMap (k + 1) d z) i *
          (p i : Complex)).re := by
            simp [Complex.mul_re, BHW.flattenCfg, flattenCLEquivReal_apply]
            apply Finset.sum_congr rfl
            intro i _
            congr 1
  · calc
      (∑ i, flattenCLEquiv (k + 1) (d + 1) z i *
          (osiiReducedToFullMomentumCLM d k p i : Complex)).im =
          ∑ i, flattenCLEquivReal (k + 1) (d + 1) (fun j mu => (z j mu).im) i *
            osiiReducedToFullMomentumCLM d k p i := by
            simp [Complex.mul_im, flattenCLEquiv_apply, flattenCLEquivReal_apply]
      _ = ∑ i, flattenCLEquivReal k (d + 1)
          (BHW.reducedDiffMapReal (k + 1) d (fun j mu => (z j mu).im)) i * p i :=
        osiiReducedToFullMomentum_pairing (fun j mu => (z j mu).im) p
      _ = (∑ i, BHW.flattenCfg k d (BHW.reducedDiffMap (k + 1) d z) i *
          (p i : Complex)).im := by
            simp [Complex.mul_im, BHW.flattenCfg, flattenCLEquivReal_apply]
            apply Finset.sum_congr rfl
            intro i _
            congr 1

theorem osiiReducedToFullMomentum_total_zero
    (p : Fin (k * (d + 1)) -> Real) :
    section43TotalMomentumFlat d (k + 1) (osiiReducedToFullMomentumCLM d k p) = 0 := by
  ext mu
  have h := congrArg (fun q : NPointDomain d (k + 1) => q 0 mu)
    (section43ReducedPhysicsFrequencyZeroHead_rawCumulative d k p)
  simpa [section43RawCumulativeTailMomentumCLE_apply, section43TotalMomentumFlat]
    using h

theorem osiiReducedToFullMomentum_mem_spectralRegion
    {p : Fin (k * (d + 1)) -> Real}
    (hp : p ∈ DualConeFlat (osiiReducedForwardFlatCone d k)) :
    osiiReducedToFullMomentumCLM d k p ∈ section43WightmanSpectralRegion d (k + 1) := by
  refine ⟨?_, osiiReducedToFullMomentum_total_zero p⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [osiiReducedToFullMomentum_pairing]
  apply hp
  change BHW.ProductForwardConeReal d k
    (BHW.unflattenCfgReal k d
      (flattenCLEquivReal k (d + 1) (BHW.reducedDiffMapReal (k + 1) d y)))
  have hflat : BHW.unflattenCfgReal k d
      (flattenCLEquivReal k (d + 1) (BHW.reducedDiffMapReal (k + 1) d y)) =
        BHW.reducedDiffMapReal (k + 1) d y := by
    ext j mu
    simp [BHW.unflattenCfgReal, flattenCLEquivReal_apply]
  rw [hflat]
  intro j
  have hj := hy j.succ
  have hcast : (⟨j.val, by omega⟩ : Fin (k + 1)) = j.castSucc := by
    ext
    rfl
  apply (inOpenForwardCone_iff _).2
  change 0 < y j.succ 0 - y j.castSucc 0 ∧
    MinkowskiSpace.minkowskiNormSq d (fun mu => y j.succ mu - y j.castSucc mu) < 0
  simpa [ForwardConeAbs, _root_.InOpenForwardCone, hcast] using hj

theorem osiiFullFrequencyRestriction_physicsFourier
    (f : SchwartzNPoint d (k + 1)) :
    osiiFullFrequencyRestriction d k
        (physicsFourierFlatCLM (_root_.flattenSchwartzNPoint (d := d) f)) =
      physicsFourierFlatCLM
        (_root_.flattenSchwartzNPoint (d := d) (diffVarReduction d k f)) := by
  ext p
  rw [physicsFourierFlatCLM_diffVarReduction_eq_zeroHead,
    osiiFullFrequencyRestriction_apply, osiiReducedToFullMomentumCLM_apply]
  rfl

namespace OSIIReducedForwardTubeSpectralData

def fullFrequencyDistribution (P : OSIIReducedForwardTubeSpectralData d k) :
    SchwartzMap (Fin ((k + 1) * (d + 1)) -> Real) Complex →L[Complex] Complex :=
  P.frequencyDistribution.comp (osiiFullFrequencyRestriction d k)

theorem fullFrequencyDistribution_support (P : OSIIReducedForwardTubeSpectralData d k) :
    HasFourierSupportIn (section43WightmanSpectralRegion d (k + 1))
      P.fullFrequencyDistribution := by
  intro f hf
  apply P.support
  intro p hp hpcone
  exact hf (osiiReducedToFullMomentumCLM d k p) hp
    (osiiReducedToFullMomentum_mem_spectralRegion hpcone)

theorem fullFrequencyDistribution_physicsFourier
    (P : OSIIReducedForwardTubeSpectralData d k)
    (f : SchwartzNPoint d (k + 1)) :
    P.fullFrequencyDistribution
        (physicsFourierFlatCLM (_root_.flattenSchwartzNPoint (d := d) f)) =
      P.reducedBoundaryDistribution (diffVarReduction d k f) := by
  change P.frequencyDistribution (osiiFullFrequencyRestriction d k _) = _
  rw [osiiFullFrequencyRestriction_physicsFourier]
  rfl

/-- The full Fourier-Laplace representative is the original reduced kernel
pulled back by differences. The proof compares actual Schwartz tests on the
spectral cone; it does not invoke a reverse Fourier-representation axiom. -/
theorem fullFrequencyDistribution_fourierLaplace
    (P : OSIIReducedForwardTubeSpectralData d k)
    (hC_open : IsOpen ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1)))
    (hC_conv : Convex Real ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1)))
    (hC_cone : IsCone ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1)))
    (hC_salient : IsSalientCone
      ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1)))
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex)
    (hz : z ∈ TubeDomainSetPi (ForwardConeAbs d (k + 1))) :
    fourierLaplaceExtMultiDim
        ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1))
        hC_open hC_conv hC_cone hC_salient P.fullFrequencyDistribution
        (flattenCLEquiv (k + 1) (d + 1) z) =
      P.kernel (BHW.reducedDiffMap (k + 1) d z) := by
  have hzfull : flattenCLEquiv (k + 1) (d + 1) z ∈ SCV.TubeDomain
      ((flattenCLEquivReal (k + 1) (d + 1)) '' ForwardConeAbs d (k + 1)) := by
    refine ⟨fun j mu => (z j mu).im, hz, ?_⟩
    ext i
    rfl
  have hred : (fun j mu => (BHW.reducedDiffMap (k + 1) d z j mu).im) ∈
      BHW.ProductForwardConeReal d k := by
    intro j
    have hcast : (⟨j.val, by omega⟩ : Fin (k + 1)) = j.castSucc := by
      ext
      rfl
    apply (inOpenForwardCone_iff _).2
    change 0 < (z j.succ 0 - z j.castSucc 0).im ∧
      MinkowskiSpace.minkowskiNormSq d
        (fun mu => (z j.succ mu - z j.castSucc mu).im) < 0
    simpa [TubeDomainSetPi, ForwardConeAbs, _root_.InOpenForwardCone, hcast] using hz j.succ
  have hzred : BHW.flattenCfg k d (BHW.reducedDiffMap (k + 1) d z) ∈
      SCV.TubeDomain (osiiReducedForwardFlatCone d k) := by
    change BHW.ProductForwardConeReal d k
      (BHW.unflattenCfgReal k d
        (fun i => (BHW.flattenCfg k d (BHW.reducedDiffMap (k + 1) d z) i).im))
    have hflat : BHW.unflattenCfgReal k d
        (fun i => (BHW.flattenCfg k d (BHW.reducedDiffMap (k + 1) d z) i).im) =
          fun j mu => (BHW.reducedDiffMap (k + 1) d z j mu).im := by
      ext j mu
      simp [BHW.unflattenCfgReal, BHW.flattenCfg]
    rw [hflat]
    exact hred
  simp only [kernel, flatKernel, fourierLaplaceExtMultiDim_eq_ext,
    fullFrequencyDistribution, ContinuousLinearMap.comp_apply]
  apply hasFourierSupportIn_eqOn P.support
  intro p hp
  rw [osiiFullFrequencyRestriction_apply,
    multiDimPsiZExt_apply_of_mem_dualCone _ hC_open hC_conv hC_cone hC_salient _ hzfull
      (osiiReducedToFullMomentum_mem_spectralRegion hp).1,
    multiDimPsiZExt_apply_of_mem_dualCone _ isOpen_osiiReducedForwardFlatCone
      osiiReducedForwardFlatCone_convex osiiReducedForwardFlatCone_isCone
      osiiReducedForwardFlatCone_salient _ hzred hp,
    osiiReducedToFullMomentum_complex_pairing]

end OSIIReducedForwardTubeSpectralData
end OSReconstruction
