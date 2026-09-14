import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFullFrequency
import OSReconstruction.Wightman.Reconstruction.WickRotation.ReducedSpectralGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwartzNPointFourier

/-!
# R-to-E spectral support from the distributional spectrum condition

The reduced distribution supplied by `Wfn.spectral_support` has positive
momentum support. Fourier normalization and the zero-total-momentum embedding
transport this support to the full Section 4.3 spectral region. No inference
from compact-height tube growth to spectral support is used.
-/

noncomputable section

open Complex Set
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

/-- Positive reduced spectral support in the repository's Fourier convention
is positive support of the canonical physics-frequency distribution. -/
theorem rToE_canonicalFrequency_support_of_reduced_spectrum
    (w : SchwartzNPoint d k →L[Complex] Complex)
    (hspec : ∀ phi : SchwartzNPointSpace d k,
      (∀ q : NPointDomain d k, phi q ≠ 0 →
        ∃ j : Fin k, q j ∉ ForwardMomentumCone d) →
      w phi.fourierTransform = 0) :
    HasFourierSupportInDualCone (osiiReducedForwardFlatCone d k)
      (osiiCanonicalFrequencyDistribution w) := by
  apply (hasFourierSupportInDualCone_osiiReducedForwardFlatCone_iff _).mpr
  intro psi hpsi
  obtain ⟨phi, hphi⟩ := schwartzNPoint_fourierTransform_surjective
    (unflattenSchwartzNPoint (d := d) (physicsFourierFlatInvCLM psi))
  have hfourier : physicsFourierFlatCLM
      (flattenSchwartzNPoint (d := d) phi.fourierTransform) = psi := by
    rw [hphi]
    have hflat : flattenSchwartzNPoint (d := d)
        (unflattenSchwartzNPoint (d := d) (physicsFourierFlatInvCLM psi)) =
        physicsFourierFlatInvCLM psi := by
      ext p
      simp [flattenSchwartzNPoint_apply, unflattenSchwartzNPoint_apply]
    rw [hflat, physicsFourierFlatCLM_inv_right]
  have heval : osiiCanonicalFrequencyDistribution w psi = w phi.fourierTransform := by
    rw [← hfourier, osiiCanonicalFrequencyDistribution_physicsFourierFlatCLM]
    change w (unflattenSchwartzNPoint
      (flattenSchwartzNPoint (d := d) phi.fourierTransform)) = _
    congr 1
    ext x
    simp [flattenSchwartzNPoint_apply, unflattenSchwartzNPoint_apply]
  rw [heval]
  apply hspec
  intro q hq
  by_contra! hcone
  let p := (2 * Real.pi) • flattenCLEquivReal k (d + 1) q
  have hp : psi p ≠ 0 := by
    rw [← hfourier, physicsFourierFlatCLM_flattenSchwartzNPoint_fourierTransform]
    have hscale : (1 / (2 * Real.pi) : Real) • p =
        flattenCLEquivReal k (d + 1) q := by
      dsimp [p]
      rw [smul_smul, one_div_mul_cancel (mul_ne_zero two_ne_zero Real.pi_ne_zero), one_smul]
    rw [hscale]
    change phi ((flattenCLEquivReal k (d + 1)).symm
      ((flattenCLEquivReal k (d + 1)) q)) ≠ 0
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hq
  apply hpsi p hp
  intro j
  rw [mem_forwardMomentumCone_iff_forall_openForward_pairing_nonneg]
  intro y hy
  have hnonneg := (mem_forwardMomentumCone_iff_forall_openForward_pairing_nonneg
    (q j)).mp (hcone j) y hy
  have hscale : euclideanDot y (osiiCanonicalFrequencyParticleBlock d k p j) =
      (2 * Real.pi) * euclideanDot y (q j) := by
    simp only [euclideanDot, osiiCanonicalFrequencyParticleBlock, p,
      Pi.smul_apply, smul_eq_mul, flattenCLEquivReal_apply,
      Equiv.symm_apply_apply, Finset.mul_sum]
    congr 1
    ext mu
    ring
  rw [hscale]
  exact mul_nonneg (by positivity) hnonneg

/-- The reduced Wightman spectral distribution, with physics normalization
fixed by the explicit inverse Fourier transform. -/
def rToEReducedSpectralData (Wfn : WightmanFunctions d) (k : Nat) :
    OSIIReducedForwardTubeBoundarySpectralData d k := by
  let hw := (Wfn.spectral_support k).choose_spec
  let w : SchwartzNPoint d k →L[Complex] Complex :=
    { toLinearMap :=
        { toFun := (Wfn.spectral_support k).choose
          map_add' := hw.2.1.map_add
          map_smul' := hw.2.1.map_smul }
      cont := hw.1 }
  exact ⟨w, rToE_canonicalFrequency_support_of_reduced_spectrum w hw.2.2.2⟩

theorem rToEReducedSpectralData_boundary (Wfn : WightmanFunctions d)
    (f : SchwartzNPoint d (k + 1)) :
    Wfn.W (k + 1) f =
      (rToEReducedSpectralData Wfn k).boundaryDistribution (diffVarReduction d k f) :=
  (Wfn.spectral_support k).choose_spec.2.2.1 f

/-- The full Wightman distribution as a continuous linear map. -/
def rToEWightmanCLM (Wfn : WightmanFunctions d) (N : Nat) :
    SchwartzNPoint d N →L[Complex] Complex where
  toLinearMap :=
    { toFun := Wfn.W N
      map_add' := (Wfn.linear N).map_add
      map_smul' := (Wfn.linear N).map_smul }
  cont := Wfn.tempered N

/-- The full momentum distribution, fixed without an analytic choice. -/
def rToEFullFrequencyDistribution (Wfn : WightmanFunctions d) (N : Nat) :
    SchwartzMap (Fin (N * (d + 1)) → Real) Complex →L[Complex] Complex :=
  osiiCanonicalFrequencyDistribution (rToEWightmanCLM Wfn N)

theorem rToEFullFrequencyDistribution_boundary (Wfn : WightmanFunctions d)
    (N : Nat) (phi : SchwartzMap (Fin (N * (d + 1)) → Real) Complex) :
    Wfn.W N (unflattenSchwartzNPoint (d := d) phi) =
      rToEFullFrequencyDistribution Wfn N (physicsFourierFlatCLM phi) := by
  rw [rToEFullFrequencyDistribution,
    osiiCanonicalFrequencyDistribution_physicsFourierFlatCLM]
  rfl

theorem rToEFullFrequencyDistribution_eq_reduced (Wfn : WightmanFunctions d)
    (k : Nat) :
    rToEFullFrequencyDistribution Wfn (k + 1) =
      (rToEReducedSpectralData Wfn k).toSpectralData.fullFrequencyDistribution := by
  ext psi
  obtain ⟨phi, rfl⟩ := physicsFourierFlatCLM_surjective ((k + 1) * (d + 1)) psi
  rw [← rToEFullFrequencyDistribution_boundary]
  let f := unflattenSchwartzNPoint (d := d) phi
  have hflat : _root_.flattenSchwartzNPoint (d := d) f = phi := by
    ext p
    change phi ((flattenCLEquivReal (k + 1) (d + 1))
      ((flattenCLEquivReal (k + 1) (d + 1)).symm p)) = phi p
    rw [ContinuousLinearEquiv.apply_symm_apply]
  conv_rhs => rw [← hflat]
  rw [OSIIReducedForwardTubeSpectralData.fullFrequencyDistribution_physicsFourier,
    OSIIReducedForwardTubeBoundarySpectralData.toSpectralData_reducedBoundaryDistribution]
  exact rToEReducedSpectralData_boundary Wfn f

/-- Full spectral support, including zero total momentum, derived only from
the distributional Wightman spectrum condition. -/
theorem rToEFullFrequencyDistribution_support (Wfn : WightmanFunctions d) (N : Nat) :
    HasFourierSupportIn (section43WightmanSpectralRegion d N)
      (rToEFullFrequencyDistribution Wfn N) := by
  cases N with
  | zero =>
    intro f hf
    have hzero : f = 0 := by
      ext p
      by_contra hp
      apply hf p hp
      constructor
      · intro y hy
        apply Finset.sum_nonneg
        intro i hi
        exact (Nat.not_lt_zero i.val (by simpa using i.isLt)).elim
      · ext mu
        simp [section43TotalMomentumFlat]
    rw [hzero, map_zero]
  | succ k =>
    rw [rToEFullFrequencyDistribution_eq_reduced]
    exact OSIIReducedForwardTubeSpectralData.fullFrequencyDistribution_support _

theorem rToEFullFrequencyDistribution_dualSupport (Wfn : WightmanFunctions d) (N : Nat) :
    HasFourierSupportInDualCone
      ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
      (rToEFullFrequencyDistribution Wfn N) := by
  intro f hf
  apply rToEFullFrequencyDistribution_support Wfn N f
  intro p hp hregion
  exact hf p hp hregion.1

end OSReconstruction
