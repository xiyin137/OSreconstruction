import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISameWitnessWickPair
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwartzNPointFourier

/-!
# The existing distributional spectrum condition for the native family

The canonical supported frequency distribution was proved from global time
growth and Ward transport. Positive Fourier dilation identifies it with the
repository's n-point Fourier convention, without a boundary-to-spectrum axiom.
-/

noncomputable section

open Complex Set
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction
namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

theorem strictGeneratedFullBoundary_spectralCondition
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    SpectralConditionDistribution d (fun n f => initial.strictGeneratedFullBoundary lgc n f) := by
  intro k
  let w := (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary
  refine ⟨w, w.continuous, ⟨w.map_add, w.map_smul⟩, (fun _ => rfl), ?_⟩
  intro phi hphi
  let psi := physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) phi.fourierTransform)
  have heval : osiiCanonicalFrequencyDistribution w psi = w phi.fourierTransform := by
    rw [osiiCanonicalFrequencyDistribution_physicsFourierFlatCLM]
    change w (_root_.unflattenSchwartzNPoint (flattenSchwartzNPoint (d := d) phi.fourierTransform)) = _
    congr 1
    ext x
    change (SchwartzNPointSpace.fourierTransform d phi) ((flattenCLEquivReal k (d + 1)).symm
      (flattenCLEquivReal k (d + 1) x)) = (SchwartzNPointSpace.fourierTransform d phi) x
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [← heval]
  apply (hasFourierSupportInDualCone_osiiReducedForwardFlatCone_iff _).mp
    (initial.strictGeneratedFrequency_support lgc k) psi
  intro p hp hcone
  let c : Real := 1 / (2 * Real.pi)
  let q : NPointSpacetime d k := fun j mu => c * p (finProdFinEquiv (j, mu))
  have hnonzero : phi q ≠ 0 := by
    change physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) phi.fourierTransform) p ≠ 0 at hp
    rw [physicsFourierFlatCLM_flattenSchwartzNPoint_fourierTransform] at hp
    exact hp
  obtain ⟨j, hj⟩ := hphi q hnonzero
  apply hj
  rw [mem_forwardMomentumCone_iff_forall_openForward_pairing_nonneg]
  intro y hy
  have hnonneg := (mem_forwardMomentumCone_iff_forall_openForward_pairing_nonneg
    (osiiCanonicalFrequencyParticleBlock d k p j)).mp (hcone j) y hy
  have hscale : euclideanDot y (q j) = c * euclideanDot y (osiiCanonicalFrequencyParticleBlock d k p j) := by
    simp only [euclideanDot, q, osiiCanonicalFrequencyParticleBlock, Finset.mul_sum]
    congr 1
    ext mu
    ring
  rw [hscale]
  exact mul_nonneg (by dsimp [c]; positivity) hnonneg

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
