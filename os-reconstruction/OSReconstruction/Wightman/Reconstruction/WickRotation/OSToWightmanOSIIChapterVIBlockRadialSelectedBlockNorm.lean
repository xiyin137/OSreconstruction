/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialSelectedBlockPairing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairCompactSupport

















noncomputable section

open Matrix Metric Set
open scoped Classical

namespace OSReconstruction

theorem norm_parityReversedBefore_le
    (d n m : Nat)
    (x : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    norm (osiiStep4ParityReversedBeforeRealBlocks d n m x) <= norm x := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro a
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
  rw [Real.norm_eq_abs]
  by_cases hmu : mu = 0
  · subst mu
    simp only [osiiStep4ParityReversedBeforeRealBlocks_apply,
      osiiStep4EuclideanParityMatrix_mulVec_zero]
    exact norm_le_pi_norm x _
  · rw [osiiStep4ParityReversedBeforeRealBlocks_apply,
      osiiStep4EuclideanParityMatrix_mulVec_apply, if_neg hmu,
      abs_neg]
    exact norm_le_pi_norm x _

theorem norm_afterBlocks_le
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real) :
    norm (osiiStep4AfterRealBlocks n m q x) <= norm x := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro a
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
  simpa [Real.norm_eq_abs] using
    (norm_le_pi_norm x (finProdFinEquiv
      (osiiStep4AfterBlockIndex n m i, mu)))

theorem radialEndpointSource_eq_zero_of_imag_norm_gt
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter endpointImag : SpacetimeDim d)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (himag : rho / 8 < norm endpointImag) :
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho endpointCenter endpointImag center y y' = 0 := by
  ext x
  rw [
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource_apply]
  have hradial :
      osiiStep4ComplexBlockRadialG (d + 1) rho
          (osiiStep4ComplexOfRealImag (x 0 - endpointCenter) endpointImag) = 0 := by
    by_contra hne
    have hzmem :
        osiiStep4ComplexOfRealImag (x 0 - endpointCenter) endpointImag ∈
          Function.support (osiiStep4ComplexBlockRadialG (d + 1) rho) := by
      simpa [Function.mem_support] using hne
    have hsupp := osiiStep4ComplexBlockRadialG_support_subset
      (d + 1) hrho hzmem
    have himag_le : norm endpointImag <=
        norm (osiiStep4ComplexBlockToEuclideanCLE (d + 1)
          (osiiStep4ComplexOfRealImag (x 0 - endpointCenter) endpointImag)) := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro mu
      calc
        norm (endpointImag mu) =
            abs ((osiiStep4ComplexOfRealImag
              (x 0 - endpointCenter) endpointImag mu).im) := by
                simp [Real.norm_eq_abs]
        _ <= norm (osiiStep4ComplexOfRealImag
              (x 0 - endpointCenter) endpointImag mu) :=
          Complex.abs_im_le_norm _
        _ <= norm (osiiStep4ComplexBlockToEuclideanCLE (d + 1)
              (osiiStep4ComplexOfRealImag
                (x 0 - endpointCenter) endpointImag)) := by
          simpa using PiLp.norm_apply_le
            (osiiStep4ComplexBlockToEuclideanCLE (d + 1)
              (osiiStep4ComplexOfRealImag
                (x 0 - endpointCenter) endpointImag)) mu
    have hfull_lt :
        norm (osiiStep4ComplexBlockToEuclideanCLE (d + 1)
          (osiiStep4ComplexOfRealImag (x 0 - endpointCenter) endpointImag)) <
            rho / 8 := by
      simpa [osiiStep4ComplexBlockBall] using hsupp
    linarith
  rw [hradial]
  simp

theorem norm_parity_eq
    (d : Nat) (x : SpacetimeDim d) :
    norm ((osiiStep4EuclideanParityMatrix d).mulVec x) = norm x := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
    intro mu
    by_cases hmu : mu = 0
    · subst mu
      simpa using norm_le_pi_norm x 0
    · rw [osiiStep4EuclideanParityMatrix_mulVec_apply, if_neg hmu,
        norm_neg]
      exact norm_le_pi_norm x mu
  · nth_rw 1 [← osiiStep4EuclideanParityMatrix_mulVec_involutive d x]
    rw [pi_norm_le_iff_of_nonneg
      (norm_nonneg ((osiiStep4EuclideanParityMatrix d).mulVec x))]
    intro mu
    by_cases hmu : mu = 0
    · subst mu
      simpa using norm_le_pi_norm
        ((osiiStep4EuclideanParityMatrix d).mulVec x) 0
    · rw [osiiStep4EuclideanParityMatrix_mulVec_apply, if_neg hmu,
        norm_neg]
      exact norm_le_pi_norm
        ((osiiStep4EuclideanParityMatrix d).mulVec x) mu

theorem selectedBlockLeftPositiveTimeSource_hasCompactSupport
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    HasCompactSupport
      ((osiiStep4SelectedBlockLeftPositiveTimeSource
        d n m hrho center y y' hcenter).1 :
          NPointDomain d (n + 1) -> Complex) := by
  exact
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernel_hasCompactSupport
      d n hrho
      (osiiStep4SelectedBlockLeftEndpointCenter d n m center)
      (osiiStep4SelectedBlockLeftEndpointImag d n m y y')
      (osiiStep4ParityReversedBeforeRealBlocks d n m center)
      (osiiStep4ParityReversedBeforeRealBlocks d n m y)
      (osiiStep4ParityReversedBeforeRealBlocks d n m y')

theorem selectedBlockRightPositiveTimeSource_hasCompactSupport
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    HasCompactSupport
      ((osiiStep4SelectedBlockRightPositiveTimeSource
        d n m hrho center y y' hcenter).1 :
          NPointDomain d (m + 1) -> Complex) := by
  exact
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernel_hasCompactSupport
      d m hrho
      (osiiStep4SelectedBlockRightEndpointCenter d n m center)
      (osiiStep4SelectedBlockRightEndpointImag d n m y')
      (osiiStep4AfterRealBlocks n m (d + 1) center)
      (osiiStep4AfterRealBlocks n m (d + 1) y)
      (osiiStep4AfterRealBlocks n m (d + 1) y')

end OSReconstruction
