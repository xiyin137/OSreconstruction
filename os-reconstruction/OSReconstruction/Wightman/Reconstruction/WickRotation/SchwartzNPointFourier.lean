import OSReconstruction.Wightman.SpectralEquivalence

/-!
# N-point and physics Fourier normalization

The existing n-point Fourier transform has Mathlib's negative `2*pi` phase.
The physics transform has the positive unit phase. Their composition is
positive momentum dilation, so it preserves the forward spectral cone.
-/

noncomputable section

open Complex

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

/-- The n-point Fourier convention is an automorphism of the full Schwartz
space, including zero arity. -/
theorem schwartzNPoint_fourierTransform_surjective
    {d n : Nat} [NeZero d] :
    Function.Surjective (SchwartzNPointSpace.fourierTransform d (n := n)) := by
  intro f
  let e := nPointToEuclidean d n
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm f
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
    (FourierTransformInv.fourierInv g), ?_⟩
  have hcancel : SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
        (FourierTransformInv.fourierInv g)) = FourierTransformInv.fourierInv g := by
    ext x
    simp
  unfold SchwartzNPointSpace.fourierTransform
  change SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
    (SchwartzMap.fourierTransformCLM Complex
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm _)) = f
  rw [hcancel, SchwartzMap.fourierTransformCLM_apply, FourierInvPair.fourier_fourierInv_eq]
  ext x
  simp [g]

theorem flattenSchwartzNPoint_fourierTransform
    {d n : Nat} [NeZero d] (phi : SchwartzNPointSpace d n) :
    flattenSchwartzNPoint (d := d) phi.fourierTransform =
      inverseFourierFlatCLM (flattenSchwartzNPoint (d := d) phi) := by
  let e := nPointToEuclidean d n
  let eF := EuclideanSpace.equiv (Fin (n * (d + 1))) Real
  let J : EuclideanSpace Real (Fin n × Fin (d + 1)) ≃ₗᵢ[Real]
      EuclideanSpace Real (Fin (n * (d + 1))) :=
    LinearIsometryEquiv.piLpCongrLeft 2 Real Real finProdFinEquiv
  let G := SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm phi
  let H := SchwartzMap.compCLMOfContinuousLinearEquiv Complex eF
    (flattenSchwartzNPoint (d := d) phi)
  have hfun : (G : EuclideanSpace Real (Fin n × Fin (d + 1)) -> Complex) ∘ J.symm = H := by
    funext v
    change phi (e.symm (J.symm v)) = flattenSchwartzNPoint (d := d) phi (eF v)
    rw [flattenSchwartzNPoint_apply]
    congr 1
    ext i mu
    change J.symm v (i, mu) = v (finProdFinEquiv (i, mu))
    simp [J, LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.piLpCongrLeft_apply]
  ext p
  change (SchwartzMap.fourierTransformCLM Complex G)
      (e ((flattenCLEquivReal n (d + 1)).symm p)) =
    (SchwartzMap.fourierTransformCLM Complex H) (eF.symm p)
  have hcoord : e ((flattenCLEquivReal n (d + 1)).symm p) = J.symm (eF.symm p) := by
    ext i
    change p (finProdFinEquiv i) = J.symm (eF.symm p) i
    simp [J, LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.piLpCongrLeft_apply, eF]
  rw [hcoord]
  simp only [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  rw [← hfun]
  exact (Real.fourier_comp_linearIsometry J.symm
    (G : EuclideanSpace Real (Fin n × Fin (d + 1)) -> Complex) (eF.symm p)).symm

theorem physicsFourierFlatCLM_flattenSchwartzNPoint_fourierTransform
    {d n : Nat} [NeZero d] (phi : SchwartzNPointSpace d n)
    (p : Fin (n * (d + 1)) -> Real) :
    physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) phi.fourierTransform) p =
      flattenSchwartzNPoint (d := d) phi ((1 / (2 * Real.pi) : Real) • p) := by
  rw [physicsFourierFlatCLM_apply, flattenSchwartzNPoint_fourierTransform]
  let e := EuclideanSpace.equiv (Fin (n * (d + 1))) Real
  let A := SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
    (flattenSchwartzNPoint (d := d) phi)
  have hround : SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm
        (SchwartzMap.fourierTransformCLM Complex A)) = SchwartzMap.fourierTransformCLM Complex A := by
    ext x
    simp
  change (SchwartzMap.fourierTransformCLM Complex
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm
          (SchwartzMap.fourierTransformCLM Complex A))))
      (e.symm ((-(1 / (2 * Real.pi) : Real)) • p)) = A (e.symm ((1 / (2 * Real.pi) : Real) • p))
  rw [hround, neg_smul, map_neg]
  have hinv : FourierTransformInv.fourierInv (FourierTransform.fourier A) = A :=
    FourierPair.fourierInv_fourier_eq A
  have h := congrArg (fun f : SchwartzMap (EuclideanSpace Real (Fin (n * (d + 1)))) Complex =>
      f (e.symm ((1 / (2 * Real.pi) : Real) • p))) hinv
  rw [SchwartzMap.fourierInv_apply_eq] at h
  exact h

end OSReconstruction
