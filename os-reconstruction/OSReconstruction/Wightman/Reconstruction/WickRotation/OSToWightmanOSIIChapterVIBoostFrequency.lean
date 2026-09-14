import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledBoostFlow
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICanonicalFrequencyTransport

/-!
# Actual contragredient boost transport in canonical momentum coordinates

Planar boosts are symmetric and have determinant one. The Fourier change of
variables therefore uses the opposite rapidity, not the same coordinate
action. Both frequency and spacetime distributions remain the native ones.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat}

/-- The actual diagonal boost in canonical flat particle-block coordinates. -/
def osiiFlatBoostCLE (d k : Nat) (a : Fin d) (t : Real) :
    (Fin (k * (d + 1)) -> Real) ≃L[Real] (Fin (k * (d + 1)) -> Real) :=
  (flattenCLEquivReal k (d + 1)).symm.trans
    ((osiiNPointBoostCLE d k a t).trans (flattenCLEquivReal k (d + 1)))

@[simp] theorem osiiFlatBoostCLE_block (a : Fin d) (t : Real)
    (p : Fin (k * (d + 1)) -> Real) (j : Fin k) (mu : Fin (d + 1)) :
    osiiFlatBoostCLE d k a t p (finProdFinEquiv (j, mu)) =
      osiiPlanarBoostCLE d a t (fun nu => p (finProdFinEquiv (j, nu))) mu := by
  simp [osiiFlatBoostCLE, flattenCLEquivReal_apply,
    osiiNPointBoostCLE_apply]
  rfl

@[simp] theorem osiiFlatBoostCLE_apply_flatten (a : Fin d) (t : Real)
    (x : NPointDomain d k) :
    osiiFlatBoostCLE d k a t (flattenCLEquivReal k (d + 1) x) =
      flattenCLEquivReal k (d + 1) (osiiNPointBoostCLE d k a t x) := by
  simp only [osiiFlatBoostCLE, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply]

@[simp] theorem osiiFlatBoostCLE_symm (a : Fin d) (t : Real) :
    (osiiFlatBoostCLE d k a t).symm = osiiFlatBoostCLE d k a (-t) := by
  apply ContinuousLinearEquiv.ext
  funext p
  change flattenCLEquivReal k (d + 1)
      (fun j => (osiiPlanarBoostCLE d a t).symm
        ((flattenCLEquivReal k (d + 1)).symm p j)) = _
  simp only [osiiPlanarBoostCLE_symm]
  rfl

theorem osiiPlanarBoostCLE_measurePreserving (a : Fin d) (t : Real) :
    MeasurePreserving (osiiPlanarBoostCLE d a t) volume volume := by
  refine ⟨(osiiPlanarBoostCLE d a t).continuous.measurable, ?_⟩
  change Measure.map (Matrix.toLin' (LorentzLieGroup.planarBoost d a t)) volume = volume
  simpa [LorentzLieGroup.planarBoost_det_one] using
    (Real.map_matrix_volume_pi_eq_smul_volume_pi
      (M := LorentzLieGroup.planarBoost d a t) (by simp [LorentzLieGroup.planarBoost_det_one]))

theorem osiiFlatBoostCLE_measurePreserving (a : Fin d) (t : Real) :
    MeasurePreserving (osiiFlatBoostCLE d k a t) volume volume := by
  have hf : MeasurePreserving (flattenCLEquivReal k (d + 1)) volume volume := by
    have he : (flattenCLEquivReal k (d + 1) : _ -> _) = flattenMeasurableEquiv k (d + 1) := by
      funext x i
      simp only [flattenCLEquivReal_apply, flattenMeasurableEquiv_apply]
    rw [he]
    exact flattenMeasurableEquiv_measurePreserving k (d + 1)
  have hi := hf.symm (flattenCLEquivReal k (d + 1)).toHomeomorph.toMeasurableEquiv
  have hb : MeasurePreserving (osiiNPointBoostCLE d k a t) volume volume :=
    volume_preserving_pi (fun _ : Fin k => osiiPlanarBoostCLE_measurePreserving a t)
  exact hf.comp (hb.comp hi)

/-- Symmetry of the actual one-block boost for the coordinate pairing. -/
theorem osiiPlanarBoostCLE_dotProduct (a : Fin d) (t : Real)
    (x y : Fin (d + 1) -> Real) :
    dotProduct (osiiPlanarBoostCLE d a t x) y =
      dotProduct x (osiiPlanarBoostCLE d a t y) := by
  rw [dotProduct_comm, osiiPlanarBoostCLE_apply, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, LorentzLieGroup.planarBoost_transpose, dotProduct_comm]
  rfl

theorem osiiFlatBoostCLE_dotProduct (a : Fin d) (t : Real)
    (x y : Fin (k * (d + 1)) -> Real) :
    dotProduct (osiiFlatBoostCLE d k a t x) y =
      dotProduct x (osiiFlatBoostCLE d k a t y) := by
  unfold dotProduct
  rw [← (finProdFinEquiv : Fin k × Fin (d + 1) ≃ Fin (k * (d + 1))).sum_comp,
    ← (finProdFinEquiv : Fin k × Fin (d + 1) ≃ Fin (k * (d + 1))).sum_comp]
  simp only [Fintype.sum_prod_type, osiiFlatBoostCLE_block]
  exact Finset.sum_congr rfl (fun j _ => osiiPlanarBoostCLE_dotProduct a t
    (fun mu => x (finProdFinEquiv (j, mu))) (fun mu => y (finProdFinEquiv (j, mu))))

theorem osiiFlatBoostCLE_dual_pair (a : Fin d) (t : Real)
    (x y : Fin (k * (d + 1)) -> Real) :
    dotProduct (osiiFlatBoostCLE d k a t x) (osiiFlatBoostCLE d k a (-t) y) =
      dotProduct x y := by
  rw [osiiFlatBoostCLE_dotProduct, ← osiiFlatBoostCLE_symm,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Positive-sign physics Fourier transform transports a boost by its
inverse transpose, which here is the negative-rapidity boost. -/
theorem physicsFourierFlatCLM_comp_osiiFlatBoostCLE (a : Fin d) (t : Real)
    (f : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex)
    (xi : Fin (k * (d + 1)) -> Real) :
    physicsFourierFlatCLM
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostCLE d k a t) f) xi =
      physicsFourierFlatCLM f (osiiFlatBoostCLE d k a (-t) xi) := by
  rw [← physicsFourierFlatCLM_integral, ← physicsFourierFlatCLM_integral]
  let g : (Fin (k * (d + 1)) -> Real) -> Complex := fun y =>
    Complex.exp (I * ∑ i, (y i : Complex) * (osiiFlatBoostCLE d k a (-t) xi i : Complex)) * f y
  calc
    _ = ∫ x, g (osiiFlatBoostCLE d k a t x) := by
      apply integral_congr_ae
      filter_upwards with x
      have hp :
          (∑ i, (osiiFlatBoostCLE d k a t x i : Complex) *
            (osiiFlatBoostCLE d k a (-t) xi i : Complex)) =
          ∑ i, (x i : Complex) * (xi i : Complex) := by
        exact_mod_cast osiiFlatBoostCLE_dual_pair a t x xi
      simp only [g, hp, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    _ = ∫ y, g y := (osiiFlatBoostCLE_measurePreserving a t).integral_comp'
      (f := (osiiFlatBoostCLE d k a t).toHomeomorph.toMeasurableEquiv) g

theorem physicsFourierFlatInvCLM_comp_osiiFlatBoostCLE (a : Fin d) (t : Real)
    (f : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
    physicsFourierFlatInvCLM
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostCLE d k a t) f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostCLE d k a (-t))
        (physicsFourierFlatInvCLM f) := by
  apply (Function.LeftInverse.injective
    (fun H : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex =>
      physicsFourierFlatInvCLM_left H))
  ext xi
  rw [physicsFourierFlatCLM_inv_right, physicsFourierFlatCLM_comp_osiiFlatBoostCLE,
    physicsFourierFlatCLM_inv_right, neg_neg]
  rfl

/-- The canonical frequency distribution inherits the actual reduced
boundary's boosts, with the explicit inverse-Fourier convention. -/
theorem osiiCanonicalFrequencyDistribution_boost_eq (a : Fin d)
    (W : SchwartzNPoint d k →L[Complex] Complex)
    (hW : ∀ (t : Real) (f : SchwartzNPoint d k),
      W (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiNPointBoostCLE d k a t) f) = W f)
    (t : Real) (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
    osiiCanonicalFrequencyDistribution W
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostCLE d k a t) phi) =
      osiiCanonicalFrequencyDistribution W phi := by
  change W (_root_.unflattenSchwartzNPoint
    (physicsFourierFlatInvCLM
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostCLE d k a t) phi))) = _
  rw [physicsFourierFlatInvCLM_comp_osiiFlatBoostCLE]
  have hsource : _root_.unflattenSchwartzNPoint (d := d)
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostCLE d k a (-t))
        (physicsFourierFlatInvCLM phi)) =
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiNPointBoostCLE d k a (-t))
        (_root_.unflattenSchwartzNPoint (d := d) (physicsFourierFlatInvCLM phi)) := by
    ext x
    change physicsFourierFlatInvCLM phi
        (osiiFlatBoostCLE d k a (-t) (flattenCLEquivReal k (d + 1) x)) =
      physicsFourierFlatInvCLM phi
        (flattenCLEquivReal k (d + 1) (osiiNPointBoostCLE d k a (-t) x))
    rw [osiiFlatBoostCLE_apply_flatten]
  rw [hsource, hW]
  rfl

end OSReconstruction
