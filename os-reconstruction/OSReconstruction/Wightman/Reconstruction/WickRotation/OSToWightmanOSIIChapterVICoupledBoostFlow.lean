/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledBoostSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISchwartzLinearFlow
import OSReconstruction.ComplexLieGroups.LorentzLieGroup









noncomputable section

open Complex Set Topology
open scoped Classical ContDiff

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat}

/-- The existing proper orthochronous planar boost as a real linear equivalence. -/
def osiiPlanarBoostCLE (d : Nat) (a : Fin d) (t : Real) :
    (Fin (d + 1) -> Real) ≃L[Real] (Fin (d + 1) -> Real) :=
  (Matrix.GeneralLinearGroup.toLin
    (LorentzLieGroup.toGL d (LorentzLieGroup.boostElement d a t).val)
    ).toLinearEquiv.toContinuousLinearEquiv

@[simp] theorem osiiPlanarBoostCLE_apply (a : Fin d) (t : Real)
    (x : Fin (d + 1) -> Real) :
    osiiPlanarBoostCLE d a t x = (LorentzLieGroup.planarBoost d a t).mulVec x := rfl

theorem osiiPlanarBoostCLE_time (a : Fin d) (t : Real)
    (x : Fin (d + 1) -> Real) :
    osiiPlanarBoostCLE d a t x 0 = Real.cosh t * x 0 + Real.sinh t * x a.succ := by
  simp [osiiPlanarBoostCLE_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    LorentzLieGroup.pb0, ite_mul]

theorem osiiPlanarBoostCLE_axis (a : Fin d) (t : Real)
    (x : Fin (d + 1) -> Real) :
    osiiPlanarBoostCLE d a t x a.succ =
      Real.sinh t * x 0 + Real.cosh t * x a.succ := by
  simp [osiiPlanarBoostCLE_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    LorentzLieGroup.pbK, ite_mul]

theorem osiiPlanarBoostCLE_other (a b : Fin d) (hba : b ≠ a) (t : Real)
    (x : Fin (d + 1) -> Real) : osiiPlanarBoostCLE d a t x b.succ = x b.succ := by
  simp only [osiiPlanarBoostCLE_apply, Matrix.mulVec, dotProduct,
    LorentzLieGroup.pbO d a t b.succ b.succ_ne_zero (by simpa using hba)]
  simp [ite_mul]

@[simp] theorem osiiPlanarBoostCLE_zero (a : Fin d) :
    osiiPlanarBoostCLE d a 0 = ContinuousLinearEquiv.refl Real _ := by
  ext x mu
  simp [LorentzLieGroup.planarBoost_zero]

@[simp] theorem osiiPlanarBoostCLE_symm (a : Fin d) (t : Real) :
    (osiiPlanarBoostCLE d a t).symm = osiiPlanarBoostCLE d a (-t) := by
  ext x mu
  have h : osiiPlanarBoostCLE d a t (osiiPlanarBoostCLE d a (-t) x) = x := by
    ext nu
    refine Fin.cases ?_ (fun b => ?_) nu
    · rw [osiiPlanarBoostCLE_time, osiiPlanarBoostCLE_time, osiiPlanarBoostCLE_axis]
      simp only [Real.cosh_neg, Real.sinh_neg]
      linear_combination x 0 * Real.cosh_sq t
    · by_cases hba : b = a
      · subst b
        rw [osiiPlanarBoostCLE_axis, osiiPlanarBoostCLE_time, osiiPlanarBoostCLE_axis]
        simp only [Real.cosh_neg, Real.sinh_neg]
        linear_combination x a.succ * Real.cosh_sq t
      · rw [osiiPlanarBoostCLE_other a b hba, osiiPlanarBoostCLE_other a b hba]
  exact congrFun ((osiiPlanarBoostCLE d a t).symm_apply_eq.mpr h.symm) mu

private def boostTangent (a : Fin d) (x : Fin (d + 1) -> Real) :
    Fin (d + 1) -> Real :=
  Fin.cons (x a.succ) (fun b => if b = a then x 0 else 0)

private theorem hasDerivAt_planarBoost (a : Fin d)
    (x : Fin (d + 1) -> Real) (t : Real) :
    HasDerivAt (fun u => osiiPlanarBoostCLE d a u x)
      (osiiPlanarBoostCLE d a t (boostTangent a x)) t := by
  apply hasDerivAt_pi.mpr
  intro mu
  refine Fin.cases ?_ (fun b => ?_) mu
  · simp only [osiiPlanarBoostCLE_time, boostTangent, Fin.cons_zero,
      Fin.cons_succ, ite_true]
    simpa only [add_comm] using
      ((Real.hasDerivAt_cosh t).mul_const (x 0)).add
        ((Real.hasDerivAt_sinh t).mul_const (x a.succ))
  · by_cases hba : b = a
    · subst b
      simp only [osiiPlanarBoostCLE_axis, boostTangent, Fin.cons_zero,
        Fin.cons_succ, ite_true]
      simpa only [add_comm] using
        ((Real.hasDerivAt_sinh t).mul_const (x 0)).add
          ((Real.hasDerivAt_cosh t).mul_const (x a.succ))
    · simp only [osiiPlanarBoostCLE_other a b hba, boostTangent,
        Fin.cons_succ, hba, ite_false]
      exact hasDerivAt_const t _

/-- The diagonal action on the existing gap-block coordinates. -/
def osiiNPointBoostCLE (d k : Nat) (a : Fin d) (t : Real) :
    NPointDomain d k ≃L[Real] NPointDomain d k :=
  ContinuousLinearEquiv.piCongrRight (fun _ : Fin k => osiiPlanarBoostCLE d a t)

@[simp] theorem osiiNPointBoostCLE_apply (a : Fin d) (t : Real)
    (x : NPointDomain d k) (j : Fin k) :
    osiiNPointBoostCLE d k a t x j = osiiPlanarBoostCLE d a t (x j) := rfl

variable [NeZero d]

/-- The same boost in the native mixed time/spatial source coordinates. -/
def osiiCoupledBoostCLE (d k : Nat) [NeZero d] (a : Fin d) (t : Real) :
    Section43TimeSpatialSpace d k ≃L[Real] Section43TimeSpatialSpace d k :=
  (nPointTimeSpatialCLE (d := d) k).symm.trans
    ((osiiNPointBoostCLE d k a t).trans (nPointTimeSpatialCLE (d := d) k))

@[simp] theorem osiiCoupledBoostCLE_apply (a : Fin d) (t : Real)
    (p : Section43TimeSpatialSpace d k) :
    osiiCoupledBoostCLE d k a t p = nPointTimeSpatialCLE (d := d) k
      (fun j => osiiPlanarBoostCLE d a t ((nPointTimeSpatialCLE (d := d) k).symm p j)) := rfl

theorem nPointTimeSpatialSchwartzCLE_boost (a : Fin d) (t : Real)
    (f : SchwartzNPoint d k) :
    nPointTimeSpatialSchwartzCLE (d := d) (n := k)
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiNPointBoostCLE d k a t) f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiCoupledBoostCLE d k a t)
        (nPointTimeSpatialSchwartzCLE (d := d) (n := k) f) := by
  ext p
  change f (osiiNPointBoostCLE d k a t ((nPointTimeSpatialCLE (d := d) k).symm p)) =
    f ((nPointTimeSpatialCLE (d := d) k).symm (osiiCoupledBoostCLE d k a t p))
  rw [osiiCoupledBoostCLE_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

@[simp] theorem osiiCoupledBoostCLE_zero (a : Fin d) :
    osiiCoupledBoostCLE d k a 0 = ContinuousLinearEquiv.refl Real _ := by
  apply ContinuousLinearEquiv.ext
  funext p
  simp only [osiiCoupledBoostCLE_apply, osiiPlanarBoostCLE_zero,
    ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem osiiCoupledBoostCLE_symm (a : Fin d) (t : Real) :
    (osiiCoupledBoostCLE d k a t).symm = osiiCoupledBoostCLE d k a (-t) := by
  apply ContinuousLinearEquiv.ext
  funext p
  change nPointTimeSpatialCLE (d := d) k
      (fun j => (osiiPlanarBoostCLE d a t).symm
        ((nPointTimeSpatialCLE (d := d) k).symm p j)) = _
  simp only [osiiPlanarBoostCLE_symm, osiiCoupledBoostCLE_apply]

theorem contDiff_osiiCoupledBoostCLE (a : Fin d) :
    ContDiff Real (⊤ : ℕ∞)
      (fun p : Real × Section43TimeSpatialSpace d k => osiiCoupledBoostCLE d k a p.1 p.2) := by
  have h : ContDiff Real (⊤ : ℕ∞)
      (fun p : Real × Section43TimeSpatialSpace d k => fun j : Fin k =>
        osiiPlanarBoostCLE d a p.1 ((nPointTimeSpatialCLE (d := d) k).symm p.2 j)) := by
    apply contDiff_pi.mpr
    intro j
    apply contDiff_pi.mpr
    intro mu
    simp only [osiiPlanarBoostCLE_apply, Matrix.mulVec, dotProduct,
      LorentzLieGroup.planarBoost, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.single_apply, smul_eq_mul]
    fun_prop
  simpa only [osiiCoupledBoostCLE_apply] using
    (nPointTimeSpatialCLE (d := d) k).contDiff.comp h

omit [NeZero d] in
@[simp] theorem osiiSpatialAxisCLM_coordinate (a b : Fin d)
    (t : Fin k -> Real) (j : Fin k) :
    osiiSpatialAxisCLM d k a t (j, b) = if b = a then t j else 0 := by
  by_cases hba : b = a
  · subst b
    simp [osiiSpatialAxisCLM, Pi.single_apply, mul_ite]
  · simp [osiiSpatialAxisCLM, hba]

omit [NeZero d] in
private theorem boostTangent_timeSpatial (a : Fin d)
    (p : Section43TimeSpatialSpace d k) (j : Fin k) :
    (nPointTimeSpatialCLE (d := d) k).symm (osiiCoupledBoostGenerator d k a p) j =
      boostTangent a ((nPointTimeSpatialCLE (d := d) k).symm p j) := by
  ext mu
  refine Fin.cases ?_ (fun b => ?_) mu
  · rfl
  · change osiiSpatialAxisCLM d k a p.1 (j, b) = if b = a then p.1 j else 0
    exact osiiSpatialAxisCLM_coordinate a b p.1 j

theorem hasDerivAt_osiiCoupledBoostCLE (a : Fin d)
    (p : Section43TimeSpatialSpace d k) (t : Real) :
    HasDerivAt (fun u => osiiCoupledBoostCLE d k a u p)
      (osiiCoupledBoostCLE d k a t (osiiCoupledBoostGenerator d k a p)) t := by
  have h := (nPointTimeSpatialCLE (d := d) k).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_pi.mpr (fun j : Fin k => hasDerivAt_planarBoost a
      ((nPointTimeSpatialCLE (d := d) k).symm p j) t))
  simpa only [osiiCoupledBoostCLE_apply, boostTangent_timeSpatial] using h

/-- A genuine boost Ward identity integrates to finite invariance on all
coupled Schwartz tests. No support or physical-tube premise is needed. -/
theorem osiiCoupledBoost_pairing_eq (a : Fin d)
    (T : SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex] Complex)
    (hWard : ∀ Phi, T (osiiCoupledBoostDeriv d k a Phi) = 0)
    (t : Real) (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (osiiCoupledBoostCLE d k a t) Phi) = T Phi := by
  apply OSIIChapterVI.linearFlow_pairing_eq T (osiiCoupledBoostGenerator d k a) hWard
    (osiiCoupledBoostCLE d k a) (contDiff_osiiCoupledBoostCLE a)
  · simpa only [osiiCoupledBoostCLE_symm] using
      (contDiff_osiiCoupledBoostCLE (k := k) a).continuous.comp
        (continuous_fst.neg.prodMk continuous_snd)
  · intro p
    rw [osiiCoupledBoostCLE_zero]
    rfl
  · exact fun s p => hasDerivAt_osiiCoupledBoostCLE a p s

end OSReconstruction
