import OSReconstruction.Wightman.Reconstruction.SchwartzPartialEval
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

noncomputable section

open SchwartzMap
open scoped FourierTransform

namespace OSReconstruction

variable (d n : ℕ) [NeZero d]

/-- Split an `n`-point spacetime configuration into its `n` time coordinates and
its combined `n*d` spatial block. -/
noncomputable def nPointTimeSpatialCLE :
    NPointDomain d n ≃L[ℝ] (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) := by
  let e : NPointDomain d n ≃ₗ[ℝ] (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) :=
    { toFun := fun x =>
        ( fun i => x i 0
        , (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)).symm
            (fun p => x p.1 (Fin.succ p.2)) )
      invFun := fun y i =>
        Fin.cons (y.1 i)
          (fun j => (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) y.2) (i, j))
      map_add' := by
        intro x y
        ext i <;> simp
      map_smul' := by
        intro c x
        ext i <;> simp
      left_inv := by
        intro x
        ext i j
        refine Fin.cases ?_ ?_ j
        · rfl
        · intro k
          simp
      right_inv := by
        intro y
        ext i <;> simp }
  exact e.toContinuousLinearEquiv

/-- The Schwartz-space lift of `nPointTimeSpatialCLE`. -/
noncomputable def nPointTimeSpatialSchwartzCLE :
    SchwartzNPoint d n ≃L[ℂ]
      SchwartzMap ((Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) ℂ := by
  let e := nPointTimeSpatialCLE (d := d) n
  let toFwd :
      SchwartzNPoint d n →L[ℂ]
        SchwartzMap ((Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let toInv :
      SchwartzMap ((Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) ℂ →L[ℂ]
        SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  exact
    { toLinearEquiv :=
        { toFun := toFwd
          map_add' := toFwd.map_add
          map_smul' := toFwd.map_smul
          invFun := toInv
          left_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e]
          right_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e] }
      continuous_toFun := toFwd.continuous
      continuous_invFun := toInv.continuous }

/-- The swapped version of `nPointTimeSpatialCLE`, so the spatial block appears
first and the time block second. This is the correct product order for
`SchwartzMap.partialEval₂`, which fixes the second factor. -/
noncomputable def nPointSpatialTimeCLE :
    NPointDomain d n ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) :=
  (nPointTimeSpatialCLE (d := d) n).trans
    (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) (EuclideanSpace ℝ (Fin n × Fin d)))

/-- The Schwartz-space lift of `nPointSpatialTimeCLE`. -/
noncomputable def nPointSpatialTimeSchwartzCLE :
    SchwartzNPoint d n ≃L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) ℂ := by
  let e := nPointSpatialTimeCLE (d := d) n
  let toFwd :
      SchwartzNPoint d n →L[ℂ]
        SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let toInv :
      SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) ℂ →L[ℂ]
        SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  exact
    { toLinearEquiv :=
        { toFun := toFwd
          map_add' := toFwd.map_add
          map_smul' := toFwd.map_smul
          invFun := toInv
          left_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e]
          right_inv := by
            intro f
            ext x
            simp [toFwd, toInv, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, e] }
      continuous_toFun := toFwd.continuous
      continuous_invFun := toInv.continuous }

omit [NeZero d] in
@[simp] theorem nPointSpatialTimeSchwartzCLE_apply
    (f : SchwartzNPoint d n)
    (η : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    nPointSpatialTimeSchwartzCLE (d := d) (n := n) f (η, t) =
      nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (t, η) := by
  simp [nPointSpatialTimeSchwartzCLE, nPointTimeSpatialCLE, nPointSpatialTimeCLE,
    nPointTimeSpatialSchwartzCLE, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- The real-product postcomposition of `nPointSpatialTimeSchwartzCLE`, used to
measure derivatives on a codomain where Lean has the needed operator norms. -/
noncomputable def nPointSpatialTimeSchwartzRealProd
    (f : SchwartzNPoint d n) :
    SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) (ℝ × ℝ) :=
  (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f).postcompCLM
    (𝕜 := ℝ) Complex.equivRealProdCLM.toContinuousLinearMap

omit [NeZero d] in
@[simp] theorem nPointSpatialTimeSchwartzRealProd_apply
    (f : SchwartzNPoint d n)
    (η : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f (η, t) =
      Complex.equivRealProdCLM (nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (t, η)) := by
  simp [nPointSpatialTimeSchwartzRealProd, nPointSpatialTimeSchwartzCLE_apply]

omit [NeZero d] in
private noncomputable def complexPhaseRealProdCLM
    (z : ℂ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Complex.equivRealProdCLM.toContinuousLinearMap).comp
    ((ContinuousLinearMap.mulLeftRight ℝ ℂ z (1 : ℂ)).comp
      (Complex.equivRealProdCLM.symm.toContinuousLinearMap))

@[simp] theorem complexPhaseRealProdCLM_apply
    (z : ℂ) (p : ℝ × ℝ) :
    complexPhaseRealProdCLM z p =
      Complex.equivRealProdCLM (z * Complex.equivRealProdCLM.symm p) := by
  simp [complexPhaseRealProdCLM, ContinuousLinearMap.mulLeftRight_apply, mul_assoc]

omit [NeZero d] in
private noncomputable def partialFourierSpatial_timeDerivativeRealProd
    (f : SchwartzNPoint d n)
    (ξ η : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (ℝ × ℝ) :=
  (complexPhaseRealProdCLM ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ))).comp
    (((fderiv ℝ
        (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f :
          EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) → ℝ × ℝ)
        (η, t)).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n × Fin d))
        (Fin n → ℝ))))

/-- Split a product-valued iterated-derivative direction family into its two
coordinate direction families. -/
noncomputable def productDirectionSplit
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : ℕ) :
    (Fin l → E × F) ≃L[ℝ] (Fin l → E) × (Fin l → F) := by
  let e : (Fin l → E × F) ≃ₗ[ℝ] (Fin l → E) × (Fin l → F) :=
    { toFun := fun m => (fun i => (m i).1, fun i => (m i).2)
      invFun := fun m i => (m.1 i, m.2 i)
      map_add' := by
        intro x y
        ext i <;> rfl
      map_smul' := by
        intro c x
        ext i <;> rfl
      left_inv := by
        intro m
        funext i
        simp
      right_inv := by
        intro m
        ext i <;> rfl }
  exact
    { toLinearEquiv := e
      continuous_toFun := by
        refine Continuous.prodMk ?_ ?_
        · exact continuous_pi fun i => (continuous_apply i).fst
        · exact continuous_pi fun i => (continuous_apply i).snd
      continuous_invFun := by
        refine continuous_pi ?_
        intro i
        refine Continuous.prodMk ?_ ?_
        · exact (continuous_apply i).comp continuous_fst
        · exact (continuous_apply i).comp continuous_snd }

/-- The concrete pointwise partial spatial Fourier transform used in theorem-3
branch `3b`: fix the time block and Fourier-transform only the spatial block. -/
noncomputable def partialFourierSpatial_fun
    (f : SchwartzNPoint d n) :
    (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) → ℂ :=
  fun p =>
    let slice :=
      SchwartzMap.partialEval₂ (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f) p.1
    (SchwartzMap.fourierTransformCLM ℂ slice) p.2

omit [NeZero d] in
theorem partialFourierSpatial_integrable
    (f : SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    MeasureTheory.Integrable (fun η : EuclideanSpace ℝ (Fin n × Fin d) =>
      𝐞 (-(inner ℝ η p.2)) • nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (p.1, η)) := by
  let slice : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d)) ℂ :=
    SchwartzMap.partialEval₂ (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f) p.1
  have hslice : MeasureTheory.Integrable
      (slice : EuclideanSpace ℝ (Fin n × Fin d) → ℂ) := slice.integrable
  simpa [slice, SchwartzMap.partialEval₂, nPointSpatialTimeSchwartzCLE_apply] using
    (Real.fourierIntegral_convergent_iff (f := (slice : EuclideanSpace ℝ (Fin n × Fin d) → ℂ))
      (w := p.2)).2 hslice

omit [NeZero d] in
theorem partialFourierSpatial_fun_eq_integral
    (f : SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := n) f p =
      ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
        𝐞 (-(inner ℝ η p.2)) •
          nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (p.1, η) := by
  simpa [partialFourierSpatial_fun, SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.partialEval₂, nPointSpatialTimeSchwartzCLE_apply] using
    (Real.fourier_eq
      (((SchwartzMap.partialEval₂
          (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f) p.1 :
            SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d)) ℂ) :
          EuclideanSpace ℝ (Fin n × Fin d) → ℂ))
      p.2)

omit [NeZero d] in
@[simp] theorem partialFourierSpatial_fun_add
    (f g : SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := n) (f + g) p =
      partialFourierSpatial_fun (d := d) (n := n) f p +
        partialFourierSpatial_fun (d := d) (n := n) g p := by
  let sf : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d)) ℂ :=
    SchwartzMap.partialEval₂ (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f) p.1
  let sg : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d)) ℂ :=
    SchwartzMap.partialEval₂ (nPointSpatialTimeSchwartzCLE (d := d) (n := n) g) p.1
  change ((SchwartzMap.fourierTransformCLM ℂ) (sf + sg)) p.2 =
      ((SchwartzMap.fourierTransformCLM ℂ) sf) p.2 +
        ((SchwartzMap.fourierTransformCLM ℂ) sg) p.2
  rw [(SchwartzMap.fourierTransformCLM ℂ).map_add]
  rfl

omit [NeZero d] in
@[simp] theorem partialFourierSpatial_fun_smul
    (a : ℂ) (f : SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := n) (a • f) p =
      a * partialFourierSpatial_fun (d := d) (n := n) f p := by
  let sf : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d)) ℂ :=
    SchwartzMap.partialEval₂ (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f) p.1
  change ((SchwartzMap.fourierTransformCLM ℂ) (a • sf)) p.2 =
      a * ((SchwartzMap.fourierTransformCLM ℂ) sf) p.2
  rw [(SchwartzMap.fourierTransformCLM ℂ).map_smul]
  simp [smul_eq_mul]

omit [NeZero d] in
theorem continuous_partialFourierSpatial_fun
    (f : SchwartzNPoint d n) :
    Continuous (partialFourierSpatial_fun (d := d) (n := n) f) := by
  let H : (Fin n → ℝ) → BoundedContinuousFunction (EuclideanSpace ℝ (Fin n × Fin d)) ℂ :=
    fun t =>
      ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ
          (EuclideanSpace ℝ (Fin n × Fin d)) ℂ).comp
        (SchwartzMap.fourierTransformCLM ℂ))
          (SchwartzMap.partialEval₂ (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f) t)
  have hH : Continuous H := by
    exact
      (((SchwartzMap.toBoundedContinuousFunctionCLM ℂ
          (EuclideanSpace ℝ (Fin n × Fin d)) ℂ).continuous.comp
        (SchwartzMap.fourierTransformCLM ℂ).continuous).comp
          (continuous_partialEval₂ (f := nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
  have hEq :
      partialFourierSpatial_fun (d := d) (n := n) f =
        fun p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) => H p.1 p.2 := by
    funext p
    simp [H, partialFourierSpatial_fun]
  rw [hEq]
  exact continuous_eval.comp (hH.prodMap continuous_id)

omit [NeZero d] in
theorem contDiff_partialFourierSpatial_fun_spatial
    (f : SchwartzNPoint d n) (t : Fin n → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n × Fin d) =>
      partialFourierSpatial_fun (d := d) (n := n) f (t, ξ)) := by
  let slice : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin d)) ℂ :=
    SchwartzMap.partialEval₂ (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f) t
  change ContDiff ℝ (⊤ : ℕ∞) (⇑((SchwartzMap.fourierTransformCLM ℂ) slice))
  exact ((SchwartzMap.fourierTransformCLM ℂ) slice).smooth (⊤ : ℕ∞)

omit [NeZero d] in
theorem hasFDerivAt_spatialTimeSlice_time
    (f : SchwartzNPoint d n)
    (η : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    HasFDerivAt
      (fun t' : Fin n → ℝ => nPointSpatialTimeSchwartzCLE (d := d) (n := n) f (η, t'))
      ((fderiv ℝ
          (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f :
            EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) → ℂ)
          (η, t)).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n × Fin d)) (Fin n → ℝ)))
      t := by
  simpa using
    (((nPointSpatialTimeSchwartzCLE (d := d) (n := n) f).differentiableAt).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_right η t))

omit [NeZero d] in
theorem hasFDerivAt_partialFourierSpatial_integrand_time
    (f : SchwartzNPoint d n)
    (ξ η : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    HasFDerivAt
      (fun t' : Fin n → ℝ =>
        𝐞 (-(inner ℝ η ξ)) • nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (t', η))
      (𝐞 (-(inner ℝ η ξ)) •
        ((fderiv ℝ
            (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f :
              EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) → ℂ)
            (η, t)).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n × Fin d))
            (Fin n → ℝ))))
      t := by
  simpa [nPointSpatialTimeSchwartzCLE_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    (hasFDerivAt_spatialTimeSlice_time (d := d) (n := n) f η t).const_smul
      (𝐞 (-(inner ℝ η ξ)))

omit [NeZero d] in
theorem integrable_partialFourierSpatial_realProdIntegrand
    (f : SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    MeasureTheory.Integrable (fun η : EuclideanSpace ℝ (Fin n × Fin d) =>
      Complex.equivRealProdCLM
        (𝐞 (-(inner ℝ η p.2)) •
          nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (p.1, η))) := by
  exact Complex.equivRealProdCLM.toContinuousLinearMap.integrable_comp
    (partialFourierSpatial_integrable (d := d) (n := n) f p)

omit [NeZero d] in
theorem partialFourierSpatial_fun_eq_integral_realProd
    (f : SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) f p) =
      ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
        Complex.equivRealProdCLM
          (𝐞 (-(inner ℝ η p.2)) •
            nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (p.1, η)) := by
  rw [partialFourierSpatial_fun_eq_integral (d := d) (n := n) f p]
  exact (Complex.equivRealProdCLM.integral_comp_comm
    (fun η : EuclideanSpace ℝ (Fin n × Fin d) =>
      𝐞 (-(inner ℝ η p.2)) • nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (p.1, η))).symm

omit [NeZero d] in
private theorem hasFDerivAt_spatialTimeSlice_time_realProd
    (f : SchwartzNPoint d n)
    (η : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    HasFDerivAt
      (fun t' : Fin n → ℝ => nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f (η, t'))
      (((fderiv ℝ
          (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f :
            EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) → ℝ × ℝ)
          (η, t)).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n × Fin d)) (Fin n → ℝ))))
      t := by
  simpa using
    (((nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f).differentiableAt).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_right η t))

omit [NeZero d] in
theorem hasFDerivAt_partialFourierSpatial_integrand_time_realProd
    (f : SchwartzNPoint d n)
    (ξ η : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    HasFDerivAt
      (fun t' : Fin n → ℝ =>
        Complex.equivRealProdCLM
          (𝐞 (-(inner ℝ η ξ)) • nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (t', η)))
      (partialFourierSpatial_timeDerivativeRealProd d n f ξ η t)
      t := by
  let c : ℂ := ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ))
  convert
    ((complexPhaseRealProdCLM c).hasFDerivAt.comp t
      (hasFDerivAt_spatialTimeSlice_time_realProd (d := d) (n := n) f η t)) using 1
  · funext t'
    ext <;> simp [c, Circle.smul_def, nPointSpatialTimeSchwartzRealProd_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]

omit [NeZero d] in
private noncomputable def partialFourierSpatial_timeDominatingBound
    (f : SchwartzNPoint d n) :
    EuclideanSpace ℝ (Fin n × Fin d) → ℝ := by
  let phaseConst : ℝ :=
    ‖Complex.equivRealProdCLM.toContinuousLinearMap‖ *
      ‖Complex.equivRealProdCLM.symm.toContinuousLinearMap‖
  let M : ℕ := Module.finrank ℝ (EuclideanSpace ℝ (Fin n × Fin d)) + 1
  let sem : ℝ :=
    ((Finset.Iic (M, 1)).sup
      (schwartzSeminormFamily ℝ
        (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) (ℝ × ℝ)))
      (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f)
  exact fun η => (phaseConst * ((2 : ℝ) ^ M * sem)) / (1 + ‖η‖) ^ M

omit [NeZero d] in
set_option maxHeartbeats 400000 in
private theorem norm_partialFourierSpatial_integrand_time_realProd_fderiv_le
    (f : SchwartzNPoint d n)
    (ξ η : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    ‖partialFourierSpatial_timeDerivativeRealProd d n f ξ η t‖ ≤
      partialFourierSpatial_timeDominatingBound d n f η := by
  let Eη := EuclideanSpace ℝ (Fin n × Fin d)
  let Et := Fin n → ℝ
  let G : SchwartzMap (Eη × Et) (ℝ × ℝ) :=
    nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f
  let phaseConst : ℝ :=
    ‖Complex.equivRealProdCLM.toContinuousLinearMap‖ *
      ‖Complex.equivRealProdCLM.symm.toContinuousLinearMap‖
  let M : ℕ := Module.finrank ℝ (EuclideanSpace ℝ (Fin n × Fin d)) + 1
  let sem : ℝ :=
    ((Finset.Iic (M, 1)).sup
      (schwartzSeminormFamily ℝ
        (EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ)) (ℝ × ℝ)))
      G
  have hη :
      ‖η‖ ≤ ‖((η, t) : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ))‖ := by
    exact le_max_left _ _
  have hseminorm :
      (1 + ‖((η, t) : EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ))‖) ^ M *
        ‖fderiv ℝ (G : Eη × Et → ℝ × ℝ) (η, t)‖ ≤
      (2 : ℝ) ^ M * sem := by
    simpa [sem, M] using
      (SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℝ) (m := (M, 1)) (k := M) (n := 1)
        le_rfl le_rfl G (η, t))
  have hphase_le :
      ‖complexPhaseRealProdCLM ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ))‖ ≤ phaseConst := by
    let c : ℂ := ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ))
    have hmull :
        ‖ContinuousLinearMap.mulLeftRight ℝ ℂ c (1 : ℂ)‖ ≤ (1 : ℝ) := by
      calc
        ‖ContinuousLinearMap.mulLeftRight ℝ ℂ c (1 : ℂ)‖ ≤ ‖c‖ * ‖(1 : ℂ)‖ := by
          exact ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ ℂ c (1 : ℂ)
        _ = 1 := by simp [c]
    have hphase_nonneg : 0 ≤ phaseConst := by positivity
    calc
      ‖complexPhaseRealProdCLM c‖
          ≤ ‖Complex.equivRealProdCLM.toContinuousLinearMap‖ *
              ‖(ContinuousLinearMap.mulLeftRight ℝ ℂ c
                  (1 : ℂ)).comp (Complex.equivRealProdCLM.symm.toContinuousLinearMap)‖ := by
            exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Complex.equivRealProdCLM.toContinuousLinearMap‖ *
            (‖ContinuousLinearMap.mulLeftRight ℝ ℂ c (1 : ℂ)‖ *
              ‖Complex.equivRealProdCLM.symm.toContinuousLinearMap‖) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Complex.equivRealProdCLM.toContinuousLinearMap‖ *
            (1 * ‖Complex.equivRealProdCLM.symm.toContinuousLinearMap‖) := by
            gcongr
      _ = phaseConst := by
            simp [phaseConst, mul_assoc, mul_left_comm, mul_comm]
  have hphaseConst_nonneg : 0 ≤ phaseConst := by positivity
  have hcomp_le :
      ‖partialFourierSpatial_timeDerivativeRealProd d n f ξ η t‖
        ≤ phaseConst * ‖fderiv ℝ (G : Eη × Et → ℝ × ℝ) (η, t)‖ := by
    calc
      ‖partialFourierSpatial_timeDerivativeRealProd d n f ξ η t‖
          ≤ ‖complexPhaseRealProdCLM ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ))‖ *
              ‖((fderiv ℝ (G : Eη × Et → ℝ × ℝ) (η, t)).comp
                  (ContinuousLinearMap.inr ℝ Eη Et))‖ := by
            exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ phaseConst *
            (‖fderiv ℝ (G : Eη × Et → ℝ × ℝ) (η, t)‖ *
              ‖ContinuousLinearMap.inr ℝ Eη Et‖) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ phaseConst * (‖fderiv ℝ (G : Eη × Et → ℝ × ℝ) (η, t)‖ * 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hphaseConst_nonneg
            exact mul_le_mul_of_nonneg_left
              (ContinuousLinearMap.norm_inr_le_one ℝ Eη Et) (norm_nonneg _)
      _ = phaseConst * ‖fderiv ℝ (G : Eη × Et → ℝ × ℝ) (η, t)‖ := by ring
  have hpow_pos : 0 < (1 + ‖η‖) ^ M := by positivity
  have hmain :
      ‖partialFourierSpatial_timeDerivativeRealProd d n f ξ η t‖ *
        (1 + ‖η‖) ^ M ≤
      phaseConst * ((2 : ℝ) ^ M * sem) := by
    calc
      ‖partialFourierSpatial_timeDerivativeRealProd d n f ξ η t‖ *
          (1 + ‖η‖) ^ M
          ≤ (phaseConst * ‖fderiv ℝ (G : Eη × Et → ℝ × ℝ) (η, t)‖) * (1 + ‖η‖) ^ M := by
            exact mul_le_mul_of_nonneg_right hcomp_le (by positivity)
      _ = phaseConst *
            (‖fderiv ℝ (G : Eη × Et → ℝ × ℝ) (η, t)‖ * (1 + ‖η‖) ^ M) := by ring
      _ ≤ phaseConst *
            (‖fderiv ℝ (G : Eη × Et → ℝ × ℝ) (η, t)‖ *
              (1 + ‖((η, t) : Eη × Et)‖) ^ M) := by
            have hpow_mono : (1 + ‖η‖) ^ M ≤ (1 + ‖((η, t) : Eη × Et)‖) ^ M := by
              exact pow_le_pow_left₀ (by positivity) (by linarith [hη]) M
            refine mul_le_mul_of_nonneg_left ?_ hphaseConst_nonneg
            exact mul_le_mul_of_nonneg_left hpow_mono (norm_nonneg _)
      _ = phaseConst *
            ((1 + ‖((η, t) : Eη × Et)‖) ^ M *
              ‖fderiv ℝ (G : Eη × Et → ℝ × ℝ) (η, t)‖) := by ring
      _ ≤ phaseConst * ((2 : ℝ) ^ M * sem) := by
            exact mul_le_mul_of_nonneg_left hseminorm hphaseConst_nonneg
  have hmain' :
      ‖partialFourierSpatial_timeDerivativeRealProd d n f ξ η t‖ ≤
      (phaseConst * ((2 : ℝ) ^ M * sem)) / (1 + ‖η‖) ^ M := by
    exact (le_div_iff₀ hpow_pos).2 <| by simpa [mul_comm] using hmain
  exact hmain'

omit [NeZero d] in
set_option maxHeartbeats 400000 in
private theorem integrable_partialFourierSpatial_timeDominatingBound
    (f : SchwartzNPoint d n) :
    MeasureTheory.Integrable
      (partialFourierSpatial_timeDominatingBound d n f)
      (MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin n × Fin d))) := by
  let Eη := EuclideanSpace ℝ (Fin n × Fin d)
  let phaseConst : ℝ :=
    ‖Complex.equivRealProdCLM.toContinuousLinearMap‖ *
      ‖Complex.equivRealProdCLM.symm.toContinuousLinearMap‖
  let M : ℕ := Module.finrank ℝ Eη + 1
  let sem : ℝ :=
    ((Finset.Iic (M, 1)).sup (schwartzSeminormFamily ℝ (Eη × (Fin n → ℝ)) (ℝ × ℝ)))
      (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f)
  have hfin : Module.finrank ℝ Eη = n * d := by
    simpa [Eη] using (finrank_euclideanSpace_fin (𝕜 := ℝ) (ι := Fin n × Fin d))
  have hM :
      (Module.finrank ℝ Eη : ℝ) < (M : ℝ) := by
    dsimp [M]
    norm_num
  have hbase :
      MeasureTheory.Integrable
        (fun η : Eη => Real.rpow (1 + ‖η‖) (-(M : ℝ)))
        (MeasureTheory.volume : MeasureTheory.Measure Eη) := by
    simpa using integrable_one_add_norm hM
  have hbound :
      partialFourierSpatial_timeDominatingBound d n f =
        fun η : Eη => (phaseConst * ((2 : ℝ) ^ M * sem)) * Real.rpow (1 + ‖η‖) (-(M : ℝ)) := by
    funext η
    have hη_nonneg : 0 ≤ 1 + ‖η‖ := by positivity
    have hpowη :
        ((1 + ‖η‖) ^ M)⁻¹ = Real.rpow (1 + ‖η‖) (-(M : ℝ)) := by
      simpa [Real.rpow_natCast] using (Real.rpow_neg hη_nonneg (M : ℝ)).symm
    calc
      partialFourierSpatial_timeDominatingBound d n f η
          = (phaseConst * ((2 : ℝ) ^ M * sem)) / (1 + ‖η‖) ^ M := by
              dsimp [partialFourierSpatial_timeDominatingBound, phaseConst, M, sem]
      _ = (phaseConst * ((2 : ℝ) ^ M * sem)) * ((1 + ‖η‖) ^ M)⁻¹ := by
              rw [div_eq_mul_inv]
      _ = (phaseConst * ((2 : ℝ) ^ M * sem)) * Real.rpow (1 + ‖η‖) (-(M : ℝ)) := by
              rw [hpowη]
  rw [hbound]
  simpa [phaseConst, M, sem, mul_assoc, mul_left_comm, mul_comm] using
    hbase.const_mul (phaseConst * ((2 : ℝ) ^ M * sem))

omit [NeZero d] in
theorem hasFDerivAt_partialFourierSpatial_fun_time_realProd
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    HasFDerivAt
      (fun s : Fin n → ℝ =>
        Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) f (s, ξ)))
      (∫ η : EuclideanSpace ℝ (Fin n × Fin d),
        partialFourierSpatial_timeDerivativeRealProd d n f ξ η t)
      t := by
  let Eη := EuclideanSpace ℝ (Fin n × Fin d)
  let Et := Fin n → ℝ
  let μ : MeasureTheory.Measure Eη := MeasureTheory.volume
  let F :
      Et → Eη → ℝ × ℝ :=
    fun s η =>
      Complex.equivRealProdCLM
        (𝐞 (-(inner ℝ η ξ)) •
          nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (s, η))
  let F' :
      Et → Eη → Et →L[ℝ] (ℝ × ℝ) :=
    fun s η => partialFourierSpatial_timeDerivativeRealProd d n f ξ η s
  let bound : Eη → ℝ := partialFourierSpatial_timeDominatingBound d n f
  have hs : (Set.univ : Set Et) ∈ nhds t := Filter.univ_mem
  have hF_meas : ∀ᶠ s in nhds t, MeasureTheory.AEStronglyMeasurable (F s) μ := by
    exact Filter.Eventually.of_forall (fun s =>
      (integrable_partialFourierSpatial_realProdIntegrand (d := d) (n := n) f (s, ξ)).aestronglyMeasurable)
  have hF_int : MeasureTheory.Integrable (F t) μ := by
    simpa [F] using
      integrable_partialFourierSpatial_realProdIntegrand (d := d) (n := n) f (t, ξ)
  have hF'_meas : MeasureTheory.AEStronglyMeasurable (F' t) μ := by
    have hpath : Continuous fun η : Eη => (η, t) := continuous_id.prodMk continuous_const
    have hcont_fderiv :
        Continuous (fun η : Eη =>
          fderiv ℝ
            (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f : Eη × Et → ℝ × ℝ)
            (η, t)) := by
      exact (((nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f).smooth 1).continuous_fderiv
        one_ne_zero).comp hpath
    have hcont_slice :
        Continuous (fun η : Eη =>
          ((fderiv ℝ
              (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f : Eη × Et → ℝ × ℝ)
              (η, t)).comp
            (ContinuousLinearMap.inr ℝ Eη Et))) := by
      exact hcont_fderiv.clm_comp continuous_const
    have hinner :
        Continuous (fun η : Eη => inner ℝ η ξ) := by
      simpa using
        ((continuous_inner : Continuous fun p : Eη × Eη => inner ℝ p.1 p.2).comp
          (continuous_id.prodMk continuous_const))
    have hkernel :
        Continuous (fun η : Eη => ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ))) := by
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp hinner.neg)
    have hmul :
        Continuous fun z : ℂ => ContinuousLinearMap.mulLeftRight ℝ ℂ z (1 : ℂ) := by
      exact (ContinuousLinearMap.mulLeftRight ℝ ℂ).continuous.clm_apply continuous_const
    have hphase0 :
        Continuous fun η : Eη =>
          (ContinuousLinearMap.mulLeftRight ℝ ℂ ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ)) (1 : ℂ)) := by
      exact hmul.comp hkernel
    have hphase1 :
        Continuous fun η : Eη =>
          (ContinuousLinearMap.mulLeftRight ℝ ℂ ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ)) (1 : ℂ)).comp
            (Complex.equivRealProdCLM.symm.toContinuousLinearMap) := by
      exact hphase0.clm_comp continuous_const
    have hphase :
        Continuous fun η : Eη =>
          complexPhaseRealProdCLM ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ)) := by
      let L : ((ℝ × ℝ) →L[ℝ] ℂ) →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
        (ContinuousLinearMap.compL ℝ (ℝ × ℝ) ℂ (ℝ × ℝ))
          (Complex.equivRealProdCLM.toContinuousLinearMap)
      simpa [complexPhaseRealProdCLM, L, ContinuousLinearMap.compL_apply] using
        L.continuous.comp hphase1
    exact (hphase.clm_comp hcont_slice).aestronglyMeasurable
  have h_bound :
      ∀ᵐ η ∂μ, ∀ s ∈ (Set.univ : Set Et), ‖F' s η‖ ≤ bound η := by
    refine Filter.Eventually.of_forall ?_
    intro η s hs_mem
    simpa [F', bound] using
      norm_partialFourierSpatial_integrand_time_realProd_fderiv_le
        (d := d) (n := n) f ξ η s
  have h_bound_int : MeasureTheory.Integrable bound μ := by
    simpa [bound] using
      integrable_partialFourierSpatial_timeDominatingBound (d := d) (n := n) f
  have h_diff :
      ∀ᵐ η ∂μ, ∀ s ∈ (Set.univ : Set Et), HasFDerivAt (F · η) (F' s η) s := by
    refine Filter.Eventually.of_forall ?_
    intro η s hs_mem
    simpa [F, F'] using
      hasFDerivAt_partialFourierSpatial_integrand_time_realProd (d := d) (n := n) f ξ η s
  have hfun :
      (fun s : Et => Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) f (s, ξ))) =
      fun s : Et => ∫ η : Eη, F s η := by
    funext s
    simpa [F] using partialFourierSpatial_fun_eq_integral_realProd (d := d) (n := n) f (s, ξ)
  rw [hfun]
  exact
    (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := μ) (s := (Set.univ : Set Et)) (x₀ := t)
      (F := F) (F' := F')
      hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff)

theorem integrable_partialFourierSpatial_timeDerivativeRealProd
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) (t : Fin n → ℝ) :
    MeasureTheory.Integrable
      (fun η : EuclideanSpace ℝ (Fin n × Fin d) =>
        partialFourierSpatial_timeDerivativeRealProd d n f ξ η t)
      (MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin n × Fin d))) := by
  let Eη := EuclideanSpace ℝ (Fin n × Fin d)
  let Et := Fin n → ℝ
  let μ : MeasureTheory.Measure Eη := MeasureTheory.volume
  let bound : Eη → ℝ := partialFourierSpatial_timeDominatingBound d n f
  have h_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun η : Eη => partialFourierSpatial_timeDerivativeRealProd d n f ξ η t) μ := by
    have hpath : Continuous fun η : Eη => (η, t) := continuous_id.prodMk continuous_const
    have hcont_fderiv :
        Continuous (fun η : Eη =>
          fderiv ℝ
            (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f : Eη × Et → ℝ × ℝ)
            (η, t)) := by
      exact (((nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f).smooth 1).continuous_fderiv
        one_ne_zero).comp hpath
    have hcont_slice :
        Continuous (fun η : Eη =>
          ((fderiv ℝ
              (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f : Eη × Et → ℝ × ℝ)
              (η, t)).comp
            (ContinuousLinearMap.inr ℝ Eη Et))) := by
      exact hcont_fderiv.clm_comp continuous_const
    have hinner :
        Continuous (fun η : Eη => inner ℝ η ξ) := by
      simpa using
        ((continuous_inner : Continuous fun p : Eη × Eη => inner ℝ p.1 p.2).comp
          (continuous_id.prodMk continuous_const))
    have hkernel :
        Continuous (fun η : Eη => ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ))) := by
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp hinner.neg)
    have hmul :
        Continuous fun z : ℂ => ContinuousLinearMap.mulLeftRight ℝ ℂ z (1 : ℂ) := by
      exact (ContinuousLinearMap.mulLeftRight ℝ ℂ).continuous.clm_apply continuous_const
    have hphase0 :
        Continuous fun η : Eη =>
          (ContinuousLinearMap.mulLeftRight ℝ ℂ ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ)) (1 : ℂ)) := by
      exact hmul.comp hkernel
    have hphase1 :
        Continuous fun η : Eη =>
          (ContinuousLinearMap.mulLeftRight ℝ ℂ ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ)) (1 : ℂ)).comp
            (Complex.equivRealProdCLM.symm.toContinuousLinearMap) := by
      exact hphase0.clm_comp continuous_const
    have hphase :
        Continuous fun η : Eη =>
          complexPhaseRealProdCLM ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ)) := by
      let L : ((ℝ × ℝ) →L[ℝ] ℂ) →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
        (ContinuousLinearMap.compL ℝ (ℝ × ℝ) ℂ (ℝ × ℝ))
          (Complex.equivRealProdCLM.toContinuousLinearMap)
      simpa [complexPhaseRealProdCLM, L, ContinuousLinearMap.compL_apply] using
        L.continuous.comp hphase1
    exact (hphase.clm_comp hcont_slice).aestronglyMeasurable
  have h_bound :
      ∀ᵐ η ∂μ, ‖partialFourierSpatial_timeDerivativeRealProd d n f ξ η t‖ ≤ bound η := by
    refine Filter.Eventually.of_forall ?_
    intro η
    simpa [bound] using
      norm_partialFourierSpatial_integrand_time_realProd_fderiv_le
        (d := d) (n := n) f ξ η t
  have h_bound_int : MeasureTheory.Integrable bound μ := by
    simpa [bound] using
      integrable_partialFourierSpatial_timeDominatingBound (d := d) (n := n) f
  exact h_bound_int.mono' h_meas h_bound

theorem continuous_partialFourierSpatial_fun_timeFDeriv_realProd
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Continuous (fun t : Fin n → ℝ =>
      ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
        partialFourierSpatial_timeDerivativeRealProd d n f ξ η t) := by
  let Eη := EuclideanSpace ℝ (Fin n × Fin d)
  let Et := Fin n → ℝ
  let μ : MeasureTheory.Measure Eη := MeasureTheory.volume
  let F :
      Et → Eη → Et →L[ℝ] (ℝ × ℝ) :=
    fun t η => partialFourierSpatial_timeDerivativeRealProd d n f ξ η t
  let bound : Eη → ℝ := partialFourierSpatial_timeDominatingBound d n f
  have hF_meas : ∀ t, MeasureTheory.AEStronglyMeasurable (F t) μ := by
    intro t
    have hpath : Continuous fun η : Eη => (η, t) := continuous_id.prodMk continuous_const
    have hcont_fderiv :
        Continuous (fun η : Eη =>
          fderiv ℝ
            (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f : Eη × Et → ℝ × ℝ)
            (η, t)) := by
      exact (((nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f).smooth 1).continuous_fderiv
        one_ne_zero).comp hpath
    have hcont_slice :
        Continuous (fun η : Eη =>
          ((fderiv ℝ
              (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f : Eη × Et → ℝ × ℝ)
              (η, t)).comp
            (ContinuousLinearMap.inr ℝ Eη Et))) := by
      exact hcont_fderiv.clm_comp continuous_const
    have hinner :
        Continuous (fun η : Eη => inner ℝ η ξ) := by
      simpa using
        ((continuous_inner : Continuous fun p : Eη × Eη => inner ℝ p.1 p.2).comp
          (continuous_id.prodMk continuous_const))
    have hkernel :
        Continuous (fun η : Eη => ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ))) := by
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp hinner.neg)
    have hmul :
        Continuous fun z : ℂ => ContinuousLinearMap.mulLeftRight ℝ ℂ z (1 : ℂ) := by
      exact (ContinuousLinearMap.mulLeftRight ℝ ℂ).continuous.clm_apply continuous_const
    have hphase0 :
        Continuous fun η : Eη =>
          (ContinuousLinearMap.mulLeftRight ℝ ℂ ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ)) (1 : ℂ)) := by
      exact hmul.comp hkernel
    have hphase1 :
        Continuous fun η : Eη =>
          (ContinuousLinearMap.mulLeftRight ℝ ℂ ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ)) (1 : ℂ)).comp
            (Complex.equivRealProdCLM.symm.toContinuousLinearMap) := by
      exact hphase0.clm_comp continuous_const
    have hphase :
        Continuous fun η : Eη =>
          complexPhaseRealProdCLM ((((𝐞 (-(inner ℝ η ξ))) : Circle) : ℂ)) := by
      let L : ((ℝ × ℝ) →L[ℝ] ℂ) →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
        (ContinuousLinearMap.compL ℝ (ℝ × ℝ) ℂ (ℝ × ℝ))
          (Complex.equivRealProdCLM.toContinuousLinearMap)
      simpa [complexPhaseRealProdCLM, L, ContinuousLinearMap.compL_apply] using
        L.continuous.comp hphase1
    exact (hphase.clm_comp hcont_slice).aestronglyMeasurable
  have h_bound : ∀ t, ∀ᵐ η ∂μ, ‖F t η‖ ≤ bound η := by
    intro t
    refine Filter.Eventually.of_forall ?_
    intro η
    simpa [F, bound] using
      norm_partialFourierSpatial_integrand_time_realProd_fderiv_le
        (d := d) (n := n) f ξ η t
  have h_bound_int : MeasureTheory.Integrable bound μ := by
    simpa [bound] using
      integrable_partialFourierSpatial_timeDominatingBound (d := d) (n := n) f
  have h_cont : ∀ᵐ η ∂μ, Continuous fun t : Et => F t η := by
    refine Filter.Eventually.of_forall ?_
    intro η
    have hpath : Continuous fun t : Et => (η, t) := continuous_const.prodMk continuous_id
    have hcont_fderiv :
        Continuous (fun t : Et =>
          fderiv ℝ
            (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f : Eη × Et → ℝ × ℝ)
            (η, t)) := by
      exact (((nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f).smooth 1).continuous_fderiv
        one_ne_zero).comp hpath
    have hcont_slice :
        Continuous (fun t : Et =>
          ((fderiv ℝ
              (nPointSpatialTimeSchwartzRealProd (d := d) (n := n) f : Eη × Et → ℝ × ℝ)
              (η, t)).comp
            (ContinuousLinearMap.inr ℝ Eη Et))) := by
      exact hcont_fderiv.clm_comp continuous_const
    simpa [F, partialFourierSpatial_timeDerivativeRealProd] using
      (continuous_const.clm_comp hcont_slice)
  exact MeasureTheory.continuous_of_dominated hF_meas h_bound h_bound_int h_cont

theorem contDiff_partialFourierSpatial_fun_time_realProd_one
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ContDiff ℝ 1 (fun s : Fin n → ℝ =>
      Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) f (s, ξ))) := by
  refine (contDiff_one_iff_fderiv).2 ?_
  refine ⟨?_, ?_⟩
  · intro t
    exact (hasFDerivAt_partialFourierSpatial_fun_time_realProd (d := d) (n := n) f ξ t).differentiableAt
  · have hcont :
        Continuous (fun t : Fin n → ℝ =>
          ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
            partialFourierSpatial_timeDerivativeRealProd d n f ξ η t) :=
      continuous_partialFourierSpatial_fun_timeFDeriv_realProd (d := d) (n := n) f ξ
    have hfderiv :
        fderiv ℝ
            (fun s : Fin n → ℝ =>
              Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) f (s, ξ))) =
          fun t : Fin n → ℝ =>
            ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
              partialFourierSpatial_timeDerivativeRealProd d n f ξ η t := by
      funext t
      exact (hasFDerivAt_partialFourierSpatial_fun_time_realProd (d := d) (n := n) f ξ t).fderiv
    rw [hfderiv]
    exact hcont

theorem lineDeriv_partialFourierSpatial_fun_time_realProd_eq_transport
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (t m : Fin n → ℝ) :
    lineDeriv ℝ
      (fun s : Fin n → ℝ =>
        Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) f (s, ξ)))
      t m =
    Complex.equivRealProdCLM
      (partialFourierSpatial_fun (d := d) (n := n)
        ((nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
          (LineDeriv.lineDerivOp ((0 : EuclideanSpace ℝ (Fin n × Fin d)), m)
            (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
        (t, ξ)) := by
  let g : SchwartzNPoint d n :=
    ((nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
      (LineDeriv.lineDerivOp ((0 : EuclideanSpace ℝ (Fin n × Fin d)), m)
        (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
  calc
    lineDeriv ℝ
        (fun s : Fin n → ℝ =>
          Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) f (s, ξ)))
        t m
        = (fderiv ℝ
            (fun s : Fin n → ℝ =>
              Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) f (s, ξ)))
            t) m := by
              exact
                (hasFDerivAt_partialFourierSpatial_fun_time_realProd
                  (d := d) (n := n) f ξ t).differentiableAt.lineDeriv_eq_fderiv
    _ = (∫ η : EuclideanSpace ℝ (Fin n × Fin d),
          partialFourierSpatial_timeDerivativeRealProd d n f ξ η t) m := by
            rw [(hasFDerivAt_partialFourierSpatial_fun_time_realProd
              (d := d) (n := n) f ξ t).fderiv]
    _ = ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
          partialFourierSpatial_timeDerivativeRealProd d n f ξ η t m := by
            simpa using
              (ContinuousLinearMap.integral_apply
                (φ_int := integrable_partialFourierSpatial_timeDerivativeRealProd
                  (d := d) (n := n) f ξ t)
                m)
    _ = Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) g (t, ξ)) := by
          have hpoint :
              ∀ η : EuclideanSpace ℝ (Fin n × Fin d),
                partialFourierSpatial_timeDerivativeRealProd d n f ξ η t m =
                  Complex.equivRealProdCLM
                    (𝐞 (-(inner ℝ η ξ)) •
                      (LineDeriv.lineDerivOp ((0 : EuclideanSpace ℝ (Fin n × Fin d)), m)
                        (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)) (η, t)) := by
            intro η
            have hreal :=
              hasFDerivAt_partialFourierSpatial_integrand_time_realProd
                (d := d) (n := n) f ξ η t
            have hcomplex :=
              (Complex.equivRealProdCLM.toContinuousLinearMap).hasFDerivAt.comp t
                (hasFDerivAt_partialFourierSpatial_integrand_time
                  (d := d) (n := n) f ξ η t)
            have hderiv_eq :
                partialFourierSpatial_timeDerivativeRealProd d n f ξ η t =
                  (Complex.equivRealProdCLM.toContinuousLinearMap).comp
                    (𝐞 (-(inner ℝ η ξ)) •
                      ((fderiv ℝ
                          (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f :
                            EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) → ℂ)
                          (η, t)).comp
                        (ContinuousLinearMap.inr ℝ
                          (EuclideanSpace ℝ (Fin n × Fin d)) (Fin n → ℝ)))) := by
              exact hreal.unique hcomplex
            let D :
                (Fin n → ℝ) →L[ℝ] (ℝ × ℝ) :=
              (Complex.equivRealProdCLM.toContinuousLinearMap).comp
                (𝐞 (-(inner ℝ η ξ)) •
                  ((fderiv ℝ
                      (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f :
                        EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) → ℂ)
                      (η, t)).comp
                    (ContinuousLinearMap.inr ℝ
                      (EuclideanSpace ℝ (Fin n × Fin d)) (Fin n → ℝ))))
            have hinr_apply :
                ((fderiv ℝ
                    (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f :
                      EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) → ℂ)
                    (η, t)).comp
                  (ContinuousLinearMap.inr ℝ
                    (EuclideanSpace ℝ (Fin n × Fin d)) (Fin n → ℝ))) m =
                  (fderiv ℝ
                    (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f :
                      EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) → ℂ)
                    (η, t)) (0, m) := by
              simp [ContinuousLinearMap.comp_apply]
            calc
              partialFourierSpatial_timeDerivativeRealProd d n f ξ η t m
                  = D m := by
                      simpa [D] using congrArg (fun L => L m) hderiv_eq
              _ = Complex.equivRealProdCLM
                    (𝐞 (-(inner ℝ η ξ)) •
                      ((LineDeriv.lineDerivOp ((0 : EuclideanSpace ℝ (Fin n × Fin d)), m)
                          (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)) (η, t))) := by
                    rw [show D m =
                        Complex.equivRealProdCLM
                          (𝐞 (-(inner ℝ η ξ)) •
                            ((fderiv ℝ
                                (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f :
                                  EuclideanSpace ℝ (Fin n × Fin d) × (Fin n → ℝ) → ℂ)
                                (η, t)).comp
                              (ContinuousLinearMap.inr ℝ
                                (EuclideanSpace ℝ (Fin n × Fin d)) (Fin n → ℝ))) m) by
                          rfl]
                    rw [hinr_apply]
                    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
                    rfl
          have hcongr :
              ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
                  partialFourierSpatial_timeDerivativeRealProd d n f ξ η t m
                =
              ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
                Complex.equivRealProdCLM
                  (𝐞 (-(inner ℝ η ξ)) •
                    (LineDeriv.lineDerivOp ((0 : EuclideanSpace ℝ (Fin n × Fin d)), m)
                      (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)) (η, t)) := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall hpoint
          symm
          calc
            Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) g (t, ξ))
                =
              ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
                Complex.equivRealProdCLM
                  (𝐞 (-(inner ℝ η ξ)) •
                    (LineDeriv.lineDerivOp ((0 : EuclideanSpace ℝ (Fin n × Fin d)), m)
                      (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)) (η, t)) := by
                        simpa [g, nPointSpatialTimeSchwartzCLE_apply] using
                          partialFourierSpatial_fun_eq_integral_realProd
                            (d := d) (n := n) g (t, ξ)
            _ =
              ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
                partialFourierSpatial_timeDerivativeRealProd d n f ξ η t m := by
                  rw [← hcongr]

theorem lineDeriv_partialFourierSpatial_fun_time_eq_transport
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (t m : Fin n → ℝ) :
    lineDeriv ℝ
      (fun s : Fin n → ℝ =>
        partialFourierSpatial_fun (d := d) (n := n) f (s, ξ))
      t m =
    partialFourierSpatial_fun (d := d) (n := n)
      ((nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
        (LineDeriv.lineDerivOp ((0 : EuclideanSpace ℝ (Fin n × Fin d)), m)
          (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
      (t, ξ) := by
  let g : SchwartzNPoint d n :=
    (nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
      (LineDeriv.lineDerivOp ((0 : EuclideanSpace ℝ (Fin n × Fin d)), m)
        (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f))
  have hreal :
      HasLineDerivAt ℝ
        (fun s : Fin n → ℝ =>
          Complex.equivRealProdCLM
            (partialFourierSpatial_fun (d := d) (n := n) f (s, ξ)))
        (Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) g (t, ξ)))
        t m := by
    convert
      (((hasFDerivAt_partialFourierSpatial_fun_time_realProd
          (d := d) (n := n) f ξ t).differentiableAt.lineDifferentiableAt).hasLineDerivAt)
      using 1
    simpa [g] using
      (lineDeriv_partialFourierSpatial_fun_time_realProd_eq_transport
        (d := d) (n := n) f ξ t m).symm
  have hcomplex :
      HasLineDerivAt ℝ
        (fun s : Fin n → ℝ =>
          partialFourierSpatial_fun (d := d) (n := n) f (s, ξ))
        (partialFourierSpatial_fun (d := d) (n := n) g (t, ξ))
        t m := by
    simp only [HasLineDerivAt] at hreal ⊢
    exact
      (Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) hreal)
  simpa [g] using hcomplex.lineDeriv

theorem differentiableAt_partialFourierSpatial_fun_time
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (t : Fin n → ℝ) :
    DifferentiableAt ℝ
      (fun s : Fin n → ℝ => partialFourierSpatial_fun (d := d) (n := n) f (s, ξ))
      t := by
  let F : (Fin n → ℝ) → ℝ × ℝ := fun s =>
    Complex.equivRealProdCLM (partialFourierSpatial_fun (d := d) (n := n) f (s, ξ))
  have hF : DifferentiableAt ℝ F t :=
    (hasFDerivAt_partialFourierSpatial_fun_time_realProd
      (d := d) (n := n) f ξ t).differentiableAt
  have hcomp :
      DifferentiableAt ℝ
        (fun s : Fin n → ℝ =>
          Complex.equivRealProdCLM.symm (F s))
        t := by
    exact (Complex.equivRealProdCLM.symm.toContinuousLinearMap.differentiableAt).comp t hF
  simpa [F] using hcomp

theorem fderiv_partialFourierSpatial_fun_time_apply_eq_transport
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (t m : Fin n → ℝ) :
    fderiv ℝ
      (fun s : Fin n → ℝ => partialFourierSpatial_fun (d := d) (n := n) f (s, ξ))
      t m =
    partialFourierSpatial_fun (d := d) (n := n)
      ((nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
        (LineDeriv.lineDerivOp ((0 : EuclideanSpace ℝ (Fin n × Fin d)), m)
          (nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
      (t, ξ) := by
  simpa [(differentiableAt_partialFourierSpatial_fun_time
    (d := d) (n := n) f ξ t).lineDeriv_eq_fderiv] using
    lineDeriv_partialFourierSpatial_fun_time_eq_transport
      (d := d) (n := n) f ξ t m

end OSReconstruction
