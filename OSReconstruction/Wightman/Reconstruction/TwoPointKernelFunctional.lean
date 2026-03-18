import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.CenterSpatialTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.TwoPointDescent
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms

noncomputable section

open scoped Topology
open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The spacetime vector with zero time component and prescribed spatial part. -/
def centerSpatialVec (a : Fin d → ℝ) : SpacetimeDim d :=
  Fin.cases 0 a

@[simp] theorem centerSpatialVec_time (a : Fin d → ℝ) :
    centerSpatialVec (d := d) a 0 = 0 := by
  simp [centerSpatialVec]

@[simp] theorem centerSpatialVec_space (a : Fin d → ℝ) (i : Fin d) :
    centerSpatialVec (d := d) a i.succ = a i := by
  simp [centerSpatialVec]

/-- Translate only the center-spatial part of a two-point center/difference
configuration `(u, ξ)`. -/
def twoPointCenterSpatialTranslate (a : Fin d → ℝ) :
    NPointDomain d 2 → NPointDomain d 2 :=
  fun z i =>
    Fin.cases (z 0 + centerSpatialVec (d := d) a)
      (fun _ => z 1) i

@[simp] theorem twoPointCenterSpatialTranslate_zero
    (a : Fin d → ℝ) (z : NPointDomain d 2) :
    twoPointCenterSpatialTranslate (d := d) a z 0 =
      z 0 + centerSpatialVec (d := d) a := by
  simp [twoPointCenterSpatialTranslate]

@[simp] theorem twoPointCenterSpatialTranslate_one
    (a : Fin d → ℝ) (z : NPointDomain d 2) :
    twoPointCenterSpatialTranslate (d := d) a z 1 = z 1 := by
  change Fin.cases (z 0 + centerSpatialVec (d := d) a)
      (fun _ => z 1) (Fin.succ 0) = z 1
  rfl

private def twoPointCenterSpatialTranslate_measurableEquiv
    (a : Fin d → ℝ) :
    NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
  let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
    MeasurableEquiv.finTwoArrow
  let etrans : SpacetimeDim d ≃ᵐ SpacetimeDim d :=
    (Homeomorph.addRight (centerSpatialVec (d := d) a)).toMeasurableEquiv
  eprod.trans ((MeasurableEquiv.prodCongr etrans (MeasurableEquiv.refl _)).trans eprod.symm)

@[simp] private theorem twoPointCenterSpatialTranslate_measurableEquiv_apply
    (a : Fin d → ℝ) (z : NPointDomain d 2) :
    twoPointCenterSpatialTranslate_measurableEquiv (d := d) a z =
      twoPointCenterSpatialTranslate (d := d) a z := by
  ext i μ
  fin_cases i
  · simp [twoPointCenterSpatialTranslate_measurableEquiv, twoPointCenterSpatialTranslate,
      centerSpatialVec, MeasurableEquiv.prodCongr]
  · change z 1 μ = z 1 μ
    rfl

private theorem twoPointCenterSpatialTranslate_measurePreserving
    (a : Fin d → ℝ) :
    MeasureTheory.MeasurePreserving
      (twoPointCenterSpatialTranslate_measurableEquiv (d := d) a)
      MeasureTheory.volume MeasureTheory.volume := by
  let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
    MeasurableEquiv.finTwoArrow
  have heprod :
      MeasureTheory.MeasurePreserving eprod
        MeasureTheory.volume MeasureTheory.volume := by
    simpa [eprod] using
      (MeasureTheory.volume_preserving_finTwoArrow (SpacetimeDim d))
  have hprod :
      MeasureTheory.MeasurePreserving
        (Prod.map (fun x : SpacetimeDim d => x + centerSpatialVec (d := d) a) id)
        MeasureTheory.volume MeasureTheory.volume :=
    (translate_spacetime_measurePreserving (d := d) (centerSpatialVec (d := d) a)).prod
      (MeasureTheory.MeasurePreserving.id
        (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
  simpa [twoPointCenterSpatialTranslate_measurableEquiv]
    using heprod.symm.comp (hprod.comp heprod)

@[simp] private theorem centerSpatialShift_castAdd_zero
    (a : Fin d → ℝ) :
    centerSpatialShift d a (Fin.castAdd (d + 1) (0 : Fin (d + 1))) = 0 := by
  have htail :
      splitLast d (d + 2) (zeroTailBlockShift (m := d) (n := d + 2) a) = 0 := by
    simpa using splitLast_zeroTailBlockShift_eq_zero (m := d) (n := d + 2) a
  have := congrArg (fun v : Fin (d + 2) → ℝ => v 0) htail
  simpa [OSReconstruction.centerSpatialShift,
    OSReconstruction.centerSpatialFirstPerm_symm_castAdd_zero, splitLast] using this

@[simp] private theorem centerSpatialShift_castAdd_succ
    (a : Fin d → ℝ) (i : Fin d) :
    centerSpatialShift d a (Fin.castAdd (d + 1) i.succ) = a i := by
  have hhead :
      splitFirst d (d + 2) (zeroTailBlockShift (m := d) (n := d + 2) a) = a := by
    simpa using splitFirst_zeroTailBlockShift_eq (m := d) (n := d + 2) a
  have := congrArg (fun v : Fin d → ℝ => v i) hhead
  simpa [OSReconstruction.centerSpatialShift,
    OSReconstruction.centerSpatialFirstPerm_symm_castAdd_succ, splitFirst] using this

@[simp] private theorem centerSpatialShift_natAdd
    (a : Fin d → ℝ) (i : Fin (d + 1)) :
    centerSpatialShift d a (Fin.natAdd (d + 1) i) = 0 := by
  have htail :
      splitLast d (d + 2) (zeroTailBlockShift (m := d) (n := d + 2) a) = 0 := by
    simpa using splitLast_zeroTailBlockShift_eq_zero (m := d) (n := d + 2) a
  have := congrArg (fun v : Fin (d + 2) → ℝ => v i.succ) htail
  rw [OSReconstruction.centerSpatialShift,
    OSReconstruction.centerSpatialFirstPerm_symm_natAdd]
  simpa [splitLast] using this

private theorem centerSpatialShift_eq_addCases
    (a : Fin d → ℝ) :
    centerSpatialShift d a =
      Fin.addCases (centerSpatialVec (d := d) a) (fun _ : Fin (d + 1) => 0) := by
  funext i
  cases i using Fin.addCases with
  | left i =>
      cases i using Fin.cases with
      | zero =>
          rw [Fin.addCases_left]
          simpa using centerSpatialShift_castAdd_zero (d := d) a
      | succ j =>
          rw [Fin.addCases_left]
          simpa using centerSpatialShift_castAdd_succ (d := d) a j
  | right i =>
      rw [Fin.addCases_right]
      exact centerSpatialShift_natAdd (d := d) a i

/-- A polynomial-growth kernel on `NPointDomain d 2` induces a continuous scalar
Schwartz functional on the flattened two-point real coordinate space. -/
def twoPointFlatKernelCLM
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ := by
  let A : SchwartzNPoint d 2 →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := fun f => ∫ x : NPointDomain d 2, K x * f x
          map_add' := by
            intro f g
            simp only [SchwartzMap.add_apply, mul_add]
            exact integral_add
              (schwartz_polynomial_kernel_integrable K hK_meas C_bd N hC hK_bound f)
              (schwartz_polynomial_kernel_integrable K hK_meas C_bd N hC hK_bound g)
          map_smul' := by
            intro a f
            simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
            simp_rw [show ∀ x : NPointDomain d 2, K x * (a * f x) = a * (K x * f x) by
              intro x
              ring]
            exact integral_const_mul a _ }
      cont := schwartz_polynomial_kernel_continuous K hK_meas C_bd N hC hK_bound }
  let e : 2 * (d + 1) = (d + 1) + (d + 1) := by ring
  let B : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] SchwartzNPoint d 2 :=
    (unflattenSchwartzNPoint (d := d)).comp (reindexSchwartzFin e.symm)
  exact A.comp B

/-- The inclusion of the zero-diagonal two-point Schwartz space into the full
two-point Schwartz space. -/
def zeroDiagonalTwoPointValCLM :
    ZeroDiagonalSchwartz d 2 →L[ℂ] SchwartzNPoint d 2 where
  toLinearMap := (zeroDiagonalSubmodule d 2).subtype
  cont := continuous_subtype_val

@[simp] theorem zeroDiagonalTwoPointValCLM_apply
    (f : ZeroDiagonalSchwartz d 2) :
    zeroDiagonalTwoPointValCLM (d := d) f = f.1 := rfl

/-- A polynomial-growth kernel on `NPointDomain d 2` induces a continuous
linear functional on the zero-diagonal two-point Schwartz space. -/
def twoPointZeroDiagonalKernelCLM
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    ZeroDiagonalSchwartz d 2 →L[ℂ] ℂ :=
  (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound).comp
    ((reindexSchwartzFin (by ring)).comp
      ((flattenSchwartzNPoint (d := d)).comp
        (zeroDiagonalTwoPointValCLM (d := d))))

theorem twoPointFlatKernelCLM_apply_reindex_flatten
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (F : SchwartzNPoint d 2) :
    twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring) (flattenSchwartzNPoint (d := d) F)) =
      ∫ x : NPointDomain d 2, K x * F x := by
  let e : 2 * (d + 1) = (d + 1) + (d + 1) := by ring
  have hreindex :
      reindexSchwartzFin e.symm
          (reindexSchwartzFin e (flattenSchwartzNPoint (d := d) F)) =
        flattenSchwartzNPoint (d := d) F := by
    ext y
    change
      flattenSchwartzNPoint (d := d) F
          (((castFinCLE e).symm) (((castFinCLE e).symm.symm) y)) =
        flattenSchwartzNPoint (d := d) F y
    simpa using
      congrArg (flattenSchwartzNPoint (d := d) F) ((castFinCLE e).symm_apply_apply y)
  have hunflat_flat :
      unflattenSchwartzNPoint (d := d) (flattenSchwartzNPoint (d := d) F) = F := by
    ext x
    simp
  simp [twoPointFlatKernelCLM, hreindex, hunflat_flat]

private def twoPointRealFlatten (z : NPointDomain d 2) :
    Fin ((d + 1) + (d + 1)) → ℝ :=
  Fin.addCases (z 0) (z 1)

@[simp] private theorem splitFirst_twoPointRealFlatten
    (z : NPointDomain d 2) :
    splitFirst (d + 1) (d + 1) (twoPointRealFlatten (d := d) z) = z 0 := by
  ext μ
  simp [twoPointRealFlatten, splitFirst]

@[simp] private theorem splitLast_twoPointRealFlatten
    (z : NPointDomain d 2) :
    splitLast (d + 1) (d + 1) (twoPointRealFlatten (d := d) z) = z 1 := by
  ext μ
  rw [splitLast, twoPointRealFlatten]
  simpa using (Fin.append_right (z 0) (z 1) μ)

private theorem unflatten_reindex_twoPoint_apply
    (F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ)
    (z : NPointDomain d 2) :
    F (twoPointRealFlatten (d := d) z) =
      unflattenSchwartzNPoint (d := d)
        (reindexSchwartzFin (show (d + 1) + (d + 1) = 2 * (d + 1) by ring) F) z := by
  let e : (d + 1) + (d + 1) = 2 * (d + 1) := by ring
  let H : SchwartzNPoint d 2 :=
    unflattenSchwartzNPoint (d := d) (reindexSchwartzFin e F)
  have hflatten : reindexSchwartzFin e.symm (flattenSchwartzNPoint (d := d) H) = F := by
    ext x
    change reindexSchwartzFin e.symm
        (flattenSchwartzNPoint (d := d)
          (unflattenSchwartzNPoint (d := d) (reindexSchwartzFin e F))) x = F x
    rw [reindexSchwartzFin_apply, flattenSchwartzNPoint_apply, unflattenSchwartzNPoint_apply,
      reindexSchwartzFin_apply]
    congr 1
    ext i
    simp
  have happly :=
    reindex_flattenSchwartzNPoint_two_apply (d := d) H (twoPointRealFlatten (d := d) z)
  rw [hflatten] at happly
  have hz :
      (fun i =>
        Fin.cases
          (splitFirst (d + 1) (d + 1) (twoPointRealFlatten (d := d) z))
          (fun _ => splitLast (d + 1) (d + 1) (twoPointRealFlatten (d := d) z)) i) = z := by
    ext i μ
    fin_cases i
    · simpa using congrArg (fun v : SpacetimeDim d => v μ)
          (splitFirst_twoPointRealFlatten (d := d) z)
    · change splitLast (d + 1) (d + 1) (twoPointRealFlatten (d := d) z) μ = z 1 μ
      simpa using congrArg (fun v : SpacetimeDim d => v μ)
        (splitLast_twoPointRealFlatten (d := d) z)
  calc
    F (twoPointRealFlatten (d := d) z)
      = H
          (fun i =>
            Fin.cases
              (splitFirst (d + 1) (d + 1) (twoPointRealFlatten (d := d) z))
              (fun _ => splitLast (d + 1) (d + 1) (twoPointRealFlatten (d := d) z)) i) := by
            simpa using happly
    _ = H z := by rw [hz]

private theorem twoPointRealFlatten_centerSpatialTranslate
    (a : Fin d → ℝ) (z : NPointDomain d 2) :
    twoPointRealFlatten (d := d) (twoPointCenterSpatialTranslate (d := d) a z) =
      twoPointRealFlatten (d := d) z + centerSpatialShift d a := by
  ext p
  cases p using Fin.addCases with
  | left μ =>
      cases μ using Fin.cases with
      | zero =>
          simp [twoPointRealFlatten, twoPointCenterSpatialTranslate, centerSpatialShift_eq_addCases,
            centerSpatialVec]
      | succ j =>
          simp [twoPointRealFlatten, twoPointCenterSpatialTranslate, centerSpatialShift_eq_addCases,
            centerSpatialVec]
  | right μ =>
      calc
        Fin.addCases (z 0 + centerSpatialVec (d := d) a) (z 1) (Fin.natAdd (d + 1) μ)
          = z 1 μ := by
              simpa using
                (Fin.append_right (z 0 + centerSpatialVec (d := d) a) (z 1) μ)
        _ = (twoPointRealFlatten (d := d) z + centerSpatialShift d a) (Fin.natAdd (d + 1) μ) := by
              calc
                z 1 μ = z 1 μ + 0 := by simp
                _ = Fin.addCases (z 0) (z 1) (Fin.natAdd (d + 1) μ) +
                      Fin.addCases (centerSpatialVec (d := d) a) (fun _ : Fin (d + 1) => 0)
                        (Fin.natAdd (d + 1) μ) := by
                      congr
                      · symm
                        simpa using (Fin.append_right (z 0) (z 1) μ)
                      · symm
                        simpa using
                          (Fin.append_right (centerSpatialVec (d := d) a)
                            (fun _ : Fin (d + 1) => (0 : ℝ)) μ)
                _ = (twoPointRealFlatten (d := d) z + centerSpatialShift d a) (Fin.natAdd (d + 1) μ) := by
                      simp [twoPointRealFlatten, centerSpatialShift_eq_addCases]

@[simp] private theorem unflatten_reindex_translate_centerSpatialShift_apply
    (a : Fin d → ℝ)
    (F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ)
    (z : NPointDomain d 2) :
    unflattenSchwartzNPoint (d := d)
        (reindexSchwartzFin (show (d + 1) + (d + 1) = 2 * (d + 1) by ring)
          (SCV.translateSchwartz (centerSpatialShift d a) F)) z =
      unflattenSchwartzNPoint (d := d)
        (reindexSchwartzFin (show (d + 1) + (d + 1) = 2 * (d + 1) by ring) F)
          (twoPointCenterSpatialTranslate (d := d) a z) := by
  rw [← unflatten_reindex_twoPoint_apply, ← unflatten_reindex_twoPoint_apply]
  simp [SCV.translateSchwartz_apply, twoPointRealFlatten_centerSpatialTranslate]

/-- Pointwise invariance of a two-point kernel under center-spatial
translations lifts to center-spatial translation invariance of the induced
flattened Schwartz functional. -/
theorem twoPointFlatKernelCLM_centerSpatialInvariant
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hK_inv : ∀ (a : Fin d → ℝ) (z : NPointDomain d 2),
      K (twoPointCenterSpatialTranslate (d := d) a z) = K z) :
    OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d
      (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) := by
  intro a
  ext F
  let eflat : (d + 1) + (d + 1) = 2 * (d + 1) := by ring
  let H : SchwartzNPoint d 2 :=
    unflattenSchwartzNPoint (d := d) (reindexSchwartzFin eflat F)
  let e : NPointDomain d 2 ≃ᵐ NPointDomain d 2 :=
    twoPointCenterSpatialTranslate_measurableEquiv (d := d) a
  have hmp : MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
    twoPointCenterSpatialTranslate_measurePreserving (d := d) a
  calc
    twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
        (SCV.translateSchwartzCLM (centerSpatialShift d a) F)
      = ∫ z : NPointDomain d 2,
          K z *
            unflattenSchwartzNPoint (d := d)
              (reindexSchwartzFin eflat
                (SCV.translateSchwartz (centerSpatialShift d a) F)) z := by
            simp [twoPointFlatKernelCLM]
    _ = ∫ z : NPointDomain d 2,
          K z * H (twoPointCenterSpatialTranslate (d := d) a z) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            rw [unflatten_reindex_translate_centerSpatialShift_apply]
    _ = ∫ z : NPointDomain d 2,
          (fun x : NPointDomain d 2 => K x * H x) (e z) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            simp [e, hK_inv a z, H]
    _ = ∫ z : NPointDomain d 2, K z * H z := by
            exact hmp.integral_comp'
              (f := e) (g := fun x : NPointDomain d 2 => K x * H x)
    _ = twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound F := by
            simp [twoPointFlatKernelCLM, H]

theorem twoPointZeroDiagonalKernelCLM_apply
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (f : ZeroDiagonalSchwartz d 2) :
    twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound f =
      ∫ x : NPointDomain d 2, K x * (f.1 x) := by
  simpa [twoPointZeroDiagonalKernelCLM] using
    twoPointFlatKernelCLM_apply_reindex_flatten
      (d := d) (K := K) hK_meas C_bd N hC hK_bound f.1

/-- A uniform `ae` bound is a special case of the polynomial-growth bound
required by `twoPointZeroDiagonalKernelCLM`. -/
theorem ae_const_bound_to_poly_bound
    (K : NPointDomain d 2 → ℂ)
    (C : ℝ)
    (hK_bdd : ∀ᵐ x : NPointDomain d 2 ∂volume, ‖K x‖ ≤ C) :
    ∀ᵐ x : NPointDomain d 2 ∂volume, ‖K x‖ ≤ (|C| + 1) * (1 + ‖x‖) ^ (0 : ℕ) := by
  filter_upwards [hK_bdd] with x hx
  have hC : C ≤ |C| + 1 := by
    have : C ≤ |C| := le_abs_self C
    linarith
  have hpow : (1 + ‖x‖) ^ (0 : ℕ) = (1 : ℝ) := by simp
  rw [hpow]
  simpa using le_trans hx hC

/-- A measurable, uniformly `ae` bounded two-point kernel induces a continuous
linear functional on `ZeroDiagonalSchwartz d 2`. -/
noncomputable def zeroDiagKernelCLM_of_const_bound
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C : ℝ)
    (hK_bdd : ∀ᵐ x : NPointDomain d 2 ∂volume, ‖K x‖ ≤ C) :
    ZeroDiagonalSchwartz d 2 →L[ℂ] ℂ :=
  twoPointZeroDiagonalKernelCLM (d := d) K hK_meas (|C| + 1) 0
    (by positivity)
    (ae_const_bound_to_poly_bound (d := d) K C hK_bdd)

/-- The induced constant-bound kernel CLM evaluates by the expected Euclidean
integral formula. -/
theorem zeroDiagKernelCLM_of_const_bound_apply
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C : ℝ)
    (hK_bdd : ∀ᵐ x : NPointDomain d 2 ∂volume, ‖K x‖ ≤ C)
    (f : ZeroDiagonalSchwartz d 2) :
    zeroDiagKernelCLM_of_const_bound (d := d) K hK_meas C hK_bdd f =
      ∫ x : NPointDomain d 2, K x * (f.1 x) := by
  simpa [zeroDiagKernelCLM_of_const_bound] using
    twoPointZeroDiagonalKernelCLM_apply (d := d) K hK_meas (|C| + 1) 0
      (by positivity)
      (ae_const_bound_to_poly_bound (d := d) K C hK_bdd) f

/-- If a measurable, uniformly `ae` bounded two-point kernel agrees with
`OS.S 2` on a dense family of positive-time difference shells, then the induced
zero-diagonal kernel CLM is exactly the Schwinger CLM. -/
theorem zeroDiagKernelCLM_of_const_bound_eq_schwinger_of_shell_agreement
    (OS : OsterwalderSchraderAxioms d)
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C : ℝ)
    (hK_bdd : ∀ᵐ x : NPointDomain d 2 ∂volume, ‖K x‖ ≤ C)
    (hShell : ∀ χ h : SchwartzSpacetime d,
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} →
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
        ∫ x : NPointDomain d 2, K x * (twoPointDifferenceLift χ h x) =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)))
    (hDense : Dense {f : ZeroDiagonalSchwartz d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} ∧
        HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
        f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}) :
    zeroDiagKernelCLM_of_const_bound (d := d) K hK_meas C hK_bdd =
      OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2 := by
  apply ContinuousLinearMap.eq_of_eq_on_dense
    (zeroDiagKernelCLM_of_const_bound (d := d) K hK_meas C hK_bdd)
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2)
    hDense
  intro f hf
  rcases hf with ⟨χ, h, hh_pos, hh_compact, rfl⟩
  have hzero_not_mem : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
    intro hmem
    have := hh_pos hmem
    simpa using this
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h) :=
    twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ h hzero_not_mem
  rw [zeroDiagKernelCLM_of_const_bound_apply (d := d) K hK_meas C hK_bdd
      (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))]
  rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := twoPointDifferenceLift χ h) hvanish]
  exact hShell χ h hh_pos hh_compact

/-- Evaluate a flat witness kernel on a two-point center/difference
configuration after fixing the time-difference coordinate by `t`. -/
def twoPointFixedTimeKernel
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ) : NPointDomain d 2 → ℂ :=
  fun z =>
    G (Function.update
      (BHW.flattenCfg 2 d (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)))
      (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
      (BHW.flattenCfg 2 d (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
        (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + t))

theorem twoPointFixedTimeKernelCLM_apply_productLift
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hK_meas : AEStronglyMeasurable (twoPointFixedTimeKernel (d := d) G t) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (χ g : SchwartzSpacetime d) :
    twoPointFlatKernelCLM (d := d) (twoPointFixedTimeKernel (d := d) G t)
        hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeKernel (d := d) G t z * (χ (z 0) * g (z 0 + z 1)) := by
  simpa [twoPointFixedTimeKernel] using
    twoPointFlatKernelCLM_apply_reindex_flatten
      (d := d) (K := twoPointFixedTimeKernel (d := d) G t)
      hK_meas C_bd N hC hK_bound
      (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g))

theorem twoPointFixedTimeKernelCLM_apply_differenceLift
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hK_meas : AEStronglyMeasurable (twoPointFixedTimeKernel (d := d) G t) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (χ : SchwartzSpacetime d) (h : SchwartzSpacetime d) :
    twoPointFlatKernelCLM (d := d) (twoPointFixedTimeKernel (d := d) G t)
        hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeKernel (d := d) G t z * (χ (z 0) * h (z 1)) := by
  simpa [twoPointFixedTimeKernel] using
    twoPointFlatKernelCLM_apply_reindex_flatten
      (d := d) (K := twoPointFixedTimeKernel (d := d) G t)
      hK_meas C_bd N hC hK_bound
      (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h))

/-! ### Schwinger difference distribution

The Schwinger 2-point function, restricted to difference coordinates via
translation invariance, defines a functional `T_diff(h) = OS.S 2(χ₀ ⊗ h)`.
By `twoPointDifferenceLift_eq_centerValue`, this is independent of χ₀ (up to
normalization) and captures the full Schwinger 2-point function in difference
coordinates.

The kernel representation of T_diff (identifying it as integration against a
locally integrable kernel) requires the spectral theory of the Hamiltonian
(Källén-Lehmann representation). This is the same infrastructure needed for
`spectrum_condition` and `vacuum_unique` in GNSHilbertSpace. -/

/-- The Schwinger difference-coordinate pairing at a single test function `h`:
for fixed normalized center cutoff χ₀ (with ∫ χ₀ = 1), this is the scalar
`OS.S 2 (twoPointDifferenceLift χ₀ h)` for zero-origin-avoiding `h`.

By `twoPointDifferenceLift_eq_centerValue`, this is independent of χ₀ (up to
normalization) and captures the full Schwinger 2-point function in difference
coordinates. -/
noncomputable def schwingerDifferenceFunctional
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (_hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (h : SchwartzSpacetime d)
    (_h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) : ℂ :=
  OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h))

/-- The Schwinger difference functional reproduces OS.S 2 on product tests:
`OS.S 2 (χ ⊗ h) = schwingerDifferenceFunctional(h) * ∫ χ`. -/
theorem schwingerDifferenceFunctional_reproduces
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ : SchwartzSpacetime d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      schwingerDifferenceFunctional OS χ₀ hχ₀ h h0 * ∫ x : SpacetimeDim d, χ x := by
  exact OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue
    (d := d) OS h h0 χ₀ hχ₀ χ

/-- A two-point Euclidean kernel depending only on the difference variable. -/
def twoPointDifferenceKernel
    (K : SpacetimeDim d → ℂ) : NPointDomain d 2 → ℂ :=
  fun x => K (x 1 - x 0)

/-- In center/difference coordinates, a kernel depending only on the difference
variable factors out of the center integral. -/
theorem integral_centerDiff_differenceOnly_kernel_factorizes
    (K : SpacetimeDim d → ℂ)
    (χ h : SchwartzSpacetime d) :
    ∫ z : NPointDomain d 2, K (z 1) * (χ (z 0) * h (z 1)) =
      (∫ u : SpacetimeDim d, χ u) * ∫ ξ : SpacetimeDim d, K ξ * h ξ := by
  let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
    MeasurableEquiv.finTwoArrow
  have heprod :
      MeasureTheory.MeasurePreserving eprod
        MeasureTheory.volume MeasureTheory.volume := by
    simpa [eprod] using
      (MeasureTheory.volume_preserving_finTwoArrow (SpacetimeDim d))
  calc
    ∫ z : NPointDomain d 2, K (z 1) * (χ (z 0) * h (z 1))
      = ∫ p : SpacetimeDim d × SpacetimeDim d,
          K p.2 * (χ p.1 * h p.2) := by
            symm
            simpa [eprod, MeasurableEquiv.finTwoArrow, mul_assoc] using
              heprod.symm.integral_comp'
                (g := fun z : NPointDomain d 2 => K (z 1) * (χ (z 0) * h (z 1)))
    _ = ∫ p : SpacetimeDim d × SpacetimeDim d,
          χ p.1 * (K p.2 * h p.2) := by
            refine integral_congr_ae ?_
            filter_upwards with p
            ring
    _ = (∫ u : SpacetimeDim d, χ u) * ∫ ξ : SpacetimeDim d, K ξ * h ξ := by
            simpa [mul_assoc] using
              (MeasureTheory.integral_prod_mul
                (μ := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
                (ν := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
                (f := fun u : SpacetimeDim d => χ u)
                (g := fun ξ : SpacetimeDim d => K ξ * h ξ))

/-- Pairing a difference-only kernel with an admissible two-point difference lift
reduces to the corresponding one-variable pairing in the difference coordinate. -/
theorem integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
    (K : SpacetimeDim d → ℂ)
    (χ h : SchwartzSpacetime d) :
    ∫ x : NPointDomain d 2,
      twoPointDifferenceKernel (d := d) K x * (twoPointDifferenceLift χ h x) =
        (∫ u : SpacetimeDim d, χ u) * ∫ ξ : SpacetimeDim d, K ξ * h ξ := by
  calc
    ∫ x : NPointDomain d 2,
        twoPointDifferenceKernel (d := d) K x * (twoPointDifferenceLift χ h x)
      = ∫ z : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K ((twoPointCenterDiffCLE d) z) *
            (χ (z 0) * h (z 1)) := by
          simpa [twoPointDifferenceKernel] using
            integral_mul_twoPointDifferenceLift_eq_centerDiff
              (d := d) (Ψ := twoPointDifferenceKernel (d := d) K) χ h
    _ = ∫ z : NPointDomain d 2, K (z 1) * (χ (z 0) * h (z 1)) := by
          refine integral_congr_ae ?_
          filter_upwards with z
          simp [twoPointDifferenceKernel, twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv]
    _ = (∫ u : SpacetimeDim d, χ u) * ∫ ξ : SpacetimeDim d, K ξ * h ξ := by
          exact integral_centerDiff_differenceOnly_kernel_factorizes (d := d) K χ h

/-- If a reduced one-variable pairing already reproduces the normalized
two-point Schwinger shell, then the corresponding difference-only two-point
kernel reproduces the full admissible difference shell. -/
theorem twoPointDifferenceKernel_eq_schwinger_on_differenceShell_of_reduced_pairing
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K : SpacetimeDim d → ℂ)
    (hK : ∀ h : SchwartzSpacetime d,
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} →
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
        ∫ ξ : SpacetimeDim d, K ξ * h ξ =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)))
    (χ h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∫ x : NPointDomain d 2,
      twoPointDifferenceKernel (d := d) K x * (twoPointDifferenceLift χ h x) =
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
  have hzero_not_mem : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
    intro hmem
    have := hh_pos hmem
    simpa using this
  calc
    ∫ x : NPointDomain d 2,
        twoPointDifferenceKernel (d := d) K x * (twoPointDifferenceLift χ h x)
      = (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d, K ξ * h ξ := by
            exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
              (d := d) K χ h
    _ = (∫ u : SpacetimeDim d, χ u) *
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
            rw [hK h hh_pos hh_compact]
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
          symm
          rw [OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue
            (d := d) (OS := OS) h hzero_not_mem χ₀ hχ₀ χ]
          ring

/-- Reduced-domain version of the previous shell theorem: once a difference
kernel reproduces the honest reduced Schwinger functional on the positive-time
compact-support test space, it reproduces the full admissible two-point
difference shell. -/
theorem twoPointDifferenceKernel_eq_schwinger_on_differenceShell_of_positiveCLM_pairing
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K : SpacetimeDim d → ℂ)
    (hK : ∀ h : positiveTimeCompactSupportSubmodule d,
      ∫ ξ : SpacetimeDim d, K ξ * (h : SchwartzSpacetime d) ξ =
        (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM (d := d) OS χ₀) h)
    (χ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ x : NPointDomain d 2,
      twoPointDifferenceKernel (d := d) K x *
        (twoPointDifferenceLift χ (h : SchwartzSpacetime d) x) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ (h : SchwartzSpacetime d))) := by
  refine twoPointDifferenceKernel_eq_schwinger_on_differenceShell_of_reduced_pairing
    (d := d) OS χ₀ hχ₀ K ?_ χ (h : SchwartzSpacetime d) h.property.1 h.property.2
  intro h' hh'_pos hh'_compact
  let hmem : positiveTimeCompactSupportSubmodule d :=
    ⟨h', hh'_pos, hh'_compact⟩
  simpa [hmem, OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM_apply]
    using hK hmem

/-- Continuous-linear packaging of the reduced-pairing route: once a
difference-only Euclidean kernel reproduces the normalized reduced pairing and
is measurable with a uniform `ae` bound, the induced zero-diagonal kernel CLM
is exactly the Schwinger two-point functional. -/
theorem zeroDiagKernelCLM_of_differenceKernel_eq_schwinger_of_reduced_pairing
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K : SpacetimeDim d → ℂ)
    (hK_meas : AEStronglyMeasurable (twoPointDifferenceKernel (d := d) K) volume)
    (C : ℝ)
    (hK_bdd : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointDifferenceKernel (d := d) K x‖ ≤ C)
    (hReduced : ∀ h : SchwartzSpacetime d,
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} →
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
        ∫ ξ : SpacetimeDim d, K ξ * h ξ =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)))
    (hDense : Dense {f : ZeroDiagonalSchwartz d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} ∧
        HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
        f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}) :
    zeroDiagKernelCLM_of_const_bound
        (d := d) (twoPointDifferenceKernel (d := d) K) hK_meas C hK_bdd =
      OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2 := by
  refine zeroDiagKernelCLM_of_const_bound_eq_schwinger_of_shell_agreement
    (d := d) OS (twoPointDifferenceKernel (d := d) K) hK_meas C hK_bdd ?_ hDense
  intro χ h hh_pos hh_compact
  exact twoPointDifferenceKernel_eq_schwinger_on_differenceShell_of_reduced_pairing
    (d := d) OS χ₀ hχ₀ K hReduced χ h hh_pos hh_compact

/-- Quotient-level two-point comparison principle. If a full flattened
functional and a concrete kernel CLM agree after center-spatial descent on
compactly supported reduced tests with positive head support, then the full
functional already has the expected product-shell and admissible
difference-shell formulas.

This is the production bridge from positive reduced-shell identities to full
two-point shell identities, using only compact-support density in the reduced
Schwartz space. -/
theorem map_productLift_and_differenceLift_of_eq_on_positive_compactSupport_centerTimeReduced
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hTK : IsCenterSpatialTranslationInvariantSchwartzCLM d
      (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound))
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ u : Fin d → ℝ, φ u = 1)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ s : ℝ, ψ s = 1)
    (hψ_compact : HasCompactSupport ψ)
    (hTred : IsHeadTranslationInvariantSchwartzCLM (centerSpatialDescentCLM d T φ))
    (hKred : IsHeadTranslationInvariantSchwartzCLM
      (centerSpatialDescentCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ))
    (hEq_pos : ∀ F : SchwartzMap (Fin (d + 2) → ℝ) ℂ,
      HasCompactSupport (F : (Fin (d + 2) → ℝ) → ℂ) →
      tsupport (F : (Fin (d + 2) → ℝ) → ℂ) ⊆ {x : Fin (d + 2) → ℝ | 0 < x 0} →
      centerSpatialDescentCLM d T φ F =
        centerSpatialDescentCLM d
          (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ F)
    (χ g h : SchwartzSpacetime d) :
    T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) =
        ∫ z : NPointDomain d 2, K z * (χ (z 0) * g (z 0 + z 1)) ∧
      T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1)) := by
  let U : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
  have hTU : T = U :=
    eq_of_eq_on_positive_compactSupport_centerTimeReduced
      d T U hT hTK φ hφ ψ hψ hψ_compact hTred hKred hEq_pos
  constructor
  · calc
      T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) =
          U (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) := by
                simpa [U] using congrArg
                  (fun L : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ =>
                    L (reindexSchwartzFin (by ring)
                      (flattenSchwartzNPoint (d := d)
                        (twoPointCenterDiffSchwartzCLM (d := d)
                          (twoPointProductLift χ g))))) hTU
      _ = ∫ z : NPointDomain d 2, K z * (χ (z 0) * g (z 0 + z 1)) := by
            simpa [U] using
              twoPointFlatKernelCLM_apply_reindex_flatten
                (d := d) (K := K) hK_meas C_bd N hC hK_bound
                (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g))
  · calc
      T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
          U (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) := by
                simpa [U] using congrArg
                  (fun L : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ =>
                    L (reindexSchwartzFin (by ring)
                      (flattenSchwartzNPoint (d := d)
                        (twoPointCenterDiffSchwartzCLM (d := d)
                          (twoPointDifferenceLift χ h))))) hTU
      _ = ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1)) := by
            simpa [U] using
              twoPointFlatKernelCLM_apply_reindex_flatten
                (d := d) (K := K) hK_meas C_bd N hC hK_bound
                (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h))


end OSReconstruction
