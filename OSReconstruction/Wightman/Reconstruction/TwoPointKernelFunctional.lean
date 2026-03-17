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

/-- Package the generic two-point kernel-functional route: once the kernel CLM
is center-spatial translation invariant and its descended reduced functional is
head-translation invariant, it produces the witness surface needed to compare
the product shell and the admissible difference shell. -/
theorem exists_twoPointFlatKernel_centerSpatialWitness
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (χ : SchwartzSpacetime d) (g h : SchwartzSpacetime d)
    (hT : OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d
      (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound))
    (φ : SchwartzMap (Fin d → ℝ) ℂ) (hφ : ∫ u : Fin d → ℝ, φ u = 1)
    (hTred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ))
    (ψ : SchwartzMap ℝ ℂ) (hψ : ∫ s : ℝ, ψ s = 1) :
    ∃ T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ,
      OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d T ∧
      ∃ φ : SchwartzMap (Fin d → ℝ) ℂ, (∫ u : Fin d → ℝ, φ u = 1) ∧
        OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
          (OSReconstruction.centerSpatialDescentCLM d T φ) ∧
        ∃ ψ : SchwartzMap ℝ ℂ, (∫ s : ℝ, ψ s = 1) ∧
          T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointProductLift χ g)))) =
            ∫ z : NPointDomain d 2, K z * (χ (z 0) * g (z 0 + z 1)) ∧
          T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ h)))) =
            ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1)) := by
  refine ⟨twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound, hT,
    φ, hφ, hTred, ψ, hψ, ?_, ?_⟩
  · simpa using
      twoPointFlatKernelCLM_apply_reindex_flatten
        (d := d) (K := K) hK_meas C_bd N hC hK_bound
        (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g))
  · simpa using
      twoPointFlatKernelCLM_apply_reindex_flatten
        (d := d) (K := K) hK_meas C_bd N hC hK_bound
        (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h))

/-- To identify an abstract full flattened two-point extension `T` with the
concrete kernel CLM induced by `K`, it is enough to prove equality after both
the center-spatial descent and the active head-time descent on a dense subset
of the reduced quotient space. This is the blocker-facing quotient version of
the kernel-functional route. -/
theorem eq_twoPointFlatKernelCLM_of_eq_on_dense_reduced
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hTK :
      OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound))
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ u : Fin d → ℝ, φ u = 1)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ s : ℝ, ψ s = 1)
    (hTred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d T φ))
    (hKred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ))
    {S : Set (SchwartzMap (Fin (d + 1) → ℝ) ℂ)}
    (hS : Dense S)
    (hEq : ∀ f ∈ S,
      OSReconstruction.headTranslationDescentCLM
          (OSReconstruction.centerSpatialDescentCLM d T φ) ψ f =
        OSReconstruction.headTranslationDescentCLM
          (OSReconstruction.centerSpatialDescentCLM d
            (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ) ψ f) :
    T = twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound := by
  exact
    OSReconstruction.eq_of_eq_on_dense_headTranslationDescentCLM_centerSpatial
      d T
      (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound)
      hT hTK φ hφ ψ hψ hTred hKred hS hEq

/-- Once an abstract full flattened extension `T` is identified with the
concrete kernel CLM from reduced dense equality, its values on the two-point
product shell and admissible difference shell are the corresponding explicit
kernel integrals. This is the direct blocker-facing payoff from the reduced
quotient comparison theorem. -/
theorem map_productLift_and_differenceLift_of_eq_on_dense_reduced
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hTK :
      OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound))
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ u : Fin d → ℝ, φ u = 1)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ s : ℝ, ψ s = 1)
    (hTred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d T φ))
    (hKred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ))
    {S : Set (SchwartzMap (Fin (d + 1) → ℝ) ℂ)}
    (hS : Dense S)
    (hEq : ∀ f ∈ S,
      OSReconstruction.headTranslationDescentCLM
          (OSReconstruction.centerSpatialDescentCLM d T φ) ψ f =
        OSReconstruction.headTranslationDescentCLM
          (OSReconstruction.centerSpatialDescentCLM d
            (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ) ψ f)
    (χ : SchwartzSpacetime d) (g h : SchwartzSpacetime d) :
    T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) =
        ∫ z : NPointDomain d 2, K z * (χ (z 0) * g (z 0 + z 1)) ∧
      T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1)) := by
  have hEqCLM :
      T = twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound :=
    eq_twoPointFlatKernelCLM_of_eq_on_dense_reduced
      (d := d) T hT K hK_meas C_bd N hC hK_bound hTK φ hφ ψ hψ
      hTred hKred hS hEq
  constructor
  · calc
      T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) =
          twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
            (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) := by
              simpa using congrArg
                (fun L : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ =>
                  L (reindexSchwartzFin (by ring)
                    (flattenSchwartzNPoint (d := d)
                      (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))))
                hEqCLM
      _ = ∫ z : NPointDomain d 2, K z * (χ (z 0) * g (z 0 + z 1)) := by
            simpa using
              twoPointFlatKernelCLM_apply_reindex_flatten
                (d := d) (K := K) hK_meas C_bd N hC hK_bound
                (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g))
  · calc
      T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
          twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
            (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) := by
              simpa using congrArg
                (fun L : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ =>
                  L (reindexSchwartzFin (by ring)
                    (flattenSchwartzNPoint (d := d)
                      (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))))
                hEqCLM
      _ = ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1)) := by
            simpa using
              twoPointFlatKernelCLM_apply_reindex_flatten
                (d := d) (K := K) hK_meas C_bd N hC hK_bound
                (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h))

/-- Compactly supported reduced Schwartz tests are dense in the reduced
difference-variable Schwartz space. This is the concrete dense family used by
the quotient-level `k = 2` wrapper below. -/
theorem dense_compactSupport_reducedSchwartz :
    Dense {h : SchwartzSpacetime d | HasCompactSupport (h : SpacetimeDim d → ℂ)} := by
  simpa [SchwartzSpacetime, SpacetimeDim] using
    (SchwartzMap.dense_hasCompactSupport (m := d + 1))

/-- Reduced dense-set wrapper for the two-point kernel comparison: to identify
an abstract full flattened extension `T` with the concrete kernel CLM induced
by `K`, it is enough to prove equality of the descended reduced functionals on
compactly supported reduced Schwartz tests. -/
theorem map_productLift_and_differenceLift_of_eq_on_compactSupport_reduced
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hTK :
      OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound))
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ u : Fin d → ℝ, φ u = 1)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ s : ℝ, ψ s = 1)
    (hTred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d T φ))
    (hKred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ))
    (hEq : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      OSReconstruction.headTranslationDescentCLM
          (OSReconstruction.centerSpatialDescentCLM d T φ) ψ h =
        OSReconstruction.headTranslationDescentCLM
          (OSReconstruction.centerSpatialDescentCLM d
            (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ) ψ h)
    (χ : SchwartzSpacetime d) (g h : SchwartzSpacetime d) :
    T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) =
        ∫ z : NPointDomain d 2, K z * (χ (z 0) * g (z 0 + z 1)) ∧
      T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1)) := by
  refine map_productLift_and_differenceLift_of_eq_on_dense_reduced
      (d := d) T hT K hK_meas C_bd N hC hK_bound hTK φ hφ ψ hψ hTred hKred
      (S := {h : SchwartzSpacetime d | HasCompactSupport (h : SpacetimeDim d → ℂ)})
      dense_compactSupport_reducedSchwartz ?_ χ g h
  intro f hf
  exact hEq f hf

/-- Positive-support compact reduced wrapper for the two-point kernel
comparison: if the reduced center-time/difference descended functionals agree
on compactly supported tests supported in the positive head half-space, then
head-translation invariance upgrades that agreement to all compactly supported
reduced tests, after which the standard compact-support reduced wrapper
finishes the product-shell / difference-shell comparison. -/
theorem map_productLift_and_differenceLift_of_eq_on_positive_compactSupport_reduced
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hTK :
      OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound))
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ u : Fin d → ℝ, φ u = 1)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ s : ℝ, ψ s = 1)
    (hψ_compact : HasCompactSupport ψ)
    (hTred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d T φ))
    (hKred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d
        (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ))
    (hEq_pos : ∀ H : SchwartzMap (Fin (d + 2) → ℝ) ℂ,
      HasCompactSupport (H : (Fin (d + 2) → ℝ) → ℂ) →
      tsupport (H : (Fin (d + 2) → ℝ) → ℂ) ⊆ {x : Fin (d + 2) → ℝ | 0 < x 0} →
      OSReconstruction.centerSpatialDescentCLM d T φ H =
        OSReconstruction.centerSpatialDescentCLM d
          (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ H)
    (χ : SchwartzSpacetime d) (g h : SchwartzSpacetime d) :
    T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) =
        ∫ z : NPointDomain d 2, K z * (χ (z 0) * g (z 0 + z 1)) ∧
      T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1)) := by
  have hEq :
      ∀ h : SchwartzSpacetime d,
        HasCompactSupport (h : SpacetimeDim d → ℂ) →
        OSReconstruction.headTranslationDescentCLM
            (OSReconstruction.centerSpatialDescentCLM d T φ) ψ h =
          OSReconstruction.headTranslationDescentCLM
            (OSReconstruction.centerSpatialDescentCLM d
              (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ) ψ h := by
    intro h hh
    exact
      OSReconstruction.headTranslationDescentCLM_eq_on_compactSupport_of_eq_on_positive_tsupport
        (OSReconstruction.centerSpatialDescentCLM d T φ)
        (OSReconstruction.centerSpatialDescentCLM d
          (twoPointFlatKernelCLM (d := d) K hK_meas C_bd N hC hK_bound) φ)
        hTred hKred ψ hψ hψ_compact hEq_pos h hh
  exact
    map_productLift_and_differenceLift_of_eq_on_compactSupport_reduced
      (d := d) T hT K hK_meas C_bd N hC hK_bound hTK φ hφ ψ hψ hTred hKred
      hEq χ g h

/-- Fixed-time specialization of the compact-support reduced wrapper. Once the
reduced descended functional agrees with the fixed-time kernel on compactly
supported reduced Schwartz tests, the full flattened extension already
reproduces the expected product-shell and admissible difference-shell
integrals. -/
theorem map_productLift_and_differenceLift_of_eq_on_compactSupport_fixedTimeKernel
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hK_meas : AEStronglyMeasurable (twoPointFixedTimeKernel (d := d) G t) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hTK :
      OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d
        (twoPointFlatKernelCLM (d := d)
          (twoPointFixedTimeKernel (d := d) G t) hK_meas C_bd N hC hK_bound))
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ u : Fin d → ℝ, φ u = 1)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ s : ℝ, ψ s = 1)
    (hTred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d T φ))
    (hKred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d
        (twoPointFlatKernelCLM (d := d)
          (twoPointFixedTimeKernel (d := d) G t) hK_meas C_bd N hC hK_bound) φ))
    (hEq : ∀ h : SchwartzSpacetime d,
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
      OSReconstruction.headTranslationDescentCLM
          (OSReconstruction.centerSpatialDescentCLM d T φ) ψ h =
        OSReconstruction.headTranslationDescentCLM
          (OSReconstruction.centerSpatialDescentCLM d
            (twoPointFlatKernelCLM (d := d)
              (twoPointFixedTimeKernel (d := d) G t) hK_meas C_bd N hC hK_bound) φ) ψ h)
    (χ : SchwartzSpacetime d) (g h : SchwartzSpacetime d) :
    T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) =
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeKernel (d := d) G t z * (χ (z 0) * g (z 0 + z 1)) ∧
      T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeKernel (d := d) G t z * (χ (z 0) * h (z 1)) := by
  simpa using
    map_productLift_and_differenceLift_of_eq_on_compactSupport_reduced
      (d := d) T hT (twoPointFixedTimeKernel (d := d) G t) hK_meas
      C_bd N hC hK_bound hTK φ hφ ψ hψ hTred hKred hEq χ g h

/-- Fixed-time specialization of the previous positive-support compact reduced
wrapper. This is the blocker-facing form used when the reduced fixed-time
kernel equality is first proved only on compactly supported tests in the
positive head half-space. -/
theorem map_productLift_and_differenceLift_of_eq_on_positive_compactSupport_fixedTimeKernel
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hK_meas : AEStronglyMeasurable (twoPointFixedTimeKernel (d := d) G t) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hTK :
      OSReconstruction.IsCenterSpatialTranslationInvariantSchwartzCLM d
        (twoPointFlatKernelCLM (d := d)
          (twoPointFixedTimeKernel (d := d) G t) hK_meas C_bd N hC hK_bound))
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ u : Fin d → ℝ, φ u = 1)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ s : ℝ, ψ s = 1)
    (hψ_compact : HasCompactSupport ψ)
    (hTred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d T φ))
    (hKred : OSReconstruction.IsHeadTranslationInvariantSchwartzCLM
      (OSReconstruction.centerSpatialDescentCLM d
        (twoPointFlatKernelCLM (d := d)
          (twoPointFixedTimeKernel (d := d) G t) hK_meas C_bd N hC hK_bound) φ))
    (hEq_pos : ∀ H : SchwartzMap (Fin (d + 2) → ℝ) ℂ,
      HasCompactSupport (H : (Fin (d + 2) → ℝ) → ℂ) →
      tsupport (H : (Fin (d + 2) → ℝ) → ℂ) ⊆ {x : Fin (d + 2) → ℝ | 0 < x 0} →
      OSReconstruction.centerSpatialDescentCLM d T φ H =
        OSReconstruction.centerSpatialDescentCLM d
          (twoPointFlatKernelCLM (d := d)
            (twoPointFixedTimeKernel (d := d) G t) hK_meas C_bd N hC hK_bound) φ H)
    (χ : SchwartzSpacetime d) (g h : SchwartzSpacetime d) :
    T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointProductLift χ g)))) =
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeKernel (d := d) G t z * (χ (z 0) * g (z 0 + z 1)) ∧
      T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeKernel (d := d) G t z * (χ (z 0) * h (z 1)) := by
  simpa using
    map_productLift_and_differenceLift_of_eq_on_positive_compactSupport_reduced
      (d := d) T hT (twoPointFixedTimeKernel (d := d) G t) hK_meas
      C_bd N hC hK_bound hTK φ hφ ψ hψ hψ_compact hTred hKred hEq_pos χ g h

end OSReconstruction
