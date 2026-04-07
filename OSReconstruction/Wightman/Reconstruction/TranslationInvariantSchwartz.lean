import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.SchwartzPartialEval
import OSReconstruction.Wightman.Reconstruction.Poincare1D
import OSReconstruction.Wightman.Reconstruction.SliceIntegral
import OSReconstruction.Wightman.Reconstruction.ZeroMeanFourierTransport
import OSReconstruction.SCV.DistributionalUniqueness
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Classical LineDeriv Topology ContDiff

open SchwartzMap

namespace OSReconstruction

set_option maxHeartbeats 1200000

/-!
# Translation-Invariant Schwartz Functionals

This file contains the zero-mean decomposition and translation-invariant
classification theorems on Schwartz space that sit directly behind the
two-point Schwinger and Wightman reduction steps.
-/

theorem norm_tailInsertCLM_eq {n : ℕ} (y : Fin n → ℝ) :
    ‖tailInsertCLM n y‖ = ‖y‖ := by
  have hle : ‖tailInsertCLM n y‖ ≤ ‖y‖ := by
    calc
      ‖tailInsertCLM n y‖ ≤ ‖tailInsertCLM n‖ * ‖y‖ := by
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖y‖ := by
        gcongr
        exact tailInsertCLM_opNorm_le n
      _ = ‖y‖ := by ring
  have hge : ‖y‖ ≤ ‖tailInsertCLM n y‖ := by
    calc
      ‖y‖ = ‖tailCLM n (E := ℝ) (tailInsertCLM n y)‖ := by
        simp [tailInsertCLM_apply, tailCLM_apply]
      _ ≤ ‖tailCLM n (E := ℝ)‖ * ‖tailInsertCLM n y‖ := by
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖tailInsertCLM n y‖ := by
        gcongr
        exact tailCLM_opNorm_le (E := ℝ) n
      _ = ‖tailInsertCLM n y‖ := by ring
  exact le_antisymm hle hge

/-- Head evaluation at the zero head coordinate, as a continuous linear map on
Schwartz space. -/
noncomputable def headSectionCLM (n : ℕ) :
    SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → ℝ) ℂ :=
  SchwartzMap.compCLM ℂ (tailInsertCLM n).hasTemperateGrowth
    ⟨1, 1, fun y => by
      calc
        ‖y‖ = ‖tailInsertCLM n y‖ := (norm_tailInsertCLM_eq y).symm
        _ ≤ 1 * (1 + ‖tailInsertCLM n y‖) ^ (1 : ℕ) := by
          have h : ‖tailInsertCLM n y‖ ≤ 1 + ‖tailInsertCLM n y‖ := by linarith
          simpa using h
    ⟩

@[simp] theorem headSectionCLM_apply {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (y : Fin n → ℝ) :
    headSectionCLM n F y = F (Fin.cons 0 y) := by
  simp [headSectionCLM, tailInsertCLM_apply]

theorem hasCompactSupport_headSection {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (hF : HasCompactSupport F) :
    HasCompactSupport (headSectionCLM n F) := by
  rcases hF.isCompact.isBounded.subset_closedBall (0 : Fin (n + 1) → ℝ) with ⟨R, hR⟩
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℝ) R) ?_
  intro y hy
  by_contra hyR
  have hy_gt : R < ‖y‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm, not_le] using hyR
  have hz_not_mem : (Fin.cons 0 y : Fin (n + 1) → ℝ) ∉ tsupport F := by
    intro hz
    have hball := hR hz
    have hnorm_ball : ‖(Fin.cons 0 y : Fin (n + 1) → ℝ)‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hball
    have hnorm_eq : ‖(Fin.cons 0 y : Fin (n + 1) → ℝ)‖ = ‖y‖ := by
      simpa [tailInsertCLM_apply] using norm_tailInsertCLM_eq (n := n) y
    exact not_lt_of_ge (hnorm_eq ▸ hnorm_ball) hy_gt
  have hzero : headSectionCLM n F y = 0 := by
    rw [headSectionCLM_apply]
    simpa using image_eq_zero_of_notMem_tsupport hz_not_mem
  exact hy hzero

@[simp] theorem headSectionCLM_zero {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (hF0 : F 0 = 0) :
    headSectionCLM n F 0 = 0 := by
  have hcons0 : (Fin.cons 0 (0 : Fin n → ℝ) : Fin (n + 1) → ℝ) = 0 := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro i
      simp
  simpa [headSectionCLM_apply, hcons0] using hF0

@[simp] theorem headSectionCLM_prependField {n : ℕ}
    (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n → ℝ) ℂ) :
    headSectionCLM n (φ.prependField g) = (φ 0) • g := by
  ext y
  simp [headSectionCLM_apply, SchwartzMap.prependField_apply]

theorem headSection_remainder_eq_zero {n : ℕ}
    (φ : SchwartzMap ℝ ℂ) (hφ0 : φ 0 = 1)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    headSectionCLM n (F - φ.prependField (headSectionCLM n F)) = 0 := by
  ext y
  simp [headSectionCLM_apply, SchwartzMap.prependField_apply, hφ0]

/-- Project to the head coordinate. -/
noncomputable def headCoordProjCLM (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0

@[simp] theorem headCoordProjCLM_apply {n : ℕ} (x : Fin (n + 1) → ℝ) :
    headCoordProjCLM n x = x 0 := rfl

/-- Insert into the head coordinate. -/
noncomputable def headCoordSingleCLM (n : ℕ) :
    ℝ →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
    (((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ))

@[simp] theorem headCoordSingleCLM_apply {n : ℕ} (a : ℝ) :
    headCoordSingleCLM n a = ((Pi.single 0 a) : Fin (n + 1) → ℝ) := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [headCoordSingleCLM, Pi.single_apply]
  · intro i
    simp [headCoordSingleCLM, Pi.single_apply]

theorem norm_le_norm_headCoordSingleCLM {n : ℕ} (a : ℝ) :
    ‖a‖ ≤ ‖headCoordSingleCLM n a‖ := by
  have hcoord : (headCoordSingleCLM n a) 0 = a := by
    simp [headCoordSingleCLM_apply]
  calc
    ‖a‖ = ‖(headCoordSingleCLM n a) 0‖ := by rw [hcoord]
    _ ≤ ‖headCoordSingleCLM n a‖ := by
      exact norm_le_pi_norm (headCoordSingleCLM n a) 0

/-- Restrict a Schwartz function on `Fin (n+1) → ℝ` to the head axis
`t ↦ Pi.single 0 t`. -/
noncomputable def headAxisSectionCLM (n : ℕ) :
    SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLM ℂ (headCoordSingleCLM n).hasTemperateGrowth
    ⟨1, 1, fun t => by
      calc
        ‖t‖ ≤ ‖headCoordSingleCLM n t‖ := norm_le_norm_headCoordSingleCLM t
        _ ≤ 1 * (1 + ‖headCoordSingleCLM n t‖) ^ (1 : ℕ) := by
          have h : ‖headCoordSingleCLM n t‖ ≤ 1 + ‖headCoordSingleCLM n t‖ := by linarith
          simpa using h
    ⟩

@[simp] theorem headAxisSectionCLM_apply {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (t : ℝ) :
    headAxisSectionCLM n F t = F (headCoordSingleCLM n t) := by
  simp [headAxisSectionCLM]

@[simp] theorem headAxisSectionCLM_apply_single {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (t : ℝ) :
    headAxisSectionCLM n F t = F (Pi.single 0 t) := by
  simp [headAxisSectionCLM_apply, headCoordSingleCLM_apply]

theorem headCoordSingle_add_tailInsert {n : ℕ} (t : ℝ) (y : Fin n → ℝ) :
    headCoordSingleCLM n t + tailInsertCLM n y = Fin.cons t y := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [headCoordSingleCLM_apply, tailInsertCLM_apply]
  · intro i
    simp [headCoordSingleCLM_apply, tailInsertCLM_apply]

/-- Restrict a Schwartz function on `Fin (n+1) → ℝ` to the affine head line
with fixed tail parameter `y`, i.e. `t ↦ F (Fin.cons t y)`. -/
noncomputable def tailSectionCLM (n : ℕ) (y : Fin n → ℝ) :
    SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (headAxisSectionCLM n).comp (SCV.translateSchwartzCLM (tailInsertCLM n y))

@[simp] theorem tailSectionCLM_apply {n : ℕ} (y : Fin n → ℝ)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (t : ℝ) :
    tailSectionCLM n y F t = F (Fin.cons t y) := by
  have hsum : ((Pi.single 0 t : Fin (n + 1) → ℝ) + Fin.cons 0 y) = Fin.cons t y := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [Pi.add_apply]
    · intro i
      simp [Pi.add_apply]
  rw [tailSectionCLM, ContinuousLinearMap.comp_apply, headAxisSectionCLM_apply_single,
    SCV.translateSchwartzCLM_apply, SCV.translateSchwartz_apply]
  simpa [hsum]

/-- For a compactly-supported Schwartz test, the affine tail slice
`y ↦ (t ↦ F (Fin.cons t y))` varies continuously with `y` in the Schwartz
topology on `𝓢(ℝ, ℂ)`. -/
theorem tendsto_tailSectionCLM_nhds_of_isCompactSupport {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (hF_compact : HasCompactSupport F)
    (y₀ : Fin n → ℝ) :
    Filter.Tendsto (fun y : Fin n → ℝ => tailSectionCLM n y F) (𝓝 y₀)
      (𝓝 (tailSectionCLM n y₀ F)) := by
  have htranslate :
      Filter.Tendsto
        (fun y : Fin n → ℝ => SCV.translateSchwartz (tailInsertCLM n y) F)
        (𝓝 y₀)
        (𝓝 (SCV.translateSchwartz (tailInsertCLM n y₀) F)) := by
    exact
      (SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport F hF_compact
        (tailInsertCLM n y₀)).comp
        ((tailInsertCLM n).continuous.tendsto y₀)
  simpa [tailSectionCLM, ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply]
    using (headAxisSectionCLM n).continuous.tendsto
      (SCV.translateSchwartz (tailInsertCLM n y₀) F) |>.comp htranslate

/-- For a compactly-supported Schwartz test, the tail-slice family is a
continuous map into one-dimensional Schwartz space. -/
theorem continuous_tailSectionCLM_of_isCompactSupport {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (hF_compact : HasCompactSupport F) :
    Continuous (fun y : Fin n → ℝ => tailSectionCLM n y F) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  exact tendsto_tailSectionCLM_nhds_of_isCompactSupport F hF_compact y₀

/-- After reindexing spacetime as `(time, spatial)`, partial evaluation in the
spatial variable is exactly the affine tail slice `t ↦ f (t, y)`. -/
theorem partialEval₂_spacetimeToTimeSpatial_eq_tailSectionCLM
    (d : ℕ) (f : SchwartzSpacetime d) (y : Fin d → ℝ) :
    SchwartzMap.partialEval₂ (OSReconstruction.spacetimeToTimeSpatialCLM d f) y =
      tailSectionCLM d y f := by
  ext t
  simp [tailSectionCLM_apply, OSReconstruction.partialEval₂_spacetimeToTimeSpatialCLM_apply]

/-- The tail-slice family of a Schwartz test varies continuously in the
Schwartz topology, without any compact-support assumption. -/
theorem continuous_tailSectionCLM {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    Continuous (fun y : Fin n → ℝ => tailSectionCLM n y F) := by
  simpa [partialEval₂_spacetimeToTimeSpatial_eq_tailSectionCLM (d := n) (f := F)] using
    (continuous_partialEval₂ (f := OSReconstruction.spacetimeToTimeSpatialCLM n F))

/-- Reindexed spacetime partial evaluation is continuous in the Schwartz
topology, without compact-support assumptions. -/
theorem continuous_partialEval₂_spacetimeToTimeSpatial
    (d : ℕ) (f : SchwartzSpacetime d) :
    Continuous (fun y : Fin d → ℝ =>
      SchwartzMap.partialEval₂ (OSReconstruction.spacetimeToTimeSpatialCLM d f) y) := by
  simpa [partialEval₂_spacetimeToTimeSpatial_eq_tailSectionCLM (d := d) (f := f)] using
    continuous_tailSectionCLM (n := d) f

/-- For a compactly-supported spacetime Schwartz test, the partial evaluation
family `y ↦ f(·, y)` is continuous in the Schwartz topology on `𝓢(ℝ, ℂ)`. -/
theorem continuous_partialEval₂_spacetimeToTimeSpatial_of_isCompactSupport
    (d : ℕ) (f : SchwartzSpacetime d) (hf_compact : HasCompactSupport f) :
    Continuous (fun y : Fin d → ℝ =>
      SchwartzMap.partialEval₂ (OSReconstruction.spacetimeToTimeSpatialCLM d f) y) := by
  simpa [partialEval₂_spacetimeToTimeSpatial_eq_tailSectionCLM (d := d) (f := f)] using
    continuous_tailSectionCLM_of_isCompactSupport (n := d) f hf_compact

/-- Project to the head-axis component. -/
noncomputable def headCoordProjectorCLM (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  (headCoordSingleCLM n).comp (headCoordProjCLM n)

@[simp] theorem headCoordProjectorCLM_apply {n : ℕ} (x : Fin (n + 1) → ℝ) :
    headCoordProjectorCLM n x = ((Pi.single 0 (x 0)) : Fin (n + 1) → ℝ) := by
  simp [headCoordProjectorCLM, headCoordSingleCLM_apply]

/-- Keep the tail coordinates and scale the head coordinate by `s`. -/
noncomputable def headCoordSegmentCLM (n : ℕ) (s : ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  (tailInsertCLM n).comp (tailCLM n) + s • headCoordProjectorCLM n

@[simp] theorem headCoordSegmentCLM_apply {n : ℕ} (s : ℝ) (x : Fin (n + 1) → ℝ) :
    headCoordSegmentCLM n s x = Fin.cons (s * x 0) (fun i : Fin n => x i.succ) := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [headCoordSegmentCLM, tailInsertCLM_apply, tailCLM_apply,
      headCoordProjectorCLM_apply, Pi.single_apply]
  · intro i
    simp [headCoordSegmentCLM, tailInsertCLM_apply, tailCLM_apply,
      headCoordProjectorCLM_apply, Pi.single_apply]

theorem headCoordSegmentCLM_norm_le_one {n : ℕ} {s : ℝ} (hs : |s| ≤ 1) :
    ‖headCoordSegmentCLM n s‖ ≤ 1 := by
  have hbound :
      ∀ x : Fin (n + 1) → ℝ, ‖headCoordSegmentCLM n s x‖ ≤ 1 * ‖x‖ := by
    intro x
    rw [one_mul]
    have hhead :
        ‖s * x 0‖ ≤ ‖x‖ := by
      calc
        ‖s * x 0‖ = |s| * ‖x 0‖ := by
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        _ ≤ 1 * ‖x 0‖ := by gcongr
        _ ≤ ‖x‖ := by
          simpa using (norm_le_pi_norm x 0)
    have htail :
        ∀ i : Fin n, ‖x i.succ‖ ≤ ‖x‖ := by
      intro i
      simpa using (norm_le_pi_norm x i.succ)
    rw [headCoordSegmentCLM_apply]
    simp only [Pi.norm_def]
    exact_mod_cast Finset.sup_le fun b _ =>
      Fin.cases hhead (fun i => htail i) b
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one hbound

theorem continuous_headCoordSegmentCLM_apply {n : ℕ} (x : Fin (n + 1) → ℝ) :
    Continuous fun s : ℝ => headCoordSegmentCLM n s x := by
  have hEq :
      (fun s : ℝ => headCoordSegmentCLM n s x) =
        (fun s : ℝ =>
          ((Fin.cons (s * x 0) (fun i : Fin n => x i.succ)) : Fin (n + 1) → ℝ)) := by
    funext s
    simpa [headCoordSegmentCLM_apply]
  rw [hEq]
  classical
  refine continuous_pi ?_
  intro j
  refine Fin.cases ?_ ?_ j
  · simpa using (continuous_id.mul continuous_const)
  · intro i
    exact continuous_const

theorem continuous_headCoordSegmentCLM {n : ℕ} :
    Continuous fun s : ℝ => headCoordSegmentCLM n s := by
  have hconst :
      Continuous fun _s : ℝ =>
        (tailInsertCLM n).comp (tailCLM n : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ)) := by
    simpa using
      (continuous_const :
        Continuous fun _s : ℝ =>
          (tailInsertCLM n).comp (tailCLM n : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ)))
  exact hconst.add ((continuous_id.smul continuous_const))

theorem hasFDerivAt_lineDeriv_comp_headCoordSegmentCLM {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (s : ℝ) (x : Fin (n + 1) → ℝ) :
    let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
      ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
    HasFDerivAt
      (fun y : Fin (n + 1) → ℝ => dF (headCoordSegmentCLM n s y))
      ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp (headCoordSegmentCLM n s))
      x := by
  dsimp
  exact (SchwartzMap.hasFDerivAt
      (f := ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)
      (x := headCoordSegmentCLM n s x)).comp x
    ((headCoordSegmentCLM n s).hasFDerivAt)

theorem continuous_fderiv_lineDeriv_comp_headCoordSegmentCLM {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (x : Fin (n + 1) → ℝ) :
    let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
      ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
    Continuous fun s : ℝ =>
      ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
        (headCoordSegmentCLM n s)) := by
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
  let C :
      ((Fin (n + 1) → ℝ) →L[ℝ] ℂ) →L[ℝ]
        (((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) →L[ℝ]
          ((Fin (n + 1) → ℝ) →L[ℝ] ℂ)) :=
    ContinuousLinearMap.compL ℝ
      (Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ) ℂ
  have hA :
      Continuous fun s : ℝ =>
        fderiv ℝ dF (headCoordSegmentCLM n s x) := by
    exact ((dF.smooth 1).continuous_fderiv one_ne_zero).comp
      (continuous_headCoordSegmentCLM_apply x)
  change Continuous fun s : ℝ =>
    C (fderiv ℝ dF (headCoordSegmentCLM n s x))
      (headCoordSegmentCLM n s)
  exact ((C.continuous.comp hA).clm_apply (continuous_headCoordSegmentCLM (n := n)))

theorem continuous_fderiv_lineDeriv_comp_headCoordSegmentCLM_uncurry {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
      ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
    Continuous fun p : ℝ × (Fin (n + 1) → ℝ) =>
      ((fderiv ℝ dF (headCoordSegmentCLM n p.1 p.2)).comp
        (headCoordSegmentCLM n p.1)) := by
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
  let C :
      ((Fin (n + 1) → ℝ) →L[ℝ] ℂ) →L[ℝ]
        (((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) →L[ℝ]
          ((Fin (n + 1) → ℝ) →L[ℝ] ℂ)) :=
    ContinuousLinearMap.compL ℝ
      (Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ) ℂ
  have hseg :
      Continuous fun p : ℝ × (Fin (n + 1) → ℝ) =>
        headCoordSegmentCLM n p.1 p.2 := by
    exact (((continuous_headCoordSegmentCLM (n := n)).comp continuous_fst).clm_apply continuous_snd)
  have hA :
      Continuous fun p : ℝ × (Fin (n + 1) → ℝ) =>
        fderiv ℝ dF (headCoordSegmentCLM n p.1 p.2) := by
    exact ((dF.smooth 1).continuous_fderiv one_ne_zero).comp hseg
  change Continuous fun p : ℝ × (Fin (n + 1) → ℝ) =>
    C (fderiv ℝ dF (headCoordSegmentCLM n p.1 p.2))
      (headCoordSegmentCLM n p.1)
  exact ((C.continuous.comp hA).clm_apply
    ((continuous_headCoordSegmentCLM (n := n)).comp continuous_fst))

/-- The explicit Hadamard coefficient along the head coordinate. -/
def headCoordCoeff {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    (Fin (n + 1) → ℝ) → ℂ :=
  fun x =>
    ∫ s in (0 : ℝ)..1,
      (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)
        (Fin.cons (s * x 0) (fun i : Fin n => x i.succ))

/-- Weighted head Hadamard coefficient. The weight `s^r` is the exact family
that appears when differentiating the basic coefficient repeatedly in the head
direction. -/
def headCoordCoeffPow {n : ℕ} (r : ℕ)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    (Fin (n + 1) → ℝ) → ℂ :=
  fun x =>
    ∫ s in (0 : ℝ)..1,
      ((s : ℝ) ^ r : ℂ) *
        (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)
          (Fin.cons (s * x 0) (fun i : Fin n => x i.succ))

@[simp] theorem headCoordCoeffPow_zero {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    headCoordCoeffPow 0 F = headCoordCoeff F := by
  funext x
  simp [headCoordCoeffPow, headCoordCoeff]

theorem eq_head_coord_smul_headCoordCoeff_of_headSection_zero {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF : headSectionCLM n F = 0)
    (x : Fin (n + 1) → ℝ) :
    F x = (x 0 : ℝ) • headCoordCoeff F x := by
  let y : Fin n → ℝ := fun i => x i.succ
  let φ : ℝ → ℂ := fun s => F (Fin.cons (s * x 0) y)
  have hy_zero : F (Fin.cons (0 : ℝ) y) = 0 := by
    have happly := congrArg (fun G : SchwartzMap (Fin n → ℝ) ℂ => G y) hF
    simpa [headSectionCLM_apply, y] using happly
  have hφ_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt φ
          ((x 0 : ℝ) •
            (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)
              (Fin.cons (s * x 0) y)) s := by
    intro s
    let γ : ℝ → Fin (n + 1) → ℝ := fun r => Fin.cons (r * x 0) y
    have hγ_deriv :
        HasDerivAt γ (((Pi.single 0 (x 0 : ℝ)) : Fin (n + 1) → ℝ)) s := by
      let L : ℝ →L[ℝ] (Fin (n + 1) → ℝ) :=
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (((Pi.single 0 (x 0 : ℝ)) : Fin (n + 1) → ℝ))
      have hL : HasDerivAt (fun r : ℝ => L r)
          (((Pi.single 0 (x 0 : ℝ)) : Fin (n + 1) → ℝ)) s := by
        simpa [L, ContinuousLinearMap.smulRight_apply, one_smul] using L.hasDerivAt
      have hγ_eq : γ = fun r : ℝ => L r + Fin.cons (0 : ℝ) y := by
        funext r
        ext j
        refine Fin.cases ?_ ?_ j
        · simp [γ, L, ContinuousLinearMap.smulRight_apply]
        · intro i
          simp [γ, L, ContinuousLinearMap.smulRight_apply]
      simpa [hγ_eq] using hL.const_add (Fin.cons (0 : ℝ) y)
    have hcomp :
        HasDerivAt φ
          ((fderiv ℝ F (γ s)) (((Pi.single 0 (x 0 : ℝ)) : Fin (n + 1) → ℝ))) s := by
      exact ((SchwartzMap.differentiableAt F (x := γ s)).hasFDerivAt.comp_hasDerivAt s hγ_deriv)
    have hdir :
        (((Pi.single 0 (x 0 : ℝ)) : Fin (n + 1) → ℝ)) =
          (x 0 : ℝ) • ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ) := by
      ext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro i
        simp [Pi.single_apply]
    convert hcomp using 1
    rw [show γ s = Fin.cons (s * x 0) y by rfl, hdir]
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_smul]
  have hφ_deriv :
      deriv φ =
        fun s =>
          (x 0 : ℝ) •
            (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)
              (Fin.cons (s * x 0) y) := by
    funext s
    exact (hφ_hasDeriv s).deriv
  have hφ_diff : ∀ s ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℝ φ s := by
    intro s hs
    exact (hφ_hasDeriv s).differentiableAt
  have hφ_cont :
      ContinuousOn
        (fun s =>
          (x 0 : ℝ) •
            (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)
              (Fin.cons (s * x 0) y))
        (Set.uIcc (0 : ℝ) 1) := by
    let γ : ℝ → Fin (n + 1) → ℝ := fun s => Fin.cons (s * x 0) y
    have hpath : Continuous γ := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id.mul continuous_const)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    exact (continuous_const.smul
      ((SchwartzMap.continuous
        (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)).comp hpath)).continuousOn
  have hFTC :
      ∫ s in (0 : ℝ)..1,
        (x 0 : ℝ) •
          (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)
            (Fin.cons (s * x 0) y)
        = F x - F (Fin.cons (0 : ℝ) y) := by
    have hφ0 : φ 0 = F (Fin.cons (0 : ℝ) y) := by simp [φ]
    have hφ1 : φ 1 = F x := by
      have hx : Fin.cons (1 * x 0) y = x := by
        ext j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro i
          simp [y]
      have hx' : Fin.cons (x 0) y = x := by
        ext j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro i
          simp [y]
      simpa [φ] using congrArg F hx'
    simpa [φ, hφ_deriv, hφ0, hφ1] using
      (intervalIntegral.integral_deriv_eq_sub' φ hφ_deriv hφ_diff hφ_cont)
  calc
    F x = F x - F (Fin.cons (0 : ℝ) y) := by rw [hy_zero, sub_zero]
    _ = ∫ s in (0 : ℝ)..1,
          (x 0 : ℝ) •
            (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)
              (Fin.cons (s * x 0) y) := by
          symm
          exact hFTC
    _ = (x 0 : ℝ) • headCoordCoeff F x := by
          rw [intervalIntegral.integral_smul]
          have hcoeff :
              ∫ s in (0 : ℝ)..1,
                (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)
                  (Fin.cons (s * x 0) y)
                =
              headCoordCoeff F x := by
            simp [headCoordCoeff, y]
          exact congrArg (fun z : ℂ => (x 0 : ℝ) • z) hcoeff

theorem headCoordCoeff_eq_lineDeriv_on_hyperplane {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x : Fin (n + 1) → ℝ) (hx0 : x 0 = 0) :
    headCoordCoeff F x =
      (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F) x := by
  have hx : Fin.cons (0 : ℝ) (fun i : Fin n => x i.succ) = x := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simpa [hx0]
    · intro i
      simp
  rw [headCoordCoeff]
  simpa [hx0, hx]

theorem headCoordCoeff_eq_inv_smul_of_ne_zero {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF : headSectionCLM n F = 0)
    (x : Fin (n + 1) → ℝ) (hx0 : x 0 ≠ 0) :
    headCoordCoeff F x = (x 0 : ℝ)⁻¹ • F x := by
  have hfactor :
      F x = (x 0 : ℝ) • headCoordCoeff F x :=
    eq_head_coord_smul_headCoordCoeff_of_headSection_zero F hF x
  have hrewrite :
      headCoordCoeff F x =
        (x 0 : ℝ)⁻¹ • ((x 0 : ℝ) • headCoordCoeff F x) := by
    simp [hx0]
  rw [hrewrite, hfactor]

theorem support_headCoordCoeff_subset_tsupport {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF : headSectionCLM n F = 0) :
    Function.support (headCoordCoeff F) ⊆ tsupport F := by
  intro x hx
  by_contra hxt
  rw [Function.mem_support] at hx
  have hFx0 : F x = 0 := by
    have hxF : x ∉ Function.support F := fun hxF => hxt (subset_tsupport F hxF)
    simpa [Function.notMem_support] using hxF
  have hcoeff0 : headCoordCoeff F x = 0 := by
    by_cases hx0 : x 0 = 0
    · rw [headCoordCoeff_eq_lineDeriv_on_hyperplane F x hx0]
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt]
      simp
    · rw [headCoordCoeff_eq_inv_smul_of_ne_zero F hF x hx0, hFx0, smul_zero]
  exact hx hcoeff0

theorem hasCompactSupport_headCoordCoeff {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF : headSectionCLM n F = 0)
    (hFcs : HasCompactSupport F) :
    HasCompactSupport (headCoordCoeff F) :=
  hFcs.mono' (support_headCoordCoeff_subset_tsupport F hF)

theorem continuous_headCoordCoeff {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    Continuous (headCoordCoeff F) := by
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
  let γ : (Fin (n + 1) → ℝ) × ℝ → Fin (n + 1) → ℝ :=
    fun p j => Fin.cases (p.2 * p.1 0) (fun i : Fin n => p.1 i.succ) j
  have huncurry :
      Continuous
        (Function.uncurry
          (fun x : Fin (n + 1) → ℝ =>
            fun s : ℝ =>
              dF (γ (x, s)))) := by
    change Continuous
      (fun p : (Fin (n + 1) → ℝ) × ℝ => dF (γ p))
    have harg :
        Continuous γ := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · have hhead :
            Continuous fun p : (Fin (n + 1) → ℝ) × ℝ => p.1 0 :=
            (continuous_apply 0).comp continuous_fst
        simpa using continuous_snd.mul hhead
      · intro i
        simpa using (continuous_apply i.succ).comp continuous_fst
    exact (SchwartzMap.continuous dF).comp harg
  simpa [headCoordCoeff] using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume) (a₀ := (0 : ℝ)) (b₀ := 1) huncurry)

theorem continuous_headCoordCoeffPow {n : ℕ} (r : ℕ)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    Continuous (headCoordCoeffPow r F) := by
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
  let γ : (Fin (n + 1) → ℝ) × ℝ → Fin (n + 1) → ℝ :=
    fun p j => Fin.cases (p.2 * p.1 0) (fun i : Fin n => p.1 i.succ) j
  have huncurry :
      Continuous
        (Function.uncurry
          (fun x : Fin (n + 1) → ℝ =>
            fun s : ℝ =>
              ((s : ℝ) ^ r : ℂ) * dF (γ (x, s)))) := by
    change Continuous
      (fun p : (Fin (n + 1) → ℝ) × ℝ => ((p.2 : ℝ) ^ r : ℂ) * dF (γ p))
    have harg :
        Continuous γ := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · have hhead :
            Continuous fun p : (Fin (n + 1) → ℝ) × ℝ => p.1 0 :=
            (continuous_apply 0).comp continuous_fst
        simpa using continuous_snd.mul hhead
      · intro i
        simpa using (continuous_apply i.succ).comp continuous_fst
    have hsPow : Continuous fun p : (Fin (n + 1) → ℝ) × ℝ => (((p.2 : ℝ) ^ r : ℝ) : ℂ) := by
      exact (Complex.ofRealCLM.continuous.comp (continuous_snd.pow r))
    simpa using hsPow.mul ((SchwartzMap.continuous dF).comp harg)
  simpa [headCoordCoeffPow] using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume) (a₀ := (0 : ℝ)) (b₀ := 1) huncurry)

theorem hasFDerivAt_headCoordCoeff {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x₀ : Fin (n + 1) → ℝ) :
    HasFDerivAt
      (headCoordCoeff F)
      (let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
        ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
      ∫ s in (0 : ℝ)..1,
        ((fderiv ℝ dF (headCoordSegmentCLM n s x₀)).comp
          (headCoordSegmentCLM n s)))
      x₀ := by
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
  let Φ :
      (Fin (n + 1) → ℝ) → ℝ → ℂ :=
    fun x s => dF (headCoordSegmentCLM n s x)
  let Φ' :
      (Fin (n + 1) → ℝ) → ℝ →
        ((Fin (n + 1) → ℝ) →L[ℝ] ℂ) :=
    fun x s =>
      ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
        (headCoordSegmentCLM n s))
  let K : Set (ℝ × (Fin (n + 1) → ℝ)) :=
    Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall x₀ 1
  have hΦ_meas :
      ∀ᶠ x in nhds x₀,
        MeasureTheory.AEStronglyMeasurable (Φ x)
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hcont : Continuous (Φ x) := by
      exact (SchwartzMap.continuous dF).comp
        (continuous_headCoordSegmentCLM_apply x)
    exact hcont.aestronglyMeasurable
  have hΦ_int :
      IntervalIntegrable (Φ x₀) MeasureTheory.volume (0 : ℝ) 1 := by
    have hcont : Continuous (Φ x₀) := by
      exact (SchwartzMap.continuous dF).comp
        (continuous_headCoordSegmentCLM_apply x₀)
    exact hcont.intervalIntegrable _ _
  have hΦ'_meas :
      MeasureTheory.AEStronglyMeasurable (Φ' x₀)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)) := by
    have hcont : Continuous (Φ' x₀) := by
      simpa [Φ'] using
        (continuous_fderiv_lineDeriv_comp_headCoordSegmentCLM F x₀)
    exact hcont.aestronglyMeasurable
  have hK_compact : IsCompact K :=
    isCompact_Icc.prod (isCompact_closedBall x₀ 1)
  have hΦ'_cont :
      Continuous fun p : ℝ × (Fin (n + 1) → ℝ) => ‖Φ' p.2 p.1‖ := by
    simpa [Φ'] using
      (continuous_fderiv_lineDeriv_comp_headCoordSegmentCLM_uncurry F).norm
  rcases hK_compact.exists_bound_of_continuousOn hΦ'_cont.continuousOn with ⟨C, hC⟩
  have h_bound :
      ∀ᵐ s ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)),
        ∀ x ∈ Metric.closedBall x₀ 1, ‖Φ' x s‖ ≤ C := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall ?_
    intro s hs x hx
    have hs0 : (0 : ℝ) < s := by simpa using hs.1
    have hs1 : s ≤ (1 : ℝ) := by simpa using hs.2
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hs0, hs1⟩
    simpa using hC (s, x) ⟨hsIcc, hx⟩
  have hC_int :
      IntervalIntegrable (fun _ : ℝ => C) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa using intervalIntegrable_const
  have h_diff :
      ∀ᵐ s ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)),
        ∀ x ∈ Metric.closedBall x₀ 1, HasFDerivAt (Φ · s) (Φ' x s) x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall ?_
    intro s hs x hx
    simpa [Φ, Φ'] using
      (hasFDerivAt_lineDeriv_comp_headCoordSegmentCLM F s x)
  have hfun :
      headCoordCoeff F =
        fun x : Fin (n + 1) → ℝ =>
          ∫ s in (0 : ℝ)..1,
            dF (headCoordSegmentCLM n s x) := by
    funext x
    simp [headCoordCoeff, dF, headCoordSegmentCLM_apply]
  rw [hfun]
  simpa [Φ, Φ', dF] using
    (hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (hs := Metric.closedBall_mem_nhds x₀ zero_lt_one)
      (F := Φ) (F' := Φ') (a := (0 : ℝ)) (b := 1)
      hΦ_meas hΦ_int hΦ'_meas h_bound hC_int h_diff)

theorem hasFDerivAt_headCoordCoeffPow {n : ℕ} (r : ℕ)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x₀ : Fin (n + 1) → ℝ) :
    HasFDerivAt
      (headCoordCoeffPow r F)
      (let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
        ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
      ∫ s in (0 : ℝ)..1,
        ((s : ℝ) ^ r : ℂ) •
          ((fderiv ℝ dF (headCoordSegmentCLM n s x₀)).comp
            (headCoordSegmentCLM n s)))
      x₀ := by
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
  let Φ :
      (Fin (n + 1) → ℝ) → ℝ → ℂ :=
    fun x s => ((s : ℝ) ^ r : ℂ) * dF (headCoordSegmentCLM n s x)
  let Φ' :
      (Fin (n + 1) → ℝ) → ℝ →
        ((Fin (n + 1) → ℝ) →L[ℝ] ℂ) :=
    fun x s =>
      ((s : ℝ) ^ r : ℂ) •
        ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
          (headCoordSegmentCLM n s))
  let K : Set (ℝ × (Fin (n + 1) → ℝ)) :=
    Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall x₀ 1
  have hΦ_meas :
      ∀ᶠ x in nhds x₀,
        MeasureTheory.AEStronglyMeasurable (Φ x)
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hcont : Continuous (Φ x) := by
      have hsPow : Continuous fun s : ℝ => (((s : ℝ) ^ r : ℝ) : ℂ) :=
        Complex.ofRealCLM.continuous.comp (continuous_id.pow r)
      simpa [Φ] using hsPow.mul ((SchwartzMap.continuous dF).comp
        (continuous_headCoordSegmentCLM_apply x))
    exact hcont.aestronglyMeasurable
  have hΦ_int :
      IntervalIntegrable (Φ x₀) MeasureTheory.volume (0 : ℝ) 1 := by
    have hcont : Continuous (Φ x₀) := by
      have hsPow : Continuous fun s : ℝ => (((s : ℝ) ^ r : ℝ) : ℂ) :=
        Complex.ofRealCLM.continuous.comp (continuous_id.pow r)
      simpa [Φ] using hsPow.mul ((SchwartzMap.continuous dF).comp
        (continuous_headCoordSegmentCLM_apply x₀))
    exact hcont.intervalIntegrable _ _
  have hΦ'_meas :
      MeasureTheory.AEStronglyMeasurable (Φ' x₀)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)) := by
    have hcont : Continuous (Φ' x₀) := by
      have hsPow : Continuous fun s : ℝ => (((s : ℝ) ^ r : ℝ) : ℂ) :=
        Complex.ofRealCLM.continuous.comp (continuous_id.pow r)
      simpa [Φ'] using hsPow.smul (continuous_fderiv_lineDeriv_comp_headCoordSegmentCLM F x₀)
    exact hcont.aestronglyMeasurable
  have hK_compact : IsCompact K :=
    isCompact_Icc.prod (isCompact_closedBall x₀ 1)
  have hΦ'_cont :
      Continuous fun p : ℝ × (Fin (n + 1) → ℝ) => ‖Φ' p.2 p.1‖ := by
    have hsPow : Continuous fun p : ℝ × (Fin (n + 1) → ℝ) => (((p.1 : ℝ) ^ r : ℝ) : ℂ) :=
      Complex.ofRealCLM.continuous.comp (continuous_fst.pow r)
    simpa [Φ'] using (hsPow.smul
      (continuous_fderiv_lineDeriv_comp_headCoordSegmentCLM_uncurry F)).norm
  rcases hK_compact.exists_bound_of_continuousOn hΦ'_cont.continuousOn with ⟨C, hC⟩
  have h_bound :
      ∀ᵐ s ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)),
        ∀ x ∈ Metric.closedBall x₀ 1, ‖Φ' x s‖ ≤ C := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall ?_
    intro s hs x hx
    have hs0 : (0 : ℝ) < s := by simpa using hs.1
    have hs1 : s ≤ (1 : ℝ) := by simpa using hs.2
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hs0, hs1⟩
    simpa using hC (s, x) ⟨hsIcc, hx⟩
  have hC_int :
      IntervalIntegrable (fun _ : ℝ => C) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa using intervalIntegrable_const
  have h_diff :
      ∀ᵐ s ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)),
        ∀ x ∈ Metric.closedBall x₀ 1, HasFDerivAt (Φ · s) (Φ' x s) x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall ?_
    intro s hs x hx
    simpa [Φ, Φ'] using
      ((hasFDerivAt_lineDeriv_comp_headCoordSegmentCLM F s x).const_smul
        (((s : ℝ) ^ r : ℝ) : ℂ))
  have hfun :
      headCoordCoeffPow r F =
        fun x : Fin (n + 1) → ℝ =>
          ∫ s in (0 : ℝ)..1,
            ((s : ℝ) ^ r : ℂ) * dF (headCoordSegmentCLM n s x) := by
    funext x
    simp [headCoordCoeffPow, dF, headCoordSegmentCLM_apply]
  rw [hfun]
  simpa [Φ, Φ', dF, smul_eq_mul] using
    (hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (hs := Metric.closedBall_mem_nhds x₀ zero_lt_one)
      (F := Φ) (F' := Φ') (a := (0 : ℝ)) (b := 1)
      hΦ_meas hΦ_int hΦ'_meas h_bound hC_int h_diff)

theorem fderiv_headCoordCoeffPow_eq {n r : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x : Fin (n + 1) → ℝ) :
    fderiv ℝ (headCoordCoeffPow r F) x =
      (let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
        ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
      ∫ s in (0 : ℝ)..1,
        ((s : ℝ) ^ r : ℂ) •
          ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
            (headCoordSegmentCLM n s))) :=
  (hasFDerivAt_headCoordCoeffPow r F x).fderiv

theorem continuous_fderiv_headCoordCoeffPow {n r : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    Continuous fun x : Fin (n + 1) → ℝ =>
      fderiv ℝ (headCoordCoeffPow r F) x := by
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
  have huncurry :
      Continuous
        (Function.uncurry
          (fun x : Fin (n + 1) → ℝ =>
            fun s : ℝ =>
              ((s : ℝ) ^ r : ℂ) •
                ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
                  (headCoordSegmentCLM n s)))) := by
    let σ :
        (Fin (n + 1) → ℝ) × ℝ → ℝ × (Fin (n + 1) → ℝ) :=
      fun p => (p.2, p.1)
    have hσ : Continuous σ := Continuous.prodMk continuous_snd continuous_fst
    have hsPow :
        Continuous fun p : (Fin (n + 1) → ℝ) × ℝ => (((p.2 : ℝ) ^ r : ℝ) : ℂ) :=
      Complex.ofRealCLM.continuous.comp (continuous_snd.pow r)
    simpa [Function.uncurry, σ, dF] using
      hsPow.smul ((continuous_fderiv_lineDeriv_comp_headCoordSegmentCLM_uncurry F).comp hσ)
  have hcont :
      Continuous fun x : Fin (n + 1) → ℝ =>
        ∫ s in (0 : ℝ)..1,
          ((s : ℝ) ^ r : ℂ) •
            ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
              (headCoordSegmentCLM n s)) := by
    simpa using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume) (a₀ := (0 : ℝ)) (b₀ := 1) huncurry)
  refine hcont.congr ?_
  intro x
  simpa [dF] using (fderiv_headCoordCoeffPow_eq (r := r) F x).symm

theorem contDiff_one_headCoordCoeffPow {n r : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    ContDiff ℝ 1 (headCoordCoeffPow r F) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_headCoordCoeffPow r F x).differentiableAt,
    continuous_fderiv_headCoordCoeffPow (r := r) F⟩

theorem fderiv_headCoordCoeff_eq {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x : Fin (n + 1) → ℝ) :
    fderiv ℝ (headCoordCoeff F) x =
      (let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
        ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
      ∫ s in (0 : ℝ)..1,
        ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
          (headCoordSegmentCLM n s))) :=
  (hasFDerivAt_headCoordCoeff F x).fderiv

theorem continuous_fderiv_headCoordCoeff {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    Continuous fun x : Fin (n + 1) → ℝ =>
      fderiv ℝ (headCoordCoeff F) x := by
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    ∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F
  have huncurry :
      Continuous
        (Function.uncurry
          (fun x : Fin (n + 1) → ℝ =>
            fun s : ℝ =>
              ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
                (headCoordSegmentCLM n s)))) := by
    let σ :
        (Fin (n + 1) → ℝ) × ℝ → ℝ × (Fin (n + 1) → ℝ) :=
      fun p => (p.2, p.1)
    have hσ : Continuous σ := Continuous.prodMk continuous_snd continuous_fst
    simpa [Function.uncurry, σ, dF] using
      (continuous_fderiv_lineDeriv_comp_headCoordSegmentCLM_uncurry F).comp hσ
  have hcont :
      Continuous fun x : Fin (n + 1) → ℝ =>
        ∫ s in (0 : ℝ)..1,
          ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
            (headCoordSegmentCLM n s)) := by
    simpa using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume) (a₀ := (0 : ℝ)) (b₀ := 1) huncurry)
  refine hcont.congr ?_
  intro x
  simpa [dF] using (fderiv_headCoordCoeff_eq F x).symm

theorem contDiff_one_headCoordCoeff {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    ContDiff ℝ 1 (headCoordCoeff F) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_headCoordCoeff F x).differentiableAt,
    continuous_fderiv_headCoordCoeff F⟩

theorem contDiffOn_headCoordCoeff_off_hyperplane {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF : headSectionCLM n F = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (headCoordCoeff F) {x : Fin (n + 1) → ℝ | x 0 ≠ 0} := by
  let fInv : (Fin (n + 1) → ℝ) → ℂ :=
    (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ Inv.inv ∘ (fun x : Fin (n + 1) → ℝ => x 0)
  have hInv : ContDiffOn ℝ (⊤ : ℕ∞) fInv {x : Fin (n + 1) → ℝ | x 0 ≠ 0} := by
    have hproj :
        ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Fin (n + 1) → ℝ => x 0)
          {x : Fin (n + 1) → ℝ | x 0 ≠ 0} := by
      exact (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1))
        (φ := fun _ => ℝ) 0).contDiff.contDiffOn
    have hInvReal :
        ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Fin (n + 1) → ℝ => (x 0 : ℝ)⁻¹)
          {x : Fin (n + 1) → ℝ | x 0 ≠ 0} := by
      exact
        ((contDiffOn_inv (𝕜 := ℝ) (𝕜' := ℝ) (n := (⊤ : ℕ∞)) :
            ContDiffOn ℝ (⊤ : ℕ∞) (Inv.inv : ℝ → ℝ) ({0}ᶜ)).comp hproj
          (by
            intro x hx
            simpa [Set.mem_setOf_eq] using hx))
    have hOfReal :
        ContDiffOn ℝ (⊤ : ℕ∞) (fun r : ℝ => (r : ℂ)) Set.univ := by
      simpa using ((Complex.ofRealCLM.contDiff.of_le le_top :
        ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => (r : ℂ))).contDiffOn)
    have hMaps :
        Set.MapsTo (fun x : Fin (n + 1) → ℝ => (x 0 : ℝ)⁻¹)
          {x : Fin (n + 1) → ℝ | x 0 ≠ 0} Set.univ := by
      intro x hx
      simp
    simpa [fInv] using hOfReal.comp hInvReal hMaps
  have hmul :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x : Fin (n + 1) → ℝ => fInv x * F x)
        {x : Fin (n + 1) → ℝ | x 0 ≠ 0} := by
    exact hInv.mul ((F.smooth (⊤ : ℕ∞)).contDiffOn)
  refine hmul.congr ?_
  intro x hx
  rw [headCoordCoeff_eq_inv_smul_of_ne_zero F hF x hx]
  simp [fInv]

/-- Translation-invariant continuous Schwartz functionals. -/
def IsTranslationInvariantSchwartzCLM {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  ∀ a : Fin m → ℝ, T.comp (SCV.translateSchwartzCLM a) = T

theorem integralCLM_translation_invariant {m : ℕ} :
    IsTranslationInvariantSchwartzCLM
      (SchwartzMap.integralCLM ℂ (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
  intro a
  ext f
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
  change ∫ x : Fin m → ℝ, SCV.translateSchwartz a f x = ∫ x : Fin m → ℝ, f x
  simpa [SCV.translateSchwartz_apply] using
    (MeasureTheory.integral_add_right_eq_self
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (fun x : Fin m → ℝ => f x) a)

theorem iteratedFDeriv_lineDeriv_eq_snoc {m n : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v x : Fin m → ℝ) (u : Fin n → Fin m → ℝ) :
    iteratedFDeriv ℝ n (((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ)) x u =
      iteratedFDeriv ℝ (n + 1) (f : (Fin m → ℝ) → ℂ) x (Fin.snoc u v) := by
  have hsucc :
      (∂^{Fin.snoc u v} f : SchwartzMap (Fin m → ℝ) ℂ) = ∂^{u} (∂_{v} f) := by
    simpa using (LineDeriv.iteratedLineDerivOp_succ_right (m := Fin.snoc u v) (f := f))
  have hsucc_apply := congrArg (fun g : SchwartzMap (Fin m → ℝ) ℂ => g x) hsucc
  simpa [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
      (f := f) (m := Fin.snoc u v) (x := x),
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
      (f := (∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ)) (m := u) (x := x)] using hsucc_apply.symm

/-- A first-order translation estimate in Schwartz seminorms. This is the core
quantitative input behind the difference-quotient convergence theorem. -/
theorem exists_seminorm_translateSchwartz_sub_le_linear {m : ℕ}
    (g : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, |t| ≤ 1 →
        SchwartzMap.seminorm ℝ k n (SCV.translateSchwartz (t • v) g - g) ≤ C * |t| := by
  obtain ⟨D, hD_nonneg, hD⟩ := SCV.seminorm_translateSchwartz_le (m := m) k (n + 1) g
  let C : ℝ := ‖v‖ * D * (1 + ‖v‖) ^ k
  refine ⟨C, by positivity, ?_⟩
  intro t ht
  refine SchwartzMap.seminorm_le_bound ℝ k n (SCV.translateSchwartz (t • v) g - g)
    (by positivity) ?_
  intro x
  let H :
      (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    iteratedFDeriv ℝ n (g : (Fin m → ℝ) → ℂ)
  let hxFun : ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun s => ‖x‖ ^ k • H (x + s • (t • v))
  have hH_diff : Differentiable ℝ H := by
    simpa [H] using
      (g.smooth (n + 1)).differentiable_iteratedFDeriv (by
        exact_mod_cast Nat.lt_succ_self n)
  have hxFun_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt hxFun
          (‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))) s := by
    intro s
    have hgamma :
        HasDerivAt (fun r : ℝ => x + r • (t • v)) (t • v) s := by
      let L : ℝ →L[ℝ] (Fin m → ℝ) :=
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (t • v)
      simpa [L, ContinuousLinearMap.smulRight_apply, one_smul, add_comm, add_left_comm, add_assoc]
        using (L.hasDerivAt).const_add x
    have hcomp :
        HasDerivAt (fun r : ℝ => H (x + r • (t • v)))
          ((fderiv ℝ H (x + s • (t • v))) (t • v)) s := by
      exact (hH_diff (x + s • (t • v))).hasFDerivAt.comp_hasDerivAt s hgamma
    simpa [hxFun] using hcomp.const_smul (‖x‖ ^ k)
  have hxFun_bound :
      ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))‖ ≤ C * |t| := by
    intro s hs
    have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_of_lt hs.2⟩
    have hs_abs : |s| ≤ 1 := by
      have hs0 : 0 ≤ s := hs.1
      have hs1 : s ≤ 1 := le_of_lt hs.2
      rw [abs_of_nonneg hs0]
      exact hs1
    have hstv_norm : ‖s • (t • v)‖ ≤ ‖v‖ := by
      calc
        ‖s • (t • v)‖ = |s| * (|t| * ‖v‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * (1 * ‖v‖) := by
          gcongr
        _ = ‖v‖ := by ring
    have hone_pow :
        (1 + ‖s • (t • v)‖) ^ k ≤ (1 + ‖v‖) ^ k := by
      gcongr
    have hseminorm0 :
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (⇑(SCV.translateSchwartz (s • (t • v)) g)) x‖ ≤
          D * (1 + ‖s • (t • v)‖) ^ k := by
      exact le_trans (SchwartzMap.le_seminorm ℂ k (n + 1) _ x) (hD (s • (t • v)))
    have hseminorm :
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (g : (Fin m → ℝ) → ℂ) (x + s • (t • v))‖ ≤
          D * (1 + ‖s • (t • v)‖) ^ k := by
      have htrans :
          iteratedFDeriv ℝ (n + 1) (⇑(SCV.translateSchwartz (s • (t • v)) g)) x =
            iteratedFDeriv ℝ (n + 1) (g : (Fin m → ℝ) → ℂ) (x + s • (t • v)) := by
        simpa [SCV.translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := (g : (Fin m → ℝ) → ℂ)) (n + 1) (s • (t • v)) x)
      simpa [htrans] using hseminorm0
    have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
    calc
      ‖‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))‖
          = ‖x‖ ^ k * ‖(fderiv ℝ H (x + s • (t • v))) (t • v)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hxpow_nonneg]
      _ ≤ ‖x‖ ^ k * (‖fderiv ℝ H (x + s • (t • v))‖ * ‖t • v‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm _ _
      _ = (‖x‖ ^ k * ‖fderiv ℝ H (x + s • (t • v))‖) * ‖t • v‖ := by ring
      _ = (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (g : (Fin m → ℝ) → ℂ)
            (x + s • (t • v))‖) * ‖t • v‖ := by
            rw [norm_fderiv_iteratedFDeriv]
      _ ≤ (D * (1 + ‖s • (t • v)‖) ^ k) * ‖t • v‖ := by
            gcongr
      _ ≤ (D * (1 + ‖v‖) ^ k) * ‖t • v‖ := by
            gcongr
      _ = (D * (1 + ‖v‖) ^ k) * (|t| * ‖v‖) := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = C * |t| := by
            dsimp [C]
            ring
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := hxFun)
      (f' := fun s => ‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v)))
      (fun s hs => (hxFun_hasDeriv s).hasDerivWithinAt)
      hxFun_bound
  have hiter_eq :
      iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) g - g)) x =
        H (x + t • v) - H x := by
    have hf : ContDiff ℝ n (⇑(SCV.translateSchwartz (t • v) g)) :=
      (SCV.translateSchwartz (t • v) g).smooth n
    have hg : ContDiff ℝ n (⇑g) := g.smooth n
    have hfg :
        (⇑(SCV.translateSchwartz (t • v) g - g) : (Fin m → ℝ) → ℂ) =
          (⇑(SCV.translateSchwartz (t • v) g)) + fun z => -(⇑g z) := by
      ext z
      simp [sub_eq_add_neg]
    have hneg : (fun z => -(⇑g z)) = -⇑g := rfl
    rw [hfg, iteratedFDeriv_add_apply hf.contDiffAt hg.neg.contDiffAt, hneg, iteratedFDeriv_neg_apply]
    have htrans :
        iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) g)) x =
          H (x + t • v) := by
      simpa [H, SCV.translateSchwartz] using
        (iteratedFDeriv_comp_add_right (f := (g : (Fin m → ℝ) → ℂ)) n (t • v) x)
    simp [H, htrans, sub_eq_add_neg]
  have hxFun_diff :
      hxFun 1 - hxFun 0 = ‖x‖ ^ k • (H (x + t • v) - H x) := by
    simp [hxFun, smul_sub]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) g - g)) x‖
        = ‖hxFun 1 - hxFun 0‖ := by
            rw [hxFun_diff, hiter_eq, norm_smul, Real.norm_eq_abs]
            have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
            simp [abs_of_nonneg hxpow_nonneg]
    _ ≤ C * |t| := by simpa [sub_eq_add_neg] using hmv

/-- A clean polynomial-weight shift bound used in the Taylor remainder route for
translation difference quotients. -/
theorem weight_shift_bound {m : ℕ}
    (k : ℕ) (x h v : Fin m → ℝ) (hh : ‖h‖ ≤ ‖v‖) :
    (1 + ‖x‖) ^ k ≤ (1 + ‖v‖) ^ k * (1 + ‖x + h‖) ^ k := by
  have h1 : 1 + ‖x‖ ≤ (1 + ‖v‖) * (1 + ‖x + h‖) := by
    have hx : ‖x‖ ≤ ‖x + h‖ + ‖h‖ := by
      calc
        ‖x‖ = ‖(x + h) - h‖ := by congr 1; abel
        _ ≤ ‖x + h‖ + ‖h‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (x + h), norm_nonneg v]
  calc
    (1 + ‖x‖) ^ k ≤ ((1 + ‖v‖) * (1 + ‖x + h‖)) ^ k := by
      gcongr
    _ = (1 + ‖v‖) ^ k * (1 + ‖x + h‖) ^ k := mul_pow _ _ _

/-- Directional derivatives of Schwartz functions commute. -/
theorem lineDerivOp_comm {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v w : Fin m → ℝ) :
    ∂_{v} ((∂_{w} f : SchwartzMap (Fin m → ℝ) ℂ)) =
      ∂_{w} ((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ)) := by
  ext x
  have hsym :=
    (f.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} f : SchwartzMap (Fin m → ℝ) ℂ))) x = (∂^{![v, w]} f) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2 (f : (Fin m → ℝ) → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2 (f : (Fin m → ℝ) → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} f) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

/-- A single directional derivative commutes past an iterated directional derivative. -/
theorem lineDerivOp_iterated_comm {m n : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) (u : Fin n → Fin m → ℝ) :
    ∂_{v} (∂^{u} f) = ∂^{u} (∂_{v} f) := by
  induction n generalizing f with
  | zero =>
      ext x
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_right,
        LineDeriv.iteratedLineDerivOp_succ_right]
      rw [ih (f := ∂_{u (Fin.last n)} f)]
      congr 1
      exact lineDerivOp_comm f v (u (Fin.last n))

theorem fderiv_headCoordCoeffPow_apply_tail {n r : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (u : Fin n → ℝ) (x : Fin (n + 1) → ℝ) :
    (fderiv ℝ (headCoordCoeffPow r F) x) (tailInsertCLM n u) =
      headCoordCoeffPow r
        (∂_{((tailInsertCLM n u : Fin (n + 1) → ℝ))} F) x := by
  let e0 : Fin (n + 1) → ℝ := Pi.single 0 (1 : ℝ)
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ := ∂_{e0} F
  let v : Fin (n + 1) → ℝ := tailInsertCLM n u
  have hInt :
      IntervalIntegrable
        (fun s : ℝ =>
          ((s : ℝ) ^ r : ℂ) •
            ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
              (headCoordSegmentCLM n s)))
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hcont : Continuous fun s : ℝ =>
        ((s : ℝ) ^ r : ℂ) •
          ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
            (headCoordSegmentCLM n s)) := by
      have hsPow : Continuous fun s : ℝ => (((s : ℝ) ^ r : ℝ) : ℂ) :=
        Complex.ofRealCLM.continuous.comp (continuous_id.pow r)
      simpa using hsPow.smul (continuous_fderiv_lineDeriv_comp_headCoordSegmentCLM F x)
    exact hcont.intervalIntegrable _ _
  have hcomm : ∂_{v} dF = ∂_{e0} (∂_{v} F) := by
    simpa [dF] using (lineDerivOp_comm F v e0)
  calc
    (fderiv ℝ (headCoordCoeffPow r F) x) v
        = (∫ s in (0 : ℝ)..1,
            (((s : ℝ) ^ r : ℂ) •
              ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
                (headCoordSegmentCLM n s)))) v := by
              rw [hasFDerivAt_headCoordCoeffPow r F x |>.fderiv]
    _ = ∫ s in (0 : ℝ)..1,
          ((((s : ℝ) ^ r : ℂ) •
            ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
              (headCoordSegmentCLM n s))) v) := by
          exact (ContinuousLinearMap.intervalIntegral_apply hInt v)
    _ = ∫ s in (0 : ℝ)..1,
          ((s : ℝ) ^ r : ℂ) *
            ((fderiv ℝ dF (headCoordSegmentCLM n s x)) v) := by
          congr 1
          ext s
          have hsegv : (headCoordSegmentCLM n s) v = v := by
            ext j
            refine Fin.cases ?_ ?_ j
            · simp [v, headCoordSegmentCLM_apply, tailInsertCLM_apply]
            · intro i
              simp [v, headCoordSegmentCLM_apply, tailInsertCLM_apply]
          simp [hsegv]
    _ = ∫ s in (0 : ℝ)..1,
          ((s : ℝ) ^ r : ℂ) *
            (∂_{e0} (∂_{v} F)) (headCoordSegmentCLM n s x) := by
          congr 1
          ext s
          have hcomm_at :
              (∂_{v} dF) (headCoordSegmentCLM n s x) =
                (∂_{e0} (∂_{v} F)) (headCoordSegmentCLM n s x) := by
            simpa using
              congrArg
                (fun G : SchwartzMap (Fin (n + 1) → ℝ) ℂ =>
                  G (headCoordSegmentCLM n s x))
                hcomm
          simpa [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
            congrArg (fun z : ℂ => ((s : ℝ) ^ r : ℂ) * z) hcomm_at
    _ = headCoordCoeffPow r (∂_{v} F) x := by
          simp [headCoordCoeffPow, e0, v, headCoordSegmentCLM_apply]

theorem fderiv_headCoordCoeffPow_apply_head {n r : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x : Fin (n + 1) → ℝ) :
    (fderiv ℝ (headCoordCoeffPow r F) x) ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ) =
      headCoordCoeffPow (r + 1)
        (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F) x := by
  let e0 : Fin (n + 1) → ℝ := Pi.single 0 (1 : ℝ)
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ := ∂_{e0} F
  have hInt :
      IntervalIntegrable
        (fun s : ℝ =>
          ((s : ℝ) ^ r : ℂ) •
            ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
              (headCoordSegmentCLM n s)))
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hcont : Continuous fun s : ℝ =>
        ((s : ℝ) ^ r : ℂ) •
          ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
            (headCoordSegmentCLM n s)) := by
      have hsPow : Continuous fun s : ℝ => (((s : ℝ) ^ r : ℝ) : ℂ) :=
        Complex.ofRealCLM.continuous.comp (continuous_id.pow r)
      simpa using hsPow.smul (continuous_fderiv_lineDeriv_comp_headCoordSegmentCLM F x)
    exact hcont.intervalIntegrable _ _
  calc
    (fderiv ℝ (headCoordCoeffPow r F) x) e0
        = (∫ s in (0 : ℝ)..1,
            (((s : ℝ) ^ r : ℂ) •
              ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
                (headCoordSegmentCLM n s)))) e0 := by
              rw [hasFDerivAt_headCoordCoeffPow r F x |>.fderiv]
    _ = ∫ s in (0 : ℝ)..1,
          ((((s : ℝ) ^ r : ℂ) •
            ((fderiv ℝ dF (headCoordSegmentCLM n s x)).comp
              (headCoordSegmentCLM n s))) e0) := by
          exact (ContinuousLinearMap.intervalIntegral_apply hInt e0)
    _ = ∫ s in (0 : ℝ)..1,
          ((s : ℝ) ^ (r + 1) : ℂ) *
            ((fderiv ℝ dF (headCoordSegmentCLM n s x)) e0) := by
          congr 1
          ext s
          have hseg :
              (headCoordSegmentCLM n s) e0 = s • e0 := by
            ext j
            refine Fin.cases ?_ ?_ j
            · simp [e0, headCoordSegmentCLM_apply]
            · intro i
              simp [e0, headCoordSegmentCLM_apply]
          rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hseg,
            ContinuousLinearMap.map_smul, Complex.real_smul]
          simp [smul_eq_mul, pow_succ, mul_assoc, mul_left_comm, mul_comm]
    _ = ∫ s in (0 : ℝ)..1,
          ((s : ℝ) ^ (r + 1) : ℂ) *
            (∂_{e0} dF) (headCoordSegmentCLM n s x) := by
          simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    _ = headCoordCoeffPow (r + 1) dF x := by
          simp [headCoordCoeffPow, dF, e0, headCoordSegmentCLM_apply]

theorem head_tail_decomposition {n : ℕ} (y : Fin (n + 1) → ℝ) :
    y = (y 0) • ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ) +
      tailInsertCLM n (tailCLM n y) := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [tailInsertCLM_apply]
  · intro i
    simp [tailInsertCLM_apply, tailCLM_apply]

theorem fderiv_headCoordCoeffPow_apply {n r : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x y : Fin (n + 1) → ℝ) :
    (fderiv ℝ (headCoordCoeffPow r F) x) y =
      (y 0 : ℝ) •
        headCoordCoeffPow (r + 1)
          (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F) x
      + headCoordCoeffPow r
          (∂_{(tailInsertCLM n (tailCLM n y) : Fin (n + 1) → ℝ)} F) x := by
  let e0 : Fin (n + 1) → ℝ := (Pi.single 0 (1 : ℝ))
  calc
    (fderiv ℝ (headCoordCoeffPow r F) x) y
        = (fderiv ℝ (headCoordCoeffPow r F) x)
            ((y 0) • e0 + tailInsertCLM n (tailCLM n y)) := by
              simpa [e0] using
                congrArg (fderiv ℝ (headCoordCoeffPow r F) x)
                  (head_tail_decomposition y)
    _ = (fderiv ℝ (headCoordCoeffPow r F) x) ((y 0) • e0) +
          (fderiv ℝ (headCoordCoeffPow r F) x)
            (tailInsertCLM n (tailCLM n y)) := by
              rw [ContinuousLinearMap.map_add]
    _ = (y 0 : ℝ) • (fderiv ℝ (headCoordCoeffPow r F) x) e0 +
          (fderiv ℝ (headCoordCoeffPow r F) x)
            (tailInsertCLM n (tailCLM n y)) := by
              rw [ContinuousLinearMap.map_smul]
    _ = (y 0 : ℝ) •
          headCoordCoeffPow (r + 1)
            (∂_{e0} F) x +
          headCoordCoeffPow r
            (∂_{(tailInsertCLM n (tailCLM n y) : Fin (n + 1) → ℝ)} F) x := by
              rw [fderiv_headCoordCoeffPow_apply_head, fderiv_headCoordCoeffPow_apply_tail]

theorem contDiff_nat_headCoordCoeffPow {n m : ℕ}
    (r : ℕ) (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    ContDiff ℝ m (headCoordCoeffPow r F) := by
  induction m generalizing r F with
  | zero =>
      exact contDiff_zero.2 (continuous_headCoordCoeffPow r F)
  | succ m ih =>
      simpa using
        (contDiff_succ_iff_fderiv_apply
          (𝕜 := ℝ) (D := Fin (n + 1) → ℝ)
          (n := (m : ℕ∞)) (f := headCoordCoeffPow r F)).2 <|
          ⟨fun x => (hasFDerivAt_headCoordCoeffPow r F x).differentiableAt, by simp,
            fun y =>
              by
                have hEq :
                    (fun x : Fin (n + 1) → ℝ => (fderiv ℝ (headCoordCoeffPow r F) x) y)
                      =
                    fun x : Fin (n + 1) → ℝ =>
                      (y 0 : ℝ) •
                        headCoordCoeffPow (r + 1)
                          (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F) x
                      + headCoordCoeffPow r
                          (∂_{(tailInsertCLM n (tailCLM n y) : Fin (n + 1) → ℝ)} F) x := by
                  funext x
                  exact fderiv_headCoordCoeffPow_apply (r := r) F x y
                rw [hEq]
                exact
                  ((ih (r + 1) (∂_{((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)} F)).const_smul
                      (y 0)).add
                    (ih r (∂_{(tailInsertCLM n (tailCLM n y) : Fin (n + 1) → ℝ)} F))⟩

theorem contDiff_headCoordCoeffPow {n r : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (headCoordCoeffPow r F) := by
  rw [contDiff_infty]
  intro m
  exact contDiff_nat_headCoordCoeffPow (r := r) (F := F)

theorem exists_eq_coord_smul_of_headSection_zero_of_hasCompactSupport {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF : headSectionCLM n F = 0)
    (hFcs : HasCompactSupport F) :
    ∃ H : SchwartzMap (Fin (n + 1) → ℝ) ℂ,
      F = SchwartzMap.smulLeftCLM ℂ (fun x : Fin (n + 1) → ℝ => x 0) H := by
  refine ⟨(hasCompactSupport_headCoordCoeff F hF hFcs).toSchwartzMap
    (by simpa [headCoordCoeffPow_zero] using (contDiff_headCoordCoeffPow (r := 0) F)), ?_⟩
  ext x
  have htemp : Function.HasTemperateGrowth (fun x : Fin (n + 1) → ℝ => x 0) :=
    (headCoordProjCLM n).hasTemperateGrowth
  simpa [headCoordCoeffPow_zero, SchwartzMap.smulLeftCLM_apply_apply htemp, Complex.real_smul,
      smul_eq_mul] using
    (eq_head_coord_smul_headCoordCoeff_of_headSection_zero (n := n) F hF x)

/-- Differentiating the `n`-th iterated derivative of a Schwartz function in the
direction `v` agrees with taking the `n`-th iterated derivative of `∂_{v} f`. -/
theorem fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv {m n : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v x : Fin m → ℝ) :
    fderiv ℝ (iteratedFDeriv ℝ n (f : (Fin m → ℝ) → ℂ)) x v =
      iteratedFDeriv ℝ n (((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ)) x := by
  ext u
  calc
    (fderiv ℝ (iteratedFDeriv ℝ n (f : (Fin m → ℝ) → ℂ)) x v) u
        = iteratedFDeriv ℝ (n + 1) (f : (Fin m → ℝ) → ℂ) x (Fin.cons v u) := by
            simp [iteratedFDeriv_succ_apply_left]
    _ = (∂^{Fin.cons v u} f) x := by
            symm
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := f) (m := Fin.cons v u) (x := x))
    _ = (∂_{v} (∂^{u} f)) x := by
            simpa using (congrArg (fun g : SchwartzMap (Fin m → ℝ) ℂ => g x)
              (LineDeriv.iteratedLineDerivOp_succ_left (m := Fin.cons v u) (f := f)))
    _ = (∂^{u} (∂_{v} f)) x := by
            rw [lineDerivOp_iterated_comm (f := f) (v := v) (u := u)]
    _ = iteratedFDeriv ℝ n
          (((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ)) x u := by
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := (∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ)) (m := u) (x := x))

/-- The key first-order translation estimate behind the derivative route:
every Schwartz seminorm of the translation difference quotient error should be
`O(|t|)` near `0`. -/
theorem exists_seminorm_diffQuotient_translateSchwartz_sub_lineDeriv_le {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
        SchwartzMap.seminorm ℝ k n
          (t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f) ≤ C * |t| := by
  let g : SchwartzMap (Fin m → ℝ) ℂ := ∂_{v} f
  obtain ⟨C, hC_nonneg, hC⟩ := exists_seminorm_translateSchwartz_sub_le_linear g v k n
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_ne ht_abs
  refine SchwartzMap.seminorm_le_bound ℝ k n
    (t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f)
    (by positivity) ?_
  intro x
  let H :
      (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    iteratedFDeriv ℝ n (f : (Fin m → ℝ) → ℂ)
  let K :
      (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    iteratedFDeriv ℝ n (g : (Fin m → ℝ) → ℂ)
  let ψ : ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun s => ‖x‖ ^ k • (t⁻¹ • H (x + s • (t • v)) - t⁻¹ • H x) - ‖x‖ ^ k • (s • K x)
  have hH_diff : Differentiable ℝ H := by
    simpa [H] using
      (f.smooth (n + 1)).differentiable_iteratedFDeriv (by
        exact_mod_cast Nat.lt_succ_self n)
  have hpsi_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt ψ (‖x‖ ^ k • (K (x + s • (t • v)) - K x)) s := by
    intro s
    have hgamma :
        HasDerivAt (fun r : ℝ => x + r • (t • v)) (t • v) s := by
      let L : ℝ →L[ℝ] (Fin m → ℝ) :=
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (t • v)
      simpa [L, ContinuousLinearMap.smulRight_apply, one_smul, add_comm, add_left_comm, add_assoc]
        using (L.hasDerivAt).const_add x
    have hcomp :
        HasDerivAt (fun r : ℝ => H (x + r • (t • v)))
          ((fderiv ℝ H (x + s • (t • v))) (t • v)) s := by
      exact (hH_diff (x + s • (t • v))).hasFDerivAt.comp_hasDerivAt s hgamma
    have hmain0 :
        HasDerivAt
          (fun r : ℝ => t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x)
          (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) s := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_sub] using
        (hcomp.const_smul t⁻¹).sub_const (t⁻¹ • H x)
    have hscale :
        t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v)) =
          K (x + s • (t • v)) := by
      calc
        t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))
            = t⁻¹ • (t • ((fderiv ℝ H (x + s • (t • v))) v)) := by
                rw [ContinuousLinearMap.map_smul]
        _ = (t⁻¹ * t) • ((fderiv ℝ H (x + s • (t • v))) v) := by
                rw [smul_smul]
        _ = (fderiv ℝ H (x + s • (t • v))) v := by
                rw [inv_mul_cancel₀ ht_ne, one_smul]
        _ = K (x + s • (t • v)) := by
                rw [fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv
                  (f := f) (v := v) (x := x + s • (t • v))]
    have hlin :
        HasDerivAt (fun r : ℝ => r • K x) (K x) s := by
      simpa [one_smul] using (hasDerivAt_id s).smul_const (K x)
    have hsub' :
        HasDerivAt
          (fun r : ℝ =>
            ‖x‖ ^ k • (t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x) - ‖x‖ ^ k • (r • K x))
          (‖x‖ ^ k • (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) - ‖x‖ ^ k • K x) s := by
      convert (hmain0.const_smul (‖x‖ ^ k)).sub (hlin.const_smul (‖x‖ ^ k)) using 1
    have hsub :
        HasDerivAt
          (fun r : ℝ =>
            ‖x‖ ^ k • (t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x) - ‖x‖ ^ k • (r • K x))
          (‖x‖ ^ k • (K (x + s • (t • v)) - K x)) s := by
      convert hsub' using 1
      calc
        ‖x‖ ^ k • (K (x + s • (t • v)) - K x)
            = ‖x‖ ^ k • K (x + s • (t • v)) - ‖x‖ ^ k • K x := by
                rw [smul_sub]
        _ = ‖x‖ ^ k • (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) - ‖x‖ ^ k • K x := by
                rw [hscale]
    exact hsub
  have hpsi_bound :
      ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖‖x‖ ^ k • (K (x + s • (t • v)) - K x)‖ ≤ C * |t| := by
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1
    have hs_le_one : s ≤ 1 := le_of_lt hs.2
    have hs_abs : |s| ≤ 1 := by
      rw [abs_of_nonneg hs_nonneg]
      exact hs_le_one
    have hst_abs : |s * t| ≤ 1 := by
      calc
        |s * t| = |s| * |t| := by rw [abs_mul]
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    have hiter_eq :
        iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz ((s * t) • v) g - g)) x =
          K (x + s • (t • v)) - K x := by
      have hshift :
          iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz ((s * t) • v) g)) x =
            K (x + s • (t • v)) := by
        simpa [K, SCV.translateSchwartz, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          (iteratedFDeriv_comp_add_right (f := (g : (Fin m → ℝ) → ℂ)) n ((s * t) • v) x)
      rw [show (⇑(SCV.translateSchwartz ((s * t) • v) g - g) : (Fin m → ℝ) → ℂ) =
            (⇑(SCV.translateSchwartz ((s * t) • v) g)) + fun z => -(⇑g z) by
              ext z; simp [sub_eq_add_neg]]
      rw [iteratedFDeriv_add_apply
          ((SCV.translateSchwartz ((s * t) • v) g).smooth n).contDiffAt
          (g.smooth n).neg.contDiffAt]
      rw [show (fun z => -(⇑g z)) = -⇑g by rfl, iteratedFDeriv_neg_apply]
      simp [K, hshift, sub_eq_add_neg]
    have hpoint :
        ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖ ≤ C * |s * t| := by
      calc
        ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖
            = ‖x‖ ^ k *
                ‖iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz ((s * t) • v) g - g)) x‖ := by
                  rw [hiter_eq]
        _ ≤ SchwartzMap.seminorm ℝ k n (SCV.translateSchwartz ((s * t) • v) g - g) := by
              exact SchwartzMap.le_seminorm ℂ k n _ x
        _ ≤ C * |s * t| := hC (s * t) hst_abs
    calc
      ‖‖x‖ ^ k • (K (x + s • (t • v)) - K x)‖
          = ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖ := by
              rw [norm_smul, Real.norm_eq_abs]
              have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
              simp [abs_of_nonneg hxpow_nonneg]
      _ ≤ C * |s * t| := hpoint
      _ = C * (|s| * |t|) := by rw [abs_mul]
      _ ≤ C * |t| := by
            have hs_t : |s| * |t| ≤ |t| := by
              simpa [one_mul] using
                (mul_le_mul_of_nonneg_right hs_abs (abs_nonneg t))
            gcongr
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (hf := fun s hs => (hpsi_hasDeriv s).hasDerivWithinAt)
      (bound := hpsi_bound)
  have htarget :
      iteratedFDeriv ℝ n
        (↑(t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f) :
          (Fin m → ℝ) → ℂ) x =
        t⁻¹ • (H (x + t • v) - H x) - K x := by
    have hshift_sub :
        iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) f - f)) x =
          H (x + t • v) - H x := by
      have hshift :
          iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) f)) x = H (x + t • v) := by
        simpa [H, SCV.translateSchwartz] using
          (iteratedFDeriv_comp_add_right (f := (f : (Fin m → ℝ) → ℂ)) n (t • v) x)
      rw [show (⇑(SCV.translateSchwartz (t • v) f - f) : (Fin m → ℝ) → ℂ) =
            (⇑(SCV.translateSchwartz (t • v) f)) + fun z => -(⇑f z) by
              ext z; simp [sub_eq_add_neg]]
      rw [iteratedFDeriv_add_apply ((SCV.translateSchwartz (t • v) f).smooth n).contDiffAt
          (f.smooth n).neg.contDiffAt]
      rw [show (fun z => -(⇑f z)) = -⇑f by rfl, iteratedFDeriv_neg_apply]
      simp [H, hshift, sub_eq_add_neg]
    change
      iteratedFDeriv ℝ n
        (⇑(t⁻¹ • (SCV.translateSchwartz (t • v) f - f)) + fun z => -((g : (Fin m → ℝ) → ℂ) z)) x =
        t⁻¹ • (H (x + t • v) - H x) - K x
    rw [iteratedFDeriv_add_apply
      ((t⁻¹ • (SCV.translateSchwartz (t • v) f - f)).smooth n).contDiffAt
      (g.smooth n).neg.contDiffAt]
    have hsc :
        iteratedFDeriv ℝ n (⇑(t⁻¹ • (SCV.translateSchwartz (t • v) f - f))) x =
          t⁻¹ • iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) f - f)) x := by
      change iteratedFDeriv ℝ n (t⁻¹ • (⇑(SCV.translateSchwartz (t • v) f - f))) x =
        t⁻¹ • iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) f - f)) x
      rw [iteratedFDeriv_const_smul_apply ((SCV.translateSchwartz (t • v) f - f).smooth n).contDiffAt]
    have hneg :
        iteratedFDeriv ℝ n (fun z => -((g : (Fin m → ℝ) → ℂ) z)) x = - K x := by
      simpa [K] using
        (iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := n) (f := (g : (Fin m → ℝ) → ℂ)) (x := x))
    rw [hsc, hneg, hshift_sub]
    simp [sub_eq_add_neg, add_left_comm, add_comm]
  have hψ0 : ψ 0 = 0 := by
    ext u
    simp [ψ]
  have hψ1 :
      ψ 1 =
        ‖x‖ ^ k •
          iteratedFDeriv ℝ n
            (↑(t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f) :
              (Fin m → ℝ) → ℂ) x := by
    rw [show ψ 1 =
          ‖x‖ ^ k • (t⁻¹ • (H (x + t • v) - H x) - K x) by
            simp [ψ, sub_eq_add_neg, add_left_comm, add_comm]]
    rw [htarget]
  calc
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (↑(t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f) :
            (Fin m → ℝ) → ℂ) x‖
        = ‖ψ 1 - ψ 0‖ := by
            rw [hψ0, hψ1, sub_zero, norm_smul, Real.norm_eq_abs]
            have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
            simp [abs_of_nonneg hxpow_nonneg]
    _ ≤ C * |t| := hmv

noncomputable def unitBumpSchwartz : SchwartzMap ℝ ℂ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : ℝ → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

theorem unitBumpSchwartz_zero : unitBumpSchwartz 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hf_smooth : ContDiff ℝ (⊤ : ENat) (fun x : ℝ => (b x : ℂ)) := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport (fun x : ℝ => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have happly :
      unitBumpSchwartz 0 = ((fun x : ℝ => (b x : ℂ)) 0) := by
    simpa [unitBumpSchwartz, b] using
      (HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth 0)
  rw [happly]
  have hball : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) (1 : ℝ) := by
    simp [Metric.mem_closedBall]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.one_of_mem_closedBall hball)

noncomputable def unitBallBumpSchwartzPi (m : ℕ) :
    SchwartzMap (Fin m → ℝ) ℂ := by
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

theorem unitBallBumpSchwartzPi_one_of_mem_closedBall {m : ℕ}
    {x : Fin m → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) 1) :
    unitBallBumpSchwartzPi m x = 1 := by
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun y => (b y : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have happly :
      unitBallBumpSchwartzPi m x = f x := by
    simpa [unitBallBumpSchwartzPi, b, f] using
      (HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x)
  rw [happly]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.one_of_mem_closedBall hx)

theorem hasCompactSupport_unitBallBumpSchwartzPi (m : ℕ) :
    HasCompactSupport ((unitBallBumpSchwartzPi m : SchwartzMap (Fin m → ℝ) ℂ) :
      (Fin m → ℝ) → ℂ) := by
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  simpa [unitBallBumpSchwartzPi, b, f] using hf_compact

/-- The unit-ball Schwartz bump rescaled to radius `R`. -/
noncomputable def unitBallBumpSchwartzPiRadius (m : ℕ) (R : ℝ) (hR : 0 < R) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')).symm
    (unitBallBumpSchwartzPi m)

@[simp] theorem unitBallBumpSchwartzPiRadius_apply {m : ℕ} (R : ℝ) (hR : 0 < R)
    (x : Fin m → ℝ) :
    unitBallBumpSchwartzPiRadius m R hR x =
      unitBallBumpSchwartzPi m (R⁻¹ • x) := by
  rw [unitBallBumpSchwartzPiRadius, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hsmul :
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin m → ℝ)
          (Units.mk0 R hR.ne')).symm) x) = R⁻¹ • x := by
    rw [show (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin m → ℝ)
          (Units.mk0 R hR.ne')).symm) x) = ((↑((Units.mk0 R hR.ne')⁻¹) : ℝ) • x) by rfl]
    simp [Units.val_inv_eq_inv_val]
  simpa [Function.comp] using congrArg (unitBallBumpSchwartzPi m) hsmul

theorem unitBallBumpSchwartzPiRadius_one_of_mem_closedBall {m : ℕ}
    {R : ℝ} (hR : 0 < R) {x : Fin m → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) R) :
    unitBallBumpSchwartzPiRadius m R hR x = 1 := by
  rw [unitBallBumpSchwartzPiRadius_apply]
  apply unitBallBumpSchwartzPi_one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_eq_norm] at hx ⊢
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hscaled : R⁻¹ * ‖x‖ ≤ 1 := by
    rw [inv_mul_le_iff₀ hR]
    simpa using hx'
  have hRinv_nonneg : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  simpa [norm_smul, Real.norm_of_nonneg hRinv_nonneg] using hscaled

theorem norm_one_sub_unitBallBumpSchwartzPiRadius_le_one {m : ℕ}
    (R : ℝ) (hR : 0 < R) (x : Fin m → ℝ) :
    ‖(1 : ℂ) - unitBallBumpSchwartzPiRadius m R hR x‖ ≤ 1 := by
  rw [unitBallBumpSchwartzPiRadius_apply]
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun y => (b y : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have happly :
      unitBallBumpSchwartzPi m (R⁻¹ • x) = f (R⁻¹ • x) := by
    simpa [unitBallBumpSchwartzPi, b, f] using
      (HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth (R⁻¹ • x))
  rw [happly]
  change ‖(1 : ℂ) - ((b (R⁻¹ • x) : ℝ) : ℂ)‖ ≤ 1
  have h0 : 0 ≤ b (R⁻¹ • x) := b.nonneg
  have h1 : b (R⁻¹ • x) ≤ 1 := b.le_one
  have hsub : 0 ≤ 1 - b (R⁻¹ • x) := sub_nonneg.mpr h1
  have hnorm : ‖((1 - b (R⁻¹ • x) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hsub]
    linarith
  have hcast :
      (1 : ℂ) - ((b (R⁻¹ • x) : ℝ) : ℂ) = (((1 - b (R⁻¹ • x) : ℝ)) : ℂ) := by
    simp
  rw [hcast]
  exact hnorm

theorem hasCompactSupport_unitBallBumpSchwartzPiRadius (m : ℕ) (R : ℝ) (hR : 0 < R) :
    HasCompactSupport ((unitBallBumpSchwartzPiRadius m R hR :
      SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ) := by
  simpa [unitBallBumpSchwartzPiRadius, Units.smul_def] using
    (hasCompactSupport_unitBallBumpSchwartzPi m).comp_homeomorph
      ((Homeomorph.smulOfNeZero R hR.ne').symm)

theorem hasCompactSupport_cutoff_mul {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    HasCompactSupport
      ((SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPi m)
        f : SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_unitBallBumpSchwartzPi m).isCompact ?_
  intro x hx
  exact (SchwartzMap.tsupport_smulLeftCLM_subset
    (g := unitBallBumpSchwartzPi m) (f := f) (subset_tsupport _ hx)).2

theorem cutoff_compl_eq_zero_on_closedBall {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    {x : Fin m → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) 1) :
    (f - SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPi m) f) x = 0 := by
  have hψ : unitBallBumpSchwartzPi m x = 1 :=
    unitBallBumpSchwartzPi_one_of_mem_closedBall hx
  have hsmul :
      (SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPi m) f) x = f x := by
    rw [SchwartzMap.smulLeftCLM_apply_apply]
    · simp [hψ]
    · exact (unitBallBumpSchwartzPi m).hasTemperateGrowth
  simp [hsmul]

theorem hasCompactSupport_cutoff_mul_radius {m : ℕ}
    (R : ℝ) (hR : 0 < R) (f : SchwartzMap (Fin m → ℝ) ℂ) :
    HasCompactSupport
      ((SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPiRadius m R hR)
        f : SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_unitBallBumpSchwartzPiRadius m R hR).isCompact ?_
  intro x hx
  exact (SchwartzMap.tsupport_smulLeftCLM_subset
    (g := unitBallBumpSchwartzPiRadius m R hR) (f := f) (subset_tsupport _ hx)).2

theorem cutoff_compl_eq_zero_on_closedBall_radius {m : ℕ}
    (R : ℝ) (hR : 0 < R) (f : SchwartzMap (Fin m → ℝ) ℂ)
    {x : Fin m → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) R) :
    (f - SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPiRadius m R hR) f) x = 0 := by
  have hψ : unitBallBumpSchwartzPiRadius m R hR x = 1 :=
    unitBallBumpSchwartzPiRadius_one_of_mem_closedBall hR hx
  have hsmul :
      (SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPiRadius m R hR) f) x = f x := by
    rw [SchwartzMap.smulLeftCLM_apply_apply]
    · simp [hψ]
    · exact (unitBallBumpSchwartzPiRadius m R hR).hasTemperateGrowth
  simp [hsmul]

theorem norm_cutoff_compl_radius_le {m : ℕ}
    (R : ℝ) (hR : 0 < R) (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) :
    ‖(f - SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPiRadius m R hR) f) x‖ ≤ ‖f x‖ := by
  have hsmul :
      (SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPiRadius m R hR) f) x
        = unitBallBumpSchwartzPiRadius m R hR x * f x := by
    simpa [smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply
        (F := ℂ) (g := unitBallBumpSchwartzPiRadius m R hR)
        (unitBallBumpSchwartzPiRadius m R hR).hasTemperateGrowth f x)
  calc
    ‖(f - SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPiRadius m R hR) f) x‖
        = ‖f x - unitBallBumpSchwartzPiRadius m R hR x * f x‖ := by simp [hsmul]
    _ = ‖((1 : ℂ) - unitBallBumpSchwartzPiRadius m R hR x) * f x‖ := by ring_nf
    _ = ‖(1 : ℂ) - unitBallBumpSchwartzPiRadius m R hR x‖ * ‖f x‖ := norm_mul _ _
    _ ≤ 1 * ‖f x‖ := by
          gcongr
          exact norm_one_sub_unitBallBumpSchwartzPiRadius_le_one R hR x
    _ = ‖f x‖ := by ring

theorem iteratedFDeriv_cutoff_compl_radius_add_one_eq_zero_on_closedBall {m l : ℕ}
    (R : ℝ) (hR : 0 < R) (f : SchwartzMap (Fin m → ℝ) ℂ)
    {x : Fin m → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) R) :
    iteratedFDeriv ℝ l
      (⇑(f - SchwartzMap.smulLeftCLM ℂ
        (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f)) x = 0 := by
  let g : (Fin m → ℝ) → ℂ :=
    ⇑(f - SchwartzMap.smulLeftCLM ℂ
      (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f)
  have hEq : g =ᶠ[𝓝 x] fun _ : Fin m → ℝ => (0 : ℂ) := by
    refine Filter.mem_of_superset
      (Metric.ball_mem_nhds x (show 0 < (1 : ℝ) / 2 by positivity)) ?_
    intro y hy
    have hy_norm : ‖y‖ ≤ R + 1 := by
      have hy_dist : ‖y - x‖ < (1 : ℝ) / 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy
      have hx_norm : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_add_le (y - x) x
      linarith
    have hy_ball : y ∈ Metric.closedBall (0 : Fin m → ℝ) (R + 1) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy_norm
    exact cutoff_compl_eq_zero_on_closedBall_radius (R := R + 1) (hR := add_pos hR zero_lt_one)
      (f := f) hy_ball
  have hx0 : g x = 0 := hEq.eq_of_nhds
  have hiter :
      iteratedFDeriv ℝ l g x = 0 := by
    have hiterWithin :
        iteratedFDerivWithin ℝ l g Set.univ x =
          iteratedFDerivWithin ℝ l (fun _ : Fin m → ℝ => (0 : ℂ)) Set.univ x :=
      (hEq.filter_mono inf_le_left).iteratedFDerivWithin_eq hx0 l
    simpa [iteratedFDerivWithin_univ, iteratedFDeriv_zero_fun] using hiterWithin
  simpa [g] using hiter

private theorem norm_iteratedFDeriv_cutoff_compl_radius_le_uniform {m n : ℕ} :
    ∃ (a : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (R : ℝ) (hR : 0 < R) (N : ℕ), N ≤ n → ∀ x : Fin m → ℝ,
        ‖iteratedFDeriv ℝ N
          (fun y : Fin m → ℝ =>
            (1 : ℂ) - unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one) y) x‖ ≤
          C * (1 + ‖x‖) ^ a := by
  let ψ : (Fin m → ℝ) → ℂ := fun y => (1 : ℂ) - unitBallBumpSchwartzPi m y
  have hψ : ψ.HasTemperateGrowth := by
    simpa [ψ] using
      (Function.HasTemperateGrowth.const (1 : ℂ)).sub
        (unitBallBumpSchwartzPi m).hasTemperateGrowth
  obtain ⟨a, C, hC, hψbound⟩ := hψ.norm_iteratedFDeriv_le_uniform n
  refine ⟨a, C, hC, ?_⟩
  intro R hR N hN x
  let ρ : ℝ := R + 1
  have hρ : 0 < ρ := add_pos hR zero_lt_one
  let e :
      (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin m → ℝ)
      (Units.mk0 ρ hρ.ne')).symm) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)).toContinuousLinearMap
  have he_apply (y : Fin m → ℝ) : e y = ρ⁻¹ • y := by
    change
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin m → ℝ)
        (Units.mk0 ρ hρ.ne')).symm) y) = ρ⁻¹ • y
    rw [show
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin m → ℝ)
        (Units.mk0 ρ hρ.ne')).symm) y) =
        ((↑((Units.mk0 ρ hρ.ne')⁻¹) : ℝ) • y) by rfl]
    simp [Units.val_inv_eq_inv_val]
  have he_norm_le : ‖e‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound e zero_le_one ?_
    intro y
    calc
      ‖e y‖ = ‖ρ⁻¹ • y‖ := by rw [he_apply]
      _ = ‖ρ⁻¹‖ * ‖y‖ := norm_smul _ _
      _ ≤ 1 * ‖y‖ := by
            gcongr
            · rw [Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
              exact inv_le_one_of_one_le₀ (by linarith : 1 ≤ ρ)
  have hcomp :
      (fun y : Fin m → ℝ =>
        (1 : ℂ) - unitBallBumpSchwartzPiRadius m ρ hρ y) = ψ ∘ e := by
    funext y
    simp [ψ, unitBallBumpSchwartzPiRadius_apply, he_apply, Function.comp]
  have hitercomp :
      iteratedFDeriv ℝ N (ψ ∘ e) x =
        (iteratedFDeriv ℝ N ψ (e x)).compContinuousLinearMap (fun _ : Fin N => e) := by
    simpa using e.iteratedFDeriv_comp_right
      (f := ψ) hψ.1 (x := x) (i := N) (by exact_mod_cast le_top)
  rw [hcomp, hitercomp]
  have hprod_le : ∏ _ : Fin N, ‖e‖ ≤ 1 := by
    simpa [Finset.prod_const] using Finset.prod_le_one (s := (Finset.univ : Finset (Fin N)))
      (fun _ _ => norm_nonneg _)
      (fun _ _ => he_norm_le)
  calc
    ‖(iteratedFDeriv ℝ N ψ (e x)).compContinuousLinearMap (fun _ : Fin N => e)‖
        ≤ ‖iteratedFDeriv ℝ N ψ (e x)‖ * ∏ _ : Fin N, ‖e‖ := by
          exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ N ψ (e x)‖ * 1 := by
          exact mul_le_mul_of_nonneg_left hprod_le (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ N ψ (e x)‖ := by ring
    _ ≤ C * (1 + ‖e x‖) ^ a := hψbound N hN (e x)
    _ ≤ C * (1 + ‖x‖) ^ a := by
          gcongr
          calc
            ‖e x‖ = ‖ρ⁻¹ • x‖ := by rw [he_apply]
            _ = ‖ρ⁻¹‖ * ‖x‖ := norm_smul _ _
            _ ≤ 1 * ‖x‖ := by
                  gcongr
                  · rw [Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
                    exact inv_le_one_of_one_le₀ (by linarith : 1 ≤ ρ)
            _ = ‖x‖ := by ring

/-- Uniform Schwartz seminorm bound for the cutoff complements `f - χ_R f`. -/
theorem smulLeftCLM_cutoff_compl_uniform_seminorm_bound {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) (k l : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ) (hR : 0 < R),
      (SchwartzMap.seminorm ℝ k l)
        (f - SchwartzMap.smulLeftCLM ℂ
          (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f) ≤ M := by
  obtain ⟨a, C, hC, hψbound⟩ :=
    norm_iteratedFDeriv_cutoff_compl_radius_le_uniform (m := m) (n := l)
  let M : ℝ :=
    (((l : ℝ) + 1) * (Nat.choose l (l / 2) : ℝ) * (C * 2 ^ (a + k))) *
      (Finset.Iic (a + k, l)).sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f
  refine ⟨M, by positivity, ?_⟩
  intro R hR
  let ψR : (Fin m → ℝ) → ℂ := fun y =>
    (1 : ℂ) - unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one) y
  have hψR_temp : ψR.HasTemperateGrowth := by
    simpa [ψR] using
      (Function.HasTemperateGrowth.const (1 : ℂ)).sub
        (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)).hasTemperateGrowth
  have hEq :
      f - SchwartzMap.smulLeftCLM ℂ
        (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f =
      SchwartzMap.smulLeftCLM ℂ ψR f := by
    ext x
    have hleft :
        (SchwartzMap.smulLeftCLM ℂ
          (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f) x =
          unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one) x * f x := by
      simpa [smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply
          (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)).hasTemperateGrowth
          f x)
    have hright :
        (SchwartzMap.smulLeftCLM ℂ ψR f) x = ψR x * f x := by
      simpa [smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply hψR_temp f x)
    calc
      (f - SchwartzMap.smulLeftCLM ℂ
        (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f) x
          = f x - unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one) x * f x := by
              simp [hleft]
      _ = ψR x * f x := by
            simp [ψR]
            ring
      _ = (SchwartzMap.smulLeftCLM ℂ ψR f) x := hright.symm
  rw [hEq]
  refine SchwartzMap.seminorm_le_bound ℝ k l (SchwartzMap.smulLeftCLM ℂ ψR f)
    (M := M) (by positivity) ?_
  intro x
  have hmul :=
    norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hψR_temp.1 (f.smooth ⊤) x
      (n := l) (by exact_mod_cast le_top)
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(SchwartzMap.smulLeftCLM ℂ ψR f)) x‖
        = ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => ψR y * f y) x‖ := by
            simp [SchwartzMap.smulLeftCLM_apply hψR_temp, smul_eq_mul]
    _ ≤ ‖x‖ ^ k *
        ∑ i ∈ Finset.range (l + 1),
          (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψR x‖ *
            ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖ := by
              exact mul_le_mul_of_nonneg_left hmul (by positivity)
    _ ≤ M := by
      rw [Finset.mul_sum]
      let B : ℝ :=
        (Nat.choose l (l / 2) : ℝ) * (C * 2 ^ (a + k)) *
          (Finset.Iic (a + k, l)).sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f
      have hsum :
          ∑ i ∈ Finset.range (l + 1),
            ‖x‖ ^ k * ((l.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψR x‖ *
              ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) ≤
            ∑ _i ∈ Finset.range (l + 1), B := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_range_succ_iff] at hi
        specialize hψbound R hR i hi x
        have hpow :
            ‖x‖ ^ k * (1 + ‖x‖) ^ a ≤ (1 + ‖x‖) ^ (a + k) := by
          have hbase : ‖x‖ ≤ 1 + ‖x‖ := by
            nlinarith [norm_nonneg x]
          have hpowk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by
            exact pow_le_pow_left₀ (norm_nonneg x) hbase k
          calc
            ‖x‖ ^ k * (1 + ‖x‖) ^ a ≤ (1 + ‖x‖) ^ k * (1 + ‖x‖) ^ a := by
              exact mul_le_mul_of_nonneg_right hpowk (by positivity)
            _ = (1 + ‖x‖) ^ a * (1 + ‖x‖) ^ k := by ring
            _ = (1 + ‖x‖) ^ (a + k) := by rw [pow_add]
        have hsup :
            (1 + ‖x‖) ^ (a + k) * ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖ ≤
              2 ^ (a + k) *
                (Finset.Iic (a + k, l)).sup
                  (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f :=
          SchwartzMap.one_add_le_sup_seminorm_apply
            (𝕜 := ℝ) (m := (a + k, l)) (k := a + k) (n := l - i)
            le_rfl (by omega) f x
        have hmain :
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ i ψR x‖ *
                ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖ ≤
              (C * 2 ^ (a + k)) *
                (Finset.Iic (a + k, l)).sup
                  (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f := by
          calc
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ i ψR x‖ *
                ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖
                = (‖x‖ ^ k * ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) *
                    ‖iteratedFDeriv ℝ i ψR x‖ := by ring
            _ ≤ (‖x‖ ^ k * ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) *
                (C * (1 + ‖x‖) ^ a) := by
                  exact mul_le_mul_of_nonneg_left hψbound (by positivity)
            _ = C * ((‖x‖ ^ k * (1 + ‖x‖) ^ a) *
                ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) := by ring
            _ ≤ C * ((1 + ‖x‖) ^ (a + k) *
                ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hpow
                      (norm_nonneg (iteratedFDeriv ℝ (l - i) (⇑f) x)))
                    hC
            _ ≤ C * (2 ^ (a + k) *
                (Finset.Iic (a + k, l)).sup
                  (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f) := by
                    exact mul_le_mul_of_nonneg_left hsup hC
            _ = (C * 2 ^ (a + k)) *
                (Finset.Iic (a + k, l)).sup
                  (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f := by ring
        calc
          ‖x‖ ^ k * ((l.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψR x‖ *
              ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖)
              = (l.choose i : ℝ) *
                  (‖x‖ ^ k * ‖iteratedFDeriv ℝ i ψR x‖ *
                    ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) := by ring
          _ ≤ (Nat.choose l (l / 2) : ℝ) *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ i ψR x‖ *
                ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) := by
                  exact mul_le_mul_of_nonneg_right
                    (by exact_mod_cast i.choose_le_middle l) (by positivity)
          _ ≤ (Nat.choose l (l / 2) : ℝ) *
              ((C * 2 ^ (a + k)) *
                (Finset.Iic (a + k, l)).sup
                  (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f) := by
                    exact mul_le_mul_of_nonneg_left hmain (by positivity)
          _ = B := by simp [B, mul_assoc, mul_left_comm]
      refine hsum.trans ?_
      simp [B, M, mul_assoc, mul_left_comm, mul_comm]

/-- On the tail `‖x‖ ≥ 1`, the weighted Schwartz seminorm is bounded by a `1 / ‖x‖²` decay
coming from the `(k + 2, l)` Schwartz bound. -/
theorem _root_.SchwartzMap.seminorm_tail_le_div_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, 1 ≤ ‖x‖ →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) x‖ ≤ C / ‖x‖ ^ 2 := by
  obtain ⟨C, hC⟩ := f.decay' (k + 2) l
  refine ⟨C, ?_, fun x hx => ?_⟩
  · have h0 := hC 0
    simp at h0
    linarith [norm_nonneg (iteratedFDeriv ℝ l (⇑f) 0)]
  · have hx_pos : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx
    have hx_sq_pos : 0 < ‖x‖ ^ 2 := pow_pos hx_pos 2
    rw [le_div_iff₀ hx_sq_pos]
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) x‖ * ‖x‖ ^ 2
          = ‖x‖ ^ (k + 2) * ‖iteratedFDeriv ℝ l (⇑f) x‖ := by ring
      _ ≤ C := hC x

/-- Every Schwartz seminorm becomes uniformly small sufficiently far out on the tail. -/
theorem _root_.SchwartzMap.seminorm_tail_small
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (k l : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : E, R < ‖x‖ →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) x‖ < ε := by
  obtain ⟨C, hC_nn, hC⟩ := f.seminorm_tail_le_div_sq k l
  refine ⟨Real.sqrt (C / ε) + 1, by positivity, fun x hx => ?_⟩
  have hx_ge_one : 1 ≤ ‖x‖ := by
    linarith [Real.sqrt_nonneg (C / ε)]
  have hx_pos : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx_ge_one
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) x‖ ≤ C / ‖x‖ ^ 2 := hC x hx_ge_one
    _ < ε := by
      rw [div_lt_iff₀ (pow_pos hx_pos 2)]
      have hR_sq : C / ε < ‖x‖ ^ 2 := by
        calc
          C / ε ≤ (Real.sqrt (C / ε)) ^ 2 := by
            rw [Real.sq_sqrt (div_nonneg hC_nn hε.le)]
          _ < (Real.sqrt (C / ε) + 1) ^ 2 := by
            nlinarith [Real.sqrt_nonneg (C / ε)]
          _ ≤ ‖x‖ ^ 2 := by
            apply sq_le_sq'
            · linarith [Real.sqrt_nonneg (C / ε), norm_nonneg x]
            · exact hx.le
      have := (div_lt_iff₀ hε).mp hR_sq
      linarith

theorem hasCompactSupport_prependField {n : ℕ}
    (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n → ℝ) ℂ)
    (hφ : HasCompactSupport φ) (hg : HasCompactSupport g) :
    HasCompactSupport (φ.prependField g) := by
  let K : Set (Fin (n + 1) → ℝ) :=
    (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) ''
      (tsupport φ ×ˢ tsupport g)
  have hKcompact : IsCompact K := by
    have hcont :
        Continuous (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) := by
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · exact continuous_fst
      · intro i
        simpa using (continuous_apply i).comp continuous_snd
    simpa [K] using (hφ.isCompact.prod hg.isCompact).image hcont
  refine HasCompactSupport.of_support_subset_isCompact hKcompact ?_
  intro x hx
  rw [Function.mem_support] at hx
  have hφx : φ (x 0) ≠ 0 := by
    intro h0
    apply hx
    simp [SchwartzMap.prependField_apply, h0]
  have hgx : g (fun i : Fin n => x i.succ) ≠ 0 := by
    intro h0
    apply hx
    simp [SchwartzMap.prependField_apply, h0]
  refine ⟨(x 0, fun i : Fin n => x i.succ), ?_, ?_⟩
  · exact ⟨subset_tsupport _ (Function.mem_support.mpr hφx),
      subset_tsupport _ (Function.mem_support.mpr hgx)⟩
  · ext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro i
      simp

theorem exists_eq_sum_coord_smul_of_zero_of_hasCompactSupport :
    ∀ {m : ℕ} (f : SchwartzMap (Fin m → ℝ) ℂ), f 0 = 0 → HasCompactSupport f →
      ∃ g : Fin m → SchwartzMap (Fin m → ℝ) ℂ,
        f = ∑ i, SchwartzMap.smulLeftCLM ℂ (fun x : Fin m → ℝ => x i) (g i) := by
  intro m
  induction m with
  | zero =>
      intro f hf0 hfcs
      refine ⟨Fin.elim0, ?_⟩
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      simpa [hx] using hf0
  | succ n ih =>
      intro f hf0 hfcs
      let h := headSectionCLM n f
      have hh0 : h 0 = 0 := headSectionCLM_zero f hf0
      have hhcs : HasCompactSupport h := hasCompactSupport_headSection f hfcs
      obtain ⟨gTail, hgTail⟩ := ih h hh0 hhcs
      let r : SchwartzMap (Fin (n + 1) → ℝ) ℂ := f - unitBumpSchwartz.prependField h
      have hprependcs : HasCompactSupport (unitBumpSchwartz.prependField h) := by
        exact hasCompactSupport_prependField unitBumpSchwartz h
          (by
            let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
            exact b.hasCompactSupport.comp_left Complex.ofReal_zero)
          hhcs
      have hrcs : HasCompactSupport r := by
        simpa [r, sub_eq_add_neg] using HasCompactSupport.add hfcs hprependcs.neg
      have hr0 : headSectionCLM n r = 0 := by
        simpa [r] using headSection_remainder_eq_zero unitBumpSchwartz unitBumpSchwartz_zero f
      obtain ⟨g0, hg0⟩ := exists_eq_coord_smul_of_headSection_zero_of_hasCompactSupport r hr0 hrcs
      refine ⟨fun j => Fin.cases g0 (fun i => unitBumpSchwartz.prependField (gTail i)) j, ?_⟩
      ext x
      have hcoord0 :
          (fun y : Fin (n + 1) → ℝ => y 0).HasTemperateGrowth :=
        (headCoordProjCLM n).hasTemperateGrowth
      have hcoordSucc :
          ∀ i : Fin n, (fun y : Fin (n + 1) → ℝ => y i.succ).HasTemperateGrowth := by
        intro i
        exact
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1))
            (φ := fun _ => ℝ) i.succ).hasTemperateGrowth
      have hg0x := congrArg (fun G : SchwartzMap (Fin (n + 1) → ℝ) ℂ => G x) hg0
      have hrx :
          r x = ((SchwartzMap.smulLeftCLM ℂ (fun y : Fin (n + 1) → ℝ => y 0) g0) x) := by
        simpa [SchwartzMap.smulLeftCLM_apply_apply, hcoord0] using hg0x
      have htailx :
          h (fun i : Fin n => x i.succ) =
            ∑ i : Fin n,
              ((SchwartzMap.smulLeftCLM ℂ (fun y : Fin n → ℝ => y i) (gTail i))
                (fun i : Fin n => x i.succ)) := by
        simpa using congrArg
          (fun G : SchwartzMap (Fin n → ℝ) ℂ => G (fun i : Fin n => x i.succ)) hgTail
      have hprependx :
          (unitBumpSchwartz.prependField h) x =
            ∑ i : Fin n,
              (SchwartzMap.smulLeftCLM ℂ
                (fun y : Fin (n + 1) → ℝ => y i.succ)
                (unitBumpSchwartz.prependField (gTail i))) x := by
        calc
          (unitBumpSchwartz.prependField h) x = unitBumpSchwartz (x 0) * h (fun i : Fin n => x i.succ) := by
            simp [SchwartzMap.prependField_apply]
          _ = unitBumpSchwartz (x 0) *
              ∑ i : Fin n,
                ((SchwartzMap.smulLeftCLM ℂ (fun y : Fin n → ℝ => y i) (gTail i))
                  (fun i : Fin n => x i.succ)) := by
                  rw [htailx]
          _ = ∑ i : Fin n, unitBumpSchwartz (x 0) *
                ((SchwartzMap.smulLeftCLM ℂ (fun y : Fin n → ℝ => y i) (gTail i))
                  (fun i : Fin n => x i.succ)) := by
                  rw [Finset.mul_sum]
          _ = ∑ i : Fin n,
                (SchwartzMap.smulLeftCLM ℂ
                  (fun y : Fin (n + 1) → ℝ => y i.succ)
                  (unitBumpSchwartz.prependField (gTail i))) x := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hcoordTail :
                      (fun y : Fin n → ℝ => y i).HasTemperateGrowth := by
                    exact
                      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
                        (φ := fun _ => ℝ) i).hasTemperateGrowth
                  rw [SchwartzMap.smulLeftCLM_apply_apply hcoordTail]
                  rw [SchwartzMap.smulLeftCLM_apply_apply (hcoordSucc i),
                    SchwartzMap.prependField_apply]
                  simp [Complex.real_smul, mul_left_comm]
      have hsum_decomp :
          (∑ i : Fin (n + 1),
            (SchwartzMap.smulLeftCLM ℂ (fun y : Fin (n + 1) → ℝ => y i)
              (Fin.cases g0 (fun i => unitBumpSchwartz.prependField (gTail i)) i))) x
            =
          (SchwartzMap.smulLeftCLM ℂ (fun y : Fin (n + 1) → ℝ => y 0) g0) x
            + ∑ i : Fin n,
                (SchwartzMap.smulLeftCLM ℂ
                  (fun y : Fin (n + 1) → ℝ => y i.succ)
                  (unitBumpSchwartz.prependField (gTail i))) x := by
        rw [Fin.sum_univ_succ]
        simp [hcoord0]
      calc
        f x = r x + (unitBumpSchwartz.prependField h) x := by
          simp [r]
        _ =
          (SchwartzMap.smulLeftCLM ℂ (fun y : Fin (n + 1) → ℝ => y 0) g0) x
            + ∑ i : Fin n,
                (SchwartzMap.smulLeftCLM ℂ
                  (fun y : Fin (n + 1) → ℝ => y i.succ)
                  (unitBumpSchwartz.prependField (gTail i))) x := by
              rw [hrx, hprependx]
        _ =
          (∑ i : Fin (n + 1),
            (SchwartzMap.smulLeftCLM ℂ (fun y : Fin (n + 1) → ℝ => y i)
              (Fin.cases g0 (fun i => unitBumpSchwartz.prependField (gTail i)) i))) x := by
              simpa using hsum_decomp.symm

/-- A one-variable smooth reciprocal cutoff that is identically `0` on
`(-∞, 1/2]` and agrees with `t ↦ t⁻¹` on `[1, ∞)`. -/
def reciprocalCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition (2 * t - 1) * t⁻¹

theorem reciprocalCutoff_eq_inv_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    reciprocalCutoff t = t⁻¹ := by
  rw [reciprocalCutoff]
  have hcut : Real.smoothTransition (2 * t - 1) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    nlinarith
  simp [hcut]

/-- The reciprocal cutoff used in the away-from-origin coordinate factorization
is a temperate multiplier. -/
theorem reciprocalCutoff_hasTemperateGrowth :
    reciprocalCutoff.HasTemperateGrowth := by
  refine ⟨?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < 1 / 2
    · have hEq : reciprocalCutoff =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        have hy' : y < 1 / 2 := hy
        have hs : Real.smoothTransition (2 * y - 1) = 0 := by
          apply Real.smoothTransition.zero_of_nonpos
          nlinarith [hy']
        simp [reciprocalCutoff, hs]
      exact contDiffAt_const.congr_of_eventuallyEq hEq
    · have hx0 : x ≠ 0 := by
        nlinarith
      simpa [reciprocalCutoff] using
        (((Real.smoothTransition.contDiffAt).comp x
          ((contDiff_const.mul contDiff_id).sub contDiff_const).contDiffAt).mul
          (contDiffAt_inv (𝕜 := ℝ) hx0))
  · intro n
    have hcontDiffN : ContDiff ℝ n reciprocalCutoff := by
      exact (show ContDiff ℝ (⊤ : ℕ∞) reciprocalCutoff by
        rw [contDiff_iff_contDiffAt]
        intro x
        by_cases hx : x < 1 / 2
        · have hEq : reciprocalCutoff =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
            filter_upwards [Iio_mem_nhds hx] with y hy
            have hy' : y < 1 / 2 := hy
            have hs : Real.smoothTransition (2 * y - 1) = 0 := by
              apply Real.smoothTransition.zero_of_nonpos
              nlinarith [hy']
            simp [reciprocalCutoff, hs]
          exact contDiffAt_const.congr_of_eventuallyEq hEq
        · have hx0 : x ≠ 0 := by
            nlinarith
          simpa [reciprocalCutoff] using
            (((Real.smoothTransition.contDiffAt).comp x
              ((contDiff_const.mul contDiff_id).sub contDiff_const).contDiffAt).mul
              (contDiffAt_inv (𝕜 := ℝ) hx0))).of_le (by exact_mod_cast le_top)
    have hcont : Continuous (iteratedDeriv n reciprocalCutoff) :=
      ContDiff.continuous_iteratedDeriv' n hcontDiffN
    obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Set.Icc (1 / 2 : ℝ) 1) (f := iteratedDeriv n reciprocalCutoff) hcont.continuousOn
    refine ⟨0, max C0 ‖(-1 : ℝ) ^ n * (n.factorial : ℝ)‖, ?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp only [pow_zero, mul_one]
    by_cases hxlt : x < 1 / 2
    · have hEq : reciprocalCutoff =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
        filter_upwards [Iio_mem_nhds hxlt] with y hy
        have hy' : y < 1 / 2 := hy
        have hs : Real.smoothTransition (2 * y - 1) = 0 := by
          apply Real.smoothTransition.zero_of_nonpos
          nlinarith [hy']
        simp [reciprocalCutoff, hs]
      have hderiv0 : iteratedDeriv n reciprocalCutoff x = 0 := by
        rw [Filter.EventuallyEq.iteratedDeriv_eq n hEq]
        simp
      simp [hderiv0]
    · by_cases hxgt : 1 < x
      · have hEq : reciprocalCutoff =ᶠ[𝓝 x] Inv.inv := by
          filter_upwards [Ioi_mem_nhds hxgt] with y hy
          exact reciprocalCutoff_eq_inv_of_one_le hy.le
        have hderiv : iteratedDeriv n reciprocalCutoff x = iteratedDeriv n Inv.inv x := by
          rw [Filter.EventuallyEq.iteratedDeriv_eq n hEq]
        rw [hderiv, iteratedDeriv_eq_iterate, iter_deriv_inv]
        have hx1 : (1 : ℝ) ≤ x := hxgt.le
        have hxpow : x ^ (-1 - n : ℤ) ≤ 1 := by
          apply zpow_le_one_of_nonpos₀ hx1
          norm_num
        have hxpow' : ‖x ^ (-1 - n : ℤ)‖ ≤ 1 := by
          have hxnonneg : 0 ≤ x ^ (-1 - n : ℤ) := by positivity
          have habs : |x ^ (-1 - n : ℤ)| = x ^ (-1 - n : ℤ) := by
            simp [abs_of_nonneg hxnonneg]
          rw [Real.norm_eq_abs, habs]
          exact hxpow
        have hmul :
            ‖(-1 : ℝ) ^ n * (n.factorial : ℝ) * x ^ (-1 - n : ℤ)‖
              ≤ ‖(-1 : ℝ) ^ n * (n.factorial : ℝ)‖ := by
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) hxpow'
        exact hmul.trans (le_max_right _ _)
      · have hxmem : x ∈ Set.Icc (1 / 2 : ℝ) 1 := by
          constructor <;> linarith
        exact le_trans (hC0 x hxmem) (le_max_left _ _)

/-- If a Schwartz function vanishes on the unit ball, then it factors as a
finite sum of coordinate multiples. -/
theorem exists_eq_sum_coord_smul_of_vanishes_closedBall
    {m : ℕ} (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hf :
      ∀ x ∈ Metric.closedBall (0 : Fin m → ℝ) 1, f x = 0) :
    ∃ g : Fin m → SchwartzMap (Fin m → ℝ) ℂ,
      f = ∑ i, SchwartzMap.smulLeftCLM ℂ
        (fun x : Fin m → ℝ => x i) (g i) := by
  let sumSq : (Fin m → ℝ) → ℝ := fun x => ∑ i : Fin m, (x i) ^ 2
  have hcoord :
      ∀ i : Fin m, (fun x : Fin m → ℝ => x i).HasTemperateGrowth := by
    intro i
    exact
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m)
        (φ := fun _ => ℝ) i).hasTemperateGrowth
  have hsumSq : sumSq.HasTemperateGrowth := by
    classical
    simpa [sumSq] using
      (Function.HasTemperateGrowth.sum (s := Finset.univ)
        (f := fun i : Fin m => fun x : Fin m → ℝ => (x i) ^ 2)
        (by
          intro i hi
          simpa [pow_two] using (hcoord i).pow 2))
  have hcut :
      (fun x : Fin m → ℝ => reciprocalCutoff (sumSq x)).HasTemperateGrowth := by
    exact reciprocalCutoff_hasTemperateGrowth.comp hsumSq
  let coeff : Fin m → (Fin m → ℝ) → ℝ :=
    fun i x => reciprocalCutoff (sumSq x) * x i
  have hcoeff :
      ∀ i : Fin m,
        (coeff i).HasTemperateGrowth := by
    intro i
    simpa [coeff] using (hcut.mul (hcoord i))
  refine ⟨fun i =>
    SchwartzMap.smulLeftCLM ℂ
      (coeff i) f, ?_⟩
  ext x
  by_cases hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) 1
  · have hfx : f x = 0 := hf x hx
    have hsum0 :
        (∑ i : Fin m,
          (SchwartzMap.smulLeftCLM ℂ (fun y : Fin m → ℝ => y i)
            (SchwartzMap.smulLeftCLM ℂ
              (coeff i) f)) x) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hinner :
          (SchwartzMap.smulLeftCLM ℂ
            (coeff i) f) x = 0 := by
        simpa [coeff, hfx] using
          (SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
            (g := coeff i) (hg := hcoeff i) f x)
      calc
        ((SchwartzMap.smulLeftCLM ℂ (fun y : Fin m → ℝ => y i)
          (SchwartzMap.smulLeftCLM ℂ (coeff i) f)) x)
            = (x i) • ((SchwartzMap.smulLeftCLM ℂ (coeff i) f) x) := by
                simpa using
                  (SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
                    (g := fun y : Fin m → ℝ => y i)
                    (hg := hcoord i)
                    (SchwartzMap.smulLeftCLM ℂ (coeff i) f) x)
        _ = 0 := by simp [hinner]
    simpa [Finset.sum_apply, hfx] using hsum0.symm
  · have hnorm_gt : 1 < ‖x‖ := by
      have hx_dist : ¬ dist x (0 : Fin m → ℝ) ≤ 1 := by
        simpa [Metric.mem_closedBall] using hx
      simpa [dist_eq_norm, not_le] using hx_dist
    have hsumSq_ge : 1 ≤ sumSq x := by
      classical
      rcases isEmpty_or_nonempty (Fin m) with hm | hm
      · exfalso
        have hx0 : x = 0 := by
          ext i
          exact (hm.false i).elim
        apply hx
        simp [hx0]
      · have hnotall : ¬ ∀ i : Fin m, ‖x i‖ ≤ 1 := by
          intro hall
          have hnorm_le : ‖x‖ ≤ 1 := by
            let M : NNReal := Finset.univ.sup (fun b : Fin m => ‖x b‖₊)
            have hsuple : M ≤ (1 : NNReal) := by
              refine Finset.sup_le ?_
              intro j hj
              exact_mod_cast hall j
            have hnorm : ‖x‖ = (M : ℝ) := by
              dsimp [M]
              rfl
            rw [hnorm]
            change (M : ℝ) ≤ (1 : ℝ)
            exact_mod_cast hsuple
          linarith
        obtain ⟨i, hi⟩ := not_forall.mp hnotall
        have hi_abs : 1 < |x i| := by
          simpa [Real.norm_eq_abs, not_le] using hi
        have hi_sq : 1 < (x i) ^ 2 := by
          have hsq_abs : 1 < |x i| ^ 2 := by
            nlinarith [hi_abs]
          simpa [sq_abs] using hsq_abs
        have hterm_le : (x i) ^ 2 ≤ sumSq x := by
          dsimp [sumSq]
          exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (by simp)
        linarith
    have hcoefR :
        (∑ i : Fin m, (x i) ^ 2 * reciprocalCutoff (sumSq x)) = 1 := by
      have hsumSq_ne : sumSq x ≠ 0 := by
        linarith
      have hsumSq_eq : (∑ i : Fin m, (x i) ^ 2) = sumSq x := by
        simp [sumSq]
      calc
        (∑ i : Fin m, (x i) ^ 2 * reciprocalCutoff (sumSq x))
            = (∑ i : Fin m, (x i) ^ 2) * reciprocalCutoff (sumSq x) := by
                rw [← Finset.sum_mul]
        _ = (sumSq x) * (sumSq x)⁻¹ := by
          rw [hsumSq_eq, reciprocalCutoff_eq_inv_of_one_le hsumSq_ge]
        _ = 1 := by
          field_simp [hsumSq_ne]
    have hsumeq :
        (∑ i : Fin m,
          (SchwartzMap.smulLeftCLM ℂ (fun y : Fin m → ℝ => y i)
            (SchwartzMap.smulLeftCLM ℂ
              (coeff i) f)) x) = f x := by
      calc
        (∑ i : Fin m,
          (SchwartzMap.smulLeftCLM ℂ (fun y : Fin m → ℝ => y i)
            (SchwartzMap.smulLeftCLM ℂ
              (coeff i) f)) x)
            = ∑ i : Fin m,
                (((x i) ^ 2 * reciprocalCutoff (sumSq x) : ℝ) • f x) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hinner :
                      (SchwartzMap.smulLeftCLM ℂ
                        (coeff i) f) x =
                      (reciprocalCutoff (sumSq x) * x i) • f x := by
                        simpa [coeff] using
                          (SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
                            (g := coeff i) (hg := hcoeff i) f x)
                  calc
                    ((SchwartzMap.smulLeftCLM ℂ (fun y : Fin m → ℝ => y i)
                      (SchwartzMap.smulLeftCLM ℂ (coeff i) f)) x)
                        = (x i) • ((reciprocalCutoff (sumSq x) * x i) • f x) := by
                            simpa [hinner] using
                              (SchwartzMap.smulLeftCLM_apply_apply (hcoord i)
                                (SchwartzMap.smulLeftCLM ℂ (coeff i) f) x)
                    _ = (((x i) ^ 2 * reciprocalCutoff (sumSq x) : ℝ) • f x) := by
                      rw [smul_smul]
                      congr 1
                      ring
        _ = ((∑ i : Fin m, (x i) ^ 2 * reciprocalCutoff (sumSq x) : ℝ) • f x) := by
          rw [Finset.sum_smul]
        _ = f x := by
          simp [hcoefR]
    simpa [Finset.sum_apply] using hsumeq.symm

/-- Reduce the full coordinate decomposition theorem to compact-support near the
origin plus away-from-origin factorization. -/
theorem exists_eq_sum_coord_smul_of_zero_of_ball_factor :
    ∀ {m : ℕ} (f : SchwartzMap (Fin m → ℝ) ℂ), f 0 = 0 →
      ∃ g : Fin m → SchwartzMap (Fin m → ℝ) ℂ,
        f = ∑ i, SchwartzMap.smulLeftCLM ℂ
          (fun x : Fin m → ℝ => x i) (g i) := by
  intro m f hf0
  let near : SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPi m) f
  let away : SchwartzMap (Fin m → ℝ) ℂ := f - near
  have hnear0 : near 0 = 0 := by
    rw [SchwartzMap.smulLeftCLM_apply_apply]
    · simp [hf0]
    · exact (unitBallBumpSchwartzPi m).hasTemperateGrowth
  have hnearcs : HasCompactSupport near := by
    simpa [near] using hasCompactSupport_cutoff_mul f
  obtain ⟨gNear, hgNear⟩ :=
    exists_eq_sum_coord_smul_of_zero_of_hasCompactSupport near hnear0 hnearcs
  have hawayBall : ∀ x ∈ Metric.closedBall (0 : Fin m → ℝ) 1, away x = 0 := by
    intro x hx
    simpa [away, near] using cutoff_compl_eq_zero_on_closedBall f hx
  obtain ⟨gAway, hgAway⟩ :=
    exists_eq_sum_coord_smul_of_vanishes_closedBall away hawayBall
  refine ⟨fun i => gNear i + gAway i, ?_⟩
  calc
    f = near + away := by
      simp [away]
    _ = (∑ i, SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin m → ℝ => x i) (gNear i)) +
          (∑ i, SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin m → ℝ => x i) (gAway i)) := by
            rw [hgNear, hgAway]
    _ = ∑ i, (SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin m → ℝ => x i) (gNear i) +
          SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin m → ℝ => x i) (gAway i)) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ i, SchwartzMap.smulLeftCLM ℂ
          (fun x : Fin m → ℝ => x i) (gNear i + gAway i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp


/-- Translation difference quotients converge to the directional derivative in
the Schwartz topology. -/
theorem tendsto_diffQuotient_translateSchwartz_zero {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (SCV.translateSchwartz (t • v) f - f))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 (∂_{v} f)) := by
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
  intro p ε hε
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_seminorm_diffQuotient_translateSchwartz_sub_lineDeriv_le f v p.1 p.2
  let δ : ℝ := min 1 (ε / (C + 1))
  have hδ_pos : 0 < δ := by
    have hC1 : 0 < C + 1 := by linarith
    have hquot : 0 < ε / (C + 1) := by positivity
    exact lt_min zero_lt_one hquot
  have hball :
      Metric.ball (0 : ℝ) δ ∩ ({0}ᶜ : Set ℝ) ∈ nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ) := by
    simpa [Set.inter_comm] using
      (inter_mem_nhdsWithin ({0}ᶜ : Set ℝ) (Metric.ball_mem_nhds (0 : ℝ) hδ_pos))
  refine Filter.mem_of_superset hball ?_
  intro t ht
  rcases ht with ⟨ht_ball, ht_punctured⟩
  have ht_abs : |t| < δ := by
    simpa [Real.dist_eq] using ht_ball
  have ht_one : |t| ≤ 1 := by
    have hδ_le_one : δ ≤ 1 := min_le_left _ _
    exact le_trans (le_of_lt ht_abs) hδ_le_one
  have ht_ne : t ≠ 0 := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ht_punctured
  show (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ p)
      (t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f) < ε
  refine lt_of_le_of_lt (hC t ht_ne ht_one) ?_
  have hC1 : 0 < C + 1 := by linarith
  have ht_eps : |t| < ε / (C + 1) := by
    exact lt_of_lt_of_le ht_abs (min_le_right _ _)
  have hbound1 : C * |t| ≤ C * (ε / (C + 1)) := by
    have ht_eps_le : |t| ≤ ε / (C + 1) := le_of_lt ht_eps
    gcongr
  have hbound2 : C * (ε / (C + 1)) < ε := by
    have htmp : (C * ε) / (C + 1) < ε := by
      refine (div_lt_iff₀ hC1).2 ?_
      nlinarith [hε, hC_nonneg, hC1]
    have hEq : (C * ε) / (C + 1) = C * (ε / (C + 1)) := by
      field_simp [hC1.ne']
    simpa [hEq] using htmp
  exact lt_of_le_of_lt hbound1 hbound2

/-- Translation-invariant Schwartz functionals annihilate directional
derivatives. -/
theorem map_lineDeriv_eq_zero_of_translationInvariant {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsTranslationInvariantSchwartzCLM T)
    (v : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ) :
    T (∂_{v} f) = 0 := by
  have hquot :
      Filter.Tendsto
        (fun t : ℝ => T (t⁻¹ • (SCV.translateSchwartz (t • v) f - f)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 (T (∂_{v} f))) :=
    (T.continuous.tendsto (∂_{v} f)).comp
      (tendsto_diffQuotient_translateSchwartz_zero f v)
  have hzero :
      Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 0) :=
    tendsto_const_nhds
  have heq :
      (fun t : ℝ => T (t⁻¹ • (SCV.translateSchwartz (t • v) f - f))) = fun _ => (0 : ℂ) := by
    funext t
    have htrans : T (SCV.translateSchwartz (t • v) f) = T f := by
      have := congrArg (fun S : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ => S f) (hT (t • v))
      simpa [ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply] using this
    rw [T.map_smul_of_tower, map_sub, sub_eq_zero.mpr htrans, smul_zero]
  have hzero' : Filter.Tendsto
      (fun t : ℝ => T (t⁻¹ • (SCV.translateSchwartz (t • v) f - f)))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 0) := by
    simpa only [heq] using hzero
  exact tendsto_nhds_unique hquot hzero'

/-- Every Schwartz function of integral zero is a finite sum of directional
derivatives of Schwartz functions. -/
theorem exists_eq_sum_lineDeriv_of_integral_eq_zero {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hf : (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) f = 0) :
    ∃ g : Fin m → SchwartzMap (Fin m → ℝ) ℂ,
      f = ∑ i, ∂_{((Pi.single i (1 : ℝ)) : Fin m → ℝ)} (g i) := by
  have hcoordPi :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ, f 0 = 0 →
        ∃ H : Fin m → SchwartzMap (Fin m → ℝ) ℂ,
          f = ∑ i, SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin m → ℝ => x i) (H i) := by
    intro f hf0
    obtain ⟨H, hH⟩ := exists_eq_sum_coord_smul_of_zero_of_ball_factor f hf0
    exact ⟨H, hH⟩
  exact pi_coord_decomp_implies_pi_zeroMean_decomp hcoordPi f hf

theorem exists_eq_sum_lineDeriv_of_integral_eq_zero_one
    (f : SchwartzMap (Fin 1 → ℝ) ℂ)
    (hf : (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 1 → ℝ))) f = 0) :
    ∃ g : Fin 1 → SchwartzMap (Fin 1 → ℝ) ℂ,
      f = ∑ i, ∂_{((Pi.single i (1 : ℝ)) : Fin 1 → ℝ)} (g i) := by
  let e : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  let f1 : SchwartzMap ℝ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f
  have hf1 : ∫ x, (f1 : ℝ → ℂ) x = 0 := by
    have hcomp :=
      MeasureTheory.MeasurePreserving.integral_comp'
        ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm)
        (fun y : Fin 1 → ℝ => f y)
    simpa [f1, e, SchwartzMap.integralCLM_apply] using hcomp.trans hf
  obtain ⟨g1, hg1⟩ := Poincare1D.poincare_lemma_1d f1 hf1
  refine ⟨fun _ => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e g1, ?_⟩
  rw [Fin.sum_univ_one]
  have hline :
      (∂_{(1 : ℝ)} g1 : SchwartzMap ℝ ℂ) = SchwartzMap.derivCLM ℂ ℂ g1 := by
    ext x
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.derivCLM_apply]
  calc
    f = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f1 := by
          ext x
          simp [f1]
    _ = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (SchwartzMap.derivCLM ℂ ℂ g1) := by
          rw [hg1]
    _ = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (∂_{(1 : ℝ)} g1) := by
          rw [hline.symm]
    _ = ∂_{((Pi.single (0 : Fin 1) (1 : ℝ)) : Fin 1 → ℝ)}
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e g1) := by
          symm
          simpa [e, ContinuousLinearEquiv.coe_funUnique, Pi.single_eq_same] using
            (SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv
              (𝕜 := ℂ)
              (((Pi.single (0 : Fin 1) (1 : ℝ)) : Fin 1 → ℝ))
              e g1)

/-- A translation-invariant continuous Schwartz functional is a constant
multiple of Lebesgue integration. -/
theorem exists_eq_const_integralCLM_of_translationInvariant {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsTranslationInvariantSchwartzCLM T) :
    ∃ c : ℂ, T = c • (SchwartzMap.integralCLM ℂ (MeasureTheory.volume :
      MeasureTheory.Measure (Fin m → ℝ))) := by
  let I : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    SchwartzMap.integralCLM ℂ (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
  by_cases hT0 : T = 0
  · refine ⟨0, ?_⟩
    simp [hT0]
  · classical
    have hTne : ∃ φ : SchwartzMap (Fin m → ℝ) ℂ, T φ ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hT0
      ext φ
      exact hnone φ
    rcases hTne with ⟨φ, hφ⟩
    have hIφ : I φ ≠ 0 := by
      intro hIφ0
      obtain ⟨g, hg⟩ := exists_eq_sum_lineDeriv_of_integral_eq_zero φ hIφ0
      have hTφ0 : T φ = 0 := by
        rw [hg, map_sum]
        refine Finset.sum_eq_zero ?_
        intro i hi
        exact map_lineDeriv_eq_zero_of_translationInvariant T hT
          ((Pi.single i (1 : ℝ)) : Fin m → ℝ) (g i)
      exact hφ hTφ0
    refine ⟨T φ / I φ, ?_⟩
    ext f
    let α : ℂ := I f / I φ
    have hker :
        T (f - α • φ) = 0 := by
      have hIntZero : I (f - α • φ) = 0 := by
        have : I f - α * I φ = 0 := by
          dsimp [α]
          field_simp [hIφ]
          ring
        simpa [I, α, map_sub, ContinuousLinearMap.map_smul_of_tower] using this
      obtain ⟨g, hg⟩ := exists_eq_sum_lineDeriv_of_integral_eq_zero (f - α • φ) hIntZero
      rw [hg, map_sum]
      refine Finset.sum_eq_zero ?_
      intro i hi
      exact map_lineDeriv_eq_zero_of_translationInvariant T hT
        ((Pi.single i (1 : ℝ)) : Fin m → ℝ) (g i)
    have hTf : T f = α * T φ := by
      have := hker
      dsimp [α] at this
      exact sub_eq_zero.mp <| by
        simpa [map_sub, ContinuousLinearMap.map_smul_of_tower] using this
    have hIf : (T φ / I φ) * I f = α * T φ := by
      dsimp [α]
      field_simp [hIφ]
    calc
      T f = α * T φ := hTf
      _ = (T φ / I φ) * I f := hIf.symm
      _ = (T φ / I φ) • I f := by simp [smul_eq_mul]
      _ = ((T φ / I φ) • I) f := rfl

theorem exists_eq_const_integralCLM_of_translationInvariant_one
    (T : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsTranslationInvariantSchwartzCLM T) :
    ∃ c : ℂ, T = c • (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 1 → ℝ))) := by
  let I : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ :=
    SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 1 → ℝ))
  by_cases hT0 : T = 0
  · refine ⟨0, ?_⟩
    simp [hT0]
  · classical
    obtain ⟨φ, hφ⟩ : ∃ φ : SchwartzMap (Fin 1 → ℝ) ℂ, T φ ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hT0
      ext ψ
      exact hnone ψ
    have hIφ : I φ ≠ 0 := by
      intro hIφ0
      obtain ⟨g, hg⟩ := exists_eq_sum_lineDeriv_of_integral_eq_zero_one φ hIφ0
      have hTφ0 : T φ = 0 := by
        rw [hg, map_sum]
        refine Finset.sum_eq_zero ?_
        intro i hi
        exact map_lineDeriv_eq_zero_of_translationInvariant T hT
          ((Pi.single i (1 : ℝ)) : Fin 1 → ℝ) (g i)
      exact hφ hTφ0
    refine ⟨T φ / I φ, ?_⟩
    ext f
    let α : ℂ := I f / I φ
    have hker : T (f - α • φ) = 0 := by
      have hIntZero : I (f - α • φ) = 0 := by
        have : I f - α * I φ = 0 := by
          dsimp [α]
          field_simp [hIφ]
          ring
        simpa [I, α, map_sub, ContinuousLinearMap.map_smul_of_tower] using this
      obtain ⟨g, hg⟩ := exists_eq_sum_lineDeriv_of_integral_eq_zero_one (f - α • φ) hIntZero
      rw [hg, map_sum]
      refine Finset.sum_eq_zero ?_
      intro i hi
      exact map_lineDeriv_eq_zero_of_translationInvariant T hT
        ((Pi.single i (1 : ℝ)) : Fin 1 → ℝ) (g i)
    have hTf : T f = α * T φ := by
      exact sub_eq_zero.mp <| by
        simpa [map_sub, ContinuousLinearMap.map_smul_of_tower] using hker
    have hIf : (T φ / I φ) * I f = α * T φ := by
      dsimp [α]
      field_simp [hIφ]
    calc
      T f = α * T φ := hTf
      _ = (T φ / I φ) * I f := hIf.symm
      _ = (T φ / I φ) • I f := by simp [smul_eq_mul]
      _ = ((T φ / I φ) • I) f := rfl

end OSReconstruction
