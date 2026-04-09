/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2Density
import OSReconstruction.Wightman.Reconstruction.TwoPointDescent
import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional
import OSReconstruction.SCV.SemigroupGroupBochner
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv


/-!
# `k = 2` Base-Step Frontier

This file now contains the honest remaining `k = 2` OS-route frontier behind
`schwinger_continuation_base_step_timeParametric`.

The older kernel / difference-lift transport chain has been removed from the
critical path. What remains here is the semigroup / distributional base-step
theorem that still needs to be rebuilt directly from the OS papers' route.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

variable {d : ℕ} [NeZero d]

private def spacetimeTimeReflectionCLE : SpacetimeDim d ≃L[ℝ] SpacetimeDim d where
  toLinearEquiv :=
    { toFun := timeReflection d
      invFun := timeReflection d
      left_inv := timeReflection_timeReflection (d := d)
      right_inv := timeReflection_timeReflection (d := d)
      map_add' := by
        intro x y
        ext i
        by_cases hi : i = 0
        · subst hi
          simp [timeReflection, add_comm]
        · simp [timeReflection, hi]
      map_smul' := by
        intro c x
        ext i
        by_cases hi : i = 0
        · subst hi
          simp [timeReflection]
        · simp [timeReflection, hi] }
  continuous_toFun := by
    refine continuous_pi ?_
    intro i
    by_cases hi : i = 0
    · subst hi
      simpa [timeReflection] using
        (continuous_apply (0 : Fin (d + 1))).neg
    · simpa [timeReflection, hi] using
        (continuous_apply i : Continuous fun y : SpacetimeDim d => y i)
  continuous_invFun := by
    refine continuous_pi ?_
    intro i
    by_cases hi : i = 0
    · subst hi
      simpa [timeReflection] using
        (continuous_apply (0 : Fin (d + 1))).neg
    · simpa [timeReflection, hi] using
        (continuous_apply i : Continuous fun y : SpacetimeDim d => y i)

private theorem timeReflection_norm_eq_local (x : SpacetimeDim d) :
    ‖timeReflection d x‖ = ‖x‖ := by
  have hnn : ‖timeReflection d x‖₊ = ‖x‖₊ := by
    simp only [Pi.nnnorm_def, timeReflection]
    apply Finset.sup_congr rfl
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      simp [nnnorm_neg]
    · simp [h0]
  exact congrArg (fun z : NNReal => (z : ℝ)) hnn

/-- The reflected positive-time companion of a negative-time Schwartz probe. -/
def reflectedSchwartzSpacetime (φ : SchwartzSpacetime d) : SchwartzSpacetime d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ spacetimeTimeReflectionCLE φ

@[simp] private theorem reflectedSchwartzSpacetime_apply
    (φ : SchwartzSpacetime d) (x : SpacetimeDim d) :
    reflectedSchwartzSpacetime φ x = φ (timeReflection d x) := by
  simp [reflectedSchwartzSpacetime, spacetimeTimeReflectionCLE]

theorem reflectedSchwartzSpacetime_hasCompactSupport
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ)) :
    HasCompactSupport (reflectedSchwartzSpacetime φ : SpacetimeDim d → ℂ) := by
  simpa [reflectedSchwartzSpacetime, Function.comp] using
    hφ_compact.comp_homeomorph (spacetimeTimeReflectionCLE.toHomeomorph)

theorem reflectedSchwartzSpacetime_tsupport_pos
    (φ : SchwartzSpacetime d)
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    tsupport (reflectedSchwartzSpacetime φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
  intro x hx
  have hx' : timeReflection d x ∈ tsupport (φ : SpacetimeDim d → ℂ) := by
    exact tsupport_comp_subset_preimage (φ : SpacetimeDim d → ℂ)
      (f := timeReflection d) spacetimeTimeReflectionCLE.continuous hx
  have hneg := hφ_neg hx'
  simpa [timeReflection] using hneg

theorem reflectedSchwartzSpacetime_tsupport_ball
    (φ : SchwartzSpacetime d) {r : ℝ}
    (hφ_support : tsupport (φ : SpacetimeDim d → ℂ) ⊆ Metric.ball (0 : SpacetimeDim d) r) :
    tsupport (reflectedSchwartzSpacetime φ : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) r := by
  intro x hx
  have hx' : timeReflection d x ∈ tsupport (φ : SpacetimeDim d → ℂ) := by
    exact tsupport_comp_subset_preimage (φ : SpacetimeDim d → ℂ)
      (f := timeReflection d) spacetimeTimeReflectionCLE.continuous hx
  have hball := hφ_support hx'
  rw [Metric.mem_ball] at hball ⊢
  simpa [timeReflection_norm_eq_local, sub_eq_add_neg]
    using hball

private theorem reflectedSchwartzSpacetime_integral_eq
    (φ : SchwartzSpacetime d) :
    ∫ x : SpacetimeDim d, reflectedSchwartzSpacetime φ x =
      ∫ x : SpacetimeDim d, φ x := by
  let e : SpacetimeDim d ≃ᵐ SpacetimeDim d :=
    spacetimeTimeReflectionCLE.toHomeomorph.toMeasurableEquiv
  have hmp : MeasureTheory.MeasurePreserving (⇑e)
      MeasureTheory.volume MeasureTheory.volume := by
    simpa [e, spacetimeTimeReflectionCLE] using
      (timeReflection_measurePreserving (d := d))
  simpa [reflectedSchwartzSpacetime_apply] using
    hmp.integral_comp'
      (φ : SpacetimeDim d → ℂ)

/-- Public support-layer form of time-reflection invariance of the total
integral of a Schwartz spacetime probe. The VI.1 file uses this when packaging
the descended normalized center regularizer. -/
theorem reflectedSchwartzSpacetime_integral_eq_local
    (φ : SchwartzSpacetime d) :
    ∫ x : SpacetimeDim d, reflectedSchwartzSpacetime φ x =
      ∫ x : SpacetimeDim d, φ x := by
  exact reflectedSchwartzSpacetime_integral_eq (d := d) φ

private theorem onePointToFin1_tsupport_orderedPositiveTime_local
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro x hx
  have hx0 : x 0 ∈ tsupport (g : SpacetimeDim d → ℂ) := by
    by_contra hx0
    have hzero :
        (x : NPointDomain d 1) ∉ tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) := by
      rw [notMem_tsupport_iff_eventuallyEq] at hx0 ⊢
      simpa [onePointToFin1CLM_apply] using
        hx0.comp_tendsto ((continuous_apply 0).continuousAt.tendsto : Filter.Tendsto
          (fun y : NPointDomain d 1 => y 0) (nhds x) (nhds (x 0)))
    exact hzero hx
  have hpos0 : 0 < (x 0) 0 := hg_pos hx0
  simpa [OrderedPositiveTimeRegion] using hpos0

private theorem tsupport_positive_of_onePointToFin1_tsupport_orderedPositiveTime_local
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
  intro x hx
  let x1 : NPointDomain d 1 := fun _ => x
  have hx1 :
      x1 ∈ tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) := by
    by_contra hx1
    have hzero : x ∉ tsupport (g : SpacetimeDim d → ℂ) := by
      rw [notMem_tsupport_iff_eventuallyEq] at hx1 ⊢
      have hconst_tendsto :
          Filter.Tendsto (fun z : SpacetimeDim d => (fun _ : Fin 1 => z : NPointDomain d 1))
            (nhds x) (nhds x1) := by
        have hcont :
            Continuous (fun z : SpacetimeDim d => (fun _ : Fin 1 => z : NPointDomain d 1)) := by
          refine continuous_pi ?_
          intro i
          simpa using (continuous_id : Continuous (fun z : SpacetimeDim d => z))
        simpa [x1] using hcont.continuousAt.tendsto
      simpa [x1, onePointToFin1CLM_apply] using
        hx1.comp_tendsto hconst_tendsto
    exact hzero hx
  have hord := hg_pos hx1
  simpa [OrderedPositiveTimeRegion, x1] using (hord 0).1

private theorem osConj_onePointToFin1_eq_onePoint_reflected_of_real
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0) :
    SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) =
      (onePointToFin1CLM d (reflectedSchwartzSpacetime φ) : SchwartzNPoint d 1) := by
  ext x
  have him : (φ (timeReflection d (x 0))).im = 0 :=
    hφ_real (timeReflection d (x 0))
  have hstar :
      starRingEnd ℂ (φ (timeReflection d (x 0))) =
        φ (timeReflection d (x 0)) := by
    apply Complex.ext <;> simp [him]
  simpa [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
    reflectedSchwartzSpacetime_apply, timeReflectionN] using hstar

/-- Public wrapper for the real-reflection one-point identity. For a real-valued
one-point spacetime test, `osConj` agrees with time reflection on the one-point
Schwartz tensor. -/
theorem osConj_onePointToFin1_eq_onePoint_reflected_of_real_local
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0) :
    SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) =
      (onePointToFin1CLM d (reflectedSchwartzSpacetime φ) : SchwartzNPoint d 1) :=
  osConj_onePointToFin1_eq_onePoint_reflected_of_real
    (d := d) φ hφ_real

/-- A sequence of nonnegative normalized positive-time Schwartz bumps with
compact support shrinking to the origin. -/
theorem exists_approx_identity_sequence :
    ∃ (φ : ℕ → SchwartzSpacetime d),
      (∀ n x, 0 ≤ (φ n x).re) ∧
      (∀ n x, (φ n x).im = 0) ∧
      (∀ n, ∫ x : SpacetimeDim d, φ n x = 1) ∧
      (∀ n, HasCompactSupport (φ n : SpacetimeDim d → ℂ)) ∧
      (∀ n, tsupport (φ n : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0}) ∧
      (∀ n, tsupport (φ n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ))) := by
  classical
  let φ : ℕ → SchwartzSpacetime d := fun n =>
    Classical.choose
      (exists_approx_identity_schwartz (d := d) (1 / (n + 1 : ℝ)) (by positivity))
  have hs :
      ∀ n,
        (∀ x : SpacetimeDim d, 0 ≤ ((φ n) x).re) ∧
        (∀ x : SpacetimeDim d, ((φ n) x).im = 0) ∧
        (∫ x : SpacetimeDim d, φ n x = 1) ∧
        HasCompactSupport (φ n : SpacetimeDim d → ℂ) ∧
        tsupport (φ n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} ∧
        tsupport (φ n : SpacetimeDim d → ℂ) ⊆
          Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := by
    intro n
    simpa [φ] using
      (Classical.choose_spec
        (exists_approx_identity_schwartz (d := d) (1 / (n + 1 : ℝ)) (by positivity)))
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    exact (hs n).1 x
  · intro n x
    exact (hs n).2.1 x
  · intro n
    exact (hs n).2.2.1
  · intro n
    exact (hs n).2.2.2.1
  · intro n
    exact (hs n).2.2.2.2.1
  · intro n
    exact (hs n).2.2.2.2.2

/-- A sequence of nonnegative normalized negative-time Schwartz bumps with
compact support shrinking to the origin. This is the honest one-point probe
needed on the OS Hilbert side before applying `osConj`, which reflects negative
time to positive time. -/
theorem exists_negative_approx_identity_sequence :
    ∃ (φ : ℕ → SchwartzSpacetime d),
      (∀ n x, 0 ≤ (φ n x).re) ∧
      (∀ n x, (φ n x).im = 0) ∧
      (∀ n, ∫ x : SpacetimeDim d, φ n x = 1) ∧
      (∀ n, HasCompactSupport (φ n : SpacetimeDim d → ℂ)) ∧
      (∀ n, tsupport (φ n : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0}) ∧
      (∀ n, tsupport (φ n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ))) := by
  have hexists :
      ∀ n : ℕ,
        ∃ (φ : SchwartzSpacetime d),
          (∀ x : SpacetimeDim d, 0 ≤ (φ x).re) ∧
          (∀ x : SpacetimeDim d, (φ x).im = 0) ∧
          (∫ x : SpacetimeDim d, φ x = 1) ∧
          HasCompactSupport (φ : SpacetimeDim d → ℂ) ∧
          tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0} ∧
          tsupport (φ : SpacetimeDim d → ℂ) ⊆
            Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := by
    intro n
    let ε : ℝ := 1 / (n + 1 : ℝ)
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    let c : SpacetimeDim d := Fin.cons (-(ε / 2)) 0
    let b : ContDiffBump c := ⟨ε / 8, ε / 4, by linarith, by linarith⟩
    let f : SpacetimeDim d → ℂ := fun x => (b x : ℂ)
    have hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f :=
      (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
    have hf_compact : HasCompactSupport f :=
      b.hasCompactSupport.comp_left Complex.ofReal_zero
    let g₀ := HasCompactSupport.toSchwartzMap hf_compact hf_smooth
    have hg₀_int_ne : ∫ x : SpacetimeDim d, g₀ x ≠ 0 := by
      change ∫ x, (↑(b x) : ℂ) ≠ 0
      rw [integral_complex_ofReal]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt b.integral_pos)
    let φ : SchwartzSpacetime d := (∫ x : SpacetimeDim d, g₀ x)⁻¹ • g₀
    have h_tsup_g₀ : tsupport (g₀ : SpacetimeDim d → ℂ) ⊆ Metric.closedBall c (ε / 4) := by
      intro y hy
      change y ∈ tsupport f at hy
      rw [← b.tsupport_eq]
      exact tsupport_comp_subset Complex.ofReal_zero _ hy
    refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      simp only [φ, SchwartzMap.smul_apply, smul_eq_mul]
      rw [Complex.mul_re]
      have hg₀_im : (g₀ x).im = 0 := Complex.ofReal_im (b x)
      have hg₀_re : 0 ≤ (g₀ x).re := Complex.ofReal_re (b x) ▸ b.nonneg
      have hint_im : (∫ u : SpacetimeDim d, g₀ u).im = 0 := by
        rw [show (fun u => g₀ u) = (fun u => (↑(b u) : ℂ)) from rfl]
        rw [integral_complex_ofReal]
        simp
      have hinv_im : ((∫ u : SpacetimeDim d, g₀ u)⁻¹).im = 0 := by
        rw [Complex.inv_im, hint_im]
        ring_nf
      rw [hg₀_im, hinv_im]
      ring_nf
      apply mul_nonneg _ hg₀_re
      rw [Complex.inv_re]
      apply div_nonneg
      · change 0 ≤ (∫ u, (↑(b u) : ℂ)).re
        rw [integral_complex_ofReal]
        simp only [Complex.ofReal_re]
        exact le_of_lt b.integral_pos
      · exact Complex.normSq_nonneg _
    · intro x
      simp only [φ, SchwartzMap.smul_apply, smul_eq_mul]
      rw [Complex.mul_im]
      have hg₀_im : (g₀ x).im = 0 := Complex.ofReal_im (b x)
      have hint_im : (∫ u : SpacetimeDim d, g₀ u).im = 0 := by
        rw [show (fun u => g₀ u) = (fun u => (↑(b u) : ℂ)) from rfl]
        rw [integral_complex_ofReal]
        simp
      have hinv_im : ((∫ u : SpacetimeDim d, g₀ u)⁻¹).im = 0 := by
        rw [Complex.inv_im, hint_im]
        ring_nf
      rw [hg₀_im, hinv_im]
      ring_nf
    · change ∫ x : SpacetimeDim d, ((∫ x : SpacetimeDim d, g₀ x)⁻¹ • g₀ x) = 1
      rw [MeasureTheory.integral_smul]
      change (∫ x : SpacetimeDim d, g₀ x)⁻¹ * ∫ x : SpacetimeDim d, g₀ x = 1
      field_simp [hg₀_int_ne]
    · simpa [φ, Pi.smul_apply] using
        (HasCompactSupport.smul_left (f := fun _ : SpacetimeDim d => (∫ x : SpacetimeDim d, g₀ x)⁻¹)
          (f' := (g₀ : SpacetimeDim d → ℂ)) hf_compact)
    · intro x hx
      have hx_supp : x ∈ Metric.closedBall c (ε / 4 : ℝ) := by
        have hx_g₀ : x ∈ tsupport (g₀ : SpacetimeDim d → ℂ) := by
          exact (tsupport_smul_subset_right
            (fun _ : SpacetimeDim d => (∫ x : SpacetimeDim d, g₀ x)⁻¹)
            (g₀ : SpacetimeDim d → ℂ)) hx
        exact h_tsup_g₀ hx_g₀
      rw [Metric.mem_closedBall] at hx_supp
      have h0 : |x 0 - (-(ε / 2))| ≤ ε / 4 := by
        calc
          |x 0 - (-(ε / 2))| = |x 0 - c 0| := by simp [c, Fin.cons]
          _ = ‖(x - c) 0‖ := by simp [Pi.sub_apply, Real.norm_eq_abs]
          _ ≤ ‖x - c‖ := norm_le_pi_norm _ 0
          _ = dist x c := by rw [dist_eq_norm]
          _ ≤ ε / 4 := hx_supp
      change x 0 < 0
      have hupper : x 0 + ε / 2 ≤ ε / 4 := by
        linarith [(abs_le.mp h0).2]
      linarith
    · intro x hx
      have hx_supp : x ∈ Metric.closedBall c (ε / 4 : ℝ) := by
        have hx_g₀ : x ∈ tsupport (g₀ : SpacetimeDim d → ℂ) := by
          exact (tsupport_smul_subset_right
            (fun _ : SpacetimeDim d => (∫ x : SpacetimeDim d, g₀ x)⁻¹)
            (g₀ : SpacetimeDim d → ℂ)) hx
        exact h_tsup_g₀ hx_g₀
      have hdist0 : dist x (0 : SpacetimeDim d) < ε := by
        calc
          dist x (0 : SpacetimeDim d) ≤ dist x c + dist c (0 : SpacetimeDim d) :=
            dist_triangle _ _ _
          _ ≤ ε / 4 + ε / 2 := by
            gcongr
            · simpa [Metric.mem_closedBall, dist_eq_norm] using hx_supp
            · rw [dist_eq_norm]
              have hc_coord : ∀ b : Fin (d + 1), ‖c b‖ ≤ ε / 2 := by
                intro b'
                refine Fin.cases ?_ ?_ b'
                · have hεabs : |ε| = ε := abs_of_pos hε
                  simp [c, Real.norm_eq_abs, hεabs]
                · intro j
                  have : (0 : ℝ) ≤ ε / 2 := by linarith
                  simpa [c] using this
              have : ‖c‖ ≤ ε / 2 := by
                rw [Pi.norm_def]
                have hs :
                    Finset.univ.sup (fun b : Fin (d + 1) => ‖c b‖₊) ≤ Real.toNNReal (ε / 2) := by
                  refine Finset.sup_le ?_
                  intro b' hb'
                  rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg]
                  · exact hc_coord b'
                  · linarith
                have hε2 : 0 ≤ ε / 2 := by linarith
                have hs_real : (↑(Finset.univ.sup (fun b : Fin (d + 1) => ‖c b‖₊) : NNReal) : ℝ) ≤
                    ↑(Real.toNNReal (ε / 2)) := by
                  exact_mod_cast hs
                simpa [Real.toNNReal_of_nonneg hε2] using hs_real
              simpa using this
          _ < ε := by linarith
      simpa [Metric.mem_ball, dist_comm, ε] using hdist0
  let φ : ℕ → SchwartzSpacetime d := fun n => Classical.choose (hexists n)
  have hs :
      ∀ n,
        (∀ x : SpacetimeDim d, 0 ≤ ((φ n) x).re) ∧
        (∀ x : SpacetimeDim d, ((φ n) x).im = 0) ∧
        (∫ x : SpacetimeDim d, φ n x = 1) ∧
        HasCompactSupport (φ n : SpacetimeDim d → ℂ) ∧
        tsupport (φ n : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0} ∧
        tsupport (φ n : SpacetimeDim d → ℂ) ⊆
          Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := by
    intro n
    simpa [φ] using (Classical.choose_spec (hexists n))
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    exact (hs n).1 x
  · intro n x
    exact (hs n).2.1 x
  · intro n
    exact (hs n).2.2.1
  · intro n
    exact (hs n).2.2.2.1
  · intro n
    exact (hs n).2.2.2.2.1
  · intro n
    exact (hs n).2.2.2.2.2

/-- A normalized real nonnegative approximate identity with shrinking support
recovers the value of any function continuous at `0`. -/
private theorem approxIdentity_integral_tendsto_of_continuousAt_zero
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_support : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    {ψ : SpacetimeDim d → ℂ}
    (hψ_cont : Continuous ψ) :
    Filter.Tendsto (fun n => ∫ x : SpacetimeDim d, φ_seq n x * ψ x)
      Filter.atTop (nhds (ψ 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hψ_cont0 : ContinuousAt ψ 0 := hψ_cont.continuousAt
  rw [Metric.continuousAt_iff] at hψ_cont0
  obtain ⟨δ, hδpos, hδ⟩ := hψ_cont0 (ε / 2) hε2
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 1 / (n + 1 : ℝ) < δ := by
    rcases exists_nat_one_div_lt hδpos with ⟨N, hN⟩
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hmono : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      have hNle : (N + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ hn
      exact one_div_le_one_div_of_le (by positivity) hNle
    exact lt_of_le_of_lt hmono hN
  filter_upwards [hsmall] with n hn
  have hnorm_int : ∫ x : SpacetimeDim d, ‖φ_seq n x‖ = 1 := by
    have hnorm_re : ∀ x : SpacetimeDim d, ‖φ_seq n x‖ = (φ_seq n x).re := by
      intro x
      rw [← Complex.re_eq_norm.mpr ⟨hφ_nonneg n x, (hφ_real n x).symm⟩]
    simp_rw [hnorm_re]
    rw [show (fun x => (φ_seq n x).re) = (fun x => RCLike.re (φ_seq n x)) from rfl]
    rw [integral_re (SchwartzMap.integrable (φ_seq n))]
    exact congrArg Complex.re (hφ_int n)
  have hbound : ∀ x : SpacetimeDim d,
      ‖φ_seq n x * (ψ x - ψ 0)‖ ≤ (ε / 2) * ‖φ_seq n x‖ := by
    intro x
    by_cases hx : x ∈ tsupport (φ_seq n : SpacetimeDim d → ℂ)
    · have hxball : x ∈ Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := hφ_support n hx
      have hxdist : dist x 0 < δ := by
        have : dist x 0 < 1 / (n + 1 : ℝ) := by
          simpa [Metric.mem_ball] using hxball
        exact lt_of_lt_of_le this hn.le
      have hψx : ‖ψ x - ψ 0‖ < ε / 2 := by
        simpa [dist_eq_norm] using hδ hxdist
      calc
        ‖φ_seq n x * (ψ x - ψ 0)‖ = ‖φ_seq n x‖ * ‖ψ x - ψ 0‖ := by
          rw [norm_mul]
        _ ≤ ‖φ_seq n x‖ * (ε / 2) := by
          gcongr
        _ = (ε / 2) * ‖φ_seq n x‖ := by ring
    · have hx0 : φ_seq n x = 0 := by
        by_contra hx0
        exact hx (subset_tsupport _ (Function.mem_support.mpr hx0))
      simp [hx0]
  have hmeas : AEStronglyMeasurable (fun x => φ_seq n x * (ψ x - ψ 0)) := by
    exact ((SchwartzMap.continuous (φ_seq n)).mul
      (hψ_cont.sub continuous_const)).aestronglyMeasurable
  have hIntDiff : Integrable (fun x : SpacetimeDim d => φ_seq n x * (ψ x - ψ 0)) := by
    refine Integrable.mono' (((SchwartzMap.integrable (φ_seq n)).norm).const_mul (ε / 2)) hmeas ?_
    exact Filter.Eventually.of_forall hbound
  have hIntProd : Integrable (fun x : SpacetimeDim d => φ_seq n x * ψ x) := by
    have hEq : (fun x : SpacetimeDim d => φ_seq n x * ψ x) =
        fun x => φ_seq n x * (ψ x - ψ 0) + (ψ 0) * φ_seq n x := by
      funext x
      ring
    rw [hEq]
    exact hIntDiff.add ((SchwartzMap.integrable (φ_seq n)).const_mul (ψ 0))
  have hEqInt :
      (∫ x : SpacetimeDim d, φ_seq n x * ψ x) - ψ 0 =
        ∫ x : SpacetimeDim d, φ_seq n x * (ψ x - ψ 0) := by
    have hconst_int :
        ∫ x : SpacetimeDim d, (ψ 0) * φ_seq n x = ψ 0 := by
      calc
        ∫ x : SpacetimeDim d, (ψ 0) * φ_seq n x
            = (ψ 0) * ∫ x : SpacetimeDim d, φ_seq n x := by
                exact MeasureTheory.integral_const_mul (ψ 0) (fun x : SpacetimeDim d => φ_seq n x)
        _ = ψ 0 := by simpa [hφ_int n]
    calc
      (∫ x : SpacetimeDim d, φ_seq n x * ψ x) - ψ 0
          = (∫ x : SpacetimeDim d, φ_seq n x * ψ x) -
              ∫ x : SpacetimeDim d, (ψ 0) * φ_seq n x := by
              rw [hconst_int]
      _ = ∫ x : SpacetimeDim d, ((φ_seq n x * ψ x) - (ψ 0) * φ_seq n x) := by
            rw [← MeasureTheory.integral_sub hIntProd ((SchwartzMap.integrable (φ_seq n)).const_mul (ψ 0))]
      _ = ∫ x : SpacetimeDim d, φ_seq n x * (ψ x - ψ 0) := by
            congr with x
            ring
  calc
    dist (∫ x : SpacetimeDim d, φ_seq n x * ψ x) (ψ 0)
        = ‖(∫ x : SpacetimeDim d, φ_seq n x * ψ x) - ψ 0‖ := by
            rw [dist_eq_norm]
    _ = ‖∫ x : SpacetimeDim d, φ_seq n x * (ψ x - ψ 0)‖ := by
          rw [hEqInt]
    _ ≤ ∫ x : SpacetimeDim d, ‖φ_seq n x * (ψ x - ψ 0)‖ := by
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ x : SpacetimeDim d, (ε / 2) * ‖φ_seq n x‖ := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact (((SchwartzMap.integrable (φ_seq n)).norm).const_mul (ε / 2))
          · exact Filter.Eventually.of_forall hbound
    _ = (ε / 2) * ∫ x : SpacetimeDim d, ‖φ_seq n x‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ = ε / 2 := by
          simp [hnorm_int]
    _ < ε := by
          linarith

/-- The reflected companions of a shrinking negative approximate identity act
as an honest positive approximate identity on translated test functions,
pointwise at every spacetime point. -/
private theorem reflected_negativeApproxIdentity_translate_tendsto_self_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_support : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (g : SchwartzSpacetime d)
    (x : SpacetimeDim d) :
    Filter.Tendsto
      (fun n =>
        ∫ ξ : SpacetimeDim d,
          reflectedSchwartzSpacetime (φ_seq n) ξ *
            (SCV.translateSchwartz (-ξ) g) x)
      Filter.atTop (nhds (g x)) := by
  have hψ_nonneg : ∀ n y, 0 ≤ (reflectedSchwartzSpacetime (φ_seq n) y).re := by
    intro n y
    simpa [reflectedSchwartzSpacetime_apply] using hφ_nonneg n (timeReflection d y)
  have hψ_real : ∀ n y, (reflectedSchwartzSpacetime (φ_seq n) y).im = 0 := by
    intro n y
    simpa [reflectedSchwartzSpacetime_apply] using hφ_real n (timeReflection d y)
  have hψ_int : ∀ n, ∫ y : SpacetimeDim d, reflectedSchwartzSpacetime (φ_seq n) y = 1 := by
    intro n
    rw [reflectedSchwartzSpacetime_integral_eq]
    exact hφ_int n
  have hψ_support :
      ∀ n, tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := by
    intro n
    exact reflectedSchwartzSpacetime_tsupport_ball (d := d) (φ_seq n) (hφ_support n)
  let ψ : SpacetimeDim d → ℂ := fun ξ => (SCV.translateSchwartz (-ξ) g) x
  have hψ_cont : Continuous ψ := by
    change Continuous (fun ξ : SpacetimeDim d => g (x + -ξ))
    exact g.continuous.comp ((continuous_const.sub continuous_id'))
  have hmain :=
    approxIdentity_integral_tendsto_of_continuousAt_zero
      (d := d) (fun n => reflectedSchwartzSpacetime (φ_seq n))
      hψ_nonneg hψ_real hψ_int hψ_support hψ_cont
  simpa [ψ, SCV.translateSchwartz_apply] using hmain

/-- Pointwise form of the previous regularization lemma on the honest positive-
time compact-support test space. The reflected probes act by convolution and
recover the original test pointwise.

This is intentionally public within the Wick-rotation route because later VI.1
arguments may need the direct smoothing statement without reopening the raw
Schwartz approximate-identity proof. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_apply_tendsto_self_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_support : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (g : positiveTimeCompactSupportSubmodule d)
    (x : SpacetimeDim d) :
    Filter.Tendsto
      (fun n =>
        let ψn : positiveTimeCompactSupportSubmodule d :=
          ⟨reflectedSchwartzSpacetime (φ_seq n),
            ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
              reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n) (hφ_compact n)⟩⟩
        (((positiveTimeCompactSupportConvolution ψn
            g : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) x))
      Filter.atTop (nhds ((g : SchwartzSpacetime d) x)) := by
  have hmain :=
    reflected_negativeApproxIdentity_translate_tendsto_self_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_support (g : SchwartzSpacetime d) x
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards with n
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n) (hφ_compact n)⟩⟩
  have hψn_coe :
      ((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) =
        reflectedSchwartzSpacetime (φ_seq n) := by
    rfl
  simpa [ψn, hψn_coe] using
    (positiveTimeCompactSupportConvolution_apply_eq_integral_translate
      (h := ψn) (g := g) x)

/-- Nonnegative real-valued normalized approximate-identity probes have
unit `L¹` norm. -/
private theorem approxIdentity_L1_norm_eq_one_local
    (φ : SchwartzSpacetime d)
    (hφ_nonneg : ∀ x, 0 ≤ (φ x).re)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_int : ∫ x : SpacetimeDim d, φ x = 1) :
    ∫ x : SpacetimeDim d, ‖φ x‖ = 1 := by
  have hnorm_re : ∀ x : SpacetimeDim d, ‖φ x‖ = (φ x).re := by
    intro x
    rw [← Complex.re_eq_norm.mpr ⟨hφ_nonneg x, (hφ_real x).symm⟩]
  simp_rw [hnorm_re]
  rw [show (fun x => (φ x).re) = (fun x => RCLike.re (φ x)) from rfl]
  rw [integral_re (SchwartzMap.integrable φ)]
  have := congrArg Complex.re hφ_int
  simpa using this

/-- Schwartz spacetime test functions are globally Lipschitz, with a constant
controlled by the first Schwartz seminorm. -/
private theorem schwartz_lipschitz_bound_local
    (h : SchwartzSpacetime d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x y : SpacetimeDim d),
      ‖(h : SpacetimeDim d → ℂ) x - h y‖ ≤ C * ‖x - y‖ := by
  set C₀ := SchwartzMap.seminorm ℝ 0 1 h
  have hfderiv_bound : ∀ x : SpacetimeDim d, ‖fderiv ℝ (h : SpacetimeDim d → ℂ) x‖ ≤ C₀ := by
    intro x
    have h1 := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ h 1 x
    rwa [norm_iteratedFDeriv_one (𝕜 := ℝ) (f := (h : SpacetimeDim d → ℂ))] at h1
  refine ⟨max C₀ 1, by positivity, fun x y => ?_⟩
  have hdiff : Differentiable ℝ (h : SpacetimeDim d → ℂ) := h.differentiable
  calc
    ‖(h : SpacetimeDim d → ℂ) x - h y‖ = ‖(h : SpacetimeDim d → ℂ) y - h x‖ := by
      rw [norm_sub_rev]
    _ ≤ C₀ * ‖y - x‖ := by
      exact Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hdiff.differentiableAt) (fun z _ => hfderiv_bound z)
        convex_univ (Set.mem_univ y) (Set.mem_univ x)
    _ ≤ max C₀ 1 * ‖y - x‖ := by
      apply mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ = max C₀ 1 * ‖x - y‖ := by rw [norm_sub_rev]

/-- Local support bridge: negative-time support of a one-point spacetime probe
becomes ordered positive-time support after `osConj`, because time reflection
flips the sign of the time coordinate. This is the exact support input needed
for the OS Hilbert one-point vector in theorem 2, without importing the
downstream kernel file. -/
theorem osConj_onePointToFin1_tsupport_orderedPositiveTime_local
    (χ : SchwartzSpacetime d)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hχ_neg : tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro v hv i
  refine ⟨?_, fun j hij => absurd hij (by omega)⟩
  rw [Fin.eq_zero i]
  by_contra h_neg
  push_neg at h_neg
  have ⟨δ, hδ_pos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧
      tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 ≤ -δ} := by
    by_cases hempty : tsupport (χ : SpacetimeDim d → ℂ) = ∅
    · exact ⟨1, one_pos, by simp [hempty]⟩
    · have hne := Set.nonempty_iff_ne_empty.mpr hempty
      have hK : IsCompact (tsupport (χ : SpacetimeDim d → ℂ)) :=
        hχ_compact.isCompact
      obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := hK.exists_isMaxOn hne (continuous_apply 0).continuousOn
      have hx₀_neg : x₀ 0 < 0 := hχ_neg hx₀_mem
      refine ⟨-(x₀ 0) / 2, by linarith, fun y hy => ?_⟩
      simp only [Set.mem_setOf_eq]
      have h_le : y 0 ≤ x₀ 0 := hx₀_max hy
      linarith
  have h_vanish : ∀ w : NPointDomain d 1, w 0 0 < δ →
      ((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ)) : NPointDomain d 1 → ℂ) w = 0 := by
    intro w hw
    simp only [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply]
    have h_not_supp : timeReflectionN d w 0 ∉ tsupport (χ : SpacetimeDim d → ℂ) := by
      intro hmem
      have h1 := hδ hmem
      simp only [Set.mem_setOf_eq, timeReflectionN, timeReflection, ite_true] at h1
      linarith
    have h_ev := (notMem_tsupport_iff_eventuallyEq.mp h_not_supp).self_of_nhds
    simp [h_ev]
  have h_not_tsupport : v ∉ tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d χ)) : NPointDomain d 1 → ℂ)) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    refine Filter.mem_of_superset (Metric.ball_mem_nhds v hδ_pos) ?_
    intro w hw
    apply h_vanish
    have h_dist : ‖w - v‖ < δ := by rwa [← dist_eq_norm]
    have h0 : w 0 0 - v 0 0 ≤ ‖w - v‖ := by
      calc
        w 0 0 - v 0 0 = (w - v) 0 0 := by simp
        _ ≤ |(w - v) 0 0| := by exact le_abs_self ((w - v) 0 0)
        _ = ‖((w - v) 0) 0‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖(w - v) 0‖ := norm_le_pi_norm _ 0
        _ ≤ ‖w - v‖ := norm_le_pi_norm _ 0
    linarith
  exact h_not_tsupport hv

private theorem mk_single_osConj_onePoint_eq_mk_single_reflected_of_real
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local φ hφ_compact hφ_neg
    let ψ := reflectedSchwartzSpacetime φ
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos φ hφ_neg
    let hψ_pos :=
      onePointToFin1_tsupport_orderedPositiveTime_local ψ hψ_pos_time
    (⟦PositiveTimeBorchersSequence.single 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d φ : SchwartzNPoint d 1))
        hφ_pos⟧ : OSPreHilbertSpace OS) =
      (⟦PositiveTimeBorchersSequence.single 1
          (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
          hψ_pos⟧ : OSPreHilbertSpace OS) := by
  dsimp
  apply OSPreHilbertSpace.mk_eq_of_funcs_eq
  intro n
  by_cases hn : n = 1
  · subst hn
    simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, osConj_onePointToFin1_eq_onePoint_reflected_of_real,
      hφ_real]
  · simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, hn]

/-- Public wrapper for the quotient-level identification of a real negative-time
probe with its reflected positive-time one-point vector. -/
theorem mk_single_osConj_onePoint_eq_mk_single_reflected_of_real_local
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local φ hφ_compact hφ_neg
    let ψ := reflectedSchwartzSpacetime φ
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos φ hφ_neg
    let hψ_pos :=
      onePointToFin1_tsupport_orderedPositiveTime_local ψ hψ_pos_time
    (⟦PositiveTimeBorchersSequence.single 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d φ : SchwartzNPoint d 1))
        hφ_pos⟧ : OSPreHilbertSpace OS) =
      (⟦PositiveTimeBorchersSequence.single 1
          (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
          hψ_pos⟧ : OSPreHilbertSpace OS) :=
  mk_single_osConj_onePoint_eq_mk_single_reflected_of_real
    (d := d) OS φ hφ_real hφ_compact hφ_neg

private theorem onePoint_osConjTensorProduct_apply_local
    (χ h : SchwartzSpacetime d) (y : NPointDomain d 2) :
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (onePointToFin1CLM d h)) y) =
      χ (y 0) * h (y 1) := by
  have hosconj :
      SchwartzNPoint.osConj (d := d) (n := 1)
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)) =
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
    ext x
    simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
      timeReflectionN, timeReflection_timeReflection]
  calc
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (onePointToFin1CLM d h)) y)
      = (((onePointToFin1CLM d χ : SchwartzNPoint d 1).tensorProduct
          (onePointToFin1CLM d h)) y) := by
            simp [SchwartzNPoint.osConjTensorProduct, hosconj]
    _ = χ (y 0) * h (y 1) := by
          rw [SchwartzMap.tensorProduct_apply]
          simp [onePointToFin1CLM_apply, splitFirst, splitLast]

private theorem twoPointProductLift_vanishes_of_orderedPositiveTime_local
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    VanishesToInfiniteOrderOnCoincidence (twoPointProductLift χ h) := by
  have hh_ord :=
    onePointToFin1_tsupport_orderedPositiveTime_local h hh_pos
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence
        ((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ)).osConjTensorProduct
          (onePointToFin1CLM d h)) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d)
      (f := SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      (g := onePointToFin1CLM d h)
      hχ_pos hh_ord
  have hprod_eq :
      (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ)).osConjTensorProduct
        (onePointToFin1CLM d h) =
        twoPointProductLift χ h := by
    ext x
    exact onePoint_osConjTensorProduct_apply_local χ h x
  simpa [hprod_eq] using hvanish

private theorem twoPointProductLift_nonzero_implies_offDiagonal_local
    (χ h : SchwartzSpacetime d)
    (hχ_neg : tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    {x : NPointDomain d 2}
    (hx : twoPointProductLift χ h x ≠ 0) :
    x 0 ≠ x 1 := by
  have hχx : χ (x 0) ≠ 0 := by
    intro hzero
    apply hx
    simp [twoPointProductLift_apply, hzero]
  have hhx : h (x 1) ≠ 0 := by
    intro hzero
    apply hx
    simp [twoPointProductLift_apply, hzero]
  have hx0_mem : x 0 ∈ tsupport (χ : SpacetimeDim d → ℂ) := by
    exact subset_tsupport _ (by simpa [Function.mem_support] using hχx)
  have hx1_mem : x 1 ∈ tsupport (h : SpacetimeDim d → ℂ) := by
    exact subset_tsupport _ (by simpa [Function.mem_support] using hhx)
  have hx0_neg : (x 0) 0 < 0 := hχ_neg hx0_mem
  have hx1_pos : 0 < (x 1) 0 := hh_pos hx1_mem
  intro hdiag
  have : (x 0) 0 = (x 1) 0 := by simpa [hdiag]
  linarith

private theorem zero_not_mem_tsupport_of_positiveTime_local
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
  intro h0
  have h0' := hh_pos h0
  simpa using h0'

private def twoPointProductLiftPositiveZeroDiagCLM_local
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    positiveTimeCompactSupportSubmodule d →L[ℂ] ZeroDiagonalSchwartz d 2 :=
  (((SchwartzMap.prependFieldCLMRight (E := SpacetimeDim d) χ).comp
      ((onePointToFin1CLM d).comp (positiveTimeCompactSupportValCLM d))).codRestrict
      (zeroDiagonalSubmodule d 2)
      (fun h =>
        twoPointProductLift_vanishes_of_orderedPositiveTime_local
          χ (h : SchwartzSpacetime d) hχ_pos h.property.1))

@[simp] private theorem twoPointProductLiftPositiveZeroDiagCLM_local_eq_ofClassical
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (h : positiveTimeCompactSupportSubmodule d) :
    twoPointProductLiftPositiveZeroDiagCLM_local χ hχ_pos h =
      ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (h : SchwartzSpacetime d)) := by
  let hvanish :=
    twoPointProductLift_vanishes_of_orderedPositiveTime_local
      χ (h : SchwartzSpacetime d) hχ_pos h.property.1
  apply Subtype.ext
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
    (f := twoPointProductLift χ (h : SchwartzSpacetime d)) hvanish]
  rfl

private def schwingerProductPositiveCLM_local
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    positiveTimeCompactSupportSubmodule d →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).comp
    (twoPointProductLiftPositiveZeroDiagCLM_local χ hχ_pos)

@[simp] private theorem schwingerProductPositiveCLM_local_apply
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (h : positiveTimeCompactSupportSubmodule d) :
    schwingerProductPositiveCLM_local OS χ hχ_pos h =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (h : SchwartzSpacetime d))) := by
  simp [schwingerProductPositiveCLM_local, ContinuousLinearMap.comp_apply,
    twoPointProductLiftPositiveZeroDiagCLM_local_eq_ofClassical,
    OsterwalderSchraderAxioms.schwingerCLM]

/-- The translated positive-time compactly supported one-point test remains in
the positive-time compact-support domain. This is the honest right-slot domain
for the reflected probe used in theorem B. -/
private def reflectedPositiveTimeCompactSupport_local
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    positiveTimeCompactSupportSubmodule d :=
  ⟨reflectedSchwartzSpacetime φ,
    ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg,
      reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact⟩⟩

/-- The reflected companion of a negative-time compactly supported probe is an
honest positive-time compact-support test. -/
@[simp] private theorem reflectedPositiveTimeCompactSupport_local_coe
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    ((reflectedPositiveTimeCompactSupport_local (d := d) φ hφ_compact hφ_neg :
        positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) =
      reflectedSchwartzSpacetime φ := by
  rfl

/-- The translated positive-time compactly supported one-point test remains in
the positive-time compact-support domain. This is the honest right-slot domain
for the reflected probe used in theorem B. -/
private def translatedPositiveTimeCompactSupport_local
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    positiveTimeCompactSupportSubmodule d := by
  let gξ : SchwartzSpacetime d := SCV.translateSchwartz (-ξ) g
  have hgξ_compact : HasCompactSupport (gξ : SpacetimeDim d → ℂ) := by
    simpa [gξ, Function.comp, SCV.translateSchwartz_apply] using
      hg_compact.comp_homeomorph (Homeomorph.addRight (-ξ))
  have hgξ_pos : tsupport (gξ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
    intro x hx
    have hx' : x + (-ξ) ∈ tsupport (g : SpacetimeDim d → ℂ) := by
      exact tsupport_comp_subset_preimage (g : SpacetimeDim d → ℂ)
        (f := fun y : SpacetimeDim d => y + (-ξ))
        (Homeomorph.addRight (-ξ)).continuous hx
    have hgx := hg_pos hx'
    simpa using add_pos_of_pos_of_nonneg hξ (show 0 ≤ (x + -ξ) 0 from le_of_lt hgx)
  exact ⟨gξ, ⟨hgξ_pos, hgξ_compact⟩⟩

@[simp] private theorem schwingerProductPositiveCLM_local_apply_translated
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    schwingerProductPositiveCLM_local OS χ hχ_pos
        (translatedPositiveTimeCompactSupport_local g hg_pos hg_compact ξ hξ) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (SCV.translateSchwartz (-ξ) g))) := by
  simpa [translatedPositiveTimeCompactSupport_local] using
    schwingerProductPositiveCLM_local_apply OS χ hχ_pos
      (translatedPositiveTimeCompactSupport_local g hg_pos hg_compact ξ hξ)

/-- The inner product of two one-point positive-time vectors is exactly the
two-point Schwinger evaluation of the corresponding OS tensor product. -/
private theorem onePoint_positive_inner_eq_schwinger_local
    (OS : OsterwalderSchraderAxioms d)
    (f g : SchwartzNPoint d 1)
    (hf : tsupport ((f : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆
      OrderedPositiveTimeRegion d 1)
    (hg : tsupport ((g : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆
      OrderedPositiveTimeRegion d 1) :
    let vf : OSPreHilbertSpace OS :=
      ⟦PositiveTimeBorchersSequence.single 1 f hf⟧
    let vg : OSPreHilbertSpace OS :=
      ⟦PositiveTimeBorchersSequence.single 1 g hg⟧
    @inner ℂ (OSPreHilbertSpace OS) _ vf vg =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  dsimp
  unfold PositiveTimeBorchersSequence.osInner
  simpa using
    (OSInnerProduct_single_single (d := d) OS.S OS.E0_linear 1 1 f g)

/-- The raw OS tensor-product witness agrees pointwise with the ordinary
two-point product lift. -/
private theorem osConjTensorProduct_eq_twoPointProductLift_local
    (χ h : SchwartzSpacetime d) :
    (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (onePointToFin1CLM d h) =
      twoPointProductLift χ h := by
  have hosconj :
      SchwartzNPoint.osConj (d := d) (n := 1)
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)) =
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
    ext x
    simp [onePointToFin1CLM_apply]
  ext y
  calc
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (onePointToFin1CLM d h)) y)
      = (((onePointToFin1CLM d χ : SchwartzNPoint d 1).tensorProduct
          (onePointToFin1CLM d h)) y) := by
            simp [SchwartzNPoint.osConjTensorProduct, hosconj]
    _ = twoPointProductLift χ h y := by
          rw [twoPointProductLift_apply]
          rw [SchwartzMap.tensorProduct_apply]
          simp [onePointToFin1CLM_apply, splitFirst, splitLast]

/-- The honest OS Hilbert vector attached to a positive-time compact-support
one-point Schwartz test. -/
private def positiveTimeOnePointVector_local
    (OS : OsterwalderSchraderAxioms d)
    (h : positiveTimeCompactSupportSubmodule d) : OSHilbertSpace OS :=
  (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single 1
          (onePointToFin1CLM d (h : SchwartzSpacetime d) : SchwartzNPoint d 1)
          (onePointToFin1_tsupport_orderedPositiveTime_local (d := d)
            (h : SchwartzSpacetime d) h.property.1)⟧)) : OSHilbertSpace OS))

/-- The positive-time one-point vector is already linear at the pre-Hilbert
quotient level. This is the OS-side linearity needed before any later
Bochner/interchange step. -/
private def positiveTimeOnePointVectorLM_local
    (OS : OsterwalderSchraderAxioms d) :
    positiveTimeCompactSupportSubmodule d →ₗ[ℂ] OSPreHilbertSpace OS where
  toFun h :=
    ⟦PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d (h : SchwartzSpacetime d) : SchwartzNPoint d 1)
      (onePointToFin1_tsupport_orderedPositiveTime_local (d := d)
        (h : SchwartzSpacetime d) h.property.1)⟧
  map_add' h₁ h₂ := by
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro n
    by_cases hn : n = 1
    · subst hn
      simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single]
    · simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single, hn]
  map_smul' c h := by
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro n
    by_cases hn : n = 1
    · subst hn
      simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single]
    · simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single, hn]

@[simp] private theorem positiveTimeOnePointVectorLM_local_coe
    (OS : OsterwalderSchraderAxioms d)
    (h : positiveTimeCompactSupportSubmodule d) :
    ((positiveTimeOnePointVectorLM_local (d := d) OS h : OSPreHilbertSpace OS) :
        OSHilbertSpace OS) =
      positiveTimeOnePointVector_local (d := d) OS h := by
  rfl

/-- The product-shell Schwinger CLM is exactly the OS Hilbert inner product
against the positive-time one-point vector. -/
private theorem inner_positiveTimeOnePointVector_eq_schwingerProductPositiveCLM_local
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (h : positiveTimeCompactSupportSubmodule d) :
    @inner ℂ (OSHilbertSpace OS) _
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1))
              hχ_pos⟧)) : OSHilbertSpace OS))
      (positiveTimeOnePointVector_local (d := d) OS h) =
      schwingerProductPositiveCLM_local OS χ hχ_pos h := by
  let hh_ord :
      tsupport (((onePointToFin1CLM d (h : SchwartzSpacetime d) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime_local (d := d) (h : SchwartzSpacetime d) h.property.1
  rw [schwingerProductPositiveCLM_local_apply]
  simp [positiveTimeOnePointVector_local]
  simpa [osConjTensorProduct_eq_twoPointProductLift_local] using
    (onePoint_positive_inner_eq_schwinger_local (d := d) OS
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      (onePointToFin1CLM d (h : SchwartzSpacetime d) : SchwartzNPoint d 1)
      hχ_pos hh_ord)

/-- The translated positive-time test, viewed as an OS Hilbert vector. -/
private def translatedPositiveTimeOnePointVector_local
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) : OSHilbertSpace OS :=
  positiveTimeOnePointVector_local (d := d) OS
    (translatedPositiveTimeCompactSupport_local g hg_pos hg_compact ξ hξ)

/-- The translated product-shell integrand is exactly the OS Hilbert inner
product against the translated positive-time one-point vector. -/
private theorem inner_translatedPositiveTimeOnePointVector_eq_translated_productShell_local
    (OS : OsterwalderSchraderAxioms d)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    @inner ℂ (OSHilbertSpace OS) _
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1))
              hχ_pos⟧)) : OSHilbertSpace OS))
      (translatedPositiveTimeOnePointVector_local (d := d) OS g hg_pos hg_compact ξ hξ) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (SCV.translateSchwartz (-ξ) g))) := by
  simpa [translatedPositiveTimeOnePointVector_local, translatedPositiveTimeCompactSupport_local] using
    (inner_positiveTimeOnePointVector_eq_schwingerProductPositiveCLM_local
      (d := d) OS χ hχ_pos
      (translatedPositiveTimeCompactSupport_local g hg_pos hg_compact ξ hξ))

/-- Positive Euclidean time shift on the OS Hilbert space sends the one-point
vector of `g` to the one-point vector of the time-translated test. -/
private theorem osTimeShiftHilbert_positiveTimeOnePointVector_eq_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (t : ℝ)
    (ht : 0 < t) :
    osTimeShiftHilbert (d := d) OS lgc t ht
      (positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩) =
      positiveTimeOnePointVector_local (d := d) OS
        (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact
          (timeShiftVec d t) (by simpa [timeShiftVec] using ht)) := by
  let gpt : positiveTimeCompactSupportSubmodule d := ⟨g, ⟨hg_pos, hg_compact⟩⟩
  let gt : SchwartzSpacetime d := SCV.translateSchwartz (-(timeShiftVec d t)) g
  let hgt : positiveTimeCompactSupportSubmodule d :=
    translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact
      (timeShiftVec d t) (by simpa [timeShiftVec] using ht)
  have hshift :
      timeShiftSchwartzNPoint (d := d) t
          (onePointToFin1CLM d g : SchwartzNPoint d 1) =
        (onePointToFin1CLM d gt : SchwartzNPoint d 1) := by
    ext x
    simp [gt, onePointToFin1CLM_apply, SCV.translateSchwartz_apply, sub_eq_add_neg]
  change osTimeShiftHilbert (d := d) OS lgc t ht
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d g : SchwartzNPoint d 1)
              (onePointToFin1_tsupport_orderedPositiveTime_local (d := d) g hg_pos)⟧)) :
          OSHilbertSpace OS)) =
    positiveTimeOnePointVector_local (d := d) OS hgt
  rw [osTimeShiftHilbert_coe (d := d) (OS := OS) (lgc := lgc) (t := t) (ht := ht)]
  apply congrArg (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS))
  apply OSPreHilbertSpace.mk_eq_of_funcs_eq
  intro n
  by_cases hn : n = 1
  · subst hn
    simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, timeShiftPositiveTimeBorchers,
      hgt, translatedPositiveTimeCompactSupport_local,
      gt, hshift]
  · simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, timeShiftPositiveTimeBorchers,
      hgt, translatedPositiveTimeCompactSupport_local, hn]

/-- Full Euclidean translation by `-ξ` factors as a time shift by `-ξ₀`
followed by a purely spatial shift by `-(0, ξₛ)`. -/
private theorem twoStepTranslateSchwartz_eq_fullTranslate_local
    (g : SchwartzSpacetime d)
    (ξ : SpacetimeDim d) :
    let ξs : Fin d → ℝ := fun i => ξ (Fin.succ i)
    let gt : SchwartzSpacetime d := SCV.translateSchwartz (-(timeShiftVec d (ξ 0))) g
    SCV.translateSchwartz (-Fin.cons 0 ξs) gt =
      SCV.translateSchwartz (-ξ) g := by
  dsimp
  let ξs : Fin d → ℝ := fun i => ξ (Fin.succ i)
  let gt : SchwartzSpacetime d := SCV.translateSchwartz (-(timeShiftVec d (ξ 0))) g
  have hvec :
      (-Fin.cons 0 ξs : SpacetimeDim d) + (-timeShiftVec d (ξ 0) : SpacetimeDim d) = -ξ := by
    ext μ
    cases μ using Fin.cases with
    | zero =>
        simp [ξs, timeShiftVec]
    | succ i =>
        simp [ξs, timeShiftVec]
  ext x
  simp [SCV.translateSchwartz_apply, add_assoc]
  simpa [add_assoc] using congrArg (fun z : SpacetimeDim d => g (x + z)) hvec

/-- The full translated positive-time one-point vector is exactly the two-step
OS orbit: first positive real-time evolution, then spatial translation. -/
private theorem translatedPositiveTimeOnePointVector_eq_twoStepOrbit_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    let ξs : Fin d → ℝ := fun i => ξ (Fin.succ i)
    translatedPositiveTimeOnePointVector_local (d := d) OS g hg_pos hg_compact ξ hξ =
      (osSpatialTranslateHilbert (d := d) OS ξs)
        ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
          (positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩)) := by
  dsimp
  let ξs : Fin d → ℝ := fun i => ξ (Fin.succ i)
  let gpt : positiveTimeCompactSupportSubmodule d := ⟨g, ⟨hg_pos, hg_compact⟩⟩
  let hg_ord :
      tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime_local (d := d) g hg_pos
  let Fg : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_ord
  have hFg_compact :
      ∀ n, HasCompactSupport ((((Fg : BorchersSequence d).funcs n :
        SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
    intro n
    by_cases hn : n = 1
    · subst hn
      have hg_compact_one :
          HasCompactSupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
            NPointDomain d 1 → ℂ)) := by
        simpa [onePointToFin1CLM] using
          (hg_compact.comp_homeomorph
            ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))
      simpa [Fg, PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single] using hg_compact_one
    · simp [Fg, PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single, hn, HasCompactSupport.zero]
  have htime_complex :
      (osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
        (positiveTimeOnePointVector_local (d := d) OS gpt) =
      osTimeShiftHilbert (d := d) OS lgc (ξ 0) hξ
        (positiveTimeOnePointVector_local (d := d) OS gpt) := by
    simpa [gpt, positiveTimeOnePointVector_local, Fg] using
      (osTimeShiftHilbertComplex_ofReal_eq_of_isCompactSupport
        (d := d) OS lgc Fg hFg_compact (ξ 0) hξ)
  let gtpt : positiveTimeCompactSupportSubmodule d :=
    translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact
      (timeShiftVec d (ξ 0)) (by simpa [timeShiftVec] using hξ)
  let gt : SchwartzSpacetime d := (gtpt : SchwartzSpacetime d)
  have hspatial :
      (osSpatialTranslateHilbert (d := d) OS ξs)
        (positiveTimeOnePointVector_local (d := d) OS gtpt) =
      translatedPositiveTimeOnePointVector_local (d := d) OS g hg_pos hg_compact ξ hξ := by
    have hraw := osSpatialTranslateHilbert_single_onePoint_eq
      (d := d) (OS := OS) gt gtpt.property.1 ξs
    have hfull :
        SCV.translateSchwartz (-Fin.cons 0 (fun i => ξ (Fin.succ i)))
            (SCV.translateSchwartz (-timeShiftVec d (ξ 0)) g) =
          SCV.translateSchwartz (-ξ) g := by
      simpa [timeShiftVec] using
        (twoStepTranslateSchwartz_eq_fullTranslate_local (d := d) g ξ)
    simpa [gtpt, gt, ξs, translatedPositiveTimeOnePointVector_local,
      translatedPositiveTimeCompactSupport_local, hfull] using hraw
  calc
    translatedPositiveTimeOnePointVector_local (d := d) OS g hg_pos hg_compact ξ hξ
        = (osSpatialTranslateHilbert (d := d) OS ξs)
            (positiveTimeOnePointVector_local (d := d) OS gtpt) := by
              symm
              exact hspatial
    _ = (osSpatialTranslateHilbert (d := d) OS ξs)
          (osTimeShiftHilbert (d := d) OS lgc (ξ 0) hξ
            (positiveTimeOnePointVector_local (d := d) OS gpt)) := by
              rw [osTimeShiftHilbert_positiveTimeOnePointVector_eq_local
                (d := d) OS lgc g hg_pos hg_compact (ξ 0) hξ]
    _ = (osSpatialTranslateHilbert (d := d) OS ξs)
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            (positiveTimeOnePointVector_local (d := d) OS gpt)) := by
              rw [htime_complex]

/-- Spatial translation preserves the ordered positive-time support of a
one-point Schwartz probe. -/
private theorem onePointToFin1_translate_spatial_tsupport_subset_local
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (y : Fin d → ℝ) :
    tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
        SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
  have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
      SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
    (((translateSchwartzNPoint (d := d) (spatialEmbed y)
      (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
    ext x
    simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
      translateSchwartzNPoint_apply, sub_eq_add_neg]
  rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
      SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
    tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
      (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
    congr_arg tsupport hsup]
  exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
    (d := d) (spatialEmbed y) ha0
    (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos

/-- The OS Hilbert vector obtained from spatially translating a positive-time
one-point Schwartz test. This isolates the spatial parameter in the `k = 2`
semigroup witness. -/
private def twoPointTranslatedOnePointVector_spatial_local
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (y : Fin d → ℝ) : OSHilbertSpace OS :=
  let g_translated := SCV.translateSchwartz (-spatialEmbed y) g
  let hg_translated_pos : tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    exact onePointToFin1_translate_spatial_tsupport_subset_local (d := d) g hg_pos y
  (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single 1
          (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)
          hg_translated_pos⟧)) : OSHilbertSpace OS))

/-- The spatially-parameterized `k = 2` semigroup witness. It separates the
complex time variable from the real spatial-difference parameter. -/
private def twoPointSpatialWitness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (z : ℂ) (y : Fin d → ℝ) : ℂ :=
  @inner ℂ (OSHilbertSpace OS) _
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
            hχ₀_pos⟧)) : OSHilbertSpace OS))
    (osTimeShiftHilbertComplex (d := d) OS lgc z
      (twoPointTranslatedOnePointVector_spatial_local (d := d) OS g hg_pos y))

/-- The corrected flattened `k = 2` witness: complex time enters through the
time-difference slot, while the spatial-difference slots are read off as real
parameters. -/
private def twoPointCorrectedWitness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (u : Fin (2 * (d + 1)) → ℂ) : ℂ :=
  twoPointSpatialWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos
    (-Complex.I * u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))))
    (extractDiffSpatialRe u)

private theorem twoPointCorrectedWitness_eq_twoPointSpatialWitness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (u : Fin (2 * (d + 1)) → ℂ) :
    twoPointCorrectedWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos u =
      twoPointSpatialWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos
        (-Complex.I * u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))))
        (extractDiffSpatialRe u) := by
  rfl

/-- Spatial-parameter continuity of the translated positive-time one-point OS
vector used in the corrected `k = 2` witness. -/
private theorem continuous_twoPointTranslatedOnePointVector_spatial_local
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    Continuous (twoPointTranslatedOnePointVector_spatial_local (d := d) OS g hg_pos) := by
  have hg_pos_time : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} :=
    tsupport_positive_of_onePointToFin1_tsupport_orderedPositiveTime_local (d := d) g hg_pos
  let xg : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d g : SchwartzNPoint d 1)
            hg_pos⟧)) : OSHilbertSpace OS))
  have hEq :
      twoPointTranslatedOnePointVector_spatial_local (d := d) OS g hg_pos =
        fun y => (osSpatialTranslateHilbert (d := d) OS y) xg := by
    funext y
    simpa [twoPointTranslatedOnePointVector_spatial_local, xg] using
      (osSpatialTranslateHilbert_single_onePoint_eq (d := d) OS g hg_pos_time y).symm
  rw [hEq]
  let hpair : Continuous (fun y : Fin d → ℝ => (y, xg)) :=
    continuous_id.prodMk continuous_const
  simpa using
    (continuous_osSpatialTranslateHilbert_jointly (d := d) OS).comp hpair

/-- Joint continuity of the spatially-parameterized corrected `k = 2` witness on
the right half-plane times the real spatial-difference parameter. -/
private theorem continuousOn_twoPointSpatialWitness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
    ContinuousOn (fun p : ℂ × (Fin d → ℝ) =>
      twoPointSpatialWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos p.1 p.2)
      ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
  let xχ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
            hχ₀_pos⟧)) : OSHilbertSpace OS))
  let Φ : ℂ × (Fin d → ℝ) → ℂ × OSHilbertSpace OS :=
    fun p => (p.1, twoPointTranslatedOnePointVector_spatial_local (d := d) OS g hg_pos p.2)
  have hΦcont : Continuous Φ := by
    refine Continuous.prodMk continuous_fst ?_
    exact (continuous_twoPointTranslatedOnePointVector_spatial_local
      (d := d) OS g hg_pos).comp continuous_snd
  have hΦmaps :
      Set.MapsTo Φ ({z : ℂ | 0 < z.re} ×ˢ Set.univ)
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    intro p hp
    exact ⟨hp.1, trivial⟩
  have heval :
      ContinuousOn
        (fun p : ℂ × (Fin d → ℝ) =>
          osTimeShiftHilbertComplex (d := d) OS lgc p.1
            (twoPointTranslatedOnePointVector_spatial_local (d := d) OS g hg_pos p.2))
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    simpa [Φ] using
      (continuousOn_osTimeShiftHilbertComplex_jointly (d := d) OS lgc).comp
        hΦcont.continuousOn hΦmaps
  have hinner :
      ContinuousOn
        (fun p : ℂ × (Fin d → ℝ) =>
          @inner ℂ (OSHilbertSpace OS) _ xχ
            (osTimeShiftHilbertComplex (d := d) OS lgc p.1
              (twoPointTranslatedOnePointVector_spatial_local (d := d) OS g hg_pos p.2)))
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) :=
    (innerSL ℂ xχ).continuous.comp_continuousOn heval
  simpa [twoPointSpatialWitness_local, xχ] using hinner

/-- OS step-B continuity on the flattened positive-time-difference tube for the
corrected `k = 2` witness built from a compact positive-time probe. -/
private theorem continuousOn_twoPointCorrectedWitness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    ContinuousOn (twoPointCorrectedWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos)
      (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d)) := by
  let Φ : (Fin (2 * (d + 1)) → ℂ) → ℂ × (Fin d → ℝ) :=
    fun u =>
      (-Complex.I * u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))),
        extractDiffSpatialRe u)
  have hΦcont : Continuous Φ := by
    refine Continuous.prodMk (continuous_const.mul (continuous_apply _)) ?_
    refine continuous_pi ?_
    intro i
    exact Complex.continuous_re.comp (continuous_apply _)
  have hΦmaps :
      Set.MapsTo Φ (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d))
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    intro u hu
    refine ⟨?_, trivial⟩
    rw [Set.mem_setOf_eq, OSReconstruction.neg_I_mul_re_eq_im]
    exact (mem_tubeDomain_flatPositiveTimeDiffReal_iff (k := 2) (d := d) u).mp hu ⟨1, by omega⟩
  have hcont_spatial :=
    continuousOn_twoPointSpatialWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos
  have hcomp :
      ContinuousOn
        (fun u =>
          twoPointSpatialWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos (Φ u).1 (Φ u).2)
        (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d)) :=
    hcont_spatial.comp hΦcont.continuousOn hΦmaps
  have hEq :
      (fun u =>
        twoPointSpatialWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos (Φ u).1 (Φ u).2) =
      twoPointCorrectedWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos := by
    funext u
    simp [Φ, twoPointCorrectedWitness_eq_twoPointSpatialWitness_local]
  simpa [hEq] using hcomp

/-- The corrected `k = 2` witness is holomorphic in the difference-time slot. -/
private theorem differentiableOn_twoPointCorrectedWitness_time_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (u : Fin (2 * (d + 1)) → ℂ) :
    DifferentiableOn ℂ
      (fun w => twoPointCorrectedWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos
        (Function.update u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) w))
      {w : ℂ | 0 < w.im} := by
  have hextract : ∀ w : ℂ,
      extractDiffSpatialRe
        (Function.update u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) w) =
      extractDiffSpatialRe u := by
    intro w
    ext i
    simp only [extractDiffSpatialRe]
    have hne : finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (0 : Fin (d + 1))) ≠
        finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (i : Fin d).succ) := by
      intro heq
      have := (Prod.mk.inj (finProdFinEquiv.injective heq)).2
      exact absurd this (Fin.succ_ne_zero i).symm
    simp [Function.update, hne, Ne.symm hne]
  let y₀ := extractDiffSpatialRe u
  let g₀ := SCV.translateSchwartz (-spatialEmbed y₀) g
  have hg₀_pos :
      tsupport (((onePointToFin1CLM d g₀ : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    simpa [g₀, y₀] using
      onePointToFin1_translate_spatial_tsupport_subset_local (d := d) g hg_pos (extractDiffSpatialRe u)
  let xχ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
            hχ₀_pos⟧)) : OSHilbertSpace OS))
  let v₀ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d g₀ : SchwartzNPoint d 1)
            hg₀_pos⟧)) : OSHilbertSpace OS))
  have hv :
      twoPointTranslatedOnePointVector_spatial_local (d := d) OS g hg_pos (extractDiffSpatialRe u) = v₀ := by
    simp [twoPointTranslatedOnePointVector_spatial_local, g₀, y₀, v₀]
  have hfun_eq :
      (fun w =>
        twoPointCorrectedWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos
          (Function.update u (finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (0 : Fin (d + 1)))) w)) =
      (fun w =>
        @inner ℂ (OSHilbertSpace OS) _ xχ
          ((osTimeShiftHilbertComplex (d := d) OS lgc (-Complex.I * w)) v₀)) := by
    ext w
    have hvw :
        twoPointTranslatedOnePointVector_spatial_local (d := d) OS g hg_pos
          (extractDiffSpatialRe
            (Function.update u (finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (0 : Fin (d + 1)))) w)) =
          v₀ := by
      rw [hextract w]
      exact hv
    rw [twoPointCorrectedWitness_local, twoPointSpatialWitness_local]
    rw [hvw]
    simpa [xχ]
  rw [hfun_eq]
  exact OSReconstruction.differentiableOn_comp_neg_I_mul
    (differentiableOn_inner_osTimeShiftHilbertComplex (d := d) OS lgc xχ v₀)

/-- The corrected `k = 2` witness is constant in the center-time slot. -/
private theorem differentiableOn_twoPointCorrectedWitness_centerTime_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (u : Fin (2 * (d + 1)) → ℂ) :
    DifferentiableOn ℂ
      (fun w => twoPointCorrectedWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos
        (Function.update u (finProdFinEquiv ((⟨0, by omega⟩ : Fin 2), (0 : Fin (d + 1)))) w))
      {w : ℂ | 0 < w.im} := by
  have hconst : ∀ w : ℂ,
      twoPointCorrectedWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos
        (Function.update u (finProdFinEquiv ((⟨0, by omega⟩ : Fin 2), (0 : Fin (d + 1)))) w) =
      twoPointCorrectedWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos u := by
    intro w
    simp only [twoPointCorrectedWitness_local]
    congr 1
  simp_rw [hconst]
  exact differentiableOn_const _

/-- The corrected `k = 2` witness already satisfies the required time-slice
holomorphicity for the flattened positive-time-difference witness surface. -/
private theorem twoPointCorrectedWitness_timeSliceDifferentiableOn_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (u : Fin (2 * (d + 1)) → ℂ)
    (_hu : ∀ j : Fin 2, 0 < (u (finProdFinEquiv (j, (0 : Fin (d + 1))))).im)
    (i : Fin 2) :
    DifferentiableOn ℂ
      (fun w => twoPointCorrectedWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos
        (Function.update u (finProdFinEquiv (i, (0 : Fin (d + 1)))) w))
      {w : ℂ | 0 < w.im} := by
  fin_cases i
  · simpa using
      differentiableOn_twoPointCorrectedWitness_centerTime_local
        (d := d) OS lgc χ₀ g hχ₀_pos hg_pos u
  · simpa using
      differentiableOn_twoPointCorrectedWitness_time_local
        (d := d) OS lgc χ₀ g hχ₀_pos hg_pos u

/-- OS step-B holomorphicity on the time-difference slices for the corrected
`k = 2` witness. -/
private theorem isTimeHolomorphicFlatPositiveTimeDiffWitness_twoPointCorrectedWitness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    IsTimeHolomorphicFlatPositiveTimeDiffWitness
      (twoPointCorrectedWitness_local (d := d) OS lgc χ₀ g hχ₀_pos hg_pos) := by
  refine ⟨continuousOn_twoPointCorrectedWitness_local
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact, ?_⟩
  intro u hu i
  have hu' : ∀ j : Fin 2, 0 < (u (finProdFinEquiv (j, (0 : Fin (d + 1))))).im := by
    exact (mem_tubeDomain_flatPositiveTimeDiffReal_iff (k := 2) (d := d) u).mp hu
  exact twoPointCorrectedWitness_timeSliceDifferentiableOn_local
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos u hu' i

/-- The OS two-step orbit attached to a compactly supported positive-time
one-point test is continuous on the positive-time Euclidean domain. -/
private theorem continuous_twoStepOrbit_positiveTime_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    let xg := positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
    Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
      (osSpatialTranslateHilbert (d := d) OS (fun i => ξp.1 (Fin.succ i)))
        ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξp.1 0 : ℝ) : ℂ)) xg)) := by
  dsimp
  let xg := positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
  let gtime : {r : ℝ // 0 < r} → OSHilbertSpace OS := fun s =>
    (osTimeShiftHilbertComplex (d := d) OS lgc ((s : ℝ) : ℂ)) xg
  have hcomplex :
      ContinuousOn
        (fun z : ℂ => (osTimeShiftHilbertComplex (d := d) OS lgc z) xg)
        {z : ℂ | 0 < z.re} :=
    continuousOn_osTimeShiftHilbertComplex_apply (d := d) OS lgc xg
  have htime0 :
      ContinuousOn
        (fun t : ℝ => (osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)) xg)
        (Set.Ioi 0) := by
    apply ContinuousOn.comp hcomplex
    · exact Complex.ofRealCLM.continuous.continuousOn
    · intro t ht
      simpa using ht
  have htimeReal : Continuous gtime := by
    rw [continuousOn_iff_continuous_restrict] at htime0
    change Continuous (fun s : {r : ℝ // 0 < r} =>
      (osTimeShiftHilbertComplex (d := d) OS lgc ((s : ℝ) : ℂ)) xg) at htime0
    simpa [gtime] using htime0
  have htime_map :
      Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
        (⟨ξp.1 0, ξp.2⟩ : {r : ℝ // 0 < r})) := by
    exact ((continuous_apply (0 : Fin (d + 1))).comp continuous_subtype_val).subtype_mk
      (fun ξp => ξp.2)
  have htime :
      Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
        (osTimeShiftHilbertComplex (d := d) OS lgc ((ξp.1 0 : ℝ) : ℂ)) xg) := by
    simpa [gtime] using htimeReal.comp htime_map
  have hspatial_map :
      Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
        ((fun i => ξp.1 (Fin.succ i)),
          (osTimeShiftHilbertComplex (d := d) OS lgc ((ξp.1 0 : ℝ) : ℂ)) xg)) := by
    let hspatialCoord : Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
        ((fun i => ξp.1 (Fin.succ i)) : Fin d → ℝ)) :=
      continuous_pi (fun i => (continuous_apply (Fin.succ i)).comp continuous_subtype_val)
    exact hspatialCoord.prodMk htime
  simpa using
    (continuous_osSpatialTranslateHilbert_jointly (d := d) OS).comp hspatial_map

/-- Consequently, the fixed-left-vector matrix element of the two-step OS orbit
is continuous on the positive-time Euclidean domain. -/
private theorem continuous_twoStepMatrixElement_positiveTime_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    let xχ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1))
              hχ_pos⟧)) : OSHilbertSpace OS))
    let xg := positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
    Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
      @inner ℂ (OSHilbertSpace OS) _ xχ
        ((osSpatialTranslateHilbert (d := d) OS (fun i => ξp.1 (Fin.succ i)))
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξp.1 0 : ℝ) : ℂ)) xg))) := by
  dsimp
  let xχ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1))
            hχ_pos⟧)) : OSHilbertSpace OS))
  exact continuous_inner.comp
    (continuous_const.prodMk
      (continuous_twoStepOrbit_positiveTime_local (d := d) OS lgc g hg_pos hg_compact))

/-- Ambient `ContinuousOn` form of the two-step matrix-element continuity on
the positive-time Euclidean region. -/
private theorem continuousOn_twoStepMatrixElement_positiveTime_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    let xχ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1))
              hχ_pos⟧)) : OSHilbertSpace OS))
    let xg := positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
    ContinuousOn (fun ξ : SpacetimeDim d =>
      @inner ℂ (OSHilbertSpace OS) _ xχ
        ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i)))
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ)) xg)))
      {ξ : SpacetimeDim d | 0 < ξ 0} := by
  dsimp
  rw [continuousOn_iff_continuous_restrict]
  simpa using
    (continuous_twoStepMatrixElement_positiveTime_local
      (d := d) OS lgc χ g hχ_pos hg_pos hg_compact)

/-- The translated positive-time compact-support test depends continuously on
the translation parameter inside the reduced positive-time compact-support
submodule. -/
private theorem continuous_translatedPositiveTimeCompactSupport_positiveTime_local
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
      translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξp.1 ξp.2) := by
  have htrans : Continuous (fun a : SpacetimeDim d => SCV.translateSchwartz a g) := by
    rw [continuous_iff_continuousAt]
    intro a
    simpa using SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport g hg_compact a
  have hbase : Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
      SCV.translateSchwartz (-ξp.1) g) := by
    exact htrans.comp (continuous_neg.comp continuous_subtype_val)
  exact hbase.subtype_mk (fun ξp =>
    (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξp.1 ξp.2).property)


/-- Consequently, the corresponding zero-diagonal product-shell orbit is
continuous on the positive-time Euclidean domain. -/
private theorem continuous_twoPointProductLiftPositiveZeroDiagOrbit_positiveTime_local
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
      twoPointProductLiftPositiveZeroDiagCLM_local χ hχ_pos
        (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξp.1 ξp.2)) := by
  exact (twoPointProductLiftPositiveZeroDiagCLM_local χ hχ_pos).continuous.comp
    (continuous_translatedPositiveTimeCompactSupport_positiveTime_local
      (d := d) g hg_pos hg_compact)

/-- The translated product-shell Schwinger scalar orbit is continuous on the
positive-time Euclidean domain. -/
private theorem continuous_translatedProductShellSchwinger_positiveTime_local
    (OS : OsterwalderSchraderAxioms d)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    Continuous (fun ξp : {x : SpacetimeDim d // 0 < x 0} =>
      schwingerProductPositiveCLM_local OS χ hχ_pos
        (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξp.1 ξp.2)) := by
  exact (schwingerProductPositiveCLM_local OS χ hχ_pos).continuous.comp
    (continuous_translatedPositiveTimeCompactSupport_positiveTime_local
      (d := d) g hg_pos hg_compact)

/-- Ambient `ContinuousOn` form of the translated product-shell Schwinger scalar
orbit on the positive-time Euclidean region. -/
private theorem continuousOn_translatedProductShellSchwinger_positiveTime_local
    (OS : OsterwalderSchraderAxioms d)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    ContinuousOn
      (fun ξ : SpacetimeDim d =>
        if hξ : 0 < ξ 0 then
          schwingerProductPositiveCLM_local OS χ hχ_pos
            (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξ hξ)
        else 0)
      {ξ : SpacetimeDim d | 0 < ξ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun ξp : {ξ : SpacetimeDim d // 0 < ξ 0} =>
    if hξ : 0 < ξp.1 0 then
      schwingerProductPositiveCLM_local OS χ hχ_pos
        (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξp.1 hξ)
    else 0)
  have hfun :
      (fun ξp : {ξ : SpacetimeDim d // 0 < ξ 0} =>
        if hξ : 0 < ξp.1 0 then
          schwingerProductPositiveCLM_local OS χ hχ_pos
            (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξp.1 hξ)
        else 0) =
      (fun ξp : {ξ : SpacetimeDim d // 0 < ξ 0} =>
        schwingerProductPositiveCLM_local OS χ hχ_pos
          (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξp.1 ξp.2)) := by
    funext ξp
    simpa using
      (dif_pos ξp.2 :
        (if hξ : 0 < ξp.1 0 then
          schwingerProductPositiveCLM_local OS χ hχ_pos
            (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξp.1 hξ)
        else 0) =
        schwingerProductPositiveCLM_local OS χ hχ_pos
          (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξp.1 ξp.2))
  rw [hfun]
  simpa using
    (continuous_translatedProductShellSchwinger_positiveTime_local
      (d := d) OS χ g hχ_pos hg_pos hg_compact)

private theorem measurableSet_positiveTimeRegion_spacetime_local :
    MeasurableSet {ξ : SpacetimeDim d | 0 < ξ 0} :=
  measurableSet_lt measurable_const (continuous_apply 0).measurable

/-- The weighted translated product-shell Schwinger orbit is integrable against
any compactly supported positive-time test. -/
private theorem integrable_translatedProductShellSchwinger_weight_local
    (OS : OsterwalderSchraderAxioms d)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (h : positiveTimeCompactSupportSubmodule d) :
    Integrable
      (fun ξ : SpacetimeDim d =>
        (if hξ : 0 < ξ 0 then
          schwingerProductPositiveCLM_local OS χ hχ_pos
            (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξ hξ)
        else 0) * ((h : SchwartzSpacetime d) ξ)) volume := by
  let F : SpacetimeDim d → ℂ := fun ξ =>
    (if hξ : 0 < ξ 0 then
      schwingerProductPositiveCLM_local OS χ hχ_pos
        (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξ hξ)
    else 0) * ((h : SchwartzSpacetime d) ξ)
  let H : Set (SpacetimeDim d) := tsupport (((h : positiveTimeCompactSupportSubmodule d) :
    SchwartzSpacetime d) : SpacetimeDim d → ℂ)
  have hH_compact : IsCompact H := h.property.2.isCompact
  have hF_support : Function.support F ⊆ H := by
    intro ξ hξ
    by_contra hξH
    have hzero : ((h : SchwartzSpacetime d) ξ) = 0 := image_eq_zero_of_notMem_tsupport hξH
    apply hξ
    simp [F, hzero]
  have hF_cont : ContinuousOn F H := by
    have horbit :
        ContinuousOn
          (fun ξ : SpacetimeDim d =>
            if hξ : 0 < ξ 0 then
              schwingerProductPositiveCLM_local OS χ hχ_pos
                (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξ hξ)
            else 0)
          H := by
      refine (continuousOn_translatedProductShellSchwinger_positiveTime_local
        (d := d) OS χ g hχ_pos hg_pos hg_compact).mono ?_
      intro ξ hξH
      exact h.property.1 hξH
    have hh_cont : ContinuousOn (fun ξ : SpacetimeDim d => ((h : SchwartzSpacetime d) ξ)) H :=
      (SchwartzMap.continuous ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)).continuousOn
    exact horbit.mul hh_cont
  apply (integrableOn_iff_integrable_of_support_subset hF_support).mp
  exact hF_cont.integrableOn_compact hH_compact

/-- The inner product of a fixed vector with the Bochner integral of
`h`-weighted orbit vectors equals the integral of scalar matrix elements. -/
private theorem inner_bochnerIntegral_orbit_eq_integral_matrixElement_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    let xχ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1))
              hχ_pos⟧)) : OSHilbertSpace OS))
    let xg := positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
    let orbit := fun ξ : SpacetimeDim d =>
      (osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i)))
        ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ)) xg)
    let matElt := fun ξ : SpacetimeDim d =>
      @inner ℂ (OSHilbertSpace OS) _ xχ (orbit ξ)
    @inner ℂ (OSHilbertSpace OS) _ xχ
        (∫ ξ : SpacetimeDim d, (h : SpacetimeDim d → ℂ) ξ • orbit ξ) =
      ∫ ξ : SpacetimeDim d, (h : SpacetimeDim d → ℂ) ξ * matElt ξ := by
  dsimp
  rw [← integral_inner (𝕜 := ℂ)]
  · congr 1
    ext ξ
    rw [inner_smul_right]
  · let xg : OSHilbertSpace OS :=
        positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
    let orbit : SpacetimeDim d → OSHilbertSpace OS := fun ξ =>
      (osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i)))
        ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ)) xg)
    let F : SpacetimeDim d → OSHilbertSpace OS := fun ξ =>
        (h : SpacetimeDim d → ℂ) ξ • orbit ξ
    let H : Set (SpacetimeDim d) := tsupport (h : SpacetimeDim d → ℂ)
    have hH_compact : IsCompact H := hh_compact.isCompact
    have hF_support : Function.support F ⊆ H := by
      intro ξ hξ
      by_contra hξH
      have hzero : h ξ = 0 := image_eq_zero_of_notMem_tsupport hξH
      apply hξ
      simp [F, hzero]
    have horbit_pos : ContinuousOn orbit {ξ : SpacetimeDim d | 0 < ξ 0} := by
      rw [continuousOn_iff_continuous_restrict]
      simpa using
        (continuous_twoStepOrbit_positiveTime_local (d := d) OS lgc g hg_pos hg_compact)
    have hF_cont : ContinuousOn F H := by
      have hh_cont : ContinuousOn (fun ξ : SpacetimeDim d => h ξ) H :=
        (SchwartzMap.continuous h).continuousOn
      have horbit_cont : ContinuousOn orbit H := by
        refine horbit_pos.mono ?_
        intro ξ hξH
        exact hh_pos hξH
      exact hh_cont.smul horbit_cont
    apply (integrableOn_iff_integrable_of_support_subset hF_support).mp
    exact hF_cont.integrableOn_compact hH_compact

/-- The weighted translated product-shell Schwinger integral is exactly the
matrix element of the Bochner-integrated OS orbit. -/
private theorem integral_translatedProductShellSchwinger_weight_eq_inner_bochnerIntegral_orbit_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (h : positiveTimeCompactSupportSubmodule d) :
    let xχ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1))
              hχ_pos⟧)) : OSHilbertSpace OS))
    let xg := positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩
    let orbit := fun ξ : SpacetimeDim d =>
      (osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i)))
        ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ)) xg)
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        schwingerProductPositiveCLM_local OS χ hχ_pos
          (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξ hξ)
      else 0) * ((h : SchwartzSpacetime d) ξ) =
      @inner ℂ (OSHilbertSpace OS) _ xχ
        (∫ ξ : SpacetimeDim d, ((h : SchwartzSpacetime d) ξ) • orbit ξ) := by
  dsimp
  have hboch :=
    inner_bochnerIntegral_orbit_eq_integral_matrixElement_local
      (d := d) OS lgc χ g hχ_pos hg_pos hg_compact
      (h : SchwartzSpacetime d) h.property.1 h.property.2
  calc
    ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          schwingerProductPositiveCLM_local OS χ hχ_pos
            (translatedPositiveTimeCompactSupport_local (d := d) g hg_pos hg_compact ξ hξ)
        else 0) * ((h : SchwartzSpacetime d) ξ)
      =
        ∫ ξ : SpacetimeDim d,
          ((h : SchwartzSpacetime d) ξ) *
            @inner ℂ (OSHilbertSpace OS) _
              (((show OSPreHilbertSpace OS from
                  (⟦PositiveTimeBorchersSequence.single 1
                      (SchwartzNPoint.osConj (d := d) (n := 1)
                        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                      hχ_pos⟧)) : OSHilbertSpace OS))
              ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i)))
                ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
                  (positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩))) := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            by_cases hξ : 0 < ξ 0
            · simp only [dif_pos hξ]
              have hprod :
                  schwingerProductPositiveCLM_local OS χ hχ_pos
                    (translatedPositiveTimeCompactSupport_local
                      (d := d) g hg_pos hg_compact ξ hξ) =
                    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                      (twoPointProductLift χ (SCV.translateSchwartz (-ξ) g))) := by
                  simp [translatedPositiveTimeCompactSupport_local]
              rw [hprod]
              rw [← translatedPositiveTimeOnePointVector_eq_twoStepOrbit_local
                (d := d) OS lgc g hg_pos hg_compact ξ hξ]
              rw [inner_translatedPositiveTimeOnePointVector_eq_translated_productShell_local
                (d := d) OS χ g hχ_pos hg_pos hg_compact ξ hξ]
              simp [hξ, mul_comm, mul_left_comm, mul_assoc]
            · have hξ_not_mem :
                  ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) :
                    SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
                intro hmem
                exact hξ (h.property.1 hmem)
              have hξ_zero :
                  ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ = 0 :=
                image_eq_zero_of_notMem_tsupport hξ_not_mem
              simp [hξ, hξ_zero]
    _ = @inner ℂ (OSHilbertSpace OS) _
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                  hχ_pos⟧)) : OSHilbertSpace OS))
          (∫ ξ : SpacetimeDim d,
            ((h : SchwartzSpacetime d) ξ) •
              ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i)))
                ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
                  (positiveTimeOnePointVector_local (d := d) OS ⟨g, ⟨hg_pos, hg_compact⟩⟩)))) := by
            exact hboch.symm

/-- Public OS-Hilbert orbit formula for the reflected-probe translated
product-shell boundary pairing.

This exposes the direct VI.1 route before any spectral factorization: the same
boundary functional can be read as an inner product against a Bochner-integrated
two-step OS orbit built from the reflected probe. -/
theorem integral_translatedProductShell_boundary_eq_inner_bochnerIntegral_reflected_orbit_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (h : positiveTimeCompactSupportSubmodule d) :
    let ψ := reflectedSchwartzSpacetime φ
    let xφ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) φ hφ_compact hφ_neg)⟧)) : OSHilbertSpace OS))
    let xψ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
              (onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) ψ
                (reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg))⟧)) :
          OSHilbertSpace OS))
    let orbit := fun ξ : SpacetimeDim d =>
      (osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i)))
        ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
          xψ)
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ)))
      else 0) * ((h : SchwartzSpacetime d) ξ) =
      @inner ℂ (OSHilbertSpace OS) _ xφ
        (∫ ξ : SpacetimeDim d, ((h : SchwartzSpacetime d) ξ) • orbit ξ) := by
  dsimp
  simpa using
    (integral_translatedProductShellSchwinger_weight_eq_inner_bochnerIntegral_orbit_local
      (d := d) OS lgc φ (reflectedSchwartzSpacetime φ)
      (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
        (d := d) φ hφ_compact hφ_neg)
      (reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg)
      (reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact)
      h)

/-- The shifted simple tensor attached to a reflected positive-time probe is
exactly the translated two-point product shell. -/
private theorem shifted_single_test_eq_twoPointProductLift_translate_local
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    ZeroDiagonalSchwartz.ofClassical
      ((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ 0)
          (onePointToFin1CLM d
            (SCV.translateSchwartz (-spatialEmbed (fun i => ξ i.succ)) g) :
              SchwartzNPoint d 1))) =
      ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift χ (SCV.translateSchwartz (-ξ) g)) := by
  let g_translated : SchwartzSpacetime d :=
    SCV.translateSchwartz (-spatialEmbed (fun i => ξ i.succ)) g
  have hg_translated_pos : tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed (fun i => ξ i.succ)) 0 = 0 := spatialEmbed_zero _
    have hsup : (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed (fun i => ξ i.succ))
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, g_translated, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed (fun i => ξ i.succ))
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed (fun i => ξ i.succ)) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  have hvanish_left :
      VanishesToInfiniteOrderOnCoincidence
        ((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0)
            (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))) := by
    exact
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (f := SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        (g := timeShiftSchwartzNPoint (d := d) (ξ 0)
          (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))
        hχ_pos
        (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
          (d := d) (ξ 0) hξ (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)
          hg_translated_pos)
  have hfun :
      (((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (ξ 0)
          (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))) :
        NPointDomain d 2 → ℂ) =
      ((twoPointProductLift χ (SCV.translateSchwartz (-ξ) g)) :
        NPointDomain d 2 → ℂ) := by
    funext y
    have hosconj :
        SchwartzNPoint.osConj (d := d) (n := 1)
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1)) =
          (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
      ext x
      simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
        timeReflectionN, timeReflection, timeReflection_timeReflection]
    calc
      (((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0)
            (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))) y)
        = (((onePointToFin1CLM d χ : SchwartzNPoint d 1).tensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0)
              (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))) y) := by
              simp [SchwartzNPoint.osConjTensorProduct, hosconj]
      _ = χ (y 0) * g_translated (y 1 - timeShiftVec d (ξ 0)) := by
            rw [SchwartzMap.tensorProduct_apply]
            simp [onePointToFin1CLM_apply, splitFirst, splitLast,
              timeShiftSchwartzNPoint_apply]
      _ = χ (y 0) * g (y 1 + -ξ) := by
            have hvec :
                (-spatialEmbed (fun i => ξ i.succ) : SpacetimeDim d) +
                    (-timeShiftVec d (ξ 0) : SpacetimeDim d) = -ξ := by
              ext μ
              cases μ using Fin.cases with
              | zero =>
                  simp [spatialEmbed, timeShiftVec]
              | succ i =>
                  simp [spatialEmbed, timeShiftVec]
            simp [g_translated, SCV.translateSchwartz_apply, sub_eq_add_neg, hvec,
              add_assoc, add_left_comm, add_comm]
  have hEq :
      twoPointProductLift χ (SCV.translateSchwartz (-ξ) g) =
        ((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0)
            (onePointToFin1CLM d g_translated : SchwartzNPoint d 1))) := by
    ext y
    exact congrFun hfun.symm y
  have hvanish_right :
      VanishesToInfiniteOrderOnCoincidence
        (twoPointProductLift χ (SCV.translateSchwartz (-ξ) g)) := by
    rw [hEq]
    exact hvanish_left
  apply Subtype.ext
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := ((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0)
            (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)))) hvanish_left,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := twoPointProductLift χ (SCV.translateSchwartz (-ξ) g)) hvanish_right]
  ext y
  exact congrFun hfun y

/-- Apply semigroup-group Bochner to the OS matrix element attached to a
single normalized positive-time one-point vector. -/
theorem exists_bochner_measure_for_approx_identity
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local
        (d := d) φ hφ_compact hφ_neg
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              hφ_pos⟧) : OSHilbertSpace OS)) t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ := by
  have hφ_pos :
      tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    exact osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  let f1 : SchwartzNPoint d 1 :=
    SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d φ : SchwartzNPoint d 1)
  let Fseq : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1 f1 hφ_pos
  let x : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from (⟦Fseq⟧)) : OSHilbertSpace OS))
  let Kext : ℝ → (Fin d → ℝ) → ℂ := fun t a =>
    if ht : 0 < t then
      osSemigroupGroupMatrixElement (d := d) OS lgc x t a
    else
      @inner ℂ (OSHilbertSpace OS) _ x
        ((osSpatialTranslateHilbert (d := d) OS a) x)
  have hf1_compact : HasCompactSupport ((f1 : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) := by
    let θSpace : SpacetimeDim d ≃ₜ SpacetimeDim d :=
      { toEquiv :=
          { toFun := timeReflection d
            invFun := timeReflection d
            left_inv := timeReflection_timeReflection (d := d)
            right_inv := timeReflection_timeReflection (d := d) }
        continuous_toFun := by
          refine continuous_pi ?_
          intro j
          by_cases hj : j = 0
          · subst hj
            simpa [timeReflection] using
              (continuous_apply (0 : Fin (d + 1))).neg
          · simpa [timeReflection, hj] using
              (continuous_apply j : Continuous fun y : SpacetimeDim d => y j)
        continuous_invFun := by
          refine continuous_pi ?_
          intro j
          by_cases hj : j = 0
          · subst hj
            simpa [timeReflection] using
              (continuous_apply (0 : Fin (d + 1))).neg
          · simpa [timeReflection, hj] using
              (continuous_apply j : Continuous fun y : SpacetimeDim d => y j) }
    have hreflect_space : HasCompactSupport (fun y : SpacetimeDim d => φ (timeReflection d y)) := by
      simpa using hφ_compact.comp_homeomorph θSpace
    have hreflect_fin1 :
        HasCompactSupport (fun y : NPointDomain d 1 => φ (timeReflection d (y 0))) := by
      simpa [onePointToFin1CLM] using
        (hreflect_space.comp_homeomorph
          ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))
    simpa [f1, SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply] using
      (hreflect_fin1.comp_left (show starRingEnd ℂ (0 : ℂ) = 0 by simp))
  have hF_compact :
      ∀ n,
        HasCompactSupport ((((Fseq : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    by_cases hn : n = 1
    · subst hn
      simpa [Fseq, f1, PositiveTimeBorchersSequence.single_toBorchersSequence] using
        hf1_compact
    · have hzero :
          ((((Fseq : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n :
              SchwartzNPoint d n) :
            NPointDomain d n → ℂ) = 0 := by
        simp [Fseq, PositiveTimeBorchersSequence.single_toBorchersSequence,
          BorchersSequence.single, hn]
      rw [hzero]
      simpa using (HasCompactSupport.zero : HasCompactSupport (0 : NPointDomain d n → ℂ))
  have hcont : Continuous (fun p : ℝ × (Fin d → ℝ) => Kext p.1 p.2) := by
    simpa [Kext, x, Fseq] using
      (continuous_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
        (d := d) OS lgc Fseq hF_compact)
  have hbdd : ∃ C : ℝ, ∀ t a, ‖Kext t a‖ ≤ C := by
    refine ⟨2 * ‖x‖ ^ 2, ?_⟩
    intro t a
    by_cases ht : 0 < t
    · have hU : osSpatialTranslateHilbert (d := d) OS a ∈
          unitary (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) := by
        constructor
        · exact osSpatialTranslateHilbert_unitary_left (d := d) OS a
        · exact osSpatialTranslateHilbert_unitary_right (d := d) OS a
      have hnormU :
          ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ = ‖x‖ :=
        ContinuousLinearMap.norm_map_of_mem_unitary
          (u := osSpatialTranslateHilbert (d := d) OS a) hU x
      have hEq :
          osSemigroupGroupMatrixElement (d := d) OS lgc x t a =
            @inner ℂ (OSHilbertSpace OS) _
              ((osSpatialTranslateHilbert (d := d) OS (0 : Fin d → ℝ)) x)
              ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS a) x)) := by
        simpa using
          (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
            (d := d) OS lgc x (0 : Fin d → ℝ) a t ht)
      calc
        ‖Kext t a‖ =
            ‖@inner ℂ (OSHilbertSpace OS) _
                ((osSpatialTranslateHilbert (d := d) OS (0 : Fin d → ℝ)) x)
                ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                  ((osSpatialTranslateHilbert (d := d) OS a) x))‖ := by
              simp [Kext, ht, hEq]
        _ =
            ‖@inner ℂ (OSHilbertSpace OS) _
                x
                ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                  ((osSpatialTranslateHilbert (d := d) OS a) x))‖ := by
              simp [osSpatialTranslateHilbert_zero]
        _ ≤ ‖x‖ *
            ‖(osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS a) x)‖ := by
              exact norm_inner_le_norm _ _
        _ ≤ ‖x‖ *
            (‖osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ)‖ *
              ‖(osSpatialTranslateHilbert (d := d) OS a) x‖) := by
              gcongr
              exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖x‖ * (2 * ‖(osSpatialTranslateHilbert (d := d) OS a) x‖) := by
              gcongr
              exact osTimeShiftHilbertComplex_norm_le (d := d) OS lgc (t : ℂ) ht
        _ = ‖x‖ * (2 * ‖x‖) := by rw [hnormU]
        _ = 2 * ‖x‖ ^ 2 := by ring
    · have hU : osSpatialTranslateHilbert (d := d) OS a ∈
          unitary (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) := by
        constructor
        · exact osSpatialTranslateHilbert_unitary_left (d := d) OS a
        · exact osSpatialTranslateHilbert_unitary_right (d := d) OS a
      have hnormU :
          ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ = ‖x‖ :=
        ContinuousLinearMap.norm_map_of_mem_unitary
          (u := osSpatialTranslateHilbert (d := d) OS a) hU x
      calc
        ‖Kext t a‖ =
            ‖@inner ℂ (OSHilbertSpace OS) _
                x ((osSpatialTranslateHilbert (d := d) OS a) x)‖ := by
              simp [Kext, ht]
        _ ≤ ‖x‖ * ‖(osSpatialTranslateHilbert (d := d) OS a) x‖ := by
              exact norm_inner_le_norm _ _
        _ = ‖x‖ * ‖x‖ := by rw [hnormU]
        _ ≤ 2 * ‖x‖ ^ 2 := by
              nlinarith [sq_nonneg ‖x‖]
  have hpd : SCV.IsSemigroupGroupPD d Kext := by
    simpa [Kext, x, Fseq] using
      (isSemigroupGroupPD_osSemigroupGroupMatrixElement_extension
        (d := d) OS lgc Fseq)
  rcases SCV.semigroupGroup_bochner d Kext hcont hbdd hpd with
    ⟨μ, hμfin, hμneg, hμrepr⟩
  refine ⟨μ, hμfin, hμneg, ?_⟩
  intro t a ht
  simpa [Kext, ht] using hμrepr t a (le_of_lt ht)

/-- The Laplace-Fourier kernel associated to a finite measure on
`[0,∞) × ℝ^d`. -/
def laplaceFourierKernel
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (ξ : SpacetimeDim d) : ℂ :=
  ∫ p : ℝ × (Fin d → ℝ),
    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) ∂μ

/-
Fubini bridge for the finite-measure Laplace-Fourier kernel: pairing the
kernel against a positive-time compact Schwartz test is the same as integrating
the pointwise Fourier-Laplace transform of that test against the measure. This
is the exact first rewrite needed in theorem 3.
-/
set_option maxHeartbeats 3000000 in
private theorem integral_laplaceFourierKernel_mul_eq
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * h ξ ∂volume =
      ∫ p : ℝ × (Fin d → ℝ),
        ∫ ξ : SpacetimeDim d,
          Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
            h ξ ∂volume ∂μ := by
  let f : SpacetimeDim d → (ℝ × (Fin d → ℝ)) → ℂ := fun ξ p =>
    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
      h ξ
  let G : SpacetimeDim d × (ℝ × (Fin d → ℝ)) → ℂ := fun z => f z.1 z.2
  have hf_meas :
      AEStronglyMeasurable (Function.uncurry f) (volume.prod μ) := by
    have hcont_sum :
        Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
          ∑ i : Fin d, z.2.2 i * z.1 (Fin.succ i)) := by
      refine continuous_finset_sum _ fun i _hi => ?_
      exact
        (((continuous_apply i).comp (continuous_snd.comp continuous_snd)) : Continuous
          fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => z.2.2 i).mul
          (((continuous_apply (Fin.succ i)).comp continuous_fst) : Continuous
            fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => z.1 (Fin.succ i))
    have hcont :
        Continuous G := by
      change Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
        Complex.exp (-(↑(z.1 0 * z.2.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, z.2.2 i * z.1 (Fin.succ i))) *
          h z.1)
      have h1base : Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
          -((z.1 0) * z.2.1)) := by
        exact
          ((((continuous_apply (0 : Fin (d + 1))).comp continuous_fst) : Continuous
              fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => z.1 0).mul
            (((continuous_fst.comp continuous_snd) : Continuous
              fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => z.2.1))).neg
      have h1 : Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
          Complex.exp (-(↑(z.1 0 * z.2.1) : ℂ))) := by
        have h1' : Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
            Complex.exp (↑(-((z.1 0) * z.2.1)) : ℂ)) := by
          exact Complex.continuous_exp.comp (Complex.continuous_ofReal.comp h1base)
        simpa using h1'
      have h2 : Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
          Complex.exp (Complex.I * ↑(∑ i : Fin d, z.2.2 i * z.1 (Fin.succ i)))) := by
        exact
          Complex.continuous_exp.comp
            (continuous_const.mul (Complex.continuous_ofReal.comp hcont_sum))
      have h3 : Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => h z.1) := by
        exact (SchwartzMap.continuous h).comp continuous_fst
      simpa [G, f, mul_assoc] using h1.mul (h2.mul h3)
    simpa [Function.uncurry, f, G] using hcont.aestronglyMeasurable
  have hbound :
      ∀ᵐ z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) ∂(volume.prod μ),
        ‖Function.uncurry f z‖ ≤ ‖h z.1‖ := by
    have h_nonneg_p : ∀ᵐ p : ℝ × (Fin d → ℝ) ∂μ, 0 ≤ p.1 := by
      rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
      suffices
          {p : ℝ × (Fin d → ℝ) | ¬ 0 ≤ p.1} ⊆ Set.prod (Set.Iio 0) Set.univ by
        exact le_antisymm (le_trans (μ.mono this) (le_of_eq hsupp)) (zero_le _)
      intro p hp
      rcases p with ⟨E, q⟩
      simp only [Set.mem_setOf_eq, not_le] at hp
      exact Set.mk_mem_prod hp (Set.mem_univ q)
    have h_nonneg_prod :
        ∀ᵐ z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) ∂(volume.prod μ), 0 ≤ z.2.1 := by
      have hmeas :
          MeasurableSet {z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) | 0 ≤ z.2.1} := by
        let g : SpacetimeDim d × (ℝ × (Fin d → ℝ)) → ℝ := fun z => z.2.1
        have hg : Measurable g := by
          exact (((continuous_fst.comp continuous_snd) : Continuous g).measurable)
        exact hg measurableSet_Ici
      rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas]
      exact Filter.Eventually.of_forall fun _ => h_nonneg_p
    filter_upwards [h_nonneg_prod] with z hz
    rcases z with ⟨ξ, p⟩
    have hp_nonneg : 0 ≤ p.1 := hz
    by_cases hhξ : h ξ = 0
    · simp [f, hhξ]
    · have hξ_pos : 0 < ξ 0 := by
        exact hh_pos (subset_tsupport (h : SpacetimeDim d → ℂ)
          (by rwa [Function.mem_support]))
      have hphase :
          (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      have hexp_le_one :
          Real.exp (-(ξ 0 * p.1)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [hξ_pos, hp_nonneg]
      calc
        ‖Function.uncurry f (ξ, p)‖
            = ‖Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i)))‖ *
              ‖h ξ‖ := by
                simp [f, mul_assoc]
        _ = Real.exp (-(ξ 0 * p.1)) * ‖h ξ‖ := by
              rw [norm_mul, Complex.norm_exp, Complex.norm_exp, hphase, Real.exp_zero, mul_one]
              simp
        _ ≤ 1 * ‖h ξ‖ := by
              gcongr
        _ = ‖h ξ‖ := by ring
  have hh_int :
      Integrable (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => h z.1) (volume.prod μ) := by
    simpa using ((h.integrable (μ := volume)).comp_fst μ)
  have hf_int : Integrable (Function.uncurry f) (volume.prod μ) := by
    exact (hh_int.norm).mono' hf_meas hbound
  calc
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * h ξ
        = ∫ ξ : SpacetimeDim d,
            ∫ p : ℝ × (Fin d → ℝ),
              f ξ p ∂μ := by
            congr 1
            ext ξ
            simpa [laplaceFourierKernel, f, mul_assoc] using
              (MeasureTheory.integral_mul_const (h ξ)
                (fun p : ℝ × (Fin d → ℝ) =>
                  cexp (-(↑(ξ 0) * ↑p.1)) *
                    cexp (Complex.I * ↑(∑ x, p.2 x * ξ x.succ)))).symm
    _ = ∫ p : ℝ × (Fin d → ℝ),
          ∫ ξ : SpacetimeDim d, f ξ p ∂volume ∂μ := by
            exact MeasureTheory.integral_integral_swap (f := f) hf_int
    _ = ∫ p : ℝ × (Fin d → ℝ),
          ∫ ξ : SpacetimeDim d,
            Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
              h ξ ∂volume ∂μ := by
            simp [f]

private lemma mul_exp_neg_bound_local (c t : ℝ) (hc : 0 < c) :
    t * Real.exp (-c * t) ≤ Real.exp (-1) / c := by
  rw [le_div_iff₀ hc]
  calc
    t * Real.exp (-c * t) * c = c * t * Real.exp (-c * t) := by ring
    _ ≤ Real.exp (c * t - 1) * Real.exp (-c * t) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (c * t - 1)]
    _ = Real.exp (-1) := by
      rw [← Real.exp_add]
      ring_nf

/-- Dominated convergence for real weights converging pointwise to `1`. This is
the exact smearing-removal engine needed for the approximate-identity Bochner
route: once the weighted spectral factors stay in `[0,1]`, any integrable test
function can be pushed through the limit. -/
private theorem tendsto_integral_mul_of_realWeights_to_one
    {α : Type} [MeasurableSpace α]
    (ρ : Measure α) [IsFiniteMeasure ρ]
    (f : α → ℂ) (hf : Integrable f ρ)
    (w : ℕ → α → ℝ)
    (hw_meas : ∀ n, Measurable (w n))
    (hw_nonneg : ∀ n x, 0 ≤ w n x)
    (hw_le : ∀ n x, w n x ≤ 1)
    (hw_lim : ∀ x, Tendsto (fun n => w n x) atTop (nhds 1)) :
    Tendsto (fun n => ∫ x, f x * (w n x : ℂ) ∂ρ) atTop (nhds (∫ x, f x ∂ρ)) := by
  let F : ℕ → α → ℂ := fun n x => f x * (w n x : ℂ)
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) ρ := by
    intro n
    exact hf.aestronglyMeasurable.mul
      ((Complex.continuous_ofReal.measurable.comp (hw_meas n)).aestronglyMeasurable)
  have h_bound : ∀ n, ∀ᵐ x ∂ρ, ‖F n x‖ ≤ ‖f x‖ := by
    intro n
    exact Filter.Eventually.of_forall fun x => by
      dsimp [F]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw_nonneg n x)]
      have hle : ‖f x‖ * w n x ≤ ‖f x‖ * 1 := by
        exact mul_le_mul_of_nonneg_left (hw_le n x) (norm_nonneg _)
      simpa using hle
  have h_lim : ∀ᵐ x ∂ρ, Tendsto (fun n => F n x) atTop (nhds (f x)) := by
    exact Filter.Eventually.of_forall fun x => by
      have hwc : Tendsto (fun n => ((w n x : ℝ) : ℂ)) atTop (nhds (1 : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp (hw_lim x)
      have hmul :
          Tendsto (fun n => f x * ((w n x : ℝ) : ℂ)) atTop (nhds (f x * (1 : ℂ))) :=
        Filter.Tendsto.const_mul (f x) hwc
      simpa [F] using hmul
  simpa [F] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      hF_meas hf.norm h_bound h_lim)

/-- Spectral bridge, step A: once a finite Bochner measure represents the
semigroup-group matrix element, pairing its Laplace-Fourier kernel against a
positive-time compact Schwartz test is the same as pairing the OS matrix element
itself against that test. -/
private theorem bochner_kernel_integral_eq_semigroup_integral
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (v : OSHilbertSpace OS)
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ t a, 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc v t a =
        ∫ p, Complex.exp (-(↑(t * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i, p.2 i * a i)) ∂μ)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * h ξ =
      ∫ ξ : SpacetimeDim d,
        osSemigroupGroupMatrixElement (d := d) OS lgc v (ξ 0) (fun i => ξ (Fin.succ i)) *
          h ξ := by
  congr 1
  ext ξ
  by_cases hξ : (h : SpacetimeDim d → ℂ) ξ = 0
  · simp [hξ]
  · have hξ_pos : 0 < ξ 0 :=
      hh_pos (subset_tsupport (h : SpacetimeDim d → ℂ) (by rwa [Function.mem_support]))
    congr 1
    rw [hμ_repr (ξ 0) (fun i => ξ (Fin.succ i)) hξ_pos]
    simp [laplaceFourierKernel]

/-- OS-route step B: the semigroup-group matrix element attached to the
one-point vector generated by `φ` matches the translated two-point product
shell directly, without introducing a standalone off-diagonal kernel theorem
on the critical path. -/
private theorem osSemigroupGroupMatrixElement_eq_translatedProductShell_of_pos
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (hφ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    let ψ := reflectedSchwartzSpacetime φ
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos φ hφ_neg
    let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local ψ hψ_pos_time
    let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport φ hφ_compact
    osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            hφ_pos⟧) : OSHilbertSpace OS))
        (ξ 0) (fun i => ξ (Fin.succ i)) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ))) := by
  dsimp
  let ψ : SchwartzSpacetime d := reflectedSchwartzSpacetime φ
  let hψ_pos_time : tsupport (ψ : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0} :=
    reflectedSchwartzSpacetime_tsupport_pos φ hφ_neg
  let hψ_pos :
      tsupport (((onePointToFin1CLM d ψ : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime_local ψ hψ_pos_time
  let hψ_compact : HasCompactSupport (ψ : SpacetimeDim d → ℂ) :=
    reflectedSchwartzSpacetime_hasCompactSupport φ hφ_compact
  let xφ : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1))
      hφ_pos⟧) : OSHilbertSpace OS))
  let xψ : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
      hψ_pos⟧) : OSHilbertSpace OS))
  let ξs : Fin d → ℝ := fun i => ξ (Fin.succ i)
  let a0 : SpacetimeDim d := Fin.cons 0 ξs
  let ψ_translated : SchwartzSpacetime d := SCV.translateSchwartz (-a0) ψ
  let fψ : SchwartzNPoint d 1 := onePointToFin1CLM d ψ
  let gψ : SchwartzNPoint d 1 := onePointToFin1CLM d ψ_translated
  have hψ_translated_pos :
      tsupport ((gψ : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0_zero : a0 0 = 0 := by simp [a0]
    have hsup : ((gψ : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ) =
      (((translateSchwartzNPoint (d := d) a0 fψ) :
          NPointDomain d 1 → ℂ)) := by
        ext x
        simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
          translateSchwartzNPoint_apply, ψ_translated, a0, gψ, fψ, sub_eq_add_neg]
    rw [show tsupport ((gψ : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ) =
      tsupport (((translateSchwartzNPoint (d := d) a0 fψ) :
          NPointDomain d 1 → ℂ)) from congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) a0 ha0_zero fψ hψ_pos
  have hψ_translated_compact :
      HasCompactSupport ((gψ : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ) := by
    have hspace : HasCompactSupport (ψ_translated : SpacetimeDim d → ℂ) := by
      simpa [ψ_translated, Function.comp, SCV.translateSchwartz_apply, a0] using
        hψ_compact.comp_homeomorph (Homeomorph.addRight (-a0))
    simpa [onePointToFin1CLM] using
      (hspace.comp_homeomorph
        ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))
  have hx_eq_pre :
      (⟦PositiveTimeBorchersSequence.single 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d φ : SchwartzNPoint d 1))
          hφ_pos⟧ : OSPreHilbertSpace OS) =
        (⟦PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
            hψ_pos⟧ : OSPreHilbertSpace OS) :=
    mk_single_osConj_onePoint_eq_mk_single_reflected_of_real
      (d := d) OS φ hφ_real hφ_compact hφ_neg
  have hx_eq : xφ = xψ := by
    exact congrArg (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS)) hx_eq_pre
  have htrans_eq :
      (osSpatialTranslateHilbert (d := d) OS ξs) xψ =
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            gψ
            hψ_translated_pos⟧) : OSHilbertSpace OS)) := by
    simpa [ψ, hψ_pos_time, hψ_pos, a0, ψ_translated, gψ, fψ] using
      (osSpatialTranslateHilbert_single_onePoint_eq
        (d := d) OS ψ hψ_pos_time ξs)
  calc
    osSemigroupGroupMatrixElement (d := d) OS lgc xφ (ξ 0) ξs
        = osSemigroupGroupMatrixElement (d := d) OS lgc xψ (ξ 0) ξs := by
            rw [hx_eq]
    _ = ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          xψ
          (((show OSPreHilbertSpace OS from
              ⟦PositiveTimeBorchersSequence.single 1
                gψ
                hψ_translated_pos⟧) : OSHilbertSpace OS))
          ((ξ 0 : ℝ) : ℂ) := by
            simpa [osSpatialTranslateHilbert_zero, htrans_eq] using
              (osSemigroupGroupMatrixElement_eq_translated_pair
                (d := d) OS lgc xψ (0 : Fin d → ℝ) ξs (ξ 0) hξ)
    _ = OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
            hψ_pos)
          (PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d ψ_translated : SchwartzNPoint d 1)
            hψ_translated_pos)
          ((ξ 0 : ℝ) : ℂ) := by
            symm
            exact OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single 1
                fψ hψ_pos)
              (PositiveTimeBorchersSequence.single 1
                gψ hψ_translated_pos)
              ((ξ 0 : ℝ) : ℂ) (by simpa using hξ)
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (fψ.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0)
              gψ))) := by
            exact OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
              (d := d) (OS := OS) (lgc := lgc)
              (f := fψ)
              (hf_ord := hψ_pos)
              (g := gψ)
              (hg_ord := hψ_translated_pos)
              (hg_compact := hψ_translated_compact)
              (t := ξ 0) hξ
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (((SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1)) : SchwartzNPoint d 1).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0)
              gψ))) := by
            exact congrArg
              (fun Z : SchwartzNPoint d 2 =>
                OS.S 2 (ZeroDiagonalSchwartz.ofClassical Z))
              (by
                simpa [fψ, ψ] using
                  congrArg
                    (fun f : SchwartzNPoint d 1 =>
                      f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (ξ 0) gψ))
                    (osConj_onePointToFin1_eq_onePoint_reflected_of_real
                      (d := d) φ hφ_real).symm)
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ))) := by
            exact congrArg (fun Z => OS.S 2 Z) <|
              by
                simpa [ξs, a0, ψ_translated] using
                  shifted_single_test_eq_twoPointProductLift_translate_local
                    (d := d) φ ψ hφ_pos hψ_pos ξ hξ

/-- Public wrapper for the real negative-probe matrix-element identity. The OS
semigroup-group matrix element of the one-point probe generated by `φ` agrees
pointwise with the translated two-point product shell. -/
theorem osSemigroupGroupMatrixElement_eq_translatedProductShell_of_real_negative_probe_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local φ hφ_compact hφ_neg
    let ψ := reflectedSchwartzSpacetime φ
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos φ hφ_neg
    let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local ψ hψ_pos_time
    let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport φ hφ_compact
    osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            hφ_pos⟧) : OSHilbertSpace OS))
        (ξ 0) (fun i => ξ (Fin.succ i)) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ))) :=
  osSemigroupGroupMatrixElement_eq_translatedProductShell_of_pos
    (d := d) OS lgc φ hφ_real hφ_compact hφ_neg
    (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg)
    ξ hξ

/-- Combining spectral bridge step A with OS-route step B: pairing the
Laplace-Fourier kernel of the Bochner measure against a positive-time compact
Schwartz weight is exactly the weighted translated product-shell Schwinger
pairing for the reflected positive-time companion of the probe `φ`. -/
private theorem bochner_kernel_integral_eq_translatedProductShell_integral_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ t a, 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS)) t a =
        ∫ p : ℝ × (Fin d → ℝ),
          Complex.exp (-(↑(t * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (h : positiveTimeCompactSupportSubmodule d) :
    let ψ := reflectedSchwartzSpacetime φ
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ)))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
  dsimp
  have hφ_pos :
      tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  have hsemigroup :=
    bochner_kernel_integral_eq_semigroup_integral
      (d := d) OS lgc
      (((show OSPreHilbertSpace OS from
        ⟦PositiveTimeBorchersSequence.single 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d φ : SchwartzNPoint d 1))
          hφ_pos⟧) : OSHilbertSpace OS))
      μ hsupp hμ_repr (h : SchwartzSpacetime d) h.property.1 h.property.2
  calc
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ
      =
        ∫ ξ : SpacetimeDim d,
          osSemigroupGroupMatrixElement (d := d) OS lgc
            (((show OSPreHilbertSpace OS from
              ⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d φ : SchwartzNPoint d 1))
                hφ_pos⟧) : OSHilbertSpace OS))
            (ξ 0) (fun i => ξ (Fin.succ i)) * (h : SchwartzSpacetime d) ξ := hsemigroup
    _ =
        ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift φ
                (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
          else 0) * ((h : SchwartzSpacetime d) ξ) := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            by_cases hξ : 0 < ξ 0
            · rw [osSemigroupGroupMatrixElement_eq_translatedProductShell_of_pos
                (d := d) OS lgc φ hφ_real hφ_compact hφ_neg hφ_pos ξ hξ]
              simp [hξ]
            · have hξ_not_mem :
                  ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) :
                    SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
                intro hmem
                exact hξ (h.property.1 hmem)
              have hξ_zero :
                  ((h : positiveTimeCompactSupportSubmodule d) :
                    SchwartzSpacetime d) ξ = 0 :=
                image_eq_zero_of_notMem_tsupport hξ_not_mem
              simp [hξ, hξ_zero]

/-- The positive-time boundary integrand appearing in the packaged Bochner
formula is exactly the scalar orbit of `schwingerProductPositiveCLM_local`
along the translated reflected probe. This is the route-faithful bridge from
the explicit translated product shell to the one-point positive-time CLM orbit
used in the OS semigroup continuity package. -/
private theorem translatedProductShell_boundary_eq_schwingerProductPositiveOrbit_local
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (ξ : SpacetimeDim d) :
    let ψ := reflectedSchwartzSpacetime φ
    (if hξ : 0 < ξ 0 then
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ)))
    else 0) =
      (if hξ : 0 < ξ 0 then
        schwingerProductPositiveCLM_local OS φ
          (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
            (d := d) φ hφ_compact hφ_neg)
          (translatedPositiveTimeCompactSupport_local (d := d)
            (reflectedSchwartzSpacetime φ)
            (reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg)
            (reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact)
            ξ hξ)
      else 0) := by
  dsimp
  have hφ_pos :
      tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  by_cases hξ : 0 < ξ 0
  · simpa [hξ] using (schwingerProductPositiveCLM_local_apply_translated
      (d := d) OS φ hφ_pos
      (reflectedSchwartzSpacetime φ)
      (reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg)
      (reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact)
      ξ hξ).symm
  · simpa [hξ]

/-- Scalar-orbit form of the packaged Bochner kernel identity. This is the
exact same positive-time boundary functional as
`bochner_kernel_integral_eq_translatedProductShell_integral_local`, but
rewritten through the continuous one-point orbit
`schwingerProductPositiveCLM_local`. -/
private theorem bochner_kernel_integral_eq_schwingerProductPositiveOrbit_integral_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ t a, 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS)) t a =
        ∫ p : ℝ × (Fin d → ℝ),
          Complex.exp (-(↑(t * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (h : positiveTimeCompactSupportSubmodule d) :
    let ψ := reflectedSchwartzSpacetime φ
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          schwingerProductPositiveCLM_local OS φ
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)
            (translatedPositiveTimeCompactSupport_local (d := d)
              ψ
              (reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg)
              (reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact)
              ξ hξ)
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
  dsimp
  rw [bochner_kernel_integral_eq_translatedProductShell_integral_local
    (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμ_repr h]
  refine integral_congr_ae ?_
  filter_upwards with ξ
  rw [translatedProductShell_boundary_eq_schwingerProductPositiveOrbit_local
    (d := d) OS φ hφ_compact hφ_neg ξ]

/-- The Euclidean kernel induced by a flattened `k = 2` time-parametric witness. -/
def k2TimeParametricKernel
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) : NPointDomain d 2 → ℂ :=
  fun x => G (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j)))

/-! ### Coordinate unfolding lemmas for the active `k = 2` witness -/

/-- At the Euclidean section, the time-difference slot of `toDiffFlat` is
`I * (x₁⁰ - x₀⁰)`. -/
private theorem toDiffFlat_wickRotate_at_j10_local
    (x : NPointDomain d 2) :
    BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))
      (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) =
        Complex.I * (↑(x 1 0) - ↑(x 0 0)) := by
  simp only [BHW.toDiffFlat, BHW.flattenCfg, finProdFinEquiv.symm_apply_apply,
    BHW.diffCoordEquiv_apply]
  simp [wickRotatePoint]
  ring

/-- Multiplying the Euclidean time-difference slot by `-I` recovers the real
time difference `x₁⁰ - x₀⁰`. -/
private theorem neg_I_mul_toDiffFlat_wickRotate_j10_local
    (x : NPointDomain d 2) :
    -Complex.I * BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))
      (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) =
        ↑(x 1 0 - x 0 0) := by
  rw [toDiffFlat_wickRotate_at_j10_local]
  calc
    -Complex.I * (Complex.I * (↑(x 1 0) - ↑(x 0 0)))
        = ((-Complex.I) * Complex.I) * (↑(x 1 0) - ↑(x 0 0)) := by ring
    _ = ↑(x 1 0) - ↑(x 0 0) := by simp
    _ = ↑(x 1 0 - x 0 0) := by
          push_cast
          ring

/-- On the Euclidean section, the extracted spatial-difference coordinates are
the honest real spatial differences `x₁ˢ - x₀ˢ`. -/
private theorem extractDiffSpatialRe_toDiffFlat_wickRotate_local
    (x : NPointDomain d 2) :
    extractDiffSpatialRe (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))) =
      fun i => x 1 i.succ - x 0 i.succ := by
  ext i
  simp [extractDiffSpatialRe, BHW.toDiffFlat, BHW.flattenCfg,
    BHW.diffCoordEquiv_apply, wickRotatePoint]

/-- Route-independent density extension: once a continuous kernel CLM agrees with
`OS.S 2` on the flat-origin difference-shell generators, it agrees on all of
`ZeroDiagonalSchwartz d 2`. -/
theorem zeroDiagKernelCLM_eq_schwinger_of_flatOrigin_differenceShell_agreement
    (OS : OsterwalderSchraderAxioms d)
    (K : NPointDomain d 2 → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hShell :
      ∀ (χ h : SchwartzSpacetime d)
        (hzero : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0),
        OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
            (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))) :
    OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound =
      OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2 := by
  let A : Submodule ℂ (ZeroDiagonalSchwartz d 2) :=
    Submodule.span ℂ
      {f : ZeroDiagonalSchwartz d 2 |
        ∃ (χ h : SchwartzSpacetime d)
          (hzero : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0),
          f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}
  have hDense : Dense (A : Set (ZeroDiagonalSchwartz d 2)) :=
    flatOrigin_differenceShell_span_dense_zeroDiagonal (d := d)
  apply ContinuousLinearMap.eq_of_eq_on_dense
    (OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound)
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2)
    hDense
  intro f hf
  change f ∈ A at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro g hg
    rcases hg with ⟨χ, h, hzero, rfl⟩
    exact hShell χ h hzero
  · simpa using (OS.E0_linear 2).map_zero
  · intro u v _ _ hu hv
    simp [hu, hv]
  · intro c u _ hu
    simp [hu]

/-- Strict OS-route `k = 2` frontier: construct the flattened witness together
with the analytic control needed to package it as a zero-diagonal kernel CLM,
and prove agreement on the flat-origin difference-shell generators. -/
private theorem exists_normalized_negative_probe_local :
    ∃ (φ : SchwartzSpacetime d),
      (∀ x, 0 ≤ (φ x).re) ∧
      (∀ x, (φ x).im = 0) ∧
      (∫ x : SpacetimeDim d, φ x = 1) ∧
      HasCompactSupport (φ : SpacetimeDim d → ℂ) ∧
      tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0} := by
  obtain ⟨φseq, hnonneg, himag, hint, hcompact, hneg, _hball⟩ :=
    exists_negative_approx_identity_sequence (d := d)
  refine ⟨φseq 0, hnonneg 0, himag 0, hint 0, hcompact 0, hneg 0⟩

/-- The canonical OS-route `k = 2` witness built from a normalized negative-time
probe and its reflected positive-time companion. -/
def k2ProbeWitness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    (Fin (2 * (d + 1)) → ℂ) → ℂ :=
  let g := reflectedSchwartzSpacetime φ
  let hφ_pos :
      tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local (d := d) φ hφ_compact hφ_neg
  let hg_pos_time : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} :=
    reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
  let hg_pos :
      tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime_local (d := d) g hg_pos_time
  twoPointCorrectedWitness_local (d := d) OS lgc φ g hφ_pos hg_pos

/-- The one-variable Euclidean difference kernel attached to the canonical
normalized `k = 2` probe. -/
private def k2ProbeDifferenceKernel_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    SpacetimeDim d → ℂ :=
  fun ξ =>
    let ψ := reflectedSchwartzSpacetime φ
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local
        (d := d) φ hφ_compact hφ_neg
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
    let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local (d := d) ψ hψ_pos_time
    twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
      (ξ 0) (fun i => ξ i.succ)

/-- On real Euclidean configurations, the canonical probe witness is exactly the
semigroup-side spatial witness evaluated at the honest time/spatial difference
coordinates. -/
private theorem k2TimeParametricKernel_k2ProbeWitness_eq_twoPointSpatialWitness_realSection_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (x : NPointDomain d 2) :
    let ψ := reflectedSchwartzSpacetime φ
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local
        (d := d) φ hφ_compact hφ_neg
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
    let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local (d := d) ψ hψ_pos_time
    k2TimeParametricKernel (d := d)
        (k2ProbeWitness_local OS lgc φ hφ_compact hφ_neg) x =
      twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
        (↑(x 1 0 - x 0 0))
        (fun i => x 1 i.succ - x 0 i.succ) := by
  simp only [k2TimeParametricKernel, k2ProbeWitness_local, twoPointCorrectedWitness_local]
  rw [neg_I_mul_toDiffFlat_wickRotate_j10_local, extractDiffSpatialRe_toDiffFlat_wickRotate_local]

/-- The Euclidean section of the canonical `k = 2` probe witness is already a
pure difference kernel: it depends only on `x₁ - x₀`, with the expected
time/spatial split. -/
private theorem k2TimeParametricKernel_k2ProbeWitness_eq_twoPointDifferenceKernel_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    k2TimeParametricKernel (d := d)
        (k2ProbeWitness_local OS lgc φ hφ_compact hφ_neg) =
      OSReconstruction.twoPointDifferenceKernel (d := d)
        (k2ProbeDifferenceKernel_local (d := d) OS lgc φ hφ_compact hφ_neg) := by
  funext x
  rw [OSReconstruction.twoPointDifferenceKernel]
  simpa [k2ProbeDifferenceKernel_local] using
    (k2TimeParametricKernel_k2ProbeWitness_eq_twoPointSpatialWitness_realSection_local
      (d := d) OS lgc φ hφ_compact hφ_neg x)

theorem isTimeHolomorphicFlatPositiveTimeDiffWitness_k2ProbeWitness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    IsTimeHolomorphicFlatPositiveTimeDiffWitness
      (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) := by
  let g : SchwartzSpacetime d := reflectedSchwartzSpacetime φ
  have hg_pos_time : tsupport (g : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} :=
    reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
  have hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ) :=
    reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact
  have hφ_pos :
      tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local (d := d) φ hφ_compact hφ_neg
  have hg_pos :
      tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime_local (d := d) g hg_pos_time
  change IsTimeHolomorphicFlatPositiveTimeDiffWitness
    (twoPointCorrectedWitness_local (d := d) OS lgc φ g hφ_pos hg_pos)
  exact isTimeHolomorphicFlatPositiveTimeDiffWitness_twoPointCorrectedWitness_local
    (d := d) OS lgc φ g hφ_pos hg_pos hg_compact

/-- Strict OS-route `k = 2` frontier: construct the flattened semigroup witness
from a normalized negative-time probe. -/
private theorem exists_k2_timeParametric_semigroup_witness
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G := by
  obtain ⟨φ, _hφ_nonneg, _hφ_real, _hφ_int, hφ_compact, hφ_neg⟩ :=
    exists_normalized_negative_probe_local (d := d)
  refine ⟨k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg, ?_⟩
  exact isTimeHolomorphicFlatPositiveTimeDiffWitness_k2ProbeWitness_local
    (d := d) OS lgc φ hφ_compact hφ_neg

/-- Honest OS Step A package for the active `k = 2` route: choose a normalized
negative-time probe and extract the finite semigroup-group Bochner measure
attached to its reflected positive-time companion. -/
private theorem exists_k2_normalized_probe_measure_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (φ : SchwartzSpacetime d)
      (_hφ_nonneg : ∀ x, 0 ≤ (φ x).re)
      (hφ_real : ∀ x, (φ x).im = 0)
      (hφ_int : ∫ x : SpacetimeDim d, φ x = 1)
      (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
      (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
      (μ : Measure (ℝ × (Fin d → ℝ)))
      (_hμfin : IsFiniteMeasure μ),
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      (∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
          t a =
            ∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ) := by
  obtain ⟨φ, hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_neg⟩ :=
    exists_normalized_negative_probe_local (d := d)
  obtain ⟨μ, hμfin, hμneg, hμrepr⟩ :=
    exists_bochner_measure_for_approx_identity
      (d := d) OS lgc φ hφ_compact hφ_neg
  refine ⟨φ, hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_neg, μ, hμfin, hμneg, ?_⟩
  intro t a ht
  exact hμrepr t a ht

/-- On positive Euclidean time, the spatially parameterized semigroup witness
for a normalized negative-time probe is exactly the corresponding semigroup-group
matrix element. -/
private theorem twoPointSpatialWitness_eq_osSemigroupGroupMatrixElement_of_pos_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    let ψ := reflectedSchwartzSpacetime φ
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local
        (d := d) φ hφ_compact hφ_neg
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
    let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local (d := d) ψ hψ_pos_time
    twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
        (ξ 0) (fun i => ξ (Fin.succ i)) =
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            hφ_pos⟧) : OSHilbertSpace OS))
        (ξ 0) (fun i => ξ (Fin.succ i)) := by
  let ψ := reflectedSchwartzSpacetime φ
  let hφ_pos :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
  let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local (d := d) ψ hψ_pos_time
  dsimp [ψ, hφ_pos, hψ_pos_time, hψ_pos]
  let xφ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        ⟦PositiveTimeBorchersSequence.single 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d φ : SchwartzNPoint d 1))
          hφ_pos⟧) : OSHilbertSpace OS))
  let xψ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        ⟦PositiveTimeBorchersSequence.single 1
          (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
          hψ_pos⟧) : OSHilbertSpace OS))
  have hx_eq_pre :
      (⟦PositiveTimeBorchersSequence.single 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d φ : SchwartzNPoint d 1))
          hφ_pos⟧ : OSPreHilbertSpace OS) =
        (⟦PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
            hψ_pos⟧ : OSPreHilbertSpace OS) :=
    mk_single_osConj_onePoint_eq_mk_single_reflected_of_real
      (d := d) OS φ hφ_real hφ_compact hφ_neg
  have hx_eq : xφ = xψ := by
    exact congrArg (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS)) hx_eq_pre
  have htrans_eq :
      twoPointTranslatedOnePointVector_spatial_local (d := d) OS ψ hψ_pos
          (fun i => ξ (Fin.succ i)) =
        (osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xψ := by
    have hEq :
        twoPointTranslatedOnePointVector_spatial_local (d := d) OS ψ hψ_pos =
          fun y => (osSpatialTranslateHilbert (d := d) OS y) xψ := by
      funext y
      simpa [twoPointTranslatedOnePointVector_spatial_local, xψ] using
        (osSpatialTranslateHilbert_single_onePoint_eq (d := d) OS ψ hψ_pos_time y).symm
    simpa [hEq]
  calc
    twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
        (ξ 0) (fun i => ξ (Fin.succ i))
      = @inner ℂ (OSHilbertSpace OS) _
          xφ
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xψ)) := by
              rw [twoPointSpatialWitness_local, htrans_eq]
    _ = @inner ℂ (OSHilbertSpace OS) _
          xφ
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xφ)) := by
              rw [hx_eq]
    _ = osSemigroupGroupMatrixElement (d := d) OS lgc xφ
          (ξ 0) (fun i => ξ (Fin.succ i)) := by
            symm
            simpa [osSpatialTranslateHilbert_zero, xφ] using
              (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
                (d := d) OS lgc xφ (0 : Fin d → ℝ) (fun i => ξ (Fin.succ i))
                (ξ 0) hξ)

/-- On positive Euclidean time, the spatially parameterized semigroup witness
attached to the normalized probe agrees pointwise with the Laplace-Fourier
kernel of its Bochner measure. -/
private theorem twoPointSpatialWitness_eq_laplaceFourierKernel_of_pos_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hμ_repr : ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    let ψ := reflectedSchwartzSpacetime φ
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local
        (d := d) φ hφ_compact hφ_neg
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
    let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local (d := d) ψ hψ_pos_time
    twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
        (ξ 0) (fun i => ξ (Fin.succ i)) =
      laplaceFourierKernel (d := d) μ ξ := by
  let ψ := reflectedSchwartzSpacetime φ
  let hφ_pos :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
  let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local (d := d) ψ hψ_pos_time
  dsimp [ψ, hφ_pos, hψ_pos_time, hψ_pos]
  calc
    twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
        (ξ 0) (fun i => ξ (Fin.succ i))
      = osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              hφ_pos⟧) : OSHilbertSpace OS))
          (ξ 0) (fun i => ξ (Fin.succ i)) := by
            exact twoPointSpatialWitness_eq_osSemigroupGroupMatrixElement_of_pos_local
              (d := d) OS lgc φ hφ_real hφ_compact hφ_neg ξ hξ
    _ = ∫ p : ℝ × (Fin d → ℝ),
          Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) ∂μ := by
            exact hμ_repr (ξ 0) (fun i => ξ (Fin.succ i)) hξ
    _ = laplaceFourierKernel (d := d) μ ξ := by
            simp [laplaceFourierKernel]

/-- On positive Euclidean-time differences, the canonical probe difference
kernel is uniformly bounded by a constant depending only on the normalized
probe vector. This is the honest OS contraction estimate, before any VI.1
regularization on the boundary. -/
private theorem k2ProbeDifferenceKernel_norm_le_of_pos_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local
        (d := d) φ hφ_compact hφ_neg
    let xφ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            hφ_pos⟧) : OSHilbertSpace OS))
    ‖k2ProbeDifferenceKernel_local (d := d) OS lgc φ hφ_compact hφ_neg ξ‖ ≤
      2 * ‖xφ‖ ^ 2 := by
  let ψ := reflectedSchwartzSpacetime φ
  let hφ_pos :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
  let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local (d := d) ψ hψ_pos_time
  let xφ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        ⟦PositiveTimeBorchersSequence.single 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d φ : SchwartzNPoint d 1))
          hφ_pos⟧) : OSHilbertSpace OS))
  have hwit :
      twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
          (ξ 0) (fun i => ξ (Fin.succ i)) =
        osSemigroupGroupMatrixElement (d := d) OS lgc xφ
          (ξ 0) (fun i => ξ (Fin.succ i)) := by
    simpa [xφ] using
      (twoPointSpatialWitness_eq_osSemigroupGroupMatrixElement_of_pos_local
        (d := d) OS lgc φ hφ_real hφ_compact hφ_neg ξ hξ)
  have hU : osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i)) ∈
      unitary (OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS) := by
    constructor
    · exact osSpatialTranslateHilbert_unitary_left (d := d) OS (fun i => ξ (Fin.succ i))
    · exact osSpatialTranslateHilbert_unitary_right (d := d) OS (fun i => ξ (Fin.succ i))
  have hnormU :
      ‖(osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xφ‖ = ‖xφ‖ :=
    ContinuousLinearMap.norm_map_of_mem_unitary
      (u := osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) hU xφ
  calc
    ‖k2ProbeDifferenceKernel_local (d := d) OS lgc φ hφ_compact hφ_neg ξ‖
      = ‖twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
          (ξ 0) (fun i => ξ (Fin.succ i))‖ := by
            simp [k2ProbeDifferenceKernel_local, ψ, hφ_pos, hψ_pos_time, hψ_pos]
    _ = ‖osSemigroupGroupMatrixElement (d := d) OS lgc xφ
          (ξ 0) (fun i => ξ (Fin.succ i))‖ := by
            rw [hwit]
    _ = ‖@inner ℂ (OSHilbertSpace OS) _
          xφ
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xφ))‖ := by
            exact congrArg norm <| by
              simpa [osSpatialTranslateHilbert_zero, xφ] using
                (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
                  (d := d) OS lgc xφ (0 : Fin d → ℝ) (fun i => ξ (Fin.succ i))
                  (ξ 0) hξ)
    _ ≤ ‖xφ‖ *
        ‖(osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xφ)‖ := by
            exact norm_inner_le_norm _ _
    _ ≤ ‖xφ‖ *
        (‖osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ)‖ *
          ‖(osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xφ‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖xφ‖ *
        (2 * ‖(osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xφ‖) := by
            gcongr
            exact osTimeShiftHilbertComplex_norm_le (d := d) OS lgc ((ξ 0 : ℝ) : ℂ) hξ
    _ = ‖xφ‖ * (2 * ‖xφ‖) := by rw [hnormU]
    _ = 2 * ‖xφ‖ ^ 2 := by ring

/-- On positive Euclidean-time differences, the one-variable difference kernel
attached to the canonical probe is exactly the Laplace-Fourier kernel of the
packaged Bochner measure. -/
private theorem k2ProbeDifferenceKernel_eq_laplaceFourier_of_pos_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hμ_repr : ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    k2ProbeDifferenceKernel_local (d := d) OS lgc φ hφ_compact hφ_neg ξ =
      laplaceFourierKernel (d := d) μ ξ := by
  simpa [k2ProbeDifferenceKernel_local] using
    (twoPointSpatialWitness_eq_laplaceFourierKernel_of_pos_local
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hμ_repr ξ hξ)

/-- Reduced positive-support pairing for the packaged probe witness. This is the
common positive-time surface on which the semigroup witness and the Bochner
measure coincide. -/
private theorem integral_twoPointSpatialWitness_mul_eq_translatedProductShell_integral_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (h : positiveTimeCompactSupportSubmodule d) :
    let ψ := reflectedSchwartzSpacetime φ
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local
        (d := d) φ hφ_compact hφ_neg
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
    let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local (d := d) ψ hψ_pos_time
    ∫ ξ : SpacetimeDim d,
      twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
        (ξ 0) (fun i => ξ (Fin.succ i)) * (h : SchwartzSpacetime d) ξ =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ
              (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
  let ψ := reflectedSchwartzSpacetime φ
  let hφ_pos :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
  let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local (d := d) ψ hψ_pos_time
  dsimp [ψ, hφ_pos, hψ_pos_time, hψ_pos]
  calc
    ∫ ξ : SpacetimeDim d,
        twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
          (ξ 0) (fun i => ξ (Fin.succ i)) * (h : SchwartzSpacetime d) ξ
      = ∫ ξ : SpacetimeDim d,
          laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            by_cases hξ : 0 < ξ 0
            · rw [twoPointSpatialWitness_eq_laplaceFourierKernel_of_pos_local
                (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hμ_repr ξ hξ]
            · have hξ_not_mem :
                  ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) :
                    SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
                intro hmem
                exact hξ (h.property.1 hmem)
              have hξ_zero :
                  ((h : positiveTimeCompactSupportSubmodule d) :
                    SchwartzSpacetime d) ξ = 0 :=
                image_eq_zero_of_notMem_tsupport hξ_not_mem
              simp [hξ, hξ_zero]
    _ = ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift φ
                (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
            exact bochner_kernel_integral_eq_translatedProductShell_integral_local
              (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμ_repr h

/-- Reduced one-variable pairing form of the canonical probe kernel on the
honest positive-time Schwartz test domain. -/
private theorem integral_k2ProbeDifferenceKernel_mul_eq_translatedProductShell_integral_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
      k2ProbeDifferenceKernel_local (d := d) OS lgc φ hφ_compact hφ_neg ξ *
        (h : SchwartzSpacetime d) ξ =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ
              (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
  simpa [k2ProbeDifferenceKernel_local] using
    (integral_twoPointSpatialWitness_mul_eq_translatedProductShell_integral_local
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμ_repr h)

/-- Honest OS Step B package for the active `k = 2` route: the normalized
probe and its semigroup-group Bochner measure already reproduce the translated
product-shell Schwinger pairing on positive-time compact-support tests. -/
private theorem exists_k2_normalized_probe_translatedProductShell_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (φ : SchwartzSpacetime d)
      (hφ_real : ∀ x, (φ x).im = 0)
      (hφ_int : ∫ x : SpacetimeDim d, φ x = 1)
      (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
      (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
      (μ : Measure (ℝ × (Fin d → ℝ)))
      (_hμfin : IsFiniteMeasure μ),
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      (∀ h : positiveTimeCompactSupportSubmodule d,
        ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ =
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift φ
                  (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
            else 0) * ((h : SchwartzSpacetime d) ξ)) := by
  obtain ⟨φ, hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_neg, μ, hμfin, hsupp, hμrepr⟩ :=
    exists_k2_normalized_probe_measure_local (d := d) OS lgc
  refine ⟨φ, hφ_real, hφ_int, hφ_compact, hφ_neg, μ, hμfin, hsupp, ?_⟩
  intro h
  letI : IsFiniteMeasure μ := hμfin
  exact bochner_kernel_integral_eq_translatedProductShell_integral_local
    (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμrepr h

/-- Combined OS-route `k = 2` local package: a single normalized negative-time
probe `φ` supplies both the analytic semigroup witness and the finite Bochner
measure whose Laplace-Fourier kernel reproduces the translated product-shell
pairing on positive-time compact-support tests. This isolates the last blocker
to the reduced comparison step, rather than repeated existence unpacking. -/
private theorem exists_k2_probe_witness_and_pairing_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (φ : SchwartzSpacetime d)
      (hφ_real : ∀ x, (φ x).im = 0)
      (hφ_int : ∫ x : SpacetimeDim d, φ x = 1)
      (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
      (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
      (μ : Measure (ℝ × (Fin d → ℝ)))
      (_hμfin : IsFiniteMeasure μ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness
          (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      (∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
          t a =
            ∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ) ∧
      (∀ h : positiveTimeCompactSupportSubmodule d,
        ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ =
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift φ
                  (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
            else 0) * ((h : SchwartzSpacetime d) ξ)) := by
  obtain ⟨φ, _hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_neg, μ, hμfin, hsupp, hμrepr⟩ :=
    exists_k2_normalized_probe_measure_local (d := d) OS lgc
  have hhol :
      IsTimeHolomorphicFlatPositiveTimeDiffWitness
        (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) :=
    isTimeHolomorphicFlatPositiveTimeDiffWitness_k2ProbeWitness_local
      (d := d) OS lgc φ hφ_compact hφ_neg
  refine ⟨φ, hφ_real, hφ_int, hφ_compact, hφ_neg, μ, hμfin, hhol, hsupp, hμrepr, ?_⟩
  intro h
  letI : IsFiniteMeasure μ := hμfin
  exact bochner_kernel_integral_eq_translatedProductShell_integral_local
    (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμrepr h

/-- On positive Euclidean-time differences, the real Euclidean section of the
canonical `k = 2` probe witness is exactly the Laplace-Fourier kernel of the
packaged Bochner measure. This is the direct boundary-value bridge from the
semigroup witness to the reduced one-variable kernel on the honest positive-time
difference cone. -/
private theorem k2TimeParametricKernel_k2ProbeWitness_eq_laplaceFourier_of_pos_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hμ_repr : ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (x : NPointDomain d 2)
    (hx : x 0 0 < x 1 0) :
    k2TimeParametricKernel (d := d)
        (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x =
      laplaceFourierKernel (d := d) μ (fun i => x 1 i - x 0 i) := by
  let ξ : SpacetimeDim d := fun i => x 1 i - x 0 i
  have hξ : 0 < ξ 0 := by
    dsimp [ξ]
    linarith
  calc
    k2TimeParametricKernel (d := d)
        (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x
      = twoPointSpatialWitness_local (d := d) OS lgc
          φ (reflectedSchwartzSpacetime φ)
          (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
            (d := d) φ hφ_compact hφ_neg)
          (onePointToFin1_tsupport_orderedPositiveTime_local
            (d := d) (reflectedSchwartzSpacetime φ)
            (reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg))
          (ξ 0) (fun i => ξ i.succ) := by
            simpa [ξ] using
              (k2TimeParametricKernel_k2ProbeWitness_eq_twoPointSpatialWitness_realSection_local
                (d := d) OS lgc φ hφ_compact hφ_neg x)
    _ = laplaceFourierKernel (d := d) μ ξ := by
          exact twoPointSpatialWitness_eq_laplaceFourierKernel_of_pos_local
            (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hμ_repr ξ hξ
    _ = laplaceFourierKernel (d := d) μ (fun i => x 1 i - x 0 i) := by
          rfl

/-- Public positive-time reduction of the canonical `k = 2` probe witness to
the one-variable Laplace-Fourier kernel of its packaged Bochner measure. This
is the reduced-difference bridge used by the isolated VI.1 file. -/
theorem k2TimeParametricKernel_probe_eq_laplaceFourier_of_pos_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hμ_repr : ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (x : NPointDomain d 2)
    (hx : x 0 0 < x 1 0) :
    k2TimeParametricKernel (d := d)
        (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x =
      laplaceFourierKernel (d := d) μ (fun i => x 1 i - x 0 i) := by
  exact k2TimeParametricKernel_k2ProbeWitness_eq_laplaceFourier_of_pos_local
    (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hμ_repr x hx

/-- On the positive time-ordering sector `x₀⁰ < x₁⁰`, the Euclidean section of
the canonical `k = 2` probe witness is continuous as a function of the real
Euclidean configuration. -/
theorem continuousOn_k2TimeParametricKernel_of_pos_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    ContinuousOn
      (k2TimeParametricKernel (d := d)
        (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg))
      {x : NPointDomain d 2 | x 0 0 < x 1 0} := by
  let ψ := reflectedSchwartzSpacetime φ
  let hφ_pos :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
  let hψ_pos := onePointToFin1_tsupport_orderedPositiveTime_local (d := d) ψ hψ_pos_time
  let Φ : NPointDomain d 2 → ℂ × (Fin d → ℝ) := fun x =>
    ((x 1 0 - x 0 0 : ℝ), fun i => x 1 i.succ - x 0 i.succ)
  have hΦ_cont : Continuous Φ := by
    refine Continuous.prodMk ?_ ?_
    · exact (Complex.continuous_ofReal.comp
        (((continuous_apply 0).comp (continuous_apply 1)).sub
          ((continuous_apply 0).comp (continuous_apply 0))))
    · refine continuous_pi ?_
      intro i
      exact ((continuous_apply i.succ).comp (continuous_apply 1)).sub
        ((continuous_apply i.succ).comp (continuous_apply 0))
  have hΦ_maps :
      Set.MapsTo Φ {x : NPointDomain d 2 | x 0 0 < x 1 0}
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    intro x hx
    refine ⟨?_, trivial⟩
    simpa [Φ] using hx
  have hcont_spatial :=
    continuousOn_twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
  have hcomp :
      ContinuousOn
        (fun x =>
          twoPointSpatialWitness_local (d := d) OS lgc φ ψ hφ_pos hψ_pos
            (Φ x).1 (Φ x).2)
        {x : NPointDomain d 2 | x 0 0 < x 1 0} :=
    hcont_spatial.comp hΦ_cont.continuousOn hΦ_maps
  refine hcomp.congr ?_
  intro x hx
  simpa [Φ] using
    (k2TimeParametricKernel_k2ProbeWitness_eq_twoPointSpatialWitness_realSection_local
      (d := d) OS lgc φ hφ_compact hφ_neg x)

/-- Positive-time Euclidean sections of the canonical probe witness satisfy the
same uniform contraction bound as the underlying one-variable difference
kernel. -/
theorem k2TimeParametricKernel_norm_le_of_pos_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (x : NPointDomain d 2)
    (hx : x 0 0 < x 1 0) :
    let hφ_pos :=
      osConj_onePointToFin1_tsupport_orderedPositiveTime_local
        (d := d) φ hφ_compact hφ_neg
    let xφ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            hφ_pos⟧) : OSHilbertSpace OS))
    ‖k2TimeParametricKernel (d := d)
        (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x‖ ≤
      2 * ‖xφ‖ ^ 2 := by
  let ξ : SpacetimeDim d := fun i => x 1 i - x 0 i
  have hξ : 0 < ξ 0 := by
    dsimp [ξ]
    linarith
  have hdiff : x 1 - x 0 = ξ := by
    ext i
    simp [ξ]
  calc
    ‖k2TimeParametricKernel (d := d)
        (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x‖
      = ‖k2ProbeDifferenceKernel_local (d := d) OS lgc φ hφ_compact hφ_neg ξ‖ := by
          rw [k2TimeParametricKernel_k2ProbeWitness_eq_twoPointDifferenceKernel_local
            (d := d) OS lgc φ hφ_compact hφ_neg]
          simp [OSReconstruction.twoPointDifferenceKernel, hdiff]
    _ ≤ 2 * ‖((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS)‖ ^ 2 := by
          simpa [ξ] using
            (k2ProbeDifferenceKernel_norm_le_of_pos_local
              (d := d) OS lgc φ hφ_real hφ_compact hφ_neg ξ hξ)

/-- The canonical probe witness reduces the full two-point difference-shell
pairing to the reduced one-variable Laplace-Fourier pairing on the positive-time
difference cone. This is the exact bridge needed before the final OS-II
boundary-value identification step. -/
theorem integral_k2ProbeWitness_mul_differenceLift_eq_reduced_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hμ_repr : ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (χ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ x : NPointDomain d 2,
      k2TimeParametricKernel (d := d)
          (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x *
        twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
      (∫ u : SpacetimeDim d, χ u) *
        ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ := by
  calc
    ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x *
          twoPointDifferenceLift χ (h : SchwartzSpacetime d) x
      =
        ∫ x : NPointDomain d 2,
          OSReconstruction.twoPointDifferenceKernel (d := d)
            (laplaceFourierKernel (d := d) μ) x *
            twoPointDifferenceLift χ (h : SchwartzSpacetime d) x := by
              refine integral_congr_ae ?_
              filter_upwards with x
              by_cases hx0 : (h : SchwartzSpacetime d) (x 1 - x 0) = 0
              · simp [twoPointDifferenceLift_apply, hx0]
              · have hx_mem :
                    x 1 - x 0 ∈ tsupport ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
                      exact subset_tsupport _
                        (Function.mem_support.mpr hx0)
                have hx_pos : 0 < (x 1 - x 0) 0 := h.property.1 hx_mem
                have hx_pos' : 0 < x 1 0 - x 0 0 := by
                  simpa using hx_pos
                have hx_time : x 0 0 < x 1 0 := by
                  exact sub_pos.mp hx_pos'
                have hdiff : (fun i => x 1 i - x 0 i) = x 1 - x 0 := by
                  ext i
                  simp
                rw [k2TimeParametricKernel_k2ProbeWitness_eq_laplaceFourier_of_pos_local
                  (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hμ_repr x hx_time]
                rw [OSReconstruction.twoPointDifferenceKernel, hdiff]
    _ =
        (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ := by
            exact OSReconstruction.integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
              (d := d) (laplaceFourierKernel (d := d) μ) χ (h : SchwartzSpacetime d)

/-- Combining the reduced pairing bridge with the packaged Bochner identity: the
canonical probe witness already reproduces the weighted translated product-shell
boundary functional on every positive-time compact-support difference shell. -/
theorem integral_k2ProbeWitness_mul_differenceLift_eq_translatedProductShell_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (χ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ x : NPointDomain d 2,
      k2TimeParametricKernel (d := d)
          (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x *
        twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
      (∫ u : SpacetimeDim d, χ u) *
        ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift φ
                (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
          else 0) * ((h : SchwartzSpacetime d) ξ) := by
  calc
    ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x *
          twoPointDifferenceLift χ (h : SchwartzSpacetime d) x
      =
        (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ := by
            exact integral_k2ProbeWitness_mul_differenceLift_eq_reduced_pairing_local
              (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hμ_repr χ h
    _ =
        (∫ u : SpacetimeDim d, χ u) *
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift φ
                  (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
            else 0) * ((h : SchwartzSpacetime d) ξ) := by
              rw [bochner_kernel_integral_eq_translatedProductShell_integral_local
                (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμ_repr h]

/-- Fixed-probe positive-time shell package.

For any normalized negative-time probe `φ`, the canonical `k = 2` witness,
its Bochner semigroup-group measure, the positive-time Laplace-Fourier
identification, and the descended difference-shell pairing formula are all
available before the VI.1 regularization step. This is the per-probe version of
the later existential package, and is the right input for a shrinking
approximate-identity sequence. -/
theorem exists_k2_positiveTime_shell_package_of_negative_probe_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_int : ∫ x : SpacetimeDim d, φ x = 1)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ)))
      (_hμfin : IsFiniteMeasure μ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness
          (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      (∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
          t a =
            ∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ) ∧
      (∀ (x : NPointDomain d 2), x 0 0 < x 1 0 →
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x =
          laplaceFourierKernel (d := d) μ (fun i => x 1 i - x 0 i)) ∧
      (∀ (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d)
              (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x *
            twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
          (∫ u : SpacetimeDim d, χ u) *
            ∫ ξ : SpacetimeDim d,
              (if hξ : 0 < ξ 0 then
                OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                  (twoPointProductLift φ
                    (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
              else 0) * ((h : SchwartzSpacetime d) ξ)) := by
  obtain ⟨μ, hμfin, hsupp, hμrepr⟩ :=
    exists_bochner_measure_for_approx_identity
      (d := d) OS lgc φ hφ_compact hφ_neg
  have hhol :
      IsTimeHolomorphicFlatPositiveTimeDiffWitness
        (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) :=
    isTimeHolomorphicFlatPositiveTimeDiffWitness_k2ProbeWitness_local
      (d := d) OS lgc φ hφ_compact hφ_neg
  refine ⟨μ, hμfin, hhol, hsupp, hμrepr, ?_, ?_⟩
  · intro x hx
    exact k2TimeParametricKernel_k2ProbeWitness_eq_laplaceFourier_of_pos_local
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hμrepr x hx
  · intro χ h
    letI : IsFiniteMeasure μ := hμfin
    exact integral_k2ProbeWitness_mul_differenceLift_eq_translatedProductShell_pairing_local
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμrepr χ h

/-- Sequence-level version of the previous package.

For a shrinking normalized negative approximate identity `φ_seq`, each probe
`φ_seq n` carries its own Bochner measure and positive-time shell package. This
is the direct OS-side input to the remaining VI.1 regularization step. -/
theorem exists_k2_positiveTime_shell_package_of_negativeApproxIdentity_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ))),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      (∀ n,
        IsTimeHolomorphicFlatPositiveTimeDiffWitness
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n))) ∧
      (∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
      (∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧) : OSHilbertSpace OS))
          t a =
            ∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n)) ∧
      (∀ n (x : NPointDomain d 2), x 0 0 < x 1 0 →
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n)) x =
          laplaceFourierKernel (d := d) (μ_seq n) (fun i => x 1 i - x 0 i)) ∧
      (∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d)
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
            twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
          (∫ u : SpacetimeDim d, χ u) *
            ∫ ξ : SpacetimeDim d,
              (if hξ : 0 < ξ 0 then
                OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                  (twoPointProductLift (φ_seq n)
                    (SCV.translateSchwartz (-ξ)
                      (reflectedSchwartzSpacetime (φ_seq n)))))
              else 0) * ((h : SchwartzSpacetime d) ξ)) := by
  have hpack :
      ∀ n,
        ∃ (μ : Measure (ℝ × (Fin d → ℝ)))
          (_hμfin : IsFiniteMeasure μ),
          IsTimeHolomorphicFlatPositiveTimeDiffWitness
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq n) (hφ_compact n) (hφ_neg n)) ∧
          μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
          (∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
            osSemigroupGroupMatrixElement (d := d) OS lgc
              (((show OSPreHilbertSpace OS from
                ⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                  (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                    (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧) : OSHilbertSpace OS))
              t a =
                ∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(t * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ) ∧
          (∀ (x : NPointDomain d 2), x 0 0 < x 1 0 →
            k2TimeParametricKernel (d := d)
                (k2ProbeWitness_local (d := d) OS lgc
                  (φ_seq n) (hφ_compact n) (hφ_neg n)) x =
              laplaceFourierKernel (d := d) μ (fun i => x 1 i - x 0 i)) ∧
          (∀ (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
            ∫ x : NPointDomain d 2,
              k2TimeParametricKernel (d := d)
                  (k2ProbeWitness_local (d := d) OS lgc
                    (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
                twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
              (∫ u : SpacetimeDim d, χ u) *
                ∫ ξ : SpacetimeDim d,
                  (if hξ : 0 < ξ 0 then
                    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                      (twoPointProductLift (φ_seq n)
                        (SCV.translateSchwartz (-ξ)
                          (reflectedSchwartzSpacetime (φ_seq n)))))
                  else 0) * ((h : SchwartzSpacetime d) ξ)) := by
    intro n
    exact exists_k2_positiveTime_shell_package_of_negative_probe_local
      (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_int n) (hφ_compact n) (hφ_neg n)
  choose μ_seq hμfin hhol hsupp hμrepr hkernel hpair using hpack
  refine ⟨μ_seq, hμfin, hhol, hsupp, hμrepr, hkernel, hpair⟩

/-- Consolidated positive-time shell package for the active `k = 2` witness.

This theorem packages all already-proved OS-side data that live strictly before
the VI.1 regularization step:
- the analytic flattened witness `G`,
- its Bochner semigroup-group representation,
- its identification with the Laplace-Fourier kernel on positive-time
  Euclidean differences,
- and the resulting difference-shell pairing formula against
  positive-time compact-support tests.

The remaining `k = 2` frontier should use this package as input, rather than
rebuilding these semigroup facts again. -/
theorem exists_k2_positiveTime_shell_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
      (φ : SchwartzSpacetime d)
      (hφ_real : ∀ x, (φ x).im = 0)
      (hφ_int : ∫ x : SpacetimeDim d, φ x = 1)
      (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
      (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
      (μ : Measure (ℝ × (Fin d → ℝ)))
      (_hμfin : IsFiniteMeasure μ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      (∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
          t a =
            ∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ) ∧
      (∀ (x : NPointDomain d 2), x 0 0 < x 1 0 →
        k2TimeParametricKernel (d := d) G x =
          laplaceFourierKernel (d := d) μ (fun i => x 1 i - x 0 i)) ∧
      (∀ (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G x *
            twoPointDifferenceLift χ (h : SchwartzSpacetime d) x =
          (∫ u : SpacetimeDim d, χ u) *
            ∫ ξ : SpacetimeDim d,
              (if hξ : 0 < ξ 0 then
                OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                  (twoPointProductLift φ
                    (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
              else 0) * ((h : SchwartzSpacetime d) ξ)) := by
  obtain ⟨φ, hφ_real, hφ_int, hφ_compact, hφ_neg, μ, hμfin, hhol, hsupp, hμrepr, hpair⟩ :=
    exists_k2_probe_witness_and_pairing_package_local (d := d) OS lgc
  refine ⟨k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg,
    φ, hφ_real, hφ_int, hφ_compact, hφ_neg, μ, hμfin, hhol, hsupp, hμrepr, ?_, ?_⟩
  · intro x hx
    exact k2TimeParametricKernel_k2ProbeWitness_eq_laplaceFourier_of_pos_local
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hμrepr x hx
  · intro χ h
    letI : IsFiniteMeasure μ := hμfin
    exact integral_k2ProbeWitness_mul_differenceLift_eq_translatedProductShell_pairing_local
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμrepr χ h

/-- For a normalized center cutoff, the reduced positive-time Schwinger
functional may be evaluated using any other normalized center test. -/
theorem schwingerDifferencePositiveCLM_eq_of_normalized_center_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d)
    (hχ : ∫ x : SpacetimeDim d, χ x = 1)
    (h : positiveTimeCompactSupportSubmodule d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ (h : SchwartzSpacetime d))) =
      (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h := by
  simpa [hχ, one_mul] using
    (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM_eq_centerValue
      (d := d) (OS := OS) χ₀ hχ₀ χ h)

/-- Public reduced positive-time pairing identity for the Bochner measure of a
fixed normalized negative-time probe. This exposes the one-variable
Laplace-Fourier pairing needed by the isolated VI.1 file without reopening the
larger witness package. -/
theorem integral_laplaceFourierKernel_mul_eq_measure_integral_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * h ξ ∂volume =
      ∫ p : ℝ × (Fin d → ℝ),
        ∫ ξ : SpacetimeDim d,
          Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
            h ξ ∂volume ∂μ := by
  exact integral_laplaceFourierKernel_mul_eq (d := d) μ hsupp h hh_pos hh_compact

/-- Public reduced positive-time pairing identity for the Bochner measure of a
fixed normalized negative-time probe. This exposes the one-variable
Laplace-Fourier pairing needed by the isolated VI.1 file without reopening the
larger witness package. -/
theorem integral_laplaceFourierKernel_mul_eq_translatedProductShell_integral_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ
              (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
  exact bochner_kernel_integral_eq_translatedProductShell_integral_local
    (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμ_repr h
end
