/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanKernel
import OSReconstruction.SCV.SemigroupGroupBochner
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# `k = 2` Base-Step Decomposition

This file isolates the genuine mathematical subproblems behind the root blocker
`schwinger_continuation_base_step_timeParametric`.

The active decomposition is:

1. construct a positive-time approximate identity sequence,
2. apply semigroup-group Bochner to each approximate-identity vector state,
3. remove the `|φ̂_n|²` smearing and recover the Schwinger difference pairing,
4. prove the resulting limit kernel is holomorphic in the time variable,
5. assemble the `k = 2` time-parametric base-step witness.

These are theorem-level `sorry`s by design: they are the real intermediate
mathematical gaps on the OS route, not wrappers or repackagings.
-/

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped Pointwise

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

/-- The reflected positive-time companion of a negative-time Schwartz probe. -/
private def reflectedSchwartzSpacetime (φ : SchwartzSpacetime d) : SchwartzSpacetime d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ spacetimeTimeReflectionCLE φ

@[simp] private theorem reflectedSchwartzSpacetime_apply
    (φ : SchwartzSpacetime d) (x : SpacetimeDim d) :
    reflectedSchwartzSpacetime φ x = φ (timeReflection d x) := by
  simp [reflectedSchwartzSpacetime, spacetimeTimeReflectionCLE]

private theorem reflectedSchwartzSpacetime_hasCompactSupport
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ)) :
    HasCompactSupport (reflectedSchwartzSpacetime φ : SpacetimeDim d → ℂ) := by
  simpa [reflectedSchwartzSpacetime, Function.comp] using
    hφ_compact.comp_homeomorph (spacetimeTimeReflectionCLE.toHomeomorph)

private theorem reflectedSchwartzSpacetime_tsupport_pos
    (φ : SchwartzSpacetime d)
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    tsupport (reflectedSchwartzSpacetime φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} := by
  intro x hx
  have hx' : timeReflection d x ∈ tsupport (φ : SpacetimeDim d → ℂ) := by
    exact tsupport_comp_subset_preimage (φ : SpacetimeDim d → ℂ)
      (f := timeReflection d) spacetimeTimeReflectionCLE.continuous hx
  have hneg := hφ_neg hx'
  simpa [timeReflection] using hneg

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

/-- Local support bridge: negative-time support of a one-point spacetime probe
becomes ordered positive-time support after `osConj`, because time reflection
flips the sign of the time coordinate. This is the exact support input needed
for the OS Hilbert one-point vector in theorem 2, without importing the
downstream kernel file. -/
private theorem osConj_onePointToFin1_tsupport_orderedPositiveTime_local
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

private theorem twoPointDifferenceLift_nonzero_implies_offDiagonal_local
    (χ h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    {x : NPointDomain d 2}
    (hx : twoPointDifferenceLift χ h x ≠ 0) :
    x 0 ≠ x 1 := by
  intro hdiag
  have hhx : h (x 1 - x 0) ≠ 0 := by
    intro hzero
    apply hx
    simp [twoPointDifferenceLift_apply, hzero]
  have hmem : x 1 - x 0 ∈ tsupport (h : SpacetimeDim d → ℂ) := by
    exact subset_tsupport _ (by simpa [Function.mem_support] using hhx)
  exact h0 (by simpa [hdiag] using hmem)

private theorem translate_nonzero_mem_tsupport_add_local
    (ψ h : SchwartzSpacetime d)
    {ξ x : SpacetimeDim d}
    (hξ : h ξ ≠ 0)
    (hx : (SCV.translateSchwartz (-ξ) ψ) x ≠ 0) :
    x ∈ tsupport (ψ : SpacetimeDim d → ℂ) + tsupport (h : SpacetimeDim d → ℂ) := by
  have hξ_mem : ξ ∈ tsupport (h : SpacetimeDim d → ℂ) := by
    exact subset_tsupport _ (by simpa [Function.mem_support] using hξ)
  have hx_mem : x + (-ξ) ∈ tsupport (ψ : SpacetimeDim d → ℂ) := by
    exact subset_tsupport _ (by
      simpa [SCV.translateSchwartz_apply, Function.mem_support] using hx)
  refine ⟨x + (-ξ), hx_mem, ξ, hξ_mem, ?_⟩
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private theorem sum_positiveTime_tsupport_pos_local
    (ψ h : SchwartzSpacetime d)
    (hψ_pos : tsupport (ψ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    {x : SpacetimeDim d}
    (hx : x ∈ tsupport (ψ : SpacetimeDim d → ℂ) + tsupport (h : SpacetimeDim d → ℂ)) :
    0 < x 0 := by
  rcases hx with ⟨u, hu, v, hv, rfl⟩
  exact add_pos (hψ_pos hu) (hh_pos hv)

private theorem negative_tsupport_prod_sum_offDiagonal_local
    (φ ψ h : SchwartzSpacetime d)
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (hψ_pos : tsupport (ψ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport (φ : SpacetimeDim d → ℂ) ×ˢ
        (tsupport (ψ : SpacetimeDim d → ℂ) + tsupport (h : SpacetimeDim d → ℂ)) ⊆
      {p : SpacetimeDim d × SpacetimeDim d | p.1 ≠ p.2} := by
  intro p hp
  rcases hp with ⟨hp1, hp2⟩
  have hp1_neg : p.1 0 < 0 := hφ_neg hp1
  have hp2_pos : 0 < p.2 0 :=
    sum_positiveTime_tsupport_pos_local ψ h hψ_pos hh_pos hp2
  intro hdiag
  have : p.1 0 = p.2 0 := by simpa [hdiag]
  linarith

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

/-- Fubini bridge for the finite-measure Laplace-Fourier kernel: pairing the
kernel against a positive-time compact Schwartz test is the same as integrating
the pointwise Fourier-Laplace transform of that test against the measure. This
is the exact first rewrite needed in theorem 3. -/
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
            rw [laplaceFourierKernel, ← MeasureTheory.integral_mul_const]
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

/-- Spectral bridge, step B: the two-point Schwinger functional is represented
by a continuous kernel away from the coincidence diagonal.

This is the genuine local regularity input needed for the `k = 2` base step.
The relevant support sets coming from the shrinking center cutoffs stay inside
compact subsets of the off-diagonal region, not inside a fixed half-space of the
form `{x₀₀ < 0 < x₁₀}`. -/
private theorem schwinger_twoPoint_kernel_repr_offDiagonal
    (OS : OsterwalderSchraderAxioms d) :
    ∃ (K : SpacetimeDim d → SpacetimeDim d → ℂ),
      ContinuousOn (fun p : SpacetimeDim d × SpacetimeDim d => K p.1 p.2)
        {p | p.1 ≠ p.2} ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f =
          ∫ p : SpacetimeDim d × SpacetimeDim d,
            K p.1 p.2 *
              f.1 (Fin.cons p.1 (Fin.cons p.2 Fin.elim0)) ∂ (volume.prod volume)) := by
  sorry

private theorem schwinger_twoPointProductLift_eq_kernelIntegral_local
    (OS : OsterwalderSchraderAxioms d)
    (K : SpacetimeDim d → SpacetimeDim d → ℂ)
    (hK_repr : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f =
        ∫ p : SpacetimeDim d × SpacetimeDim d,
          K p.1 p.2 *
            f.1 (Fin.cons p.1 (Fin.cons p.2 Fin.elim0)) ∂ (volume.prod volume))
    (φ : SchwartzSpacetime d)
    (hφ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (gpt : positiveTimeCompactSupportSubmodule d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
      (twoPointProductLift φ (gpt : SchwartzSpacetime d))) =
      ∫ p : SpacetimeDim d × SpacetimeDim d,
        K p.1 p.2 * φ p.1 * (gpt : SchwartzSpacetime d) p.2 ∂ (volume.prod volume) := by
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence
        (twoPointProductLift φ (gpt : SchwartzSpacetime d)) :=
    twoPointProductLift_vanishes_of_orderedPositiveTime_local
      φ (gpt : SchwartzSpacetime d) hφ_pos gpt.property.1
  have hcoe :
      (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ (gpt : SchwartzSpacetime d))).1 =
        twoPointProductLift φ (gpt : SchwartzSpacetime d) :=
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes (f := twoPointProductLift φ (gpt : SchwartzSpacetime d))
      hvanish
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ (gpt : SchwartzSpacetime d))) =
      ∫ p : SpacetimeDim d × SpacetimeDim d,
        K p.1 p.2 *
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ (gpt : SchwartzSpacetime d))).1
            (Fin.cons p.1 (Fin.cons p.2 Fin.elim0)) ∂ (volume.prod volume) := by
          exact hK_repr _
    _ =
      ∫ p : SpacetimeDim d × SpacetimeDim d,
        K p.1 p.2 *
          (twoPointProductLift φ (gpt : SchwartzSpacetime d))
            (Fin.cons p.1 (Fin.cons p.2 Fin.elim0)) ∂ (volume.prod volume) := by
          congr 1
          ext p
          rw [hcoe]
    _ =
      ∫ p : SpacetimeDim d × SpacetimeDim d,
        K p.1 p.2 * φ p.1 * (gpt : SchwartzSpacetime d) p.2 ∂ (volume.prod volume) := by
          congr 1
          ext p
          simp [twoPointProductLift_apply, mul_assoc]

/-- Spectral bridge, step B: the semigroup-group matrix-element integral
attached to the one-point vector generated by `φ` is exactly the two-point
Schwinger value of the corresponding convolution-form product-shell test.

The hard analytic content is the disjoint-time kernel representation above; the
remaining proof here is the Fubini/convolution transport step built on top of
that kernel formula. -/
private theorem kernel_integral_translatedProductShell_eq_convolution
    (OS : OsterwalderSchraderAxioms d)
    (K : SpacetimeDim d → SpacetimeDim d → ℂ)
    (hK_cont : ContinuousOn (fun p : SpacetimeDim d × SpacetimeDim d => K p.1 p.2)
      {p | p.1 ≠ p.2})
    (hK_repr : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f =
        ∫ p : SpacetimeDim d × SpacetimeDim d,
          K p.1 p.2 *
            f.1 (Fin.cons p.1 (Fin.cons p.2 Fin.elim0)) ∂ (volume.prod volume))
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (hφ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hpt ψpt : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ
            (SCV.translateSchwartz (-ξ) (ψpt : SchwartzSpacetime d)))) *
          ((hpt : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          (((positiveTimeCompactSupportConvolution hpt ψpt :
              positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) := by
  let convh : positiveTimeCompactSupportSubmodule d :=
    positiveTimeCompactSupportConvolution hpt ψpt
  have htranslate :
      ∀ ξ : SpacetimeDim d, 0 < ξ 0 →
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ
            (SCV.translateSchwartz (-ξ) (ψpt : SchwartzSpacetime d)))) =
          ∫ p : SpacetimeDim d × SpacetimeDim d,
            K p.1 p.2 * φ p.1 *
              (SCV.translateSchwartz (-ξ) (ψpt : SchwartzSpacetime d)) p.2
              ∂ (volume.prod volume) := by
    intro ξ hξ
    simpa [translatedPositiveTimeCompactSupport_local] using
      (schwinger_twoPointProductLift_eq_kernelIntegral_local
        (d := d) OS K hK_repr φ hφ_pos
        (translatedPositiveTimeCompactSupport_local
          (ψpt : SchwartzSpacetime d) ψpt.property.1 ψpt.property.2 ξ hξ))
  have hconv_repr :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          ((convh : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))) =
        ∫ p : SpacetimeDim d × SpacetimeDim d,
          K p.1 p.2 * φ p.1 *
            ((convh : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) p.2
            ∂ (volume.prod volume) := by
    exact schwinger_twoPointProductLift_eq_kernelIntegral_local
      (d := d) OS K hK_repr φ hφ_pos convh
  have hscalar :
      ∫ ξ : SpacetimeDim d,
          (∫ p : SpacetimeDim d × SpacetimeDim d,
            K p.1 p.2 * φ p.1 *
              (SCV.translateSchwartz (-ξ) (ψpt : SchwartzSpacetime d)) p.2
              ∂ (volume.prod volume)) *
            ((hpt : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ =
        ∫ p : SpacetimeDim d × SpacetimeDim d,
          K p.1 p.2 * φ p.1 *
            ((convh : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) p.2
            ∂ (volume.prod volume) := by
    let ψ : SchwartzSpacetime d := (ψpt : positiveTimeCompactSupportSubmodule d)
    let h : SchwartzSpacetime d := (hpt : positiveTimeCompactSupportSubmodule d)
    let F : SpacetimeDim d → (SpacetimeDim d × SpacetimeDim d) → ℂ := fun ξ p =>
      (K p.1 p.2 * φ p.1) *
        ((SCV.translateSchwartz (-ξ) ψ) p.2 * h ξ)
    let Tpair : Set (SpacetimeDim d × SpacetimeDim d) :=
      tsupport (φ : SpacetimeDim d → ℂ) ×ˢ
        (tsupport (ψ : SpacetimeDim d → ℂ) + tsupport (h : SpacetimeDim d → ℂ))
    let T : Set (SpacetimeDim d × (SpacetimeDim d × SpacetimeDim d)) :=
      tsupport (h : SpacetimeDim d → ℂ) ×ˢ Tpair
    have hsum_compact :
        IsCompact (tsupport (ψ : SpacetimeDim d → ℂ) + tsupport (h : SpacetimeDim d → ℂ)) := by
      exact ψpt.property.2.isCompact.add hpt.property.2.isCompact
    have hTpair_compact : IsCompact Tpair := by
      exact hφ_compact.prod hsum_compact
    have hT_compact : IsCompact T := by
      exact hpt.property.2.prod hTpair_compact
    have hT_offdiag : Tpair ⊆ {p : SpacetimeDim d × SpacetimeDim d | p.1 ≠ p.2} :=
      negative_tsupport_prod_sum_offDiagonal_local φ ψ h
        hφ_neg ψpt.property.1 hpt.property.1
    have hF_support :
        Function.support F.uncurry ⊆ T := by
      intro z hz
      rcases z with ⟨ξ, p⟩
      rcases p with ⟨x₀, x₁⟩
      have hξ : h ξ ≠ 0 := by
        intro hξ0
        apply hz
        simp [F, h, hξ0]
      have hx₀ : φ x₀ ≠ 0 := by
        intro hx₀0
        apply hz
        simp [F, hx₀0]
      have hx₁ : (SCV.translateSchwartz (-ξ) ψ) x₁ ≠ 0 := by
        intro hx₁0
        have hx₁0' : ψ (x₁ + -ξ) = 0 := by
          simpa [SCV.translateSchwartz_apply] using hx₁0
        apply hz
        have : F ξ (x₀, x₁) = 0 := by
          simp [F, SCV.translateSchwartz_apply, hx₁0']
        simpa [Function.uncurry, F] using this
      have hξ_mem : ξ ∈ tsupport (h : SpacetimeDim d → ℂ) := by
        exact subset_tsupport _ (by simpa [Function.mem_support] using hξ)
      have hx₀_mem : x₀ ∈ tsupport (φ : SpacetimeDim d → ℂ) := by
        exact subset_tsupport _ (by simpa [Function.mem_support] using hx₀)
      have hx₁_mem :
          x₁ ∈ tsupport (ψ : SpacetimeDim d → ℂ) + tsupport (h : SpacetimeDim d → ℂ) :=
        translate_nonzero_mem_tsupport_add_local ψ h hξ hx₁
      exact ⟨hξ_mem, hx₀_mem, hx₁_mem⟩
    have hK_on :
        ContinuousOn
          (fun z : SpacetimeDim d × (SpacetimeDim d × SpacetimeDim d) =>
            K z.2.1 z.2.2) T := by
      refine hK_cont.comp continuous_snd.continuousOn ?_
      intro z hz
      exact hT_offdiag hz.2
    have hφ_on :
        ContinuousOn
          (fun z : SpacetimeDim d × (SpacetimeDim d × SpacetimeDim d) => φ z.2.1) T :=
      ((SchwartzMap.continuous φ).comp
        ((continuous_fst.comp continuous_snd) :
          Continuous fun z : SpacetimeDim d × (SpacetimeDim d × SpacetimeDim d) => z.2.1)).continuousOn
    have hψ_on :
        ContinuousOn
          (fun z : SpacetimeDim d × (SpacetimeDim d × SpacetimeDim d) =>
            (SCV.translateSchwartz (-z.1) ψ) z.2.2) T := by
      have hcont :
          Continuous
            (fun z : SpacetimeDim d × (SpacetimeDim d × SpacetimeDim d) =>
              ψ (z.2.2 - z.1)) := by
        exact (SchwartzMap.continuous ψ).comp
          (((continuous_snd.comp continuous_snd) :
              Continuous fun z : SpacetimeDim d × (SpacetimeDim d × SpacetimeDim d) => z.2.2).sub
            continuous_fst)
      simpa [ψ, SCV.translateSchwartz_apply, sub_eq_add_neg] using hcont.continuousOn
    have hh_on :
        ContinuousOn
          (fun z : SpacetimeDim d × (SpacetimeDim d × SpacetimeDim d) => h z.1) T :=
      ((SchwartzMap.continuous h).comp continuous_fst).continuousOn
    have hF_on : ContinuousOn F.uncurry T := by
      simpa [F, Function.uncurry, mul_assoc] using
        hK_on.mul (hφ_on.mul (hψ_on.mul hh_on))
    have hF_int :
        Integrable F.uncurry (volume.prod (volume.prod volume)) := by
      apply (integrableOn_iff_integrable_of_support_subset hF_support).mp
      exact hF_on.integrableOn_compact hT_compact
    calc
      ∫ ξ : SpacetimeDim d,
          (∫ p : SpacetimeDim d × SpacetimeDim d,
            K p.1 p.2 * φ p.1 *
              (SCV.translateSchwartz (-ξ) (ψpt : SchwartzSpacetime d)) p.2
              ∂ (volume.prod volume)) *
            ((hpt : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ
          =
        ∫ ξ : SpacetimeDim d,
          ∫ p : SpacetimeDim d × SpacetimeDim d, F ξ p ∂ (volume.prod volume) := by
            congr 1
            ext ξ
            rw [← MeasureTheory.integral_mul_const]
            congr 1
            ext p
            simp [F, ψ, h, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∫ p : SpacetimeDim d × SpacetimeDim d,
          ∫ ξ : SpacetimeDim d, F ξ p ∂ volume ∂ (volume.prod volume) := by
            exact MeasureTheory.integral_integral_swap hF_int
      _ =
        ∫ p : SpacetimeDim d × SpacetimeDim d,
          K p.1 p.2 * φ p.1 *
            ((convh : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) p.2
            ∂ (volume.prod volume) := by
            refine integral_congr_ae ?_
            filter_upwards with p
            rw [show (∫ ξ : SpacetimeDim d, F ξ p ∂ volume) =
                ∫ ξ : SpacetimeDim d,
                  (K p.1 p.2 * φ p.1) *
                    (((SCV.translateSchwartz (-ξ) ψ) p.2) * h ξ) ∂ volume by
                  rfl]
            rw [MeasureTheory.integral_const_mul]
            rw [positiveTimeCompactSupportConvolution_apply_eq_integral_translate hpt ψpt p.2]
            congr 1
            apply MeasureTheory.integral_congr_ae
            filter_upwards with ξ
            ring
  calc
    ∫ ξ : SpacetimeDim d,
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ
            (SCV.translateSchwartz (-ξ) (ψpt : SchwartzSpacetime d)))) *
          ((hpt : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ =
      ∫ ξ : SpacetimeDim d,
        (∫ p : SpacetimeDim d × SpacetimeDim d,
          K p.1 p.2 * φ p.1 *
            (SCV.translateSchwartz (-ξ) (ψpt : SchwartzSpacetime d)) p.2
            ∂ (volume.prod volume)) *
          ((hpt : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            by_cases hξ : 0 < ξ 0
            · rw [htranslate ξ hξ]
            · have hξ_not_mem :
                  ξ ∉ tsupport (((hpt : positiveTimeCompactSupportSubmodule d) :
                    SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
                intro hmem
                exact hξ (hpt.property.1 hmem)
              have hξ_zero :
                  ((hpt : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ = 0 :=
                image_eq_zero_of_notMem_tsupport hξ_not_mem
              simp [hξ_zero]
    _ =
      ∫ p : SpacetimeDim d × SpacetimeDim d,
        K p.1 p.2 * φ p.1 *
          ((convh : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) p.2
          ∂ (volume.prod volume) := hscalar
    _ =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          (((positiveTimeCompactSupportConvolution hpt ψpt :
              positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) := by
            simpa [convh] using hconv_repr.symm

/-- Spectral bridge, step B: the semigroup-group matrix-element integral
attached to the one-point vector generated by `φ` is exactly the two-point
Schwinger value of the corresponding convolution-form product-shell test.

The hard analytic content is the disjoint-time kernel representation above; the
remaining proof here is the Fubini/convolution transport step built on top of
that kernel formula. -/
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

private theorem semigroup_integral_eq_schwinger_productShell
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (hφ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    let ψ := reflectedSchwartzSpacetime φ
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos φ hφ_neg
    let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport φ hφ_compact
    let ψpt : positiveTimeCompactSupportSubmodule d := ⟨ψ, ⟨hψ_pos_time, hψ_compact⟩⟩
    let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
    ∫ ξ : SpacetimeDim d,
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              hφ_pos⟧) : OSHilbertSpace OS))
          (ξ 0) (fun i => ξ (Fin.succ i)) * h ξ =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          (((positiveTimeCompactSupportConvolution hpt ψpt :
              positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) := by
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
  let ψpt : positiveTimeCompactSupportSubmodule d := ⟨ψ, ⟨hψ_pos_time, hψ_compact⟩⟩
  let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
  calc
    ∫ ξ : SpacetimeDim d,
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d φ : SchwartzNPoint d 1))
              hφ_pos⟧) : OSHilbertSpace OS))
          (ξ 0) (fun i => ξ (Fin.succ i)) * h ξ =
      ∫ ξ : SpacetimeDim d,
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ))) * h ξ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with ξ
            by_cases hξ : 0 < ξ 0
            · rw [show
                    osSemigroupGroupMatrixElement (d := d) OS lgc
                        (((show OSPreHilbertSpace OS from
                          ⟦PositiveTimeBorchersSequence.single 1
                            (SchwartzNPoint.osConj (d := d) (n := 1)
                              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
                            hφ_pos⟧) : OSHilbertSpace OS))
                        (ξ 0) (fun i => ξ (Fin.succ i)) =
                      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                        (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ))) by
                    simpa [ψ, hψ_pos_time, hψ_pos, hψ_compact] using
                      (osSemigroupGroupMatrixElement_eq_translatedProductShell_of_pos
                        (d := d) OS lgc φ hφ_real hφ_compact hφ_neg hφ_pos ξ hξ)]
            · have hξ_not_mem : ξ ∉ tsupport (h : SpacetimeDim d → ℂ) := by
                intro hmem
                exact hξ (hh_pos hmem)
              have hξ_zero : h ξ = 0 :=
                image_eq_zero_of_notMem_tsupport hξ_not_mem
              simp [hξ_zero]
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ
            (((positiveTimeCompactSupportConvolution hpt ψpt :
                positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) := by
          rcases schwinger_twoPoint_kernel_repr_offDiagonal (d := d) OS with
            ⟨K, hK_cont, hK_repr⟩
          simpa [ψ, hψ_pos_time, hψ_compact, ψpt, hpt] using
            (kernel_integral_translatedProductShell_eq_convolution
              (d := d) OS K hK_cont hK_repr φ hφ_compact hφ_neg hφ_pos hpt ψpt)

/-- Spectral bridge, step C: once the center factor has unit integral, the
convolution-form product-shell pairing differs from the canonical difference
lift by a single explicit error term. -/
private theorem productShell_eq_differenceLift_plus_error
    (OS : OsterwalderSchraderAxioms d)
    (φ χ₀ h : SchwartzSpacetime d)
    (hφ_int : ∫ u : SpacetimeDim d, φ u = 1)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (hχ₀_int : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    let ψ := reflectedSchwartzSpacetime φ
    let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos φ hφ_neg
    let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport φ hφ_compact
    let ψpt : positiveTimeCompactSupportSubmodule d := ⟨ψ, ⟨hψ_pos_time, hψ_compact⟩⟩
    let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
      (twoPointProductLift φ
        (((positiveTimeCompactSupportConvolution hpt ψpt :
            positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) +
        (OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ
              (((positiveTimeCompactSupportConvolution hpt ψpt :
                  positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) -
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift φ h))) := by
  let ψ := reflectedSchwartzSpacetime φ
  let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos φ hφ_neg
  let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport φ hφ_compact
  let ψpt : positiveTimeCompactSupportSubmodule d := ⟨ψ, ⟨hψ_pos_time, hψ_compact⟩⟩
  let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
  let convh : SchwartzSpacetime d :=
    ((positiveTimeCompactSupportConvolution hpt ψpt : positiveTimeCompactSupportSubmodule d) :
      SchwartzSpacetime d)
  have h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
    intro hz
    have hz' := hh_pos hz
    simpa using hz'
  have hcenter :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift φ h)) =
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
    rw [OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue
      (d := d) OS h h0 χ₀ hχ₀_int φ]
    simp [hφ_int]
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ convh)) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift φ h)) +
        (OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ convh)) -
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift φ h))) := by
            ring
    _ =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) +
        (OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ convh)) -
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift φ h))) := by
            rw [hcenter]

/-- Spectral bridge, step D: after replacing the Bochner measures by the scalar
spectral measure and removing the `|φ̂_n|²` weight by dominated convergence, the
approximate-identity kernel pairings converge to the canonical Schwinger
difference functional. This is the key smearing-removal step from OS II. -/
private theorem schwinger_convolution_product_error_tendsto_zero
    (OS : OsterwalderSchraderAxioms d)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ ((φ_seq n) x).re)
    (hφ_real : ∀ n x, ((φ_seq n) x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (hφ_support : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    Tendsto
      (fun n =>
        let ψ := reflectedSchwartzSpacetime (φ_seq n)
        let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (φ_seq n) (hφ_neg n)
        let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport (φ_seq n) (hφ_compact n)
        let ψpt : positiveTimeCompactSupportSubmodule d := ⟨ψ, ⟨hψ_pos_time, hψ_compact⟩⟩
        let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift (φ_seq n)
            (((positiveTimeCompactSupportConvolution hpt ψpt :
                positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) -
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift (φ_seq n) h)))
      atTop (nhds 0) := by
  sorry

/-- Spectral bridge, step D: once the center cutoff `φ_n` has unit mass and
shrinking negative-time support, the residual difference between the raw
product shell and the canonical difference lift vanishes. -/
private theorem schwinger_product_difference_error_tendsto_zero
    (OS : OsterwalderSchraderAxioms d)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ ((φ_seq n) x).re)
    (hφ_real : ∀ n x, ((φ_seq n) x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (hφ_support : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    Tendsto
      (fun n =>
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift (φ_seq n) h)) -
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift (φ_seq n) h)))
      atTop (nhds 0) := by
  sorry

/-- Spectral bridge, step D: after replacing the Bochner measures by the scalar
spectral measure and removing the `|φ̂_n|²` weight by dominated convergence, the
approximate-identity kernel pairings converge to the canonical Schwinger
difference functional. This is the key smearing-removal step from OS II. -/
private theorem schwinger_error_tendsto_zero
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_support : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (hφ_onePoint_pos : ∀ n,
      tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (χ₀ : SchwartzSpacetime d) (hχ₀_int : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ))
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (hμ_fin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hμ_supp : ∀ n, (μ_seq n) (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ n t a, 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
            (hφ_onePoint_pos n)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p, Complex.exp (-(↑(t * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i, p.2 i * a i)) ∂(μ_seq n)) :
    Tendsto (fun n => ∫ ξ : SpacetimeDim d,
        laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ)
      atTop
      (nhds
        (OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)))) := by
  have h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
    intro hz
    have hz' := hh_pos hz
    simpa using hz'
  have hB :
      ∀ n,
        let ψ := reflectedSchwartzSpacetime (φ_seq n)
        let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (φ_seq n) (hφ_neg n)
        let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport (φ_seq n) (hφ_compact n)
        let ψpt : positiveTimeCompactSupportSubmodule d := ⟨ψ, ⟨hψ_pos_time, hψ_compact⟩⟩
        let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
        ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift (φ_seq n)
              (((positiveTimeCompactSupportConvolution hpt ψpt :
                  positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) := by
    intro n
    calc
      ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ =
          ∫ ξ : SpacetimeDim d,
            osSemigroupGroupMatrixElement (d := d) OS lgc
              (((show OSPreHilbertSpace OS from
                ⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                  (hφ_onePoint_pos n)⟧) : OSHilbertSpace OS))
              (ξ 0) (fun i => ξ (Fin.succ i)) * h ξ := by
                exact bochner_kernel_integral_eq_semigroup_integral
                  (d := d) OS lgc
                  (((show OSPreHilbertSpace OS from
                    ⟦PositiveTimeBorchersSequence.single 1
                      (SchwartzNPoint.osConj (d := d) (n := 1)
                        (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                      (hφ_onePoint_pos n)⟧) : OSHilbertSpace OS))
                  (μ_seq n) (hμ_supp n) (hμ_repr n) h hh_pos hh_compact
      _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift (φ_seq n)
              (((positiveTimeCompactSupportConvolution
                  (⟨h, ⟨hh_pos, hh_compact⟩⟩ : positiveTimeCompactSupportSubmodule d)
                  (⟨reflectedSchwartzSpacetime (φ_seq n),
                    ⟨reflectedSchwartzSpacetime_tsupport_pos (φ_seq n) (hφ_neg n),
                      reflectedSchwartzSpacetime_hasCompactSupport (φ_seq n) (hφ_compact n)⟩⟩ :
                    positiveTimeCompactSupportSubmodule d) :
                  positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) := by
            simpa using
              (semigroup_integral_eq_schwinger_productShell
                (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n)
                (hφ_onePoint_pos n) h hh_pos hh_compact)
  have hcenter :
      ∀ n,
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift (φ_seq n) h)) =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
    intro n
    rw [OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue
      (d := d) OS h h0 χ₀ hχ₀_int (φ_seq n)]
    simp [hφ_int n]
  have hconv :
      Tendsto
        (fun n =>
          let ψ := reflectedSchwartzSpacetime (φ_seq n)
          let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (φ_seq n) (hφ_neg n)
          let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport (φ_seq n) (hφ_compact n)
          let ψpt : positiveTimeCompactSupportSubmodule d := ⟨ψ, ⟨hψ_pos_time, hψ_compact⟩⟩
          let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift (φ_seq n)
              (((positiveTimeCompactSupportConvolution hpt ψpt :
                  positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) -
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift (φ_seq n) h)))
        atTop (nhds 0) :=
    schwinger_convolution_product_error_tendsto_zero
      (d := d) OS φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_support
      h hh_pos hh_compact
  have hprod_diff :
      Tendsto
        (fun n =>
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift (φ_seq n) h)) -
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift (φ_seq n) h)))
        atTop (nhds 0) :=
    schwinger_product_difference_error_tendsto_zero
      (d := d) OS φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_support
      h hh_pos hh_compact
  have hsum :
      Tendsto
        (fun n =>
          (let ψ := reflectedSchwartzSpacetime (φ_seq n)
           let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (φ_seq n) (hφ_neg n)
           let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport (φ_seq n) (hφ_compact n)
           let ψpt : positiveTimeCompactSupportSubmodule d := ⟨ψ, ⟨hψ_pos_time, hψ_compact⟩⟩
           let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
           OS.S 2 (ZeroDiagonalSchwartz.ofClassical
             (twoPointProductLift (φ_seq n)
               (((positiveTimeCompactSupportConvolution hpt ψpt :
                   positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) -
           OS.S 2 (ZeroDiagonalSchwartz.ofClassical
             (twoPointProductLift (φ_seq n) h))) +
          (OS.S 2 (ZeroDiagonalSchwartz.ofClassical
             (twoPointProductLift (φ_seq n) h)) -
           OS.S 2 (ZeroDiagonalSchwartz.ofClassical
             (twoPointDifferenceLift (φ_seq n) h))))
        atTop (nhds (0 + 0)) := by
    exact hconv.add hprod_diff
  have hsum' :
      Tendsto
        (fun n =>
          let ψ := reflectedSchwartzSpacetime (φ_seq n)
          let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (φ_seq n) (hφ_neg n)
          let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport (φ_seq n) (hφ_compact n)
          let ψpt : positiveTimeCompactSupportSubmodule d := ⟨ψ, ⟨hψ_pos_time, hψ_compact⟩⟩
          let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift (φ_seq n)
              (((positiveTimeCompactSupportConvolution hpt ψpt :
                  positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) -
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift (φ_seq n) h)))
        atTop (nhds 0) := by
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hsum
  have hdiff :
      Tendsto
        (fun n =>
          (∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ) -
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)))
        atTop (nhds 0) := by
    have hEqFun :
        (fun n =>
          (∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ) -
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h))) =
        (fun n =>
          let ψ := reflectedSchwartzSpacetime (φ_seq n)
          let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (φ_seq n) (hφ_neg n)
          let hψ_compact := reflectedSchwartzSpacetime_hasCompactSupport (φ_seq n) (hφ_compact n)
          let ψpt : positiveTimeCompactSupportSubmodule d := ⟨ψ, ⟨hψ_pos_time, hψ_compact⟩⟩
          let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift (φ_seq n)
              (((positiveTimeCompactSupportConvolution hpt ψpt :
                  positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)))) -
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift (φ_seq n) h))) := by
      funext n
      let pconv :=
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift (φ_seq n)
            (((positiveTimeCompactSupportConvolution
                (⟨h, ⟨hh_pos, hh_compact⟩⟩ :
                  positiveTimeCompactSupportSubmodule d)
                (⟨reflectedSchwartzSpacetime (φ_seq n),
                  ⟨reflectedSchwartzSpacetime_tsupport_pos (φ_seq n) (hφ_neg n),
                    reflectedSchwartzSpacetime_hasCompactSupport (φ_seq n) (hφ_compact n)⟩⟩ :
                  positiveTimeCompactSupportSubmodule d) :
                positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))))
      let target :=
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h))
      have hb :
          (∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ) = pconv := by
        dsimp [pconv]
        simpa using hB n
      have hc :
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift (φ_seq n) h)) =
            target := by
        dsimp [target]
        exact hcenter n
      calc
        (∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ) - target =
            pconv - target := by
              exact congrArg (fun z : ℂ => z - target) hb
        _ = pconv -
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift (φ_seq n) h)) := by
              exact congrArg (fun z : ℂ => pconv - z) hc.symm
    simpa [hEqFun] using hsum'
  have hshift :
      Tendsto
        (fun n =>
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) +
            ((∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ) -
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h))))
        atTop
        (nhds
          (OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) + 0)) :=
    tendsto_const_nhds.add hdiff
  have hEqFinal :
      (fun n =>
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) +
          ((∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ) -
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)))) =
      (fun n => ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) (μ_seq n) ξ * h ξ) := by
    funext n
    ring
  have hEqLim :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) + 0 =
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
    ring
  simpa [hEqFinal, hEqLim] using hshift

/-- Smearing removal for the approximate-identity/Bochner route: the limit
Laplace-Fourier kernel reproduces the normalized-center two-point Schwinger
difference shell on positive-time compact-support tests. -/
theorem limit_bochner_kernel_reproduces_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀_int : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      ContinuousOn (laplaceFourierKernel (d := d) μ) {ξ : SpacetimeDim d | 0 < ξ 0} ∧
      (∃ C : ℝ, ∀ ξ, 0 < ξ 0 → ‖laplaceFourierKernel (d := d) μ ξ‖ ≤ C) ∧
      AEStronglyMeasurable (laplaceFourierKernel (d := d) μ) volume ∧
      ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * h ξ =
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
  rcases exists_negative_approx_identity_sequence (d := d) with
    ⟨φ_seq, hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_neg, hφ_support⟩
  have hφ_onePoint_pos : ∀ n,
      tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    intro n
    exact osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n)
  have hbochner :
      ∀ n, ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
        IsFiniteMeasure μ ∧
        μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
        ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
          osSemigroupGroupMatrixElement (d := d) OS lgc
            (((show OSPreHilbertSpace OS from
              ⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (hφ_onePoint_pos n)⟧) : OSHilbertSpace OS)) t a =
            ∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ := by
    intro n
    simpa [hφ_onePoint_pos] using
      (exists_bochner_measure_for_approx_identity (d := d) OS lgc
        (φ_seq n) (hφ_compact n) (hφ_neg n))
  choose μ_seq hμ_fin hμ_supp hμ_repr using hbochner
  sorry

/-- The limit Laplace-Fourier kernel extends holomorphically in the time
variable on the right half-plane. -/
theorem limit_kernel_time_holomorphic
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0) :
    ∃ (K_ext : ℂ → (Fin d → ℝ) → ℂ),
      (∀ ξ_s : Fin d → ℝ,
        DifferentiableOn ℂ (fun z => K_ext z ξ_s) {z : ℂ | 0 < z.re}) ∧
      (∀ (t : ℝ) (ξ_s : Fin d → ℝ), 0 < t →
        K_ext (t : ℂ) ξ_s =
          laplaceFourierKernel (d := d) μ (Fin.cons t (fun i => ξ_s i))) := by
  let phase : (Fin d → ℝ) → (ℝ × (Fin d → ℝ)) → ℂ := fun ξ_s p =>
    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ_s i))
  let F : (Fin d → ℝ) → ℂ → (ℝ × (Fin d → ℝ)) → ℂ := fun ξ_s z p =>
    Complex.exp (-(z * ↑p.1)) * phase ξ_s p
  let F' : (Fin d → ℝ) → ℂ → (ℝ × (Fin d → ℝ)) → ℂ := fun ξ_s z p =>
    F ξ_s z p * -(↑p.1 : ℂ)
  refine ⟨fun z ξ_s => ∫ p, F ξ_s z p ∂μ, ?_, ?_⟩
  · intro ξ_s z₀ hz₀
    simp only [Set.mem_setOf_eq] at hz₀
    apply DifferentiableAt.differentiableWithinAt
    set δ : ℝ := z₀.re / 2 with hδ_def
    have hδ : 0 < δ := by
      linarith
    set c : ℝ := z₀.re - δ with hc_def
    have hc : 0 < c := by
      linarith
    have hsum_cont : Continuous (fun p : ℝ × (Fin d → ℝ) => ∑ i : Fin d, p.2 i * ξ_s i) := by
      refine continuous_finset_sum _ fun i _hi => ?_
      exact (((continuous_apply i).comp continuous_snd) : Continuous fun p : ℝ × (Fin d → ℝ) => p.2 i).mul
        (continuous_const : Continuous fun _ : ℝ × (Fin d → ℝ) => ξ_s i)
    have hphase_cont : Continuous (phase ξ_s) := by
      show Continuous (fun p : ℝ × (Fin d → ℝ) =>
        Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ_s i)))
      exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp hsum_cont))
    have hF_cont : ∀ z : ℂ, Continuous (F ξ_s z) := by
      intro z
      show Continuous (fun p : ℝ × (Fin d → ℝ) =>
        Complex.exp (-(z * ↑p.1)) * phase ξ_s p)
      exact
        (Complex.continuous_exp.comp
          ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).neg)).mul
          hphase_cont
    have hF'_cont : ∀ z : ℂ, Continuous (F' ξ_s z) := by
      intro z
      show Continuous (fun p : ℝ × (Fin d → ℝ) => F ξ_s z p * -(↑p.1 : ℂ))
      exact (hF_cont z).mul ((Complex.continuous_ofReal.comp continuous_fst).neg)
    have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F ξ_s z) μ := by
      exact Filter.Eventually.of_forall fun z => (hF_cont z).aestronglyMeasurable
    have hF_int : Integrable (F ξ_s z₀) μ := by
      apply Integrable.mono' (integrable_const (1 : ℝ))
      · exact
          (hF_cont z₀).aestronglyMeasurable
      · rw [ae_iff]
        apply measure_mono_null _ hsupp
        intro p hp
        refine Set.mem_prod.mpr ?_
        constructor
        · by_contra hp_nonneg
          apply hp
          have hp_nonneg' : 0 ≤ p.1 := le_of_not_gt hp_nonneg
          have hphase : (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ_s i) : ℂ).re = 0 := by
            simp
          have hre : (-(z₀ * ↑p.1) : ℂ).re = -z₀.re * p.1 := by
            simp [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
          rw [show ‖F ξ_s z₀ p‖ =
              ‖Complex.exp (-(z₀ * ↑p.1)) * phase ξ_s p‖ by rfl]
          rw [Complex.norm_mul, Complex.norm_exp, Complex.norm_exp, hphase,
            Real.exp_zero, mul_one, hre, Real.exp_le_one_iff]
          nlinarith [hz₀, hp_nonneg']
        · exact Set.mem_univ _
    have hF'_meas : AEStronglyMeasurable (F' ξ_s z₀) μ := by
      exact (hF'_cont z₀).aestronglyMeasurable
    have h_bound :
        ∀ᵐ p ∂μ, ∀ z ∈ Metric.ball z₀ δ, ‖F' ξ_s z p‖ ≤ Real.exp (-1) / c := by
      rw [ae_iff]
      apply measure_mono_null _ hsupp
      intro p hp
      refine Set.mem_prod.mpr ?_
      constructor
      · by_contra hp_nonneg
        apply hp
        intro z hzball
        have hp_nonneg' : 0 ≤ p.1 := by
          exact le_of_not_gt hp_nonneg
        have hzre : z₀.re - δ ≤ z.re := by
          rw [Metric.mem_ball, dist_eq_norm] at hzball
          have habs : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
            simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - z₀)
          linarith [neg_abs_le (z.re - z₀.re)]
        have hphase : (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ_s i) : ℂ).re = 0 := by
          simp
        have hre : (-(z * ↑p.1) : ℂ).re = -z.re * p.1 := by
          simp [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
        rw [show ‖F' ξ_s z p‖ =
            ‖Complex.exp (-(z * ↑p.1)) * phase ξ_s p * -(↑p.1 : ℂ)‖ by rfl]
        rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_exp, Complex.norm_exp,
          hphase, Real.exp_zero, mul_one, hre]
        have hnormp : ‖-(↑p.1 : ℂ)‖ = p.1 := by
          have hcast : (-(↑p.1 : ℂ)) = (((-p.1 : ℝ)) : ℂ) := by simp
          rw [hcast, Complex.norm_real, Real.norm_of_nonpos]
          · ring
          · linarith
        rw [hnormp]
        have hmain : Real.exp (-z.re * p.1) * p.1 ≤ Real.exp (-1) / c := by
          have h1 : p.1 * Real.exp (-z.re * p.1) ≤ p.1 * Real.exp (-(z₀.re - δ) * p.1) := by
            apply mul_le_mul_of_nonneg_left ?_ hp_nonneg'
            apply Real.exp_le_exp.mpr
            nlinarith
          simpa [mul_comm] using h1.trans (mul_exp_neg_bound_local c p.1 hc)
        exact hmain
      · exact Set.mem_univ _
    have h_bound_int : Integrable (fun _ : ℝ × (Fin d → ℝ) => (Real.exp (-1) / c : ℝ)) μ := by
      simpa using (integrable_const (Real.exp (-1) / c : ℝ))
    have h_diff : ∀ᵐ p ∂μ, ∀ z ∈ Metric.ball z₀ δ, HasDerivAt (F ξ_s · p) (F' ξ_s z p) z := by
      exact Filter.Eventually.of_forall fun p => by
        intro z hz
        have hlin : HasDerivAt (fun z : ℂ => -(z * ↑p.1)) (-(↑p.1 : ℂ)) z := by
          simpa [neg_mul] using (((hasDerivAt_id z).mul_const (↑p.1 : ℂ)).neg)
        simpa [F, F', phase, mul_assoc, mul_left_comm, mul_comm] using
          (hlin.cexp.mul_const (phase ξ_s p))
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (s := Metric.ball z₀ δ) (bound := fun _ => (Real.exp (-1) / c : ℝ))
      (F := F ξ_s) (F' := F' ξ_s) (Metric.ball_mem_nhds z₀ hδ)
      hF_meas hF_int hF'_meas h_bound h_bound_int h_diff).2.differentiableAt
  · intro t ξ_s ht
    simp [laplaceFourierKernel, F, phase, Fin.cons_zero, Fin.cons_succ]

/-- The `k = 2` time-parametric base step obtained by assembling the previous
sub-lemmas. -/
theorem schwinger_continuation_base_step_timeParametric_k2
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))) * (f.1 x)) := by
  sorry

end
