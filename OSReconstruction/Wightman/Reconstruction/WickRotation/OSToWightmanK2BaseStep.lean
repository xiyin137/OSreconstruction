/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.SCV.SemigroupGroupBochner

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

variable {d : ℕ} [NeZero d]

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

/-- Apply semigroup-group Bochner to the OS matrix element attached to a
single normalized positive-time one-point vector. -/
theorem exists_bochner_measure_for_approx_identity
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1) :
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
  sorry

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
