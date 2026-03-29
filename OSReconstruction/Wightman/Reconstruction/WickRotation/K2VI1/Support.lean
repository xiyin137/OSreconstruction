/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2BaseStep
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum

/-!
# OS to Wightman `k = 2` VI.1 Support Layer

This file contains the proved support infrastructure for the honest OS II Section VI.1 `k = 2` route: negative approximate identities, weight packages, supported-symbol representation lemmas, descended-center approximate-identity estimates, and the proved wrappers that reduce the live frontier to the remaining open theorems.

The small frontier file `K2VI1/Frontier.lean` should remain the only place where the surviving VI.1 `sorry`s live.
-/

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal
open BigOperators Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

variable {d : ℕ} [NeZero d]

theorem exists_k2_VI1_regularization_input_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (φ_seq : ℕ → SchwartzSpacetime d)
      (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
      (hφ_real : ∀ n x, (φ_seq n x).im = 0)
      (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
      (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
      (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
        {x : SpacetimeDim d | x 0 < 0})
      (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
      (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ))),
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
                (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧) :
              OSHilbertSpace OS))
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
  obtain ⟨φ_seq, hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_neg, hφ_ball⟩ :=
    exists_negative_approx_identity_sequence (d := d)
  obtain ⟨μ_seq, hμfin, hhol, hsupp, hμrepr, hkernel, hpair⟩ :=
    exists_k2_positiveTime_shell_package_of_negativeApproxIdentity_local
      (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
  refine ⟨φ_seq, hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_neg, hφ_ball,
    μ_seq, hμfin, hhol, hsupp, hμrepr, hkernel, hpair⟩

/-- The negative one-point probe sequence attached to `φ_seq` already carries a
Bochner measure sequence on the semigroup-group side, extracted uniformly from
the compact-support extension theorem in `OSToWightmanSpatialMomentum`. This is
the reusable measure-construction layer that later diagonal spectral packages
should build on, rather than choosing fresh `μ_n` ad hoc inside VI.1 proofs. -/
theorem exists_measure_sequence_for_negative_probe_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ))),
      (∀ n, IsFiniteMeasure (μ_seq n)) ∧
      (∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
      (∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
        osSemigroupGroupMatrixElement (d := d) OS lgc
          (((show OSPreHilbertSpace OS from
            ⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧) :
              OSHilbertSpace OS))
          t a =
            ∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n)) := by
  classical
  have h_exists :
      ∀ n,
        ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
          IsFiniteMeasure μ ∧
          μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
          ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
            osSemigroupGroupMatrixElement (d := d) OS lgc
              (((show OSPreHilbertSpace OS from
                ⟦PositiveTimeBorchersSequence.single 1
                  (SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                  (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                    (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧) :
                  OSHilbertSpace OS))
              t a =
                ∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(t * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ := by
    intro n
    have hprobe_compact :
        HasCompactSupport
          (((SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
            NPointDomain d 1 → ℂ)) := by
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
      have hreflect_space :
          HasCompactSupport (fun y : SpacetimeDim d => φ_seq n (timeReflection d y)) := by
        simpa using (hφ_compact n).comp_homeomorph θSpace
      have hreflect_fin1 :
          HasCompactSupport (fun y : NPointDomain d 1 => φ_seq n (timeReflection d (y 0))) := by
        simpa [onePointToFin1CLM] using
          (hreflect_space.comp_homeomorph
            ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))
      simpa [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply] using
        (hreflect_fin1.comp_left (show starRingEnd ℂ (0 : ℂ) = 0 by simp))
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
        (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
          (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))
    have hF_compact :
        ∀ m,
          HasCompactSupport ((((F : BorchersSequence d).funcs m : SchwartzNPoint d m) :
            NPointDomain d m → ℂ)) := by
      intro m
      by_cases hm : m = 1
      · subst hm
        simpa [F, PositiveTimeBorchersSequence.single_toBorchersSequence] using
          hprobe_compact
      · have hzero :
          ((((F : BorchersSequence d).funcs m : SchwartzNPoint d m) :
            NPointDomain d m → ℂ)) = 0 := by
          simp [F, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hm]
        rw [hzero]
        simpa using
          (HasCompactSupport.zero : HasCompactSupport (0 : NPointDomain d m → ℂ))
    obtain ⟨μ, hμfin, hsupp, hrepr⟩ :=
      exists_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
        (d := d) OS lgc F hF_compact
    refine ⟨μ, hμfin, hsupp, ?_⟩
    intro t a ht
    simpa [ht] using hrepr t a (le_of_lt ht)
  choose μ_seq hμfin hsupp hμrepr using h_exists
  exact ⟨μ_seq, hμfin, hsupp, hμrepr⟩

theorem onePointToFin1_tsupport_orderedPositiveTime_vi1_local
    (f : SchwartzSpacetime d)
    (hf : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport (((onePointToFin1CLM d f : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro v hv i
  refine ⟨?_, fun j hij => absurd hij (by omega)⟩
  rw [Fin.eq_zero i]
  have hv0 : v 0 ∈ tsupport (f : SpacetimeDim d → ℂ) := by
    have :=
      tsupport_comp_subset_preimage (f : SpacetimeDim d → ℂ)
        (f := fun w : Fin 1 → SpacetimeDim d => w 0) (continuous_apply 0) hv
    exact this
  exact Set.mem_setOf.mp (hf hv0)

/-- Specialization of the generic polarized compact-support semigroup-group
Bochner theorem to positive-time one-point test vectors. This packages the four
diagonal measures attached to `h ± g` and `h ± i g` directly on the one-point
OS surface that later VI.1 arguments use. -/
theorem exists_polarized_measure_positiveTimeOnePoint_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (h g : positiveTimeCompactSupportSubmodule d) :
    let Fh : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single 1
        (onePointToFin1CLM d (h : SchwartzSpacetime d) : SchwartzNPoint d 1)
        (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
          (h : SchwartzSpacetime d) h.property.1)
    let Fg : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single 1
        (onePointToFin1CLM d (g : SchwartzSpacetime d) : SchwartzNPoint d 1)
        (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
          (g : SchwartzSpacetime d) g.property.1)
    let xh : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Fh⟧)) : OSHilbertSpace OS))
    let xg : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Fg⟧)) : OSHilbertSpace OS))
    ∃ (ν₁ : Measure (ℝ × (Fin d → ℝ))) (_hν₁fin : IsFiniteMeasure ν₁)
      (ν₂ : Measure (ℝ × (Fin d → ℝ))) (_hν₂fin : IsFiniteMeasure ν₂)
      (ν₃ : Measure (ℝ × (Fin d → ℝ))) (_hν₃fin : IsFiniteMeasure ν₃)
      (ν₄ : Measure (ℝ × (Fin d → ℝ))) (_hν₄fin : IsFiniteMeasure ν₄)
      (_hsupp₁ : ν₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₂ : ν₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₃ : ν₃ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₄ : ν₄ (Set.prod (Set.Iio 0) Set.univ) = 0),
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        (if ht : 0 < t then
          @inner ℂ (OSHilbertSpace OS) _ xh
            ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS a) xg))
        else
          @inner ℂ (OSHilbertSpace OS) _ xh
            ((osSpatialTranslateHilbert (d := d) OS a) xg)) =
          (1 / 4 : ℂ) *
            ((∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₁) -
              (∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₂) -
              Complex.I *
                (∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(t * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₃) +
              Complex.I *
                (∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(t * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₄)) := by
  let Fh : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d (h : SchwartzSpacetime d) : SchwartzNPoint d 1)
      (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
        (h : SchwartzSpacetime d) h.property.1)
  let Fg : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d (g : SchwartzSpacetime d) : SchwartzNPoint d 1)
      (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
        (g : SchwartzSpacetime d) g.property.1)
  let xh : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Fh⟧)) : OSHilbertSpace OS))
  let xg : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Fg⟧)) : OSHilbertSpace OS))
  have hFh_compact :
      ∀ n,
        HasCompactSupport ((((Fh : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    by_cases hn : n = 1
    · subst hn
      have hh_compact_one :
          HasCompactSupport (((onePointToFin1CLM d (h : SchwartzSpacetime d) : SchwartzNPoint d 1) :
            NPointDomain d 1 → ℂ)) := by
        simpa [onePointToFin1CLM] using
          (h.property.2.comp_homeomorph
            ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))
      simpa [Fh, PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single] using hh_compact_one
    · simp [Fh, PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single, hn, HasCompactSupport.zero]
  have hFg_compact :
      ∀ n,
        HasCompactSupport ((((Fg : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    by_cases hn : n = 1
    · subst hn
      have hg_compact_one :
          HasCompactSupport (((onePointToFin1CLM d (g : SchwartzSpacetime d) : SchwartzNPoint d 1) :
            NPointDomain d 1 → ℂ)) := by
        simpa [onePointToFin1CLM] using
          (g.property.2.comp_homeomorph
            ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))
      simpa [Fg, PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single] using hg_compact_one
    · simp [Fg, PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single, hn, HasCompactSupport.zero]
  simpa [Fh, Fg, xh, xg] using
    (exists_polarized_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
      (d := d) OS lgc Fh Fg hFh_compact hFg_compact)

/-- The reflected companions of the shrinking negative approximate-identity
sequence already produce honest real spectral weights in `[0,1]` converging to
`1` pointwise on the nonnegative-energy spectral side. This is the exact input
needed if the remaining VI.1 limit is completed by dominated convergence over a
fixed spectral measure, rather than by a direct shell estimate. -/
theorem reflected_negativeApproxIdentity_fourierLaplace_weight_package_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (E : ℝ) (hE : 0 ≤ E) (p : Fin d → ℝ) :
    let ψ_seq : ℕ → SchwartzSpacetime d := fun n => reflectedSchwartzSpacetime (φ_seq n)
    let w : ℕ → ℝ := fun n =>
      ‖∫ x : SpacetimeDim d,
          ψ_seq n x * Complex.exp (-(↑(x 0 * E) : ℂ) +
            Complex.I * ↑(∑ i : Fin d, p i * x (Fin.succ i)))‖ ^ 2
    (∀ n, 0 ≤ w n) ∧
      (∀ n, w n ≤ 1) ∧
      Filter.Tendsto w Filter.atTop (𝓝 1) := by
  dsimp
  have hψ_nonneg : ∀ n x, 0 ≤ (reflectedSchwartzSpacetime (φ_seq n) x).re := by
    intro n x
    simpa [reflectedSchwartzSpacetime, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      hφ_nonneg n (timeReflection d x)
  have hψ_real : ∀ n x, (reflectedSchwartzSpacetime (φ_seq n) x).im = 0 := by
    intro n x
    simpa [reflectedSchwartzSpacetime, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      hφ_real n (timeReflection d x)
  have hψ_int : ∀ n, ∫ x : SpacetimeDim d, reflectedSchwartzSpacetime (φ_seq n) x = 1 := by
    intro n
    rw [reflectedSchwartzSpacetime_integral_eq_local]
    exact hφ_int n
  have hψ_pos : ∀ n,
      tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ) ⊆ {x | 0 ≤ x 0} := by
    intro n x hx
    have hxpos : 0 < x 0 := reflectedSchwartzSpacetime_tsupport_pos
      (d := d) (φ_seq n) (hφ_neg n) hx
    exact le_of_lt hxpos
  have hψ_ball : ∀ n,
      tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := by
    intro n
    exact reflectedSchwartzSpacetime_tsupport_ball (d := d) (φ_seq n) (hφ_ball n)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    positivity
  · intro n
    have hbound :=
      fourierLaplace_nonneg_normalized_le_one
        (d := d) (reflectedSchwartzSpacetime (φ_seq n))
        (hψ_nonneg n) (hψ_real n) (hψ_int n) (hψ_pos n) E hE p
    have hsq :
        ‖∫ x : SpacetimeDim d,
            reflectedSchwartzSpacetime (φ_seq n) x * Complex.exp (-(↑(x 0 * E) : ℂ) +
              Complex.I * ↑(∑ i : Fin d, p i * x (Fin.succ i)))‖ ^ 2 ≤ 1 := by
      have hnn :
          0 ≤ ‖∫ x : SpacetimeDim d,
              reflectedSchwartzSpacetime (φ_seq n) x * Complex.exp (-(↑(x 0 * E) : ℂ) +
                Complex.I * ↑(∑ i : Fin d, p i * x (Fin.succ i)))‖ := norm_nonneg _
      nlinarith
    simpa using hsq
  · have hFL :
        Filter.Tendsto
          (fun n =>
            ∫ x : SpacetimeDim d,
              reflectedSchwartzSpacetime (φ_seq n) x * Complex.exp (-(↑(x 0 * E) : ℂ) +
                Complex.I * ↑(∑ i : Fin d, p i * x (Fin.succ i))))
          Filter.atTop (𝓝 (1 : ℂ)) :=
        fourierLaplace_approx_identity_tendsto_one
          (d := d) (fun n => reflectedSchwartzSpacetime (φ_seq n))
          hψ_nonneg hψ_real hψ_int hψ_ball E p
    have hcont :
        Continuous fun z : ℂ => ‖z‖ ^ 2 := by
      continuity
    simpa using hcont.tendsto 1 |>.comp hFL

/-- Explicit VI.1 spectral weight attached to the reflected negative
approximate-identity probe `φ_seq n`. This is the concrete weight expected to
appear in the missing fixed-measure representation theorem. -/
def reflected_negativeApproxIdentity_weight_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  ‖∫ x : SpacetimeDim d,
      reflectedSchwartzSpacetime (φ_seq n) x *
        Complex.exp (-(↑(x 0 * p.1) : ℂ) +
          Complex.I * ↑(∑ i : Fin d, p.2 i * x (Fin.succ i)))‖ ^ 2

/-- Explicit integral form of the local reflected-probe weight. This keeps the
weight on the same Fourier-Laplace surface used later, without needing any of
the downstream symbol abbreviations yet. -/
theorem reflected_negativeApproxIdentity_weight_local_eq_norm_sq_laplaceSymbol_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    reflected_negativeApproxIdentity_weight_local (d := d) φ_seq n =
      fun p =>
        ‖∫ x : SpacetimeDim d,
            reflectedSchwartzSpacetime (φ_seq n) x *
              Complex.exp (-(↑(x 0 * p.1) : ℂ) +
                Complex.I * ↑(∑ i : Fin d, p.2 i * x (Fin.succ i)))‖ ^ 2 := by
  funext p
  simp [reflected_negativeApproxIdentity_weight_local]

/-- For each fixed reflected probe, the corresponding VI.1 weight is a continuous
function of the spectral variable. This gives the measurability needed to use the
explicit OS weight sequence in the remaining spectral-limit step. -/
theorem continuous_reflected_negativeApproxIdentity_weight_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ)) :
    Continuous (reflected_negativeApproxIdentity_weight_local (d := d) φ_seq n) := by
  let ψ : SchwartzSpacetime d := reflectedSchwartzSpacetime (φ_seq n)
  let K : Set (SpacetimeDim d) := tsupport (ψ : SpacetimeDim d → ℂ)
  have hψ_compact : HasCompactSupport (ψ : SpacetimeDim d → ℂ) :=
    reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n) (hφ_compact n)
  have hK : IsCompact K := hψ_compact.isCompact
  let F : (ℝ × (Fin d → ℝ)) → SpacetimeDim d → ℂ := fun p x =>
    ψ x * Complex.exp (-(↑(x 0 * p.1) : ℂ) +
      Complex.I * ↑(∑ i : Fin d, p.2 i * x (Fin.succ i)))
  have hF_cont : Continuous F.uncurry := by
    change Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
      ψ z.2 * Complex.exp (-(↑(z.2 0 * z.1.1) : ℂ) +
        Complex.I * ↑(∑ i : Fin d, z.1.2 i * z.2 (Fin.succ i))))
    have hsum :
        Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
          ∑ i : Fin d, z.1.2 i * z.2 (Fin.succ i)) := by
      refine continuous_finset_sum _ fun i _ => ?_
      exact
        (((continuous_apply i).comp (continuous_snd.comp continuous_fst)) : Continuous
          fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d => z.1.2 i).mul
          (((continuous_apply (Fin.succ i)).comp continuous_snd) : Continuous
            fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d => z.2 (Fin.succ i))
    have h1 :
        Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
          Complex.exp (-(↑(z.2 0 * z.1.1) : ℂ))) := by
      have hbase :
          Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
            -((z.2 0) * z.1.1)) := by
        exact
          ((((continuous_apply (0 : Fin (d + 1))).comp continuous_snd) : Continuous
              fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d => z.2 0).mul
            (((continuous_fst.comp continuous_fst) : Continuous
              fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d => z.1.1))).neg
      have h1' :
          Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
            Complex.exp (↑(-((z.2 0) * z.1.1)) : ℂ)) := by
        exact Complex.continuous_exp.comp (Complex.continuous_ofReal.comp hbase)
      simpa using h1'
    have h2 :
        Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
          Complex.exp (Complex.I * ↑(∑ i : Fin d, z.1.2 i * z.2 (Fin.succ i)))) := by
      exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp hsum))
    have h12 :
        Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
          Complex.exp (-(↑(z.2 0 * z.1.1) : ℂ) +
            Complex.I * ↑(∑ i : Fin d, z.1.2 i * z.2 (Fin.succ i)))) := by
      simpa [Complex.exp_add, add_comm, add_left_comm, add_assoc, mul_assoc] using h1.mul h2
    have h3 :
        Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d => ψ z.2) := by
      exact (SchwartzMap.continuous ψ).comp continuous_snd
    simpa [F, Function.uncurry, mul_assoc] using h3.mul h12
  have hF_zero :
      ∀ p x, p ∈ (Set.univ : Set (ℝ × (Fin d → ℝ))) → x ∉ K → F p x = 0 := by
    intro p x _ hx
    have hx0 : ψ x = 0 := by
      exact image_eq_zero_of_notMem_tsupport hx
    simp [F, K, hx0]
  have hcont_int :
      ContinuousOn (fun p => ∫ x, F p x ∂volume) Set.univ := by
    simpa [K] using
      (continuousOn_integral_of_compact_support
        (μ := volume) (s := (Set.univ : Set (ℝ × (Fin d → ℝ)))) (k := K)
        hK hF_cont.continuousOn hF_zero)
  have hcont_int' : Continuous (fun p => ∫ x, F p x ∂volume) := by
    simpa using hcont_int
  change Continuous (fun p => ‖∫ x, F p x ∂volume‖ ^ 2)
  exact (continuous_norm.comp hcont_int').pow 2

theorem measurable_reflected_negativeApproxIdentity_weight_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ)) :
    Measurable (reflected_negativeApproxIdentity_weight_local (d := d) φ_seq n) :=
  (continuous_reflected_negativeApproxIdentity_weight_local
    (d := d) φ_seq n hφ_compact).measurable

theorem measurable_reflected_negativeApproxIdentity_weight_nonnegSubtype_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ)) :
    Measurable (fun p : {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1} =>
      reflected_negativeApproxIdentity_weight_local (d := d) φ_seq n p.1) :=
  ((continuous_reflected_negativeApproxIdentity_weight_local
      (d := d) φ_seq n hφ_compact).comp continuous_subtype_val).measurable

/-- Globalized version of the explicit VI.1 reflected-probe weight. On the
negative-energy region we set the weight to `1`; this does not change any future
integrals against supported spectral measures but gives a global `[0,1]`-valued
approximate-identity sequence. -/
def reflected_negativeApproxIdentity_weight_global_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  if hp : 0 ≤ p.1 then
    reflected_negativeApproxIdentity_weight_local (d := d) φ_seq n p
  else
    1

/-- Package for the explicit global VI.1 reflected-probe weight sequence:
nonnegativity, the universal bound `≤ 1`, measurability, and pointwise
convergence to `1`. -/
theorem reflected_negativeApproxIdentity_weight_global_package_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ)) :
    (∀ n p, 0 ≤ reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p) ∧
      (∀ n p, reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p ≤ 1) ∧
      (∀ n, Measurable (reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n)) ∧
      (∀ p,
        Filter.Tendsto
          (fun n => reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p)
          Filter.atTop (𝓝 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n p
    by_cases hp : 0 ≤ p.1
    · simp [reflected_negativeApproxIdentity_weight_global_local, hp,
        reflected_negativeApproxIdentity_weight_local]
    · simp [reflected_negativeApproxIdentity_weight_global_local, hp]
  · intro n p
    by_cases hp : 0 ≤ p.1
    · have hpack :=
        reflected_negativeApproxIdentity_fourierLaplace_weight_package_local
          (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_neg hφ_ball p.1 hp p.2
      simpa [reflected_negativeApproxIdentity_weight_global_local, hp,
        reflected_negativeApproxIdentity_weight_local] using hpack.2.1 n
    · simp [reflected_negativeApproxIdentity_weight_global_local, hp]
  · intro n
    have hIci :
        MeasurableSet {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1} := by
      exact measurable_fst measurableSet_Ici
    simpa [reflected_negativeApproxIdentity_weight_global_local] using
      (measurable_reflected_negativeApproxIdentity_weight_local
        (d := d) φ_seq n hφ_compact).piecewise hIci measurable_const
  · intro p
    by_cases hp : 0 ≤ p.1
    · have hpack :=
        reflected_negativeApproxIdentity_fourierLaplace_weight_package_local
          (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_neg hφ_ball p.1 hp p.2
      simpa [reflected_negativeApproxIdentity_weight_global_local, hp,
        reflected_negativeApproxIdentity_weight_local] using hpack.2.2
    · simpa [reflected_negativeApproxIdentity_weight_global_local, hp] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1))

/-- On the nonnegative-energy half-space, the globalized VI.1 weight is still
the same explicit norm-square Fourier-Laplace expression. -/
theorem reflected_negativeApproxIdentity_weight_global_eq_norm_sq_supportedSymbol_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (p : ℝ × (Fin d → ℝ))
    (hp : 0 ≤ p.1) :
    reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p =
      ‖∫ x : SpacetimeDim d,
          reflectedSchwartzSpacetime (φ_seq n) x *
            Complex.exp (-(↑(x 0 * p.1) : ℂ) +
              Complex.I * ↑(∑ i : Fin d, p.2 i * x (Fin.succ i)))‖ ^ 2 := by
  have hbase :=
    reflected_negativeApproxIdentity_weight_local_eq_norm_sq_laplaceSymbol_local
      (d := d) φ_seq n hφ_compact hφ_neg
  simp [reflected_negativeApproxIdentity_weight_global_local, hp]
  simpa using congrArg (fun f => f p) hbase

/-- Pointwise package for the explicit VI.1 reflected-probe weight sequence:
nonnegativity, the universal bound `≤ 1`, and convergence to `1` on the
nonnegative-energy spectral side. -/
theorem reflected_negativeApproxIdentity_weight_bounds_tendsto_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (p : ℝ × (Fin d → ℝ))
    (hp : 0 ≤ p.1) :
    (∀ n, 0 ≤ reflected_negativeApproxIdentity_weight_local (d := d) φ_seq n p) ∧
      (∀ n, reflected_negativeApproxIdentity_weight_local (d := d) φ_seq n p ≤ 1) ∧
      Filter.Tendsto
        (fun n => reflected_negativeApproxIdentity_weight_local (d := d) φ_seq n p)
        Filter.atTop (𝓝 1) := by
  simpa [reflected_negativeApproxIdentity_weight_local] using
    reflected_negativeApproxIdentity_fourierLaplace_weight_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_neg hφ_ball p.1 hp p.2

/-- The closed nonnegative-energy half-space used by the remaining VI.1 spectral
representation theorem. -/
private def nonnegEnergySet_local : Set (ℝ × (Fin d → ℝ)) :=
  {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1}

theorem measurableSet_nonnegEnergySet_local :
    MeasurableSet (nonnegEnergySet_local (d := d)) := by
  change MeasurableSet (((fun p : ℝ × (Fin d → ℝ) => p.1) ⁻¹' Set.Ici (0 : ℝ)))
  exact measurable_fst (measurableSet_Ici : MeasurableSet (Set.Ici (0 : ℝ)))

theorem ae_mem_nonnegEnergySet_of_measure_Iio_zero_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0) :
    ∀ᵐ p ∂μ, p ∈ nonnegEnergySet_local (d := d) := by
  rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
  suffices
      hsub :
        {x : ℝ × (Fin d → ℝ) | x ∉ nonnegEnergySet_local (d := d)} ⊆
          Set.prod (Set.Iio 0) Set.univ by
    exact le_antisymm (le_trans (μ.mono hsub) (le_of_eq hsupp)) (zero_le _)
  intro x hx
  rcases x with ⟨E, p⟩
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, nonnegEnergySet_local] at hx ⊢
  exact Set.mk_mem_prod (by simpa using hx) (Set.mem_univ _)

theorem restrict_nonnegEnergySet_eq_self_of_measure_Iio_zero_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0) :
    μ.restrict (nonnegEnergySet_local (d := d)) = μ := by
  exact Measure.restrict_eq_self_of_ae_mem
    (ae_mem_nonnegEnergySet_of_measure_Iio_zero_local (d := d) μ hsupp)

/-- The nonnegative-energy subtype measure associated to a measure supported on
`[0, ∞) × ℝ^d`. This is the natural carrier for the remaining VI.1 weighted
representation theorem. -/
private def nonnegEnergySubtypeMeasure_local
    (μ : Measure (ℝ × (Fin d → ℝ))) :
    Measure {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1} :=
  Measure.comap ((↑) : {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1} → ℝ × (Fin d → ℝ)) μ

theorem map_nonnegEnergySubtypeMeasure_eq_of_measure_Iio_zero_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0) :
    (nonnegEnergySubtypeMeasure_local (d := d) μ).map
        ((↑) : {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1} → ℝ × (Fin d → ℝ)) = μ := by
  calc
    (nonnegEnergySubtypeMeasure_local (d := d) μ).map
        ((↑) : {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1} → ℝ × (Fin d → ℝ))
        = μ.restrict (nonnegEnergySet_local (d := d)) := by
            simpa [nonnegEnergySubtypeMeasure_local] using
              (map_comap_subtype_coe
                (hs := measurableSet_nonnegEnergySet_local (d := d)) μ)
    _ = μ := restrict_nonnegEnergySet_eq_self_of_measure_Iio_zero_local (d := d) μ hsupp

theorem integral_nonnegEnergySubtypeMeasure_eq_of_measure_Iio_zero_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (f : (ℝ × (Fin d → ℝ)) → ℂ) :
    ∫ p : {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1}, f p.1 ∂(nonnegEnergySubtypeMeasure_local (d := d) μ) =
      ∫ p, f p ∂μ := by
  calc
    ∫ p : {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1}, f p.1 ∂(nonnegEnergySubtypeMeasure_local (d := d) μ)
        = ∫ p in nonnegEnergySet_local (d := d), f p ∂μ := by
            simpa [nonnegEnergySubtypeMeasure_local] using
              (MeasureTheory.integral_subtype_comap
                (μ := μ) (s := nonnegEnergySet_local (d := d)) (f := f)
                (measurableSet_nonnegEnergySet_local (d := d)))
    _ = ∫ p, f p ∂μ := by
          rw [restrict_nonnegEnergySet_eq_self_of_measure_Iio_zero_local (d := d) μ hsupp]

/-- Weighting a nonnegative-energy spectral measure by a real-valued density
preserves the same support condition. This is the exact candidate-measure
surface behind the remaining VI.1 weighted diagonal bridge. -/
theorem withDensity_measure_Iio_zero_of_measure_Iio_zero_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (w : (ℝ × (Fin d → ℝ)) → ℝ) :
    μ.withDensity (fun p => ENNReal.ofReal (w p)) (Set.prod (Set.Iio 0) Set.univ) = 0 := by
  let s : Set (ℝ × (Fin d → ℝ)) := Set.prod (Set.Iio 0) Set.univ
  have hs : MeasurableSet s := measurableSet_Iio.prod MeasurableSet.univ
  rw [withDensity_apply _ hs, Measure.restrict_zero_set hsupp, lintegral_zero_measure]

/-- Integral rewrite against the weighted candidate measure produced by
`withDensity`. This packages the exact conversion needed once a fixed diagonal
measure `ν` is identified and one wants to regard the explicit VI.1 weight as
part of the measure rather than part of the integrand. -/
theorem integral_eq_integral_withDensity_ofReal_weight_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (f : (ℝ × (Fin d → ℝ)) → ℂ)
    (w : (ℝ × (Fin d → ℝ)) → ℝ)
    (hw_meas : Measurable w)
    (hw_nonneg : ∀ p, 0 ≤ w p) :
    ∫ p, f p ∂(μ.withDensity (fun p => ENNReal.ofReal (w p))) =
      ∫ p, f p * ↑(w p) ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul
      (μ := μ) (f := fun p => ENNReal.ofReal (w p))]
  · apply integral_congr_ae
    filter_upwards with p
    rw [ENNReal.toReal_ofReal (hw_nonneg p)]
    simp [smul_eq_mul, mul_comm]
  · exact ENNReal.measurable_ofReal.comp hw_meas
  · exact Filter.Eventually.of_forall fun p => by simp

/-- The explicit reflected VI.1 weight defines a bona fide weighted candidate
measure with the same nonnegative-energy support as the original one. This is
the exact fixed-measure candidate that would solve the remaining line-40 seam
once the semigroup-group uniqueness/identification step is available. -/
theorem withDensity_reflected_negativeApproxIdentity_weight_measure_Iio_zero_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (n : ℕ) :
    μ.withDensity
        (fun p =>
          ENNReal.ofReal
            (reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p))
          (Set.prod (Set.Iio 0) Set.univ) = 0 := by
  exact withDensity_measure_Iio_zero_of_measure_Iio_zero_local (d := d) μ hsupp _

/-- Specialized integral rewrite for the explicit reflected VI.1 weight. This
repackages the weighted supported-symbol integrals on the surviving frontier as
ordinary integrals against the corresponding weighted candidate measures. -/
theorem integral_eq_integral_withDensity_reflected_negativeApproxIdentity_weight_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (f : (ℝ × (Fin d → ℝ)) → ℂ)
    (n : ℕ) :
    ∫ p,
        f p
        ∂(μ.withDensity
            (fun p =>
              ENNReal.ofReal
                (reflected_negativeApproxIdentity_weight_global_local
                  (d := d) φ_seq n p))) =
      ∫ p,
        f p *
          ↑(reflected_negativeApproxIdentity_weight_global_local
              (d := d) φ_seq n p) ∂μ := by
  obtain ⟨hw_nonneg, -, hw_meas, -⟩ :=
    reflected_negativeApproxIdentity_weight_global_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_neg hφ_ball hφ_compact
  exact integral_eq_integral_withDensity_ofReal_weight_local
    (d := d) μ f
    (reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n)
    (hw_meas n) (hw_nonneg n)

/-- If a supported finite measure has the same Laplace-Fourier transform as the
explicit reflected-weighted candidate measure, then the two measures coincide.

This packages the new SCV uniqueness input on the exact VI.1 weighted surface:
once one proves transform equality against the explicit reflected weight, the
common-measure identification step is finished. -/
theorem measure_eq_withDensity_reflected_negativeApproxIdentity_weight_of_laplaceFourier_eq_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (μ ν : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsuppμ : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hsuppν : ν (Set.prod (Set.Iio 0) Set.univ) = 0)
    (n : ℕ)
    (heq : ∀ (t : ℝ), 0 < t → ∀ (a : Fin d → ℝ),
      ∫ p : ℝ × (Fin d → ℝ),
        Complex.exp (-(↑(t * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ =
      ∫ p : ℝ × (Fin d → ℝ),
        (Complex.exp (-(↑(t * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))) *
            ↑(reflected_negativeApproxIdentity_weight_global_local
              (d := d) φ_seq n p) ∂ν) :
    μ =
      ν.withDensity
        (fun p =>
          ENNReal.ofReal
            (reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p)) := by
  obtain ⟨hw_nonneg, hw_le, _, _⟩ :=
    reflected_negativeApproxIdentity_weight_global_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_neg hφ_ball hφ_compact
  let νw : Measure (ℝ × (Fin d → ℝ)) :=
    ν.withDensity
      (fun p =>
        ENNReal.ofReal
          (reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p))
  have hνw_fin : νw Set.univ < ⊤ := by
    dsimp [νw]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc
      ∫⁻ a, ENNReal.ofReal
          (reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n a) ∂ν
          ≤ ∫⁻ _a, (1 : ENNReal) ∂ν := by
              refine lintegral_mono ?_
              intro a
              simpa using ENNReal.ofReal_le_ofReal (hw_le n a)
      _ = ν Set.univ := by simp
      _ < ⊤ := measure_lt_top ν Set.univ
  letI : IsFiniteMeasure νw := ⟨by
    simpa [νw] using hνw_fin⟩
  have hsuppνw :
      νw (Set.prod (Set.Iio 0) Set.univ) = 0 := by
    dsimp [νw]
    exact withDensity_reflected_negativeApproxIdentity_weight_measure_Iio_zero_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_neg hφ_ball hφ_compact ν hsuppν n
  exact SCV.laplaceFourier_measure_unique μ νw hsuppμ hsuppνw
    (fun t ht a => by
      dsimp [νw]
      rw [integral_eq_integral_withDensity_reflected_negativeApproxIdentity_weight_local
        (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_neg hφ_ball hφ_compact ν
        (fun p : ℝ × (Fin d → ℝ) =>
          Complex.exp (-(↑(t * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))) n]
      simpa [mul_assoc] using heq t ht a)

/-- Dominated-convergence wrapper for fixed finite spectral measures weighted by
approximate-identity factors in `[0,1]`. This is the exact scalar measure-limit
step one needs once the remaining VI.1 argument is reduced to a fixed spectral
measure with probe-dependent weights. -/
theorem weighted_measure_tendsto_of_approx_identity_bdd_measurable_local
    {α : Type*} [MeasurableSpace α]
    (ρ : Measure α)
    [IsFiniteMeasure ρ]
    (w_seq : ℕ → α → ℝ)
    (hw_le : ∀ n p, w_seq n p ≤ 1)
    (hw_nonneg : ∀ n p, 0 ≤ w_seq n p)
    (hw_meas : ∀ n, Measurable (w_seq n))
    (hw_tendsto : ∀ p, Filter.Tendsto (fun n => w_seq n p) Filter.atTop (𝓝 1))
    (f : α → ℂ)
    (hf_meas : AEStronglyMeasurable f ρ)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hf_bound : ∀ᵐ p ∂ρ, ‖f p‖ ≤ C) :
    Filter.Tendsto
      (fun n => ∫ p, f p * ↑(w_seq n p) ∂ρ)
      Filter.atTop
      (𝓝 (∫ p, f p ∂ρ)) := by
  rw [show (fun p => f p) = (fun p => f p * (1 : ℂ)) from by
    ext p
    simp]
  apply MeasureTheory.tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun n =>
      hf_meas.mul ((measurable_ofReal.comp (hw_meas n)).aestronglyMeasurable)
  · refine ⟨C, Filter.Eventually.of_forall ?_⟩
    intro n
    filter_upwards [hf_bound] with p hp
    simp only [norm_mul, Complex.norm_real]
    calc
      ‖f p‖ * ‖w_seq n p‖
          ≤ C * ‖w_seq n p‖ := by
            gcongr
      _ ≤ C * 1 := by
            gcongr
            rw [Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [hw_nonneg n p], hw_le n p⟩
      _ = C := by simp
  · exact Filter.Eventually.of_forall fun p => by
      have hw_c :
          Filter.Tendsto (fun n => (↑(w_seq n p) : ℂ)) Filter.atTop (𝓝 (↑(1 : ℝ))) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp (hw_tendsto p)
      have hmul :
          Filter.Tendsto
            (fun n => f p * (↑(w_seq n p) : ℂ))
            Filter.atTop
            (𝓝 (f p * ↑(1 : ℝ))) :=
        Filter.Tendsto.const_mul (f p) hw_c
      simpa using hmul

/-- On a finite control measure, a bounded measurable complex symbol remains
integrable after multiplication by any measurable real weight taking values in
`[0,1]`. This is the basic weighted-integrability input needed for the future
Radon-Nikodym control-measure factorization in the first VI.1 blocker. -/
theorem integrable_bdd_measurable_mul_weight_of_le_one_local
    {α : Type*} [MeasurableSpace α]
    (ρ : Measure α)
    [IsFiniteMeasure ρ]
    (f : α → ℂ)
    (hf_meas : AEStronglyMeasurable f ρ)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hf_bound : ∀ᵐ p ∂ρ, ‖f p‖ ≤ C)
    (w : α → ℝ)
    (hw_meas : Measurable w)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (hw_le : ∀ p, w p ≤ 1) :
    Integrable (fun p => f p * ↑(w p)) ρ := by
  refine Integrable.mono' (integrable_const C) ?_ ?_
  · exact hf_meas.mul ((Complex.measurable_ofReal.comp hw_meas).aestronglyMeasurable)
  · filter_upwards [hf_bound] with p hp
    simp only [norm_mul, Complex.norm_real]
    calc
      ‖f p‖ * ‖w p‖
          ≤ C * ‖w p‖ := by
            gcongr
      _ ≤ C * 1 := by
            gcongr
            rw [Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [hw_nonneg p], hw_le p⟩
      _ = C := by simp

/-- Dominated-convergence wrapper for fixed finite spectral measures weighted by
approximate-identity factors in `[0,1]`. This bounded-continuous specialization
is the form used on the current VI.1 route. -/
theorem weighted_measure_tendsto_of_approx_identity_local
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (ρ : Measure α)
    [IsFiniteMeasure ρ]
    (w_seq : ℕ → α → ℝ)
    (hw_le : ∀ n p, w_seq n p ≤ 1)
    (hw_nonneg : ∀ n p, 0 ≤ w_seq n p)
    (hw_meas : ∀ n, Measurable (w_seq n))
    (hw_tendsto : ∀ p, Filter.Tendsto (fun n => w_seq n p) Filter.atTop (𝓝 1)) :
    ∀ f : BoundedContinuousFunction α ℂ,
      Filter.Tendsto
        (fun n => ∫ p, f p * ↑(w_seq n p) ∂ρ)
        Filter.atTop
        (𝓝 (∫ p, f p ∂ρ)) := by
  intro f
  exact weighted_measure_tendsto_of_approx_identity_bdd_measurable_local
    (ρ := ρ) (w_seq := w_seq) hw_le hw_nonneg hw_meas hw_tendsto
    (fun p => f p) f.continuous.aestronglyMeasurable ‖f‖ (norm_nonneg _)
    (Filter.Eventually.of_forall fun p => f.norm_coe_le_norm p)

/-- Once a VI.1 pairing is rewritten against a fixed finite spectral measure
with approximate-identity weights, the convergence step is immediate from the
weighted dominated-convergence lemma above. This isolates the remaining first
`sorry` to producing the weighted spectral representation, not the scalar limit
argument itself. -/
theorem tendsto_of_weighted_measure_representation_local
    {α : Type*} [MeasurableSpace α]
    (ρ : Measure α)
    [IsFiniteMeasure ρ]
    (w_seq : ℕ → α → ℝ)
    (hw_le : ∀ n p, w_seq n p ≤ 1)
    (hw_nonneg : ∀ n p, 0 ≤ w_seq n p)
    (hw_meas : ∀ n, Measurable (w_seq n))
    (hw_tendsto : ∀ p, Filter.Tendsto (fun n => w_seq n p) Filter.atTop (𝓝 1))
    (f : α → ℂ)
    (hf_meas : AEStronglyMeasurable f ρ)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hf_bound : ∀ᵐ p ∂ρ, ‖f p‖ ≤ C)
    (L : ℂ)
    (hL : L = ∫ p, f p ∂ρ)
    (a_seq : ℕ → ℂ)
    (ha : ∀ n, a_seq n = ∫ p, f p * ↑(w_seq n p) ∂ρ) :
    Filter.Tendsto a_seq Filter.atTop (𝓝 L) := by
  have hmain :=
    weighted_measure_tendsto_of_approx_identity_bdd_measurable_local
      (ρ := ρ) (w_seq := w_seq) hw_le hw_nonneg hw_meas hw_tendsto
      f hf_meas C hC hf_bound
  have hL' : ∫ p, f p ∂ρ = L := hL.symm
  have hmain' :
      Filter.Tendsto
        (fun n => ∫ p, f p * ↑(w_seq n p) ∂ρ)
        Filter.atTop
        (𝓝 L) := by
    simpa [hL'] using hmain
  refine Filter.Tendsto.congr' ?_ hmain'
  filter_upwards with n
  exact (ha n).symm

/-- Schwinger-target specialization of the fixed-measure VI.1 convergence step.

Once the remaining probe-dependent spectral representation is supplied, this is
the exact theorem that closes the first active `k = 2` blocker. -/
theorem tendsto_to_schwingerDifferencePositive_of_weighted_measure_representation_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d)
    {α : Type*} [MeasurableSpace α]
    (ρ : Measure α)
    [IsFiniteMeasure ρ]
    (w_seq : ℕ → α → ℝ)
    (hw_le : ∀ n p, w_seq n p ≤ 1)
    (hw_nonneg : ∀ n p, 0 ≤ w_seq n p)
    (hw_meas : ∀ n, Measurable (w_seq n))
    (hw_tendsto : ∀ p, Filter.Tendsto (fun n => w_seq n p) Filter.atTop (𝓝 1))
    (f : α → ℂ)
    (hf_meas : AEStronglyMeasurable f ρ)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hf_bound : ∀ᵐ p ∂ρ, ‖f p‖ ≤ C)
    (a_seq : ℕ → ℂ)
    (ha : ∀ n, a_seq n = ∫ p, f p * ↑(w_seq n p) ∂ρ)
    (htarget :
      (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h = ∫ p, f p ∂ρ) :
    Filter.Tendsto a_seq Filter.atTop
      (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h)) := by
  exact tendsto_of_weighted_measure_representation_local
    (ρ := ρ) (w_seq := w_seq) hw_le hw_nonneg hw_meas hw_tendsto
    f hf_meas C hC hf_bound
    ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
      (d := d) OS χ₀) h) htarget a_seq ha

/-- The common finite control measure obtained by summing the four positive
diagonal spectral measures appearing in the off-diagonal polarization formula. -/
private def polarizationControlMeasure_local
    {α : Type*} [MeasurableSpace α]
    (ν₁ ν₂ ν₃ ν₄ : Measure α) : Measure α :=
  ν₁ + ν₂ + ν₃ + ν₄

/-- The explicit polarized Radon-Nikodym density attached to the four diagonal
measures under their common control measure. This is the measure-theoretic core
of the future off-diagonal VI.1 factorization. -/
private def polarizationControlDensity_local
    {α : Type*} [MeasurableSpace α]
    (ν₁ ν₂ ν₃ ν₄ : Measure α) (p : α) : ℂ :=
  let ρ := polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄
  (1 / 4 : ℂ) *
    (((ν₁.rnDeriv ρ p).toReal : ℂ) -
      ((ν₂.rnDeriv ρ p).toReal : ℂ) -
      Complex.I * ((ν₃.rnDeriv ρ p).toReal : ℂ) +
      Complex.I * ((ν₄.rnDeriv ρ p).toReal : ℂ))

theorem aestronglyMeasurable_polarizationControlDensity_local
    {α : Type*} [MeasurableSpace α]
    (ν₁ ν₂ ν₃ ν₄ : Measure α)
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [IsFiniteMeasure ν₃] [IsFiniteMeasure ν₄] :
    let ρ := polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄
    AEStronglyMeasurable (polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄) ρ := by
  let ρ := polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄
  letI : IsFiniteMeasure ρ := by
    dsimp [ρ, polarizationControlMeasure_local]
    infer_instance
  have hν₁ :
      AEStronglyMeasurable (fun p => ((ν₁.rnDeriv ρ p).toReal : ℂ)) ρ :=
    ((Complex.measurable_ofReal.comp
      (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv ν₁ ρ))).aestronglyMeasurable)
  have hν₂ :
      AEStronglyMeasurable (fun p => ((ν₂.rnDeriv ρ p).toReal : ℂ)) ρ :=
    ((Complex.measurable_ofReal.comp
      (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv ν₂ ρ))).aestronglyMeasurable)
  have hν₃ :
      AEStronglyMeasurable (fun p => ((ν₃.rnDeriv ρ p).toReal : ℂ)) ρ :=
    ((Complex.measurable_ofReal.comp
      (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv ν₃ ρ))).aestronglyMeasurable)
  have hν₄ :
      AEStronglyMeasurable (fun p => ((ν₄.rnDeriv ρ p).toReal : ℂ)) ρ :=
    ((Complex.measurable_ofReal.comp
      (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv ν₄ ρ))).aestronglyMeasurable)
  exact
    ((((hν₁.sub hν₂).sub (hν₃.const_mul Complex.I)).add
      (hν₄.const_mul Complex.I))).const_mul (1 / 4 : ℂ)

theorem ae_norm_polarizationControlDensity_le_one_local
    {α : Type*} [MeasurableSpace α]
    (ν₁ ν₂ ν₃ ν₄ : Measure α)
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [IsFiniteMeasure ν₃] [IsFiniteMeasure ν₄] :
    let ρ := polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄
    ∀ᵐ p ∂ρ, ‖polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p‖ ≤ 1 := by
  let ρ := polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄
  letI : IsFiniteMeasure ρ := by
    dsimp [ρ, polarizationControlMeasure_local]
    infer_instance
  have hle₁ : ν₁ ≤ ρ := by
    calc
      ν₁ ≤ ν₁ + ν₂ := le_add_of_nonneg_right bot_le
      _ ≤ (ν₁ + ν₂) + ν₃ := le_add_of_nonneg_right bot_le
      _ ≤ ((ν₁ + ν₂) + ν₃) + ν₄ := le_add_of_nonneg_right bot_le
      _ = ρ := by simp [ρ, polarizationControlMeasure_local, add_assoc]
  have hle₂ : ν₂ ≤ ρ := by
    calc
      ν₂ ≤ ν₁ + ν₂ := le_add_of_nonneg_left bot_le
      _ ≤ (ν₁ + ν₂) + ν₃ := le_add_of_nonneg_right bot_le
      _ ≤ ((ν₁ + ν₂) + ν₃) + ν₄ := le_add_of_nonneg_right bot_le
      _ = ρ := by simp [ρ, polarizationControlMeasure_local, add_assoc]
  have hle₃ : ν₃ ≤ ρ := by
    calc
      ν₃ ≤ ν₁ + ν₂ + ν₃ := by
        simpa [add_assoc, add_comm, add_left_comm] using
          (le_add_of_nonneg_left (show 0 ≤ (ν₁ + ν₂) from bot_le) : ν₃ ≤ (ν₁ + ν₂) + ν₃)
      _ ≤ ((ν₁ + ν₂) + ν₃) + ν₄ := le_add_of_nonneg_right bot_le
      _ = ρ := by simp [ρ, polarizationControlMeasure_local, add_assoc]
  have hle₄ : ν₄ ≤ ρ := by
    calc
      ν₄ ≤ ((ν₁ + ν₂) + ν₃) + ν₄ := by
        simpa [add_assoc, add_comm, add_left_comm] using
          (le_add_of_nonneg_left (show 0 ≤ (ν₁ + ν₂ + ν₃) from bot_le) :
            ν₄ ≤ (ν₁ + ν₂ + ν₃) + ν₄)
      _ = ρ := by simp [ρ, polarizationControlMeasure_local, add_assoc]
  have hν₁_le : ν₁.rnDeriv ρ ≤ᵐ[ρ] 1 := Measure.rnDeriv_le_one_of_le hle₁
  have hν₂_le : ν₂.rnDeriv ρ ≤ᵐ[ρ] 1 := Measure.rnDeriv_le_one_of_le hle₂
  have hν₃_le : ν₃.rnDeriv ρ ≤ᵐ[ρ] 1 := Measure.rnDeriv_le_one_of_le hle₃
  have hν₄_le : ν₄.rnDeriv ρ ≤ᵐ[ρ] 1 := Measure.rnDeriv_le_one_of_le hle₄
  have hν₁_norm : ∀ᵐ p ∂ρ, ‖((ν₁.rnDeriv ρ p).toReal : ℂ)‖ ≤ 1 := by
    filter_upwards [hν₁_le] with p hp
    have hto : (ν₁.rnDeriv ρ p).toReal ≤ 1 := by
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp)
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hto
  have hν₂_norm : ∀ᵐ p ∂ρ, ‖((ν₂.rnDeriv ρ p).toReal : ℂ)‖ ≤ 1 := by
    filter_upwards [hν₂_le] with p hp
    have hto : (ν₂.rnDeriv ρ p).toReal ≤ 1 := by
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp)
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hto
  have hν₃_norm : ∀ᵐ p ∂ρ, ‖((ν₃.rnDeriv ρ p).toReal : ℂ)‖ ≤ 1 := by
    filter_upwards [hν₃_le] with p hp
    have hto : (ν₃.rnDeriv ρ p).toReal ≤ 1 := by
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp)
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hto
  have hν₄_norm : ∀ᵐ p ∂ρ, ‖((ν₄.rnDeriv ρ p).toReal : ℂ)‖ ≤ 1 := by
    filter_upwards [hν₄_le] with p hp
    have hto : (ν₄.rnDeriv ρ p).toReal ≤ 1 := by
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp)
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hto
  filter_upwards [hν₁_norm, hν₂_norm, hν₃_norm, hν₄_norm] with p hp₁ hp₂ hp₃ hp₄
  have hsum :
      ‖((ν₁.rnDeriv ρ p).toReal : ℂ) -
          ((ν₂.rnDeriv ρ p).toReal : ℂ) -
          Complex.I * ((ν₃.rnDeriv ρ p).toReal : ℂ) +
          Complex.I * ((ν₄.rnDeriv ρ p).toReal : ℂ)‖ ≤ 4 := by
    calc
      ‖((ν₁.rnDeriv ρ p).toReal : ℂ) -
            ((ν₂.rnDeriv ρ p).toReal : ℂ) -
            Complex.I * ((ν₃.rnDeriv ρ p).toReal : ℂ) +
            Complex.I * ((ν₄.rnDeriv ρ p).toReal : ℂ)‖
          ≤ ‖((ν₁.rnDeriv ρ p).toReal : ℂ) -
              ((ν₂.rnDeriv ρ p).toReal : ℂ) -
              Complex.I * ((ν₃.rnDeriv ρ p).toReal : ℂ)‖ +
            ‖Complex.I * ((ν₄.rnDeriv ρ p).toReal : ℂ)‖ := by
              exact norm_add_le _ _
      _ ≤ ‖((ν₁.rnDeriv ρ p).toReal : ℂ) -
              ((ν₂.rnDeriv ρ p).toReal : ℂ)‖ +
            ‖Complex.I * ((ν₃.rnDeriv ρ p).toReal : ℂ)‖ +
            ‖Complex.I * ((ν₄.rnDeriv ρ p).toReal : ℂ)‖ := by
              gcongr
              exact norm_sub_le _ _
      _ ≤ ‖((ν₁.rnDeriv ρ p).toReal : ℂ)‖ +
            ‖((ν₂.rnDeriv ρ p).toReal : ℂ)‖ +
            ‖Complex.I * ((ν₃.rnDeriv ρ p).toReal : ℂ)‖ +
            ‖Complex.I * ((ν₄.rnDeriv ρ p).toReal : ℂ)‖ := by
              gcongr
              exact norm_sub_le _ _
      _ ≤ 1 + 1 + 1 + 1 := by
              have hp₃' : ‖Complex.I * ((ν₃.rnDeriv ρ p).toReal : ℂ)‖ ≤ 1 := by
                simpa [norm_mul] using hp₃
              have hp₄' : ‖Complex.I * ((ν₄.rnDeriv ρ p).toReal : ℂ)‖ ≤ 1 := by
                simpa [norm_mul] using hp₄
              linarith
      _ = 4 := by norm_num
  calc
    ‖polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p‖
        =
      ‖(1 / 4 : ℂ) *
          (((ν₁.rnDeriv ρ p).toReal : ℂ) -
            ((ν₂.rnDeriv ρ p).toReal : ℂ) -
            Complex.I * ((ν₃.rnDeriv ρ p).toReal : ℂ) +
            Complex.I * ((ν₄.rnDeriv ρ p).toReal : ℂ))‖ := by
              simp [polarizationControlDensity_local, ρ, polarizationControlMeasure_local]
    _ = ‖(1 / 4 : ℂ)‖ *
          ‖((ν₁.rnDeriv ρ p).toReal : ℂ) -
            ((ν₂.rnDeriv ρ p).toReal : ℂ) -
            Complex.I * ((ν₃.rnDeriv ρ p).toReal : ℂ) +
            Complex.I * ((ν₄.rnDeriv ρ p).toReal : ℂ)‖ := by
              rw [norm_mul]
    _ ≤ ‖(1 / 4 : ℂ)‖ * 4 := by
          gcongr
    _ = 1 := by norm_num

theorem ae_norm_mul_polarizationControlDensity_le_local
    {α : Type*} [MeasurableSpace α]
    (ν₁ ν₂ ν₃ ν₄ : Measure α)
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [IsFiniteMeasure ν₃] [IsFiniteMeasure ν₄]
    (s : α → ℂ)
    (hs_meas : AEStronglyMeasurable s (polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄))
    (C : ℝ)
    (hC : 0 ≤ C)
    (hs_bound : ∀ᵐ p ∂(polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄), ‖s p‖ ≤ C) :
    ∀ᵐ p ∂(polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄),
      ‖s p * polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p‖ ≤ C := by
  filter_upwards
    [hs_bound, ae_norm_polarizationControlDensity_le_one_local (ν₁ := ν₁) (ν₂ := ν₂)
      (ν₃ := ν₃) (ν₄ := ν₄)] with p hp hs
  calc
    ‖s p * polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p‖
        = ‖s p‖ * ‖polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p‖ := by
            rw [norm_mul]
    _ ≤ C * ‖polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p‖ := by
          gcongr
    _ ≤ C * 1 := by
          gcongr
    _ = C := by simp


/-- Swap the two Euclidean arguments of a two-point configuration. -/
private def swapTwoPoint_local (x : NPointDomain d 2) : NPointDomain d 2 :=
  fun i => x (Equiv.swap (0 : Fin 2) (1 : Fin 2) i)

@[simp] private theorem swapTwoPoint_local_apply_zero
    (x : NPointDomain d 2) :
    swapTwoPoint_local x 0 = x 1 := by
  simp [swapTwoPoint_local]

@[simp] private theorem swapTwoPoint_local_apply_one
    (x : NPointDomain d 2) :
    swapTwoPoint_local x 1 = x 0 := by
  simp [swapTwoPoint_local]

/-- Honest real Euclidean kernel for the canonical `k = 2` probe witness.

On positive time-difference we use the direct Euclidean section of the witness.
On negative time-difference we swap the two Euclidean arguments so that the
same positive-time contraction bound applies. The diagonal itself is set to `0`,
which is harmless for the later a.e. kernel packaging. -/
private def k2TimeParametricKernel_real_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    NPointDomain d 2 → ℂ := fun x =>
  if hx : x 0 0 < x 1 0 then
    k2TimeParametricKernel (d := d)
      (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg) x
  else if hy : x 1 0 < x 0 0 then
    k2TimeParametricKernel (d := d)
      (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg)
      (swapTwoPoint_local x)
  else
    0

/-- One-variable real difference kernel corresponding to the honest piecewise
real Euclidean `k = 2` kernel. On positive time it is the Laplace-Fourier
kernel of the packaged Bochner measure, and on negative time it is its swapped
counterpart `ξ ↦ K(-ξ)`. -/
def k2DifferenceKernel_real_local
    (μ : Measure (ℝ × (Fin d → ℝ))) :
    SpacetimeDim d → ℂ := fun ξ =>
  if hξ : 0 < ξ 0 then
    laplaceFourierKernel (d := d) μ ξ
  else if hξ' : ξ 0 < 0 then
    laplaceFourierKernel (d := d) μ (-ξ)
  else
    0

/-- The honest piecewise real Euclidean kernel is already a difference-only
kernel. This is the reduced-difference reformulation needed before the final
boundary identification step. -/
theorem k2TimeParametricKernel_real_eq_twoPointDifferenceKernel_local
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ) :
    k2TimeParametricKernel_real_local (d := d) OS lgc φ hφ_compact hφ_neg =
      OSReconstruction.twoPointDifferenceKernel (d := d)
        (k2DifferenceKernel_real_local (d := d) μ) := by
  funext x
  by_cases hx : x 0 0 < x 1 0
  · have hξ : 0 < (fun i => x 1 i - x 0 i) 0 := by
      simpa using sub_pos.mpr hx
    have hnot : ¬ (fun i => x 1 i - x 0 i) 0 < 0 := by linarith
    simp [k2TimeParametricKernel_real_local, hx,
      OSReconstruction.twoPointDifferenceKernel, k2DifferenceKernel_real_local, hξ, hnot]
    exact k2TimeParametricKernel_probe_eq_laplaceFourier_of_pos_local
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hμ_repr x hx
  · by_cases hy : x 1 0 < x 0 0
    · have hswap : (swapTwoPoint_local (d := d) x) 0 0 < (swapTwoPoint_local (d := d) x) 1 0 := by
        simpa [swapTwoPoint_local] using hy
      have hξ_not : ¬ 0 < (fun i => x 1 i - x 0 i) 0 := by linarith
      have hξ_neg : (fun i => x 1 i - x 0 i) 0 < 0 := by
        simpa using sub_neg.mpr hy
      simp [k2TimeParametricKernel_real_local, hx, hy,
        OSReconstruction.twoPointDifferenceKernel, k2DifferenceKernel_real_local, hξ_not, hξ_neg]
      rw [k2TimeParametricKernel_probe_eq_laplaceFourier_of_pos_local
        (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hμ_repr (swapTwoPoint_local (d := d) x) hswap]
      change laplaceFourierKernel (d := d) μ (fun i => x 0 i - x 1 i) =
        laplaceFourierKernel (d := d) μ (fun i => x 0 i - x 1 i)
      rfl
    · have hξ_not : ¬ 0 < (fun i => x 1 i - x 0 i) 0 := by linarith
      have hξ_not' : ¬ (fun i => x 1 i - x 0 i) 0 < 0 := by linarith
      simp [k2TimeParametricKernel_real_local, hx, hy,
        OSReconstruction.twoPointDifferenceKernel, k2DifferenceKernel_real_local, hξ_not, hξ_not']

/-- On positive-time compact-support tests, the reduced one-variable kernel
attached to the honest piecewise real Euclidean section reproduces the same
translated product-shell boundary integral as the original Bochner
Laplace-Fourier kernel. -/
theorem integral_k2DifferenceKernel_real_mul_eq_translatedProductShell_integral_local
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
    ∫ ξ : SpacetimeDim d, k2DifferenceKernel_real_local (d := d) μ ξ * (h : SchwartzSpacetime d) ξ =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ
              (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
  calc
    ∫ ξ : SpacetimeDim d, k2DifferenceKernel_real_local (d := d) μ ξ * (h : SchwartzSpacetime d) ξ
      = ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          by_cases hξ : 0 < ξ 0
          · simp [k2DifferenceKernel_real_local, hξ]
          · have hξ_not_mem :
                ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) :
                  SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
              intro hmem
              exact hξ (h.property.1 hmem)
            have hξ_zero :
                ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ = 0 :=
              image_eq_zero_of_notMem_tsupport hξ_not_mem
            by_cases hξ' : ξ 0 < 0
            · simp [k2DifferenceKernel_real_local, hξ, hξ', hξ_zero]
            · simp [k2DifferenceKernel_real_local, hξ, hξ', hξ_zero]
    _ =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ
              (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
          exact integral_laplaceFourierKernel_mul_eq_translatedProductShell_integral_local
            (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμ_repr h

/-- Explicit spectral test symbol attached to a positive-time compact-support
test `h`. This is the concrete Fourier-Laplace factor appearing when the
reduced one-variable kernel pairing is rewritten by Fubini against a fixed
finite measure. -/
def positiveTimeCompactSupportLaplaceSymbol_local
    (h : positiveTimeCompactSupportSubmodule d)
    (p : ℝ × (Fin d → ℝ)) : ℂ :=
  ∫ ξ : SpacetimeDim d,
    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
      ((h : SchwartzSpacetime d) ξ) ∂volume

theorem continuous_positiveTimeCompactSupportLaplaceSymbol_local
    (h : positiveTimeCompactSupportSubmodule d) :
    Continuous (positiveTimeCompactSupportLaplaceSymbol_local (d := d) h) := by
  let ψ : SchwartzSpacetime d := (h : SchwartzSpacetime d)
  let K : Set (SpacetimeDim d) := tsupport (ψ : SpacetimeDim d → ℂ)
  have hK : IsCompact K := h.property.2.isCompact
  let F : (ℝ × (Fin d → ℝ)) → SpacetimeDim d → ℂ := fun p ξ =>
    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
      ψ ξ
  have hF_cont : Continuous F.uncurry := by
    change Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
      Complex.exp (-(↑(z.2 0 * z.1.1) : ℂ)) *
        Complex.exp (Complex.I * ↑(∑ i : Fin d, z.1.2 i * z.2 (Fin.succ i))) *
        ψ z.2)
    have hsum :
        Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
          ∑ i : Fin d, z.1.2 i * z.2 (Fin.succ i)) := by
      refine continuous_finset_sum _ fun i _ => ?_
      exact
        (((continuous_apply i).comp (continuous_snd.comp continuous_fst)) : Continuous
          fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d => z.1.2 i).mul
          (((continuous_apply (Fin.succ i)).comp continuous_snd) : Continuous
            fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d => z.2 (Fin.succ i))
    have h1 :
        Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
          Complex.exp (-(↑(z.2 0 * z.1.1) : ℂ))) := by
      have hbase :
          Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
            -((z.2 0) * z.1.1)) := by
        exact
          ((((continuous_apply (0 : Fin (d + 1))).comp continuous_snd) : Continuous
              fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d => z.2 0).mul
            (((continuous_fst.comp continuous_fst) : Continuous
              fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d => z.1.1))).neg
      have h1' :
          Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
            Complex.exp (↑(-((z.2 0) * z.1.1)) : ℂ)) := by
        exact Complex.continuous_exp.comp (Complex.continuous_ofReal.comp hbase)
      simpa using h1'
    have h2 :
        Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
          Complex.exp (Complex.I * ↑(∑ i : Fin d, z.1.2 i * z.2 (Fin.succ i)))) := by
      exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp hsum))
    have h3 :
        Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d => ψ z.2) := by
      exact (SchwartzMap.continuous ψ).comp continuous_snd
    have hF_cont' :
        Continuous (fun z : (ℝ × (Fin d → ℝ)) × SpacetimeDim d =>
          Complex.exp (-(↑(z.2 0 * z.1.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, z.1.2 i * z.2 (Fin.succ i))) *
            ψ z.2) := by
      simpa [mul_assoc] using (h1.mul (h2.mul h3))
    simpa [F, Function.uncurry, mul_assoc] using hF_cont'
  have hF_zero :
      ∀ p ξ,
        p ∈ (Set.univ : Set (ℝ × (Fin d → ℝ))) →
        ξ ∉ K →
        F p ξ = 0 := by
    intro p ξ _ hξ
    have hξ0 : ψ ξ = 0 := image_eq_zero_of_notMem_tsupport hξ
    simp [F, K, hξ0]
  have hcont_int :
      ContinuousOn (fun p => ∫ ξ, F p ξ ∂volume) Set.univ := by
    simpa [K] using
      (continuousOn_integral_of_compact_support
        (μ := volume) (s := (Set.univ : Set (ℝ × (Fin d → ℝ)))) (k := K)
        hK hF_cont.continuousOn hF_zero)
  have hcont_int' : Continuous (fun p => ∫ ξ, F p ξ ∂volume) := by
    simpa using hcont_int
  have hEq :
      (fun p => ∫ ξ, F p ξ ∂volume) =
        positiveTimeCompactSupportLaplaceSymbol_local (d := d) h := by
    funext p
    simp [positiveTimeCompactSupportLaplaceSymbol_local, F, ψ, mul_assoc]
  simpa [hEq] using hcont_int'

theorem measurable_positiveTimeCompactSupportLaplaceSymbol_local
    (h : positiveTimeCompactSupportSubmodule d) :
    Measurable (positiveTimeCompactSupportLaplaceSymbol_local (d := d) h) :=
  (continuous_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h).measurable

/-- The reflected negative-time probe, re-read as an honest positive-time
compact-support test. This is the concrete one-point input whose Laplace symbol
produces the explicit VI.1 weight. -/
private def reflected_negativeApproxIdentity_positiveTimeProbe_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    positiveTimeCompactSupportSubmodule d :=
  ⟨reflectedSchwartzSpacetime (φ_seq n),
    ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
      reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
        (hφ_compact n)⟩⟩

/-- The explicit VI.1 reflected-probe weight is the squared norm of the
positive-time Laplace symbol of the reflected probe itself. This is the exact
support-layer form needed when the first remaining blocker is read as a
one-point weighted spectral theorem rather than as an abstract `[0,1]` weight
package. -/
theorem reflected_negativeApproxIdentity_weight_global_eq_norm_sq_positiveTimeCompactSupportLaplaceSymbol_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (p : ℝ × (Fin d → ℝ))
    (hp : 0 ≤ p.1) :
    reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p =
      ‖(positiveTimeCompactSupportLaplaceSymbol_local (d := d)
          (reflected_negativeApproxIdentity_positiveTimeProbe_local
            (d := d) φ_seq n hφ_compact hφ_neg) p)‖ ^ 2 := by
  let ψpt : positiveTimeCompactSupportSubmodule d :=
    reflected_negativeApproxIdentity_positiveTimeProbe_local
      (d := d) φ_seq n hφ_compact hφ_neg
  have hbase :
      reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p =
        ‖∫ ξ : SpacetimeDim d,
            Complex.exp (-(↑(ξ 0 * p.1) : ℂ) +
              Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
              ((ψpt : SchwartzSpacetime d) ξ)
            ∂volume‖ ^ 2 := by
    have hswap :
        ∫ ξ : SpacetimeDim d,
            (φ_seq n) (timeReflection d ξ) *
              Complex.exp (-(↑(ξ 0 * p.1) : ℂ) +
                Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) ∂volume
          =
        ∫ ξ : SpacetimeDim d,
            Complex.exp (-(↑(ξ 0 * p.1) : ℂ) +
              Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
              (φ_seq n) (timeReflection d ξ) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards with ξ
      ring
    calc
      reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p
        =
          ‖∫ ξ : SpacetimeDim d,
              (φ_seq n) (timeReflection d ξ) *
                Complex.exp (-(↑(ξ 0 * p.1) : ℂ) +
                  Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) ∂volume‖ ^ 2 := by
              simpa using
                reflected_negativeApproxIdentity_weight_global_eq_norm_sq_supportedSymbol_local
                  φ_seq n hφ_compact hφ_neg p hp
      _ =
          ‖∫ ξ : SpacetimeDim d,
              Complex.exp (-(↑(ξ 0 * p.1) : ℂ) +
                Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
                (φ_seq n) (timeReflection d ξ) ∂volume‖ ^ 2 := by
              rw [hswap]
      _ =
          ‖∫ ξ : SpacetimeDim d,
              Complex.exp (-(↑(ξ 0 * p.1) : ℂ) +
                Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
                ((ψpt : SchwartzSpacetime d) ξ) ∂volume‖ ^ 2 := by
              refine congrArg (fun z : ℂ => ‖z‖ ^ 2) ?_
              refine integral_congr_ae ?_
              filter_upwards with ξ
              have hψ :
                  ((ψpt : SchwartzSpacetime d) ξ) =
                    (φ_seq n) (timeReflection d ξ) := by
                rw [show ((ψpt : SchwartzSpacetime d) ξ) =
                    reflectedSchwartzSpacetime (φ_seq n) ξ by
                      rfl]
                change (φ_seq n) (timeReflection d ξ) =
                  (φ_seq n) (timeReflection d ξ)
                rfl
              rw [hψ]
  have hsplit :
      ∫ ξ : SpacetimeDim d,
          Complex.exp (-(↑(ξ 0 * p.1) : ℂ) +
            Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
            ((ψpt : SchwartzSpacetime d) ξ) ∂volume
        =
      ∫ ξ : SpacetimeDim d,
          Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
            (Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
              ((ψpt : SchwartzSpacetime d) ξ)) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards with ξ
    simp [Complex.exp_add, mul_assoc, mul_left_comm, mul_comm]
  calc
    reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p
      =
        ‖∫ ξ : SpacetimeDim d,
            Complex.exp (-(↑(ξ 0 * p.1) : ℂ) +
              Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
              ((ψpt : SchwartzSpacetime d) ξ) ∂volume‖ ^ 2 := hbase
    _ =
        ‖∫ ξ : SpacetimeDim d,
            Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
              (Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
                ((ψpt : SchwartzSpacetime d) ξ)) ∂volume‖ ^ 2 := by
          rw [hsplit]
    _ = ‖(positiveTimeCompactSupportLaplaceSymbol_local (d := d) ψpt p)‖ ^ 2 := by
          simp [positiveTimeCompactSupportLaplaceSymbol_local, mul_assoc]

/-- Complex-valued form of the explicit VI.1 reflected-probe weight: it is the
Hermitian square `conj(z) * z` of the reflected positive-time Laplace symbol.
This is the algebraic shape needed by the future weighted semigroup-group
spectral theorem. -/
theorem reflected_negativeApproxIdentity_weight_global_eq_star_mul_positiveTimeCompactSupportLaplaceSymbol_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (p : ℝ × (Fin d → ℝ))
    (hp : 0 ≤ p.1) :
    ↑(reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p) =
      starRingEnd ℂ
          (positiveTimeCompactSupportLaplaceSymbol_local (d := d)
            (reflected_negativeApproxIdentity_positiveTimeProbe_local
              (d := d) φ_seq n hφ_compact hφ_neg) p) *
        positiveTimeCompactSupportLaplaceSymbol_local (d := d)
          (reflected_negativeApproxIdentity_positiveTimeProbe_local
            (d := d) φ_seq n hφ_compact hφ_neg) p := by
  let z : ℂ :=
    positiveTimeCompactSupportLaplaceSymbol_local (d := d)
      (reflected_negativeApproxIdentity_positiveTimeProbe_local
        (d := d) φ_seq n hφ_compact hφ_neg) p
  have hnorm :
      reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p =
        ‖z‖ ^ 2 := by
    simpa [z] using
      reflected_negativeApproxIdentity_weight_global_eq_norm_sq_positiveTimeCompactSupportLaplaceSymbol_local
        (d := d) (φ_seq := φ_seq) (n := n) hφ_compact hφ_neg p hp
  calc
    ↑(reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p)
      = ↑(‖z‖ ^ 2) := by
          exact congrArg (fun r : ℝ => (r : ℂ)) hnorm
    _ = ↑(Complex.normSq z) := by
          rw [Complex.normSq_eq_norm_sq]
    _ = starRingEnd ℂ z * z := by
          simpa using (Complex.normSq_eq_conj_mul_self (z := z))

/-- The explicit Fourier-Laplace symbol factors multiplicatively across the
reduced positive-time convolution. This is the basic scalar spectral algebra
behind the VI.1 reflected-weight formulas: convolving a fixed reduced test by a
positive-time probe multiplies its symbol by the probe symbol. -/
theorem positiveTimeCompactSupportLaplaceSymbol_convolution_local
    (g h : positiveTimeCompactSupportSubmodule d)
    (p : ℝ × (Fin d → ℝ)) :
    positiveTimeCompactSupportLaplaceSymbol_local (d := d)
        (positiveTimeCompactSupportConvolution g h) p =
      positiveTimeCompactSupportLaplaceSymbol_local (d := d) g p *
        positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p := by
  let K : SpacetimeDim d → ℂ := fun ξ =>
    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i)))
  let gK : SpacetimeDim d → ℂ := fun ξ => K ξ * ((g : SchwartzSpacetime d) ξ)
  let hK : SpacetimeDim d → ℂ := fun ξ => K ξ * ((h : SchwartzSpacetime d) ξ)
  have hK_add :
      ∀ x ξ : SpacetimeDim d, K ξ * K (x - ξ) = K x := by
    intro x ξ
    have hsum :
        (∑ i : Fin d, p.2 i * ξ (Fin.succ i)) +
            ∑ i : Fin d, p.2 i * (x - ξ) (Fin.succ i) =
          ∑ i : Fin d, p.2 i * x (Fin.succ i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      change
        p.2 i * ξ (Fin.succ i) + p.2 i * (x (Fin.succ i) - ξ (Fin.succ i)) =
          p.2 i * x (Fin.succ i)
      ring
    have htime :
        -(↑(ξ 0 * p.1) : ℂ) + -(↑((x - ξ) 0 * p.1) : ℂ) =
          -(↑(x 0 * p.1) : ℂ) := by
      have htime_real :
          ξ 0 * p.1 + (x - ξ) 0 * p.1 = x 0 * p.1 := by
        change ξ 0 * p.1 + (x 0 - ξ 0) * p.1 = x 0 * p.1
        ring
      calc
        -(↑(ξ 0 * p.1) : ℂ) + -(↑((x - ξ) 0 * p.1) : ℂ)
            = -((↑(ξ 0 * p.1) : ℂ) + ↑((x - ξ) 0 * p.1)) := by ring
        _ = -(↑(ξ 0 * p.1 + (x - ξ) 0 * p.1) : ℂ) := by simp
        _ = -(↑(x 0 * p.1) : ℂ) := by rw [htime_real]
    have hsumI :
        Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i)) +
            Complex.I * ↑(∑ i : Fin d, p.2 i * (x - ξ) (Fin.succ i)) =
          Complex.I * ↑(∑ i : Fin d, p.2 i * x (Fin.succ i)) := by
      calc
        Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i)) +
            Complex.I * ↑(∑ i : Fin d, p.2 i * (x - ξ) (Fin.succ i))
            =
          Complex.I *
            (↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i)) +
              ↑(∑ i : Fin d, p.2 i * (x - ξ) (Fin.succ i))) := by ring
        _ = Complex.I *
            ↑((∑ i : Fin d, p.2 i * ξ (Fin.succ i)) +
              ∑ i : Fin d, p.2 i * (x - ξ) (Fin.succ i)) := by simp
        _ = Complex.I * ↑(∑ i : Fin d, p.2 i * x (Fin.succ i)) := by rw [hsum]
    calc
      K ξ * K (x - ξ)
          =
        Complex.exp (-(↑(ξ 0 * p.1) : ℂ) + -(↑((x - ξ) 0 * p.1) : ℂ)) *
          Complex.exp
            (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i)) +
              Complex.I * ↑(∑ i : Fin d, p.2 i * (x - ξ) (Fin.succ i))) := by
              simp [K, Complex.exp_add, mul_assoc, mul_left_comm, mul_comm]
      _ =
        Complex.exp (-(↑(x 0 * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * x (Fin.succ i))) := by
              rw [htime, hsumI]
      _ = K x := by simp [K]
  have hK_cont : Continuous K := by
    change Continuous (fun ξ : SpacetimeDim d =>
      Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
        Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))))
    have hsum :
        Continuous (fun ξ : SpacetimeDim d =>
          ∑ i : Fin d, p.2 i * ξ (Fin.succ i)) := by
      refine continuous_finset_sum _ fun i _ => ?_
      exact continuous_const.mul (continuous_apply (Fin.succ i))
    have h1 :
        Continuous (fun ξ : SpacetimeDim d =>
          Complex.exp (-(↑(ξ 0 * p.1) : ℂ))) := by
      have hmul :
          Continuous (fun ξ : SpacetimeDim d => ((ξ 0 : ℝ) : ℂ) * (p.1 : ℂ)) := by
        exact (Complex.continuous_ofReal.comp (continuous_apply (0 : Fin (d + 1)))).mul
          continuous_const
      simpa [mul_comm] using Complex.continuous_exp.comp hmul.neg
    have h2 :
        Continuous (fun ξ : SpacetimeDim d =>
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i)))) := by
      exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp hsum))
    simpa [mul_assoc] using h1.mul h2
  have hgK_cont : Continuous gK := by
    simpa [gK] using hK_cont.mul (SchwartzMap.continuous (g : SchwartzSpacetime d))
  have hhK_cont : Continuous hK := by
    simpa [hK] using hK_cont.mul (SchwartzMap.continuous (h : SchwartzSpacetime d))
  have hgK_compact : HasCompactSupport gK := by
    simpa [gK] using (HasCompactSupport.mul_left (f := K) g.property.2)
  have hhK_compact : HasCompactSupport hK := by
    simpa [hK] using (HasCompactSupport.mul_left (f := K) h.property.2)
  have hgK_int : Integrable gK := hgK_cont.integrable_of_hasCompactSupport hgK_compact
  have hhK_int : Integrable hK := hhK_cont.integrable_of_hasCompactSupport hhK_compact
  have hconv :
      (fun x => K x *
        (((positiveTimeCompactSupportConvolution g h : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d) x)) =
      (fun x =>
        MeasureTheory.convolution (L := ContinuousLinearMap.lsmul ℝ ℂ)
          (μ := volume) gK hK x) := by
    funext x
    calc
      K x *
          (((positiveTimeCompactSupportConvolution g h : positiveTimeCompactSupportSubmodule d) :
            SchwartzSpacetime d) x)
        =
      K x * ∫ ξ : SpacetimeDim d,
          ((g : SchwartzSpacetime d) ξ) *
            (SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x := by
              rw [positiveTimeCompactSupportConvolution_apply_eq_integral_translate]
      _ =
      ∫ ξ : SpacetimeDim d,
        K x * (((g : SchwartzSpacetime d) ξ) *
          (SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x) := by
            rw [← MeasureTheory.integral_const_mul]
      _ =
      ∫ ξ : SpacetimeDim d,
        gK ξ * hK (x - ξ) := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          have htranslate :
              (SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x =
                (h : SchwartzSpacetime d) (x - ξ) := by
            simp [SCV.translateSchwartz_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          rw [htranslate]
          calc
            K x * (((g : SchwartzSpacetime d) ξ) * ((h : SchwartzSpacetime d) (x - ξ)))
                =
              (K ξ * ((g : SchwartzSpacetime d) ξ)) *
                (K (x - ξ) * ((h : SchwartzSpacetime d) (x - ξ))) := by
                  rw [← hK_add x ξ]
                  ring
            _ = gK ξ * hK (x - ξ) := by
                  simp [gK, hK, mul_assoc]
      _ =
      MeasureTheory.convolution (L := ContinuousLinearMap.lsmul ℝ ℂ)
        (μ := volume) gK hK x := by
          simp [MeasureTheory.convolution]
  calc
    positiveTimeCompactSupportLaplaceSymbol_local (d := d)
        (positiveTimeCompactSupportConvolution g h) p
      = ∫ x : SpacetimeDim d,
          K x *
            (((positiveTimeCompactSupportConvolution g h :
              positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) x) ∂volume := by
          simp [positiveTimeCompactSupportLaplaceSymbol_local, K, mul_assoc]
    _ = ∫ x : SpacetimeDim d,
          MeasureTheory.convolution (L := ContinuousLinearMap.lsmul ℝ ℂ)
            (μ := volume) gK hK x ∂volume := by
          rw [hconv]
    _ = (∫ x : SpacetimeDim d, gK x ∂volume) * (∫ x : SpacetimeDim d, hK x ∂volume) := by
          simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
            (MeasureTheory.integral_convolution
              (L := ContinuousLinearMap.lsmul ℝ ℂ) hgK_int hhK_int)
    _ =
      positiveTimeCompactSupportLaplaceSymbol_local (d := d) g p *
        positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p := by
          simp [gK, hK, K, positiveTimeCompactSupportLaplaceSymbol_local, mul_assoc]

/-- The explicit Laplace symbol, truncated to `0` on the negative-energy region.
Since the VI.1 spectral measures already vanish there, this is the natural global
symbol to use in the weighted dominated-convergence step. -/
def supported_positiveTimeCompactSupportLaplaceSymbol_local
    (h : positiveTimeCompactSupportSubmodule d)
    (p : ℝ × (Fin d → ℝ)) : ℂ :=
  if hp : 0 ≤ p.1 then
    positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p
  else
    0

theorem measurable_supported_positiveTimeCompactSupportLaplaceSymbol_local
    (h : positiveTimeCompactSupportSubmodule d) :
    Measurable (supported_positiveTimeCompactSupportLaplaceSymbol_local h) := by
  have hs : MeasurableSet {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1} :=
    measurable_fst measurableSet_Ici
  refine Measurable.piecewise hs
    (measurable_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h)
    measurable_const

/-- On measures supported in nonnegative energy, the truncated supported symbol
and the raw Laplace-Fourier symbol have identical integrals, even after
multiplication by an auxiliary weight. This lets the remaining VI.1 blocker be
stated on the more natural raw-symbol surface while the generic
polarization/control-measure package below continues to use the supported
version. -/
theorem integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (h : positiveTimeCompactSupportSubmodule d)
    (w : (ℝ × (Fin d → ℝ)) → ℂ) :
    ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local h p * w p ∂μ =
      ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p * w p ∂μ := by
  have hsupp_neg : μ {p : ℝ × (Fin d → ℝ) | p.1 < 0} = 0 := by
    have hset :
        {p : ℝ × (Fin d → ℝ) | p.1 < 0} = (Set.Iio 0).prod Set.univ := by
      ext p
      constructor
      · intro hp
        exact ⟨hp, by simp⟩
      · intro hp
        exact hp.1
    rw [hset]
    exact hsupp
  have hae_nonneg : ∀ᵐ p ∂μ, 0 ≤ p.1 := by
    rw [ae_iff]
    simpa [Set.compl_setOf, not_le] using hsupp_neg
  refine integral_congr_ae ?_
  filter_upwards [hae_nonneg] with p hp
  simp [supported_positiveTimeCompactSupportLaplaceSymbol_local, hp]

/-- Transform equality against the explicit reflected weighted candidate measure
implies the exact weighted supported-symbol formula on the VI.1 surface.

This is the practical consumer of the new uniqueness helper: once the weighted
candidate measure is identified by Laplace-Fourier uniqueness, the frontier
integral formula follows immediately for every positive-time compactly
supported test. -/
theorem supported_symbol_formula_of_laplaceFourier_eq_reflected_weight_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (μ ν : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsuppμ : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hsuppν : ν (Set.prod (Set.Iio 0) Set.univ) = 0)
    (n : ℕ)
    (heq : ∀ (t : ℝ), 0 < t → ∀ (a : Fin d → ℝ),
      ∫ p : ℝ × (Fin d → ℝ),
        Complex.exp (-(↑(t * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ =
      ∫ p : ℝ × (Fin d → ℝ),
        (Complex.exp (-(↑(t * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))) *
            ↑(reflected_negativeApproxIdentity_weight_global_local
              (d := d) φ_seq n p) ∂ν) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂μ =
        ∫ p,
          supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
            ↑(reflected_negativeApproxIdentity_weight_global_local
              (d := d) φ_seq n p) ∂ν := by
  intro h
  let νw : Measure (ℝ × (Fin d → ℝ)) :=
    ν.withDensity
      (fun p =>
        ENNReal.ofReal
          (reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p))
  have hμeq :
      μ = νw :=
    measure_eq_withDensity_reflected_negativeApproxIdentity_weight_of_laplaceFourier_eq_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_neg hφ_ball hφ_compact
      μ ν hsuppμ hsuppν n heq
  have hsymb :
      ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂νw =
        ∫ p,
          supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
            ↑(reflected_negativeApproxIdentity_weight_global_local
              (d := d) φ_seq n p) ∂ν := by
    calc
      ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂νw
          =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
          ↑(reflected_negativeApproxIdentity_weight_global_local
            (d := d) φ_seq n p) ∂ν := by
              dsimp [νw]
              rw [integral_eq_integral_withDensity_reflected_negativeApproxIdentity_weight_local
                (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_neg hφ_ball hφ_compact ν
                (fun p => positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p) n]
      _ =
        ∫ p,
          supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
            ↑(reflected_negativeApproxIdentity_weight_global_local
              (d := d) φ_seq n p) ∂ν := by
              symm
              exact integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
                (d := d) (μ := ν) hsuppν h
                (fun p =>
                  ↑(reflected_negativeApproxIdentity_weight_global_local
                    (d := d) φ_seq n p))
  simpa [hμeq] using hsymb

/-- Pointwise weighted-symbol rewrite for the reflected negative approximate
identity. The explicit supported symbol multiplied by the global VI.1 weight is
exactly the conjugate reflected-probe symbol times the supported symbol of the
reflected positive-time convolution. This is the algebraic bridge from the
frontier weight to the one-point convolution geometry. -/
theorem supported_positiveTimeCompactSupportLaplaceSymbol_mul_reflected_weight_eq_conj_mul_convolution_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (h : positiveTimeCompactSupportSubmodule d)
    (p : ℝ × (Fin d → ℝ)) :
    supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
        ↑(reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p) =
      starRingEnd ℂ
          (positiveTimeCompactSupportLaplaceSymbol_local (d := d)
            (reflected_negativeApproxIdentity_positiveTimeProbe_local
              (d := d) φ_seq n hφ_compact hφ_neg) p) *
        supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d)
          (positiveTimeCompactSupportConvolution
            (reflected_negativeApproxIdentity_positiveTimeProbe_local
              (d := d) φ_seq n hφ_compact hφ_neg)
            h) p := by
  let ψpt : positiveTimeCompactSupportSubmodule d :=
    reflected_negativeApproxIdentity_positiveTimeProbe_local
      (d := d) φ_seq n hφ_compact hφ_neg
  by_cases hp : 0 ≤ p.1
  · simp [supported_positiveTimeCompactSupportLaplaceSymbol_local, hp]
    rw [reflected_negativeApproxIdentity_weight_global_eq_star_mul_positiveTimeCompactSupportLaplaceSymbol_local
      (d := d) (φ_seq := φ_seq) (n := n) hφ_compact hφ_neg p hp]
    rw [positiveTimeCompactSupportLaplaceSymbol_convolution_local (d := d) ψpt h p]
    simp [ψpt, mul_assoc, mul_left_comm, mul_comm]
  · simp [supported_positiveTimeCompactSupportLaplaceSymbol_local, hp,
      reflected_negativeApproxIdentity_weight_global_local]

/-- Measure-level form of the explicit VI.1 reflected-weight rewrite.

This is the actual integration surface used by the frontier: weighting the fixed
supported symbol of `h` by the reflected approximate-identity factor is the same
as testing the same measure against the conjugate reflected-probe symbol times
the supported symbol of the reflected positive-time convolution. -/
theorem integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_reflected_weight_eq_conj_mul_convolution_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (ν : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure ν]
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ p,
      supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
        ↑(reflected_negativeApproxIdentity_weight_global_local (d := d) φ_seq n p) ∂ν =
      ∫ p,
        starRingEnd ℂ
            (positiveTimeCompactSupportLaplaceSymbol_local (d := d)
              (reflected_negativeApproxIdentity_positiveTimeProbe_local
                (d := d) φ_seq n hφ_compact hφ_neg) p) *
          supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d)
            (positiveTimeCompactSupportConvolution
              (reflected_negativeApproxIdentity_positiveTimeProbe_local
                (d := d) φ_seq n hφ_compact hφ_neg)
              h) p ∂ν := by
  refine integral_congr_ae ?_
  filter_upwards with p
  simpa using
    supported_positiveTimeCompactSupportLaplaceSymbol_mul_reflected_weight_eq_conj_mul_convolution_local
      (d := d) (φ_seq := φ_seq) (n := n) hφ_compact hφ_neg h p

/-- Polarization form of the explicit reflected-weight rewrite.

This is the exact four-measure algebra used later in the VI.1 frontier. It does
not solve the common-measure problem by itself, but it places the reflected
weight on the same polarization surface as the diagonal supported-symbol
packages. -/
theorem polarization_supported_symbol_mul_reflected_weight_eq_conj_mul_convolution_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (n : ℕ)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (ν₁ ν₂ ν₃ ν₄ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [IsFiniteMeasure ν₃] [IsFiniteMeasure ν₄]
    (h : positiveTimeCompactSupportSubmodule d) :
    (1 / 4 : ℂ) *
        ((∫ p,
            supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
              ↑(reflected_negativeApproxIdentity_weight_global_local
                  (d := d) φ_seq n p) ∂ν₁) -
          (∫ p,
            supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
              ↑(reflected_negativeApproxIdentity_weight_global_local
                  (d := d) φ_seq n p) ∂ν₂) -
          Complex.I *
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
                ↑(reflected_negativeApproxIdentity_weight_global_local
                    (d := d) φ_seq n p) ∂ν₃) +
          Complex.I *
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
                ↑(reflected_negativeApproxIdentity_weight_global_local
                    (d := d) φ_seq n p) ∂ν₄)) =
      (1 / 4 : ℂ) *
        ((∫ p,
            starRingEnd ℂ
                (positiveTimeCompactSupportLaplaceSymbol_local (d := d)
                  (reflected_negativeApproxIdentity_positiveTimeProbe_local
                    (d := d) φ_seq n hφ_compact hφ_neg) p) *
              supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d)
                (positiveTimeCompactSupportConvolution
                  (reflected_negativeApproxIdentity_positiveTimeProbe_local
                    (d := d) φ_seq n hφ_compact hφ_neg)
                  h) p ∂ν₁) -
          (∫ p,
            starRingEnd ℂ
                (positiveTimeCompactSupportLaplaceSymbol_local (d := d)
                  (reflected_negativeApproxIdentity_positiveTimeProbe_local
                    (d := d) φ_seq n hφ_compact hφ_neg) p) *
              supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d)
                (positiveTimeCompactSupportConvolution
                  (reflected_negativeApproxIdentity_positiveTimeProbe_local
                    (d := d) φ_seq n hφ_compact hφ_neg)
                  h) p ∂ν₂) -
          Complex.I *
            (∫ p,
              starRingEnd ℂ
                  (positiveTimeCompactSupportLaplaceSymbol_local (d := d)
                    (reflected_negativeApproxIdentity_positiveTimeProbe_local
                      (d := d) φ_seq n hφ_compact hφ_neg) p) *
                supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d)
                  (positiveTimeCompactSupportConvolution
                    (reflected_negativeApproxIdentity_positiveTimeProbe_local
                      (d := d) φ_seq n hφ_compact hφ_neg)
                    h) p ∂ν₃) +
          Complex.I *
            (∫ p,
              starRingEnd ℂ
                  (positiveTimeCompactSupportLaplaceSymbol_local (d := d)
                    (reflected_negativeApproxIdentity_positiveTimeProbe_local
                      (d := d) φ_seq n hφ_compact hφ_neg) p) *
                supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d)
                  (positiveTimeCompactSupportConvolution
                    (reflected_negativeApproxIdentity_positiveTimeProbe_local
                      (d := d) φ_seq n hφ_compact hφ_neg)
                    h) p ∂ν₄)) := by
  rw [integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_reflected_weight_eq_conj_mul_convolution_local
      (d := d) (φ_seq := φ_seq) (n := n) hφ_compact hφ_neg (ν := ν₁) (h := h)]
  rw [integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_reflected_weight_eq_conj_mul_convolution_local
      (d := d) (φ_seq := φ_seq) (n := n) hφ_compact hφ_neg (ν := ν₂) (h := h)]
  rw [integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_reflected_weight_eq_conj_mul_convolution_local
      (d := d) (φ_seq := φ_seq) (n := n) hφ_compact hφ_neg (ν := ν₃) (h := h)]
  rw [integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_reflected_weight_eq_conj_mul_convolution_local
      (d := d) (φ_seq := φ_seq) (n := n) hφ_compact hφ_neg (ν := ν₄) (h := h)]

theorem norm_positiveTimeCompactSupportLaplaceSymbol_le_integral_norm_of_nonnegEnergy_local
    (h : positiveTimeCompactSupportSubmodule d)
    (p : ℝ × (Fin d → ℝ))
    (hp : 0 ≤ p.1) :
    ‖positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p‖ ≤
      ∫ ξ : SpacetimeDim d, ‖((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖ ∂volume := by
  calc
    ‖positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p‖
        =
      ‖∫ ξ : SpacetimeDim d,
          Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
            ((h : SchwartzSpacetime d) ξ) ∂volume‖ := by
              rfl
    _ ≤ ∫ ξ : SpacetimeDim d,
          ‖Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
              ((h : SchwartzSpacetime d) ξ)‖ ∂volume := by
            exact norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : SpacetimeDim d,
          ‖((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖ ∂volume := by
            apply MeasureTheory.integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
            · exact ((h : SchwartzSpacetime d).integrable.norm)
            · exact Filter.Eventually.of_forall fun ξ => by
                by_cases hξ : ((h : SchwartzSpacetime d) ξ) = 0
                · simp [hξ]
                · have hξ_pos : 0 < ξ 0 := by
                    exact h.property.1
                      (subset_tsupport ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
                        (by rwa [Function.mem_support]))
                  have hphase :
                      (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))).re = 0 := by
                    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
                  have hexp_le_one : Real.exp (-(ξ 0 * p.1)) ≤ 1 := by
                    apply Real.exp_le_one_iff.mpr
                    nlinarith [hξ_pos, hp]
                  calc
                    ‖Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
                        Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
                        ((h : SchwartzSpacetime d) ξ)‖
                        = Real.exp (-(ξ 0 * p.1)) * ‖((h : SchwartzSpacetime d) ξ)‖ := by
                            rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, hphase,
                              Real.exp_zero, mul_one]
                            simp
                    _ ≤ 1 * ‖((h : SchwartzSpacetime d) ξ)‖ := by
                          gcongr
                    _ = ‖((h : SchwartzSpacetime d) ξ)‖ := by ring

theorem exists_uniform_bound_supported_positiveTimeCompactSupportLaplaceSymbol_local
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ p, ‖supported_positiveTimeCompactSupportLaplaceSymbol_local h p‖ ≤ C := by
  let C : ℝ :=
    ∫ ξ : SpacetimeDim d, ‖((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖
      ∂volume
  refine ⟨C, MeasureTheory.integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro p
  by_cases hp : 0 ≤ p.1
  · simpa [supported_positiveTimeCompactSupportLaplaceSymbol_local, hp] using
      norm_positiveTimeCompactSupportLaplaceSymbol_le_integral_norm_of_nonnegEnergy_local
        (d := d) h p hp
  · have hC_nonneg : 0 ≤ C := MeasureTheory.integral_nonneg fun _ => norm_nonneg _
    simpa [supported_positiveTimeCompactSupportLaplaceSymbol_local, hp] using hC_nonneg

theorem tendsto_to_schwingerDifferencePositive_of_supported_symbol_density_representation_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d)
    (ρ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure ρ]
    (w_seq : ℕ → (ℝ × (Fin d → ℝ)) → ℝ)
    (hw_le : ∀ n p, w_seq n p ≤ 1)
    (hw_nonneg : ∀ n p, 0 ≤ w_seq n p)
    (hw_meas : ∀ n, Measurable (w_seq n))
    (hw_tendsto : ∀ p, Filter.Tendsto (fun n => w_seq n p) Filter.atTop (𝓝 1))
    (s : (ℝ × (Fin d → ℝ)) → ℂ)
    (hs_meas : AEStronglyMeasurable s ρ)
    (Cs : ℝ)
    (hCs : 0 ≤ Cs)
    (hs_bound : ∀ᵐ p ∂ρ, ‖s p‖ ≤ Cs)
    (a_seq : ℕ → ℂ)
    (ha : ∀ n, a_seq n =
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local h p * s p *
        ↑(w_seq n p) ∂ρ)
    (htarget :
      (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h =
          ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local h p * s p ∂ρ) :
    Filter.Tendsto a_seq Filter.atTop
      (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h)) := by
  obtain ⟨Ch, hCh, hsymb_bound⟩ :=
    exists_uniform_bound_supported_positiveTimeCompactSupportLaplaceSymbol_local h
  let f : (ℝ × (Fin d → ℝ)) → ℂ :=
    fun p => supported_positiveTimeCompactSupportLaplaceSymbol_local h p * s p
  have hf_meas : AEStronglyMeasurable f ρ := by
    exact
      (measurable_supported_positiveTimeCompactSupportLaplaceSymbol_local h).aestronglyMeasurable.mul
        hs_meas
  have hf_bound : ∀ᵐ p ∂ρ, ‖f p‖ ≤ Ch * Cs := by
    filter_upwards [hs_bound] with p hp
    calc
      ‖f p‖
          = ‖supported_positiveTimeCompactSupportLaplaceSymbol_local h p‖ * ‖s p‖ := by
              simp [f, norm_mul]
      _ ≤ Ch * ‖s p‖ := by
            gcongr
            exact hsymb_bound p
      _ ≤ Ch * Cs := by
            gcongr
      _ = Ch * Cs := by rfl
  have hChCs : 0 ≤ Ch * Cs := mul_nonneg hCh hCs
  exact tendsto_to_schwingerDifferencePositive_of_weighted_measure_representation_local
    (d := d) OS χ₀ h ρ w_seq hw_le hw_nonneg hw_meas hw_tendsto
    f hf_meas (Ch * Cs) hChCs hf_bound a_seq
    (fun n => by simpa [f, mul_assoc] using ha n) (by simpa [f] using htarget)

theorem tendsto_to_schwingerDifferencePositive_of_supported_symbol_representation_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (h : positiveTimeCompactSupportSubmodule d)
    (ρ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure ρ]
    (w_seq : ℕ → (ℝ × (Fin d → ℝ)) → ℝ)
    (hw_le : ∀ n p, w_seq n p ≤ 1)
    (hw_nonneg : ∀ n p, 0 ≤ w_seq n p)
    (hw_meas : ∀ n, Measurable (w_seq n))
    (hw_tendsto : ∀ p, Filter.Tendsto (fun n => w_seq n p) Filter.atTop (𝓝 1))
    (a_seq : ℕ → ℂ)
    (ha : ∀ n, a_seq n =
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
        ↑(w_seq n p) ∂ρ)
    (htarget :
      (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h =
          ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local h p ∂ρ) :
    Filter.Tendsto a_seq Filter.atTop
      (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h)) := by
  exact
    tendsto_to_schwingerDifferencePositive_of_supported_symbol_density_representation_local
      (d := d) OS χ₀ h ρ w_seq hw_le hw_nonneg hw_meas hw_tendsto
      (fun _ => (1 : ℂ)) measurable_const.aestronglyMeasurable 1 (by norm_num)
      (Filter.Eventually.of_forall fun _ => by simp)
      a_seq
      (fun n => by simpa [mul_assoc] using ha n) (by simpa using htarget)

/-- The explicit polarized control density reproduces the weighted polarization
combination of the four diagonal symbol measures. This is the generic
measure-theoretic bridge needed before the remaining VI.1 blocker can be
reduced to extracting the four diagonal spectral measures on the OS route. -/
theorem integral_supported_symbol_mul_weight_eq_polarization_local
    (h : positiveTimeCompactSupportSubmodule d)
    (ν₁ ν₂ ν₃ ν₄ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [IsFiniteMeasure ν₃] [IsFiniteMeasure ν₄]
    (w : (ℝ × (Fin d → ℝ)) → ℝ)
    (hw_meas : Measurable w)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (hw_le : ∀ p, w p ≤ 1) :
    let ρ := polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄
    ∫ p, (supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
        polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p) * ↑(w p) ∂ρ =
      (1 / 4 : ℂ) *
        ((∫ p,
            supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
              ↑(w p) ∂ν₁) -
          (∫ p,
            supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
              ↑(w p) ∂ν₂) -
          Complex.I *
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                ↑(w p) ∂ν₃) +
          Complex.I *
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                ↑(w p) ∂ν₄)) := by
  let ρ := polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄
  letI : IsFiniteMeasure ρ := by
    dsimp [ρ, polarizationControlMeasure_local]
    infer_instance
  change
    ∫ p, (supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
        polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p) * ↑(w p) ∂ρ =
      (1 / 4 : ℂ) *
        ((∫ p,
            supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
              ↑(w p) ∂ν₁) -
          (∫ p,
            supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
              ↑(w p) ∂ν₂) -
          Complex.I *
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                ↑(w p) ∂ν₃) +
          Complex.I *
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                ↑(w p) ∂ν₄))
  let s : (ℝ × (Fin d → ℝ)) → ℂ :=
    supported_positiveTimeCompactSupportLaplaceSymbol_local h
  let g : (ℝ × (Fin d → ℝ)) → ℂ := fun p => s p * ↑(w p)
  obtain ⟨C, hC, hs_bound⟩ :=
    exists_uniform_bound_supported_positiveTimeCompactSupportLaplaceSymbol_local h
  have hs_meas : AEStronglyMeasurable s ρ :=
    (measurable_supported_positiveTimeCompactSupportLaplaceSymbol_local h).aestronglyMeasurable
  have hg_int : Integrable g ρ := by
    exact integrable_bdd_measurable_mul_weight_of_le_one_local
      (ρ := ρ) s hs_meas C hC (Filter.Eventually.of_forall hs_bound) w hw_meas hw_nonneg hw_le
  have hle₁ : ν₁ ≤ ρ := by
    calc
      ν₁ ≤ ν₁ + ν₂ := le_add_of_nonneg_right bot_le
      _ ≤ (ν₁ + ν₂) + ν₃ := le_add_of_nonneg_right bot_le
      _ ≤ ((ν₁ + ν₂) + ν₃) + ν₄ := le_add_of_nonneg_right bot_le
      _ = ρ := by simp [ρ, polarizationControlMeasure_local, add_assoc]
  have hle₂ : ν₂ ≤ ρ := by
    calc
      ν₂ ≤ ν₁ + ν₂ := le_add_of_nonneg_left bot_le
      _ ≤ (ν₁ + ν₂) + ν₃ := le_add_of_nonneg_right bot_le
      _ ≤ ((ν₁ + ν₂) + ν₃) + ν₄ := le_add_of_nonneg_right bot_le
      _ = ρ := by simp [ρ, polarizationControlMeasure_local, add_assoc]
  have hle₃ : ν₃ ≤ ρ := by
    calc
      ν₃ ≤ ν₁ + ν₂ + ν₃ := by
        simpa [add_assoc, add_comm, add_left_comm] using
          (le_add_of_nonneg_left (show 0 ≤ (ν₁ + ν₂) from bot_le) : ν₃ ≤ (ν₁ + ν₂) + ν₃)
      _ ≤ ((ν₁ + ν₂) + ν₃) + ν₄ := le_add_of_nonneg_right bot_le
      _ = ρ := by simp [ρ, polarizationControlMeasure_local, add_assoc]
  have hle₄ : ν₄ ≤ ρ := by
    calc
      ν₄ ≤ ((ν₁ + ν₂) + ν₃) + ν₄ := by
        simpa [add_assoc, add_comm, add_left_comm] using
          (le_add_of_nonneg_left (show 0 ≤ (ν₁ + ν₂ + ν₃) from bot_le) :
            ν₄ ≤ (ν₁ + ν₂ + ν₃) + ν₄)
      _ = ρ := by simp [ρ, polarizationControlMeasure_local, add_assoc]
  have hν₁_ac : ν₁ ≪ ρ := Measure.absolutelyContinuous_of_le hle₁
  have hν₂_ac : ν₂ ≪ ρ := Measure.absolutelyContinuous_of_le hle₂
  have hν₃_ac : ν₃ ≪ ρ := Measure.absolutelyContinuous_of_le hle₃
  have hν₄_ac : ν₄ ≪ ρ := Measure.absolutelyContinuous_of_le hle₄
  letI : ν₁.HaveLebesgueDecomposition ρ :=
    MeasureTheory.Measure.haveLebesgueDecomposition_of_finiteMeasure
  letI : ν₂.HaveLebesgueDecomposition ρ :=
    MeasureTheory.Measure.haveLebesgueDecomposition_of_finiteMeasure
  letI : ν₃.HaveLebesgueDecomposition ρ :=
    MeasureTheory.Measure.haveLebesgueDecomposition_of_finiteMeasure
  letI : ν₄.HaveLebesgueDecomposition ρ :=
    MeasureTheory.Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hg₁_int : Integrable g ν₁ := hg_int.mono_measure hle₁
  have hg₂_int : Integrable g ν₂ := hg_int.mono_measure hle₂
  have hg₃_int : Integrable g ν₃ := hg_int.mono_measure hle₃
  have hg₄_int : Integrable g ν₄ := hg_int.mono_measure hle₄
  let r₁ : (ℝ × (Fin d → ℝ)) → ℂ := fun p => ((ν₁.rnDeriv ρ p).toReal : ℂ) * g p
  let r₂ : (ℝ × (Fin d → ℝ)) → ℂ := fun p => ((ν₂.rnDeriv ρ p).toReal : ℂ) * g p
  let r₃ : (ℝ × (Fin d → ℝ)) → ℂ := fun p => ((ν₃.rnDeriv ρ p).toReal : ℂ) * g p
  let r₄ : (ℝ × (Fin d → ℝ)) → ℂ := fun p => ((ν₄.rnDeriv ρ p).toReal : ℂ) * g p
  have hr₁_int : Integrable r₁ ρ := by
    have h :=
      (MeasureTheory.integrable_rnDeriv_smul_iff (μ := ν₁) (ν := ρ) (f := g) hν₁_ac).2 hg₁_int
    simpa [r₁, g, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hr₂_int : Integrable r₂ ρ := by
    have h :=
      (MeasureTheory.integrable_rnDeriv_smul_iff (μ := ν₂) (ν := ρ) (f := g) hν₂_ac).2 hg₂_int
    simpa [r₂, g, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hr₃_int : Integrable r₃ ρ := by
    have h :=
      (MeasureTheory.integrable_rnDeriv_smul_iff (μ := ν₃) (ν := ρ) (f := g) hν₃_ac).2 hg₃_int
    simpa [r₃, g, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hr₄_int : Integrable r₄ ρ := by
    have h :=
      (MeasureTheory.integrable_rnDeriv_smul_iff (μ := ν₄) (ν := ρ) (f := g) hν₄_ac).2 hg₄_int
    simpa [r₄, g, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hr₁ :
      ∫ p, r₁ p ∂ρ = ∫ p, g p ∂ν₁ := by
    simpa [r₁, g, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.integral_rnDeriv_smul (μ := ν₁) (ν := ρ) (f := g) hν₁_ac)
  have hr₂ :
      ∫ p, r₂ p ∂ρ = ∫ p, g p ∂ν₂ := by
    simpa [r₂, g, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.integral_rnDeriv_smul (μ := ν₂) (ν := ρ) (f := g) hν₂_ac)
  have hr₃ :
      ∫ p, r₃ p ∂ρ = ∫ p, g p ∂ν₃ := by
    simpa [r₃, g, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.integral_rnDeriv_smul (μ := ν₃) (ν := ρ) (f := g) hν₃_ac)
  have hr₄ :
      ∫ p, r₄ p ∂ρ = ∫ p, g p ∂ν₄ := by
    simpa [r₄, g, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.integral_rnDeriv_smul (μ := ν₄) (ν := ρ) (f := g) hν₄_ac)
  have hpoint :
      (fun p =>
        (s p * polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p) * ↑(w p)) =
      (fun p => (1 / 4 : ℂ) * (r₁ p - r₂ p - Complex.I * r₃ p + Complex.I * r₄ p)) := by
    funext p
    simp [s, g, r₁, r₂, r₃, r₄, polarizationControlDensity_local]
    ring
  have hsplit :
      ∫ p, (r₁ p - r₂ p - Complex.I * r₃ p + Complex.I * r₄ p) ∂ρ =
        (∫ p, r₁ p ∂ρ - ∫ p, r₂ p ∂ρ - Complex.I * ∫ p, r₃ p ∂ρ +
          Complex.I * ∫ p, r₄ p ∂ρ) := by
    have hr₂_neg : Integrable (fun p => -r₂ p) ρ := hr₂_int.neg
    have hr₃_negI : Integrable (fun p => -(Complex.I * r₃ p)) ρ :=
      (hr₃_int.const_mul Complex.I).neg
    have hr₄_I : Integrable (fun p => Complex.I * r₄ p) ρ :=
      hr₄_int.const_mul Complex.I
    calc
      ∫ p, (r₁ p - r₂ p - Complex.I * r₃ p + Complex.I * r₄ p) ∂ρ
          = ∫ p, ((r₁ p + (-r₂ p)) + (-(Complex.I * r₃ p) + Complex.I * r₄ p)) ∂ρ := by
              refine integral_congr_ae ?_
              filter_upwards with p
              ring
      _ = ∫ p, (r₁ p + (-r₂ p)) ∂ρ + ∫ p, (-(Complex.I * r₃ p) + Complex.I * r₄ p) ∂ρ := by
              simpa using
                (integral_add (hr₁_int.add hr₂_neg) (hr₃_negI.add hr₄_I))
      _ = (∫ p, r₁ p ∂ρ + ∫ p, (-r₂ p) ∂ρ) +
            (∫ p, (-(Complex.I * r₃ p)) ∂ρ + ∫ p, Complex.I * r₄ p ∂ρ) := by
              congr 1
              · simpa using (integral_add hr₁_int hr₂_neg)
              · simpa using (integral_add hr₃_negI hr₄_I)
      _ = (∫ p, r₁ p ∂ρ + ∫ p, (-r₂ p) ∂ρ + ∫ p, (-(Complex.I * r₃ p)) ∂ρ +
            ∫ p, Complex.I * r₄ p ∂ρ) := by
              ring
      _ = (∫ p, r₁ p ∂ρ - ∫ p, r₂ p ∂ρ - Complex.I * ∫ p, r₃ p ∂ρ +
            Complex.I * ∫ p, r₄ p ∂ρ) := by
              rw [integral_neg, integral_neg, integral_const_mul, integral_const_mul]
              ring
  calc
    ∫ p, (s p * polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p) * ↑(w p) ∂ρ
        = ∫ p, ((1 / 4 : ℂ) * (r₁ p - r₂ p - Complex.I * r₃ p + Complex.I * r₄ p)) ∂ρ := by
            simp [hpoint]
    _ = (1 / 4 : ℂ) *
        (∫ p, r₁ p ∂ρ - ∫ p, r₂ p ∂ρ - Complex.I * ∫ p, r₃ p ∂ρ +
          Complex.I * ∫ p, r₄ p ∂ρ) := by
            rw [integral_const_mul, hsplit]
    _ = (1 / 4 : ℂ) *
        ((∫ p, g p ∂ν₁) - (∫ p, g p ∂ν₂) - Complex.I * (∫ p, g p ∂ν₃) +
          Complex.I * (∫ p, g p ∂ν₄)) := by
            simp [hr₁, hr₂, hr₃, hr₄]
    _ = (1 / 4 : ℂ) *
        ((∫ p,
            supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
              ↑(w p) ∂ν₁) -
          (∫ p,
            supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
              ↑(w p) ∂ν₂) -
          Complex.I *
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                ↑(w p) ∂ν₃) +
          Complex.I *
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                ↑(w p) ∂ν₄)) := by
            simp [g, s]

/-- Once the four diagonal weighted formulas are available, the off-diagonal
polarization/control-measure representation needed for VI.1 is automatic. This
packages all generic RN bookkeeping so the remaining blocker can focus only on
extracting the four supported diagonal measures on the OS route. -/
theorem exists_weighted_measure_representation_of_supported_symbol_polarization_local
    (h : positiveTimeCompactSupportSubmodule d)
    (ν₁ ν₂ ν₃ ν₄ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [IsFiniteMeasure ν₃] [IsFiniteMeasure ν₄]
    (hsupp₁ : ν₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hsupp₂ : ν₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hsupp₃ : ν₃ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hsupp₄ : ν₄ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (w_seq : ℕ → (ℝ × (Fin d → ℝ)) → ℝ)
    (hw_meas : ∀ n, Measurable (w_seq n))
    (hw_nonneg : ∀ n p, 0 ≤ w_seq n p)
    (hw_le : ∀ n p, w_seq n p ≤ 1)
    (pairSeq : ℕ → ℂ)
    (target : ℂ)
    (hpair : ∀ n,
      pairSeq n =
        (1 / 4 : ℂ) *
          ((∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                ↑(w_seq n p) ∂ν₁) -
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                ↑(w_seq n p) ∂ν₂) -
            Complex.I *
              (∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                  ↑(w_seq n p) ∂ν₃) +
            Complex.I *
              (∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                  ↑(w_seq n p) ∂ν₄)))
    (htarget :
      target =
        (1 / 4 : ℂ) *
          ((∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local h p ∂ν₁) -
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local h p ∂ν₂) -
            Complex.I *
              (∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local h p ∂ν₃) +
            Complex.I *
              (∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local h p ∂ν₄))) :
    ∃ (ρ : Measure (ℝ × (Fin d → ℝ))) (_hρfin : IsFiniteMeasure ρ)
      (_hsuppρ : ρ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (f : (ℝ × (Fin d → ℝ)) → ℂ)
      (_hf_meas : AEStronglyMeasurable f ρ)
      (C : ℝ) (_hC : 0 ≤ C)
      (_hf_bound : ∀ᵐ p ∂ρ, ‖f p‖ ≤ C),
      (∀ n, pairSeq n = ∫ p, f p * ↑(w_seq n p) ∂ρ) ∧
      (target = ∫ p, f p ∂ρ) := by
  let ρ := polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄
  letI : IsFiniteMeasure ρ := by
    dsimp [ρ, polarizationControlMeasure_local]
    infer_instance
  let s : (ℝ × (Fin d → ℝ)) → ℂ :=
    supported_positiveTimeCompactSupportLaplaceSymbol_local h
  let f : (ℝ × (Fin d → ℝ)) → ℂ :=
    fun p => s p * polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p
  obtain ⟨C, hC, hs_bound⟩ :=
    exists_uniform_bound_supported_positiveTimeCompactSupportLaplaceSymbol_local h
  have hs_meas : AEStronglyMeasurable s ρ :=
    (measurable_supported_positiveTimeCompactSupportLaplaceSymbol_local h).aestronglyMeasurable
  have hf_meas : AEStronglyMeasurable f ρ := by
    refine hs_meas.mul ?_
    simpa [ρ] using
      (aestronglyMeasurable_polarizationControlDensity_local
        (ν₁ := ν₁) (ν₂ := ν₂) (ν₃ := ν₃) (ν₄ := ν₄))
  have hf_bound : ∀ᵐ p ∂ρ, ‖f p‖ ≤ C := by
    simpa [f, s] using
      (ae_norm_mul_polarizationControlDensity_le_local
        (ν₁ := ν₁) (ν₂ := ν₂) (ν₃ := ν₃) (ν₄ := ν₄) s
        hs_meas C hC (Filter.Eventually.of_forall hs_bound))
  have hsuppρ : ρ (Set.prod (Set.Iio 0) Set.univ) = 0 := by
    simp [ρ, polarizationControlMeasure_local, hsupp₁, hsupp₂, hsupp₃, hsupp₄]
  refine ⟨ρ, inferInstance, hsuppρ, f, hf_meas, C, hC, hf_bound, ?_, ?_⟩
  · intro n
    calc
      pairSeq n =
          (1 / 4 : ℂ) *
            ((∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                  ↑(w_seq n p) ∂ν₁) -
              (∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                  ↑(w_seq n p) ∂ν₂) -
              Complex.I *
                (∫ p,
                  supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                    ↑(w_seq n p) ∂ν₃) +
              Complex.I *
                (∫ p,
                  supported_positiveTimeCompactSupportLaplaceSymbol_local h p *
                    ↑(w_seq n p) ∂ν₄)) := hpair n
      _ = ∫ p, (s p * polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p) *
            ↑(w_seq n p) ∂ρ := by
            symm
            simpa [ρ, s] using
              (integral_supported_symbol_mul_weight_eq_polarization_local
                (d := d) h ν₁ ν₂ ν₃ ν₄ (w_seq n) (hw_meas n)
                (hw_nonneg n) (hw_le n))
      _ = ∫ p, f p * ↑(w_seq n p) ∂ρ := by
            simp [f, s, mul_assoc]
  · calc
      target =
          (1 / 4 : ℂ) *
            ((∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local h p ∂ν₁) -
              (∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local h p ∂ν₂) -
              Complex.I *
                (∫ p,
                  supported_positiveTimeCompactSupportLaplaceSymbol_local h p ∂ν₃) +
              Complex.I *
                (∫ p,
                  supported_positiveTimeCompactSupportLaplaceSymbol_local h p ∂ν₄)) := htarget
      _ = ∫ p, (s p * polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄ p) *
            ↑((1 : ℝ)) ∂ρ := by
            symm
            simpa [ρ, s] using
              (integral_supported_symbol_mul_weight_eq_polarization_local
                (d := d) h ν₁ ν₂ ν₃ ν₄ (fun _ => (1 : ℝ))
                measurable_const (by intro p; norm_num) (by intro p; norm_num))
      _ = ∫ p, f p ∂ρ := by
            simp [f, s]

/-- Rewriting the reduced `k = 2` kernel pairing against the explicit spectral
test symbol attached to `h`. This makes the remaining VI.1 blocker visibly a
measure-factorization problem, not a hidden Fubini problem. -/
theorem integral_k2DifferenceKernel_real_mul_eq_measure_symbol_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d, k2DifferenceKernel_real_local (d := d) μ ξ * (h : SchwartzSpacetime d) ξ =
      ∫ p : ℝ × (Fin d → ℝ),
        positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂μ := by
  calc
    ∫ ξ : SpacetimeDim d, k2DifferenceKernel_real_local (d := d) μ ξ * (h : SchwartzSpacetime d) ξ
        = ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            by_cases hξ : 0 < ξ 0
            · simp [k2DifferenceKernel_real_local, hξ]
            · have hξ_not_mem :
                  ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) :
                    SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
                intro hmem
                exact hξ (h.property.1 hmem)
              have hξ_zero :
                  ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ = 0 :=
                image_eq_zero_of_notMem_tsupport hξ_not_mem
              by_cases hξ' : ξ 0 < 0
              · simp [k2DifferenceKernel_real_local, hξ, hξ', hξ_zero]
              · simp [k2DifferenceKernel_real_local, hξ, hξ', hξ_zero]
    _ = ∫ p : ℝ × (Fin d → ℝ),
          positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂μ := by
          have hmeasure :=
            integral_laplaceFourierKernel_mul_eq_measure_integral_local
              (d := d) μ hsupp (h : SchwartzSpacetime d) h.property.1 h.property.2
          simpa [positiveTimeCompactSupportLaplaceSymbol_local] using hmeasure

/-- Integrability of the reduced Laplace-Fourier kernel against a positive-time
compact-support Schwartz test. This is the reusable Bochner/Fubini input needed
when pointwise spectral formulas are later integrated against a fixed reduced
test function. -/
theorem integrable_laplaceFourierKernel_mul_of_nonnegEnergy_local
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (h : positiveTimeCompactSupportSubmodule d) :
    Integrable (fun ξ : SpacetimeDim d =>
      laplaceFourierKernel (d := d) μ ξ * (h : SchwartzSpacetime d) ξ) := by
  let f : SpacetimeDim d → (ℝ × (Fin d → ℝ)) → ℂ := fun ξ p =>
    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) *
      ((h : SchwartzSpacetime d) ξ)
  let G : SpacetimeDim d × (ℝ × (Fin d → ℝ)) → ℂ := fun z => f z.1 z.2
  have hf_meas :
      AEStronglyMeasurable (Function.uncurry f) (volume.prod μ) := by
    have hcont_sum :
        Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
          ∑ i : Fin d, z.2.2 i * z.1 (Fin.succ i)) := by
      refine continuous_finset_sum _ fun i _ => ?_
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
          ((h : SchwartzSpacetime d) z.1))
      have h1base :
          Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
            -((z.1 0) * z.2.1)) := by
        exact
          ((((continuous_apply (0 : Fin (d + 1))).comp continuous_fst) : Continuous
              fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => z.1 0).mul
            (((continuous_fst.comp continuous_snd) : Continuous
              fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) => z.2.1))).neg
      have h1 :
          Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
            Complex.exp (-(↑(z.1 0 * z.2.1) : ℂ))) := by
        have h1' :
            Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
              Complex.exp (↑(-((z.1 0) * z.2.1)) : ℂ)) := by
          exact Complex.continuous_exp.comp (Complex.continuous_ofReal.comp h1base)
        simpa using h1'
      have h2 :
          Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
            Complex.exp (Complex.I * ↑(∑ i : Fin d, z.2.2 i * z.1 (Fin.succ i)))) := by
        exact
          Complex.continuous_exp.comp
            (continuous_const.mul (Complex.continuous_ofReal.comp hcont_sum))
      have h3 :
          Continuous (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
            ((h : SchwartzSpacetime d) z.1)) := by
        exact (SchwartzMap.continuous (h : SchwartzSpacetime d)).comp continuous_fst
      simpa [G, f, mul_assoc] using h1.mul (h2.mul h3)
    simpa [Function.uncurry, f, G] using hcont.aestronglyMeasurable
  have hbound :
      ∀ᵐ z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) ∂(volume.prod μ),
        ‖Function.uncurry f z‖ ≤ ‖((h : SchwartzSpacetime d) z.1)‖ := by
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
    by_cases hhξ : ((h : SchwartzSpacetime d) ξ) = 0
    · simp [f, hhξ]
    · have hξ_pos : 0 < ξ 0 := by
        exact h.property.1
          (subset_tsupport ((h : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
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
              ‖((h : SchwartzSpacetime d) ξ)‖ := by
                simp [f, mul_assoc]
        _ = Real.exp (-(ξ 0 * p.1)) * ‖((h : SchwartzSpacetime d) ξ)‖ := by
              rw [norm_mul, Complex.norm_exp, Complex.norm_exp, hphase, Real.exp_zero, mul_one]
              simp
        _ ≤ 1 * ‖((h : SchwartzSpacetime d) ξ)‖ := by
              gcongr
        _ = ‖((h : SchwartzSpacetime d) ξ)‖ := by ring
  have hh_int :
      Integrable (fun z : SpacetimeDim d × (ℝ × (Fin d → ℝ)) =>
        ((h : SchwartzSpacetime d) z.1)) (volume.prod μ) := by
    simpa using (((h : SchwartzSpacetime d).integrable (μ := volume)).comp_fst μ)
  have hf_int : Integrable (Function.uncurry f) (volume.prod μ) := by
    exact (hh_int.norm).mono' hf_meas hbound
  have hint :
      Integrable (fun ξ : SpacetimeDim d => ∫ p : ℝ × (Fin d → ℝ), f ξ p ∂μ) volume := by
    simpa [Function.uncurry] using hf_int.integral_prod_left
  refine hint.congr ?_
  filter_upwards with ξ
  rw [laplaceFourierKernel, ← MeasureTheory.integral_mul_const]

/-- The compact-support one-point polarization package may be integrated
against any positive-time compact-support reduced test, yielding the explicit
Laplace-symbol formula for its four diagonal measures. This is a reusable
target-side spectral bridge underneath the first remaining VI.1 blocker. -/
theorem supported_symbol_formula_of_polarized_measure_positiveTimeOnePoint_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (xf xg : OSHilbertSpace OS)
    (ν₁ ν₂ ν₃ ν₄ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [IsFiniteMeasure ν₃] [IsFiniteMeasure ν₄]
    (hsupp₁ : ν₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hsupp₂ : ν₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hsupp₃ : ν₃ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hsupp₄ : ν₄ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (horbit : ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
      (if ht : 0 < t then
        @inner ℂ (OSHilbertSpace OS) _ xf
          ((osTimeShiftHilbertComplex (d := d) OS lgc (t : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS a) xg))
      else
        @inner ℂ (OSHilbertSpace OS) _ xf
          ((osSpatialTranslateHilbert (d := d) OS a) xg)) =
        (1 / 4 : ℂ) *
          ((∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₁) -
            (∫ p : ℝ × (Fin d → ℝ),
              Complex.exp (-(↑(t * p.1) : ℂ)) *
                Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₂) -
            Complex.I *
              (∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₃) +
            Complex.I *
              (∫ p : ℝ × (Fin d → ℝ),
                Complex.exp (-(↑(t * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂ν₄)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        @inner ℂ (OSHilbertSpace OS) _ xf
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xg))
      else 0) * ((h : SchwartzSpacetime d) ξ) =
    (1 / 4 : ℂ) *
      ((∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
        (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
        Complex.I * (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
        Complex.I * (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄)) := by
  have hI₁ :
      Integrable (fun ξ : SpacetimeDim d =>
        laplaceFourierKernel (d := d) ν₁ ξ * ((h : SchwartzSpacetime d) ξ)) :=
    integrable_laplaceFourierKernel_mul_of_nonnegEnergy_local
      (d := d) (μ := ν₁) hsupp₁ h
  have hI₂ :
      Integrable (fun ξ : SpacetimeDim d =>
        laplaceFourierKernel (d := d) ν₂ ξ * ((h : SchwartzSpacetime d) ξ)) :=
    integrable_laplaceFourierKernel_mul_of_nonnegEnergy_local
      (d := d) (μ := ν₂) hsupp₂ h
  have hI₃ :
      Integrable (fun ξ : SpacetimeDim d =>
        laplaceFourierKernel (d := d) ν₃ ξ * ((h : SchwartzSpacetime d) ξ)) :=
    integrable_laplaceFourierKernel_mul_of_nonnegEnergy_local
      (d := d) (μ := ν₃) hsupp₃ h
  have hI₄ :
      Integrable (fun ξ : SpacetimeDim d =>
        laplaceFourierKernel (d := d) ν₄ ξ * ((h : SchwartzSpacetime d) ξ)) :=
    integrable_laplaceFourierKernel_mul_of_nonnegEnergy_local
      (d := d) (μ := ν₄) hsupp₄ h
  have hI₁₂ :
      Integrable (fun ξ : SpacetimeDim d =>
        laplaceFourierKernel (d := d) ν₁ ξ * ((h : SchwartzSpacetime d) ξ) -
          laplaceFourierKernel (d := d) ν₂ ξ * ((h : SchwartzSpacetime d) ξ)) :=
    hI₁.sub hI₂
  have hI₁₂₃ :
      Integrable (fun ξ : SpacetimeDim d =>
        (laplaceFourierKernel (d := d) ν₁ ξ * ((h : SchwartzSpacetime d) ξ) -
            laplaceFourierKernel (d := d) ν₂ ξ * ((h : SchwartzSpacetime d) ξ)) -
          Complex.I * (laplaceFourierKernel (d := d) ν₃ ξ * ((h : SchwartzSpacetime d) ξ))) :=
    hI₁₂.sub (hI₃.const_mul Complex.I)
  have hν₁ :
      ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) ν₁ ξ * ((h : SchwartzSpacetime d) ξ) =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁ := by
    simpa [positiveTimeCompactSupportLaplaceSymbol_local] using
      (integral_laplaceFourierKernel_mul_eq_measure_integral_local
        (d := d) (μ := ν₁) hsupp₁ (h : SchwartzSpacetime d) h.property.1 h.property.2)
  have hν₂ :
      ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) ν₂ ξ * ((h : SchwartzSpacetime d) ξ) =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂ := by
    simpa [positiveTimeCompactSupportLaplaceSymbol_local] using
      (integral_laplaceFourierKernel_mul_eq_measure_integral_local
        (d := d) (μ := ν₂) hsupp₂ (h : SchwartzSpacetime d) h.property.1 h.property.2)
  have hν₃ :
      ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) ν₃ ξ * ((h : SchwartzSpacetime d) ξ) =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃ := by
    simpa [positiveTimeCompactSupportLaplaceSymbol_local] using
      (integral_laplaceFourierKernel_mul_eq_measure_integral_local
        (d := d) (μ := ν₃) hsupp₃ (h : SchwartzSpacetime d) h.property.1 h.property.2)
  have hν₄ :
      ∫ ξ : SpacetimeDim d, laplaceFourierKernel (d := d) ν₄ ξ * ((h : SchwartzSpacetime d) ξ) =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄ := by
    simpa [positiveTimeCompactSupportLaplaceSymbol_local] using
      (integral_laplaceFourierKernel_mul_eq_measure_integral_local
        (d := d) (μ := ν₄) hsupp₄ (h : SchwartzSpacetime d) h.property.1 h.property.2)
  calc
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        @inner ℂ (OSHilbertSpace OS) _ xf
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xg))
      else 0) * ((h : SchwartzSpacetime d) ξ)
      =
    ∫ ξ : SpacetimeDim d,
      ((1 / 4 : ℂ) *
          ((laplaceFourierKernel (d := d) ν₁ ξ) -
            (laplaceFourierKernel (d := d) ν₂ ξ) -
            Complex.I * (laplaceFourierKernel (d := d) ν₃ ξ) +
            Complex.I * (laplaceFourierKernel (d := d) ν₄ ξ))) *
        ((h : SchwartzSpacetime d) ξ) := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        by_cases hmem : ξ ∈ tsupport (((h : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ)
        · have hξ : 0 < ξ 0 := h.property.1 hmem
          have horbitξ :=
            horbit (ξ 0) (fun i => ξ (Fin.succ i)) hξ.le
          have hmul :=
            congrArg (fun z : ℂ => z * (((h : SchwartzSpacetime d) ξ))) horbitξ
          simpa [hξ, laplaceFourierKernel, mul_assoc, mul_left_comm, mul_comm] using hmul
        · have hzero : ((h : SchwartzSpacetime d) ξ) = 0 :=
            image_eq_zero_of_notMem_tsupport hmem
          by_cases hξ : 0 < ξ 0 <;> simp [hzero, hξ]
    _ =
      (1 / 4 : ℂ) *
        ((∫ ξ : SpacetimeDim d,
            laplaceFourierKernel (d := d) ν₁ ξ * ((h : SchwartzSpacetime d) ξ)) -
          (∫ ξ : SpacetimeDim d,
            laplaceFourierKernel (d := d) ν₂ ξ * ((h : SchwartzSpacetime d) ξ)) -
          Complex.I * (∫ ξ : SpacetimeDim d,
            laplaceFourierKernel (d := d) ν₃ ξ * ((h : SchwartzSpacetime d) ξ)) +
          Complex.I * (∫ ξ : SpacetimeDim d,
            laplaceFourierKernel (d := d) ν₄ ξ * ((h : SchwartzSpacetime d) ξ))) := by
        calc
          ∫ ξ : SpacetimeDim d,
            ((1 / 4 : ℂ) *
                ((laplaceFourierKernel (d := d) ν₁ ξ) -
                  (laplaceFourierKernel (d := d) ν₂ ξ) -
                  Complex.I * (laplaceFourierKernel (d := d) ν₃ ξ) +
                  Complex.I * (laplaceFourierKernel (d := d) ν₄ ξ))) *
              ((h : SchwartzSpacetime d) ξ) =
            ∫ ξ : SpacetimeDim d,
              (1 / 4 : ℂ) *
                (((laplaceFourierKernel (d := d) ν₁ ξ) * ((h : SchwartzSpacetime d) ξ) -
                    (laplaceFourierKernel (d := d) ν₂ ξ) * ((h : SchwartzSpacetime d) ξ)) -
                  Complex.I *
                    ((laplaceFourierKernel (d := d) ν₃ ξ) * ((h : SchwartzSpacetime d) ξ)) +
                  Complex.I *
                    ((laplaceFourierKernel (d := d) ν₄ ξ) * ((h : SchwartzSpacetime d) ξ))) := by
              congr 1
              ext ξ
              ring
          _ =
            (1 / 4 : ℂ) *
              ∫ ξ : SpacetimeDim d,
                (((laplaceFourierKernel (d := d) ν₁ ξ) * ((h : SchwartzSpacetime d) ξ) -
                    (laplaceFourierKernel (d := d) ν₂ ξ) * ((h : SchwartzSpacetime d) ξ)) -
                  Complex.I *
                    ((laplaceFourierKernel (d := d) ν₃ ξ) * ((h : SchwartzSpacetime d) ξ)) +
                  Complex.I *
                    ((laplaceFourierKernel (d := d) ν₄ ξ) * ((h : SchwartzSpacetime d) ξ))) := by
                rw [MeasureTheory.integral_const_mul]
          _ =
            (1 / 4 : ℂ) *
              (((∫ ξ : SpacetimeDim d,
                  laplaceFourierKernel (d := d) ν₁ ξ * ((h : SchwartzSpacetime d) ξ)) -
                (∫ ξ : SpacetimeDim d,
                  laplaceFourierKernel (d := d) ν₂ ξ * ((h : SchwartzSpacetime d) ξ))) -
                Complex.I *
                  (∫ ξ : SpacetimeDim d,
                    laplaceFourierKernel (d := d) ν₃ ξ * ((h : SchwartzSpacetime d) ξ)) +
                Complex.I *
                  (∫ ξ : SpacetimeDim d,
                    laplaceFourierKernel (d := d) ν₄ ξ * ((h : SchwartzSpacetime d) ξ))) := by
                rw [MeasureTheory.integral_add hI₁₂₃ (hI₄.const_mul Complex.I)]
                rw [MeasureTheory.integral_sub hI₁₂ (hI₃.const_mul Complex.I)]
                rw [MeasureTheory.integral_sub hI₁ hI₂]
                simp [MeasureTheory.integral_const_mul, mul_assoc]
    _ =
      (1 / 4 : ℂ) *
        ((∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
          (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
          Complex.I * (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
          Complex.I * (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄)) := by
        rw [hν₁, hν₂, hν₃, hν₄]

/-- The compact-support one-point polarization package may be integrated
against any positive-time compact-support reduced test, yielding the explicit
Laplace-symbol formula for its four diagonal measures. This is a reusable
target-side spectral bridge underneath the first remaining VI.1 blocker. -/
theorem exists_supported_symbol_formula_positiveTimeOnePoint_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (f g h : positiveTimeCompactSupportSubmodule d) :
    let Ff : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single 1
        (onePointToFin1CLM d (f : SchwartzSpacetime d) : SchwartzNPoint d 1)
        (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
          (f : SchwartzSpacetime d) f.property.1)
    let Fg : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single 1
        (onePointToFin1CLM d (g : SchwartzSpacetime d) : SchwartzNPoint d 1)
        (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
          (g : SchwartzSpacetime d) g.property.1)
    let xf : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Ff⟧)) : OSHilbertSpace OS))
    let xg : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Fg⟧)) : OSHilbertSpace OS))
    ∃ (ν₁ : Measure (ℝ × (Fin d → ℝ))) (_hν₁fin : IsFiniteMeasure ν₁)
      (ν₂ : Measure (ℝ × (Fin d → ℝ))) (_hν₂fin : IsFiniteMeasure ν₂)
      (ν₃ : Measure (ℝ × (Fin d → ℝ))) (_hν₃fin : IsFiniteMeasure ν₃)
      (ν₄ : Measure (ℝ × (Fin d → ℝ))) (_hν₄fin : IsFiniteMeasure ν₄)
      (_hsupp₁ : ν₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₂ : ν₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₃ : ν₃ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₄ : ν₄ (Set.prod (Set.Iio 0) Set.univ) = 0),
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          @inner ℂ (OSHilbertSpace OS) _ xf
            ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xg))
        else 0) * ((h : SchwartzSpacetime d) ξ) =
      (1 / 4 : ℂ) *
        ((∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
          (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
          Complex.I * (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
          Complex.I * (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄)) := by
  let Ff : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d (f : SchwartzSpacetime d) : SchwartzNPoint d 1)
      (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
        (f : SchwartzSpacetime d) f.property.1)
  let Fg : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d (g : SchwartzSpacetime d) : SchwartzNPoint d 1)
      (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
        (g : SchwartzSpacetime d) g.property.1)
  let xf : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Ff⟧)) : OSHilbertSpace OS))
  let xg : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Fg⟧)) : OSHilbertSpace OS))
  obtain ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
      hsupp₁, hsupp₂, hsupp₃, hsupp₄, horbit⟩ :=
    exists_polarized_measure_positiveTimeOnePoint_local
      (d := d) OS lgc f g
  letI : IsFiniteMeasure ν₁ := hν₁fin
  letI : IsFiniteMeasure ν₂ := hν₂fin
  letI : IsFiniteMeasure ν₃ := hν₃fin
  letI : IsFiniteMeasure ν₄ := hν₄fin
  exact ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
    hsupp₁, hsupp₂, hsupp₃, hsupp₄,
    supported_symbol_formula_of_polarized_measure_positiveTimeOnePoint_local
      (d := d) OS lgc xf xg ν₁ ν₂ ν₃ ν₄ hsupp₁ hsupp₂ hsupp₃ hsupp₄ horbit h⟩

/-- Diagonal one-point version of the positive-time supported-symbol formula.

For a fixed positive-time compact-support one-point vector `g`, the entire
reduced test family is represented by one fixed supported finite measure. This
is the honest same-vector specialization underneath the VI.1 weighted bridge,
and avoids introducing polarization when the geometry is already diagonal. -/
theorem exists_supported_symbol_formula_positiveTimeOnePoint_diagonal_family_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (g : positiveTimeCompactSupportSubmodule d) :
    let Fg : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single 1
        (onePointToFin1CLM d (g : SchwartzSpacetime d) : SchwartzNPoint d 1)
        (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
          (g : SchwartzSpacetime d) g.property.1)
    let xg : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Fg⟧)) : OSHilbertSpace OS))
    ∃ (ν : Measure (ℝ × (Fin d → ℝ))) (_hνfin : IsFiniteMeasure ν)
      (_hsupp : ν (Set.prod (Set.Iio 0) Set.univ) = 0),
      ∀ h : positiveTimeCompactSupportSubmodule d,
        ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            @inner ℂ (OSHilbertSpace OS) _ xg
              ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xg))
          else 0) * ((h : SchwartzSpacetime d) ξ) =
          ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν := by
  let Fg : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d (g : SchwartzSpacetime d) : SchwartzNPoint d 1)
      (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
        (g : SchwartzSpacetime d) g.property.1)
  let xg : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Fg⟧)) : OSHilbertSpace OS))
  have hFg_compact :
      ∀ n,
        HasCompactSupport ((((Fg : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) := by
    intro n
    by_cases hn : n = 1
    · subst hn
      have hg_compact_one :
          HasCompactSupport (((onePointToFin1CLM d (g : SchwartzSpacetime d) : SchwartzNPoint d 1) :
            NPointDomain d 1 → ℂ)) := by
        simpa [onePointToFin1CLM] using
          (g.property.2.comp_homeomorph
            ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph))
      simpa [Fg, PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single] using hg_compact_one
    · simp [Fg, PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.single, hn, HasCompactSupport.zero]
  obtain ⟨ν, hνfin, hsupp, hrepr⟩ :=
    exists_measure_osSemigroupGroupMatrixElement_extension_of_isCompactSupport
      (d := d) OS lgc Fg hFg_compact
  letI : IsFiniteMeasure ν := hνfin
  refine ⟨ν, hνfin, hsupp, ?_⟩
  intro h
  have hν_supported :
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν := by
    simpa [mul_one] using
      (integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
        (d := d) (μ := ν) hsupp h (fun _ => (1 : ℂ)))
  calc
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        @inner ℂ (OSHilbertSpace OS) _ xg
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xg))
      else 0) * ((h : SchwartzSpacetime d) ξ)
        =
      ∫ ξ : SpacetimeDim d,
        laplaceFourierKernel (d := d) ν ξ * ((h : SchwartzSpacetime d) ξ) := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          by_cases hξ : 0 < ξ 0
          · have hinner :
              @inner ℂ (OSHilbertSpace OS) _ xg
                ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
                  ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xg)) =
                osSemigroupGroupMatrixElement (d := d) OS lgc xg
                  (ξ 0) (fun i => ξ (Fin.succ i)) := by
                simpa [osSpatialTranslateHilbert_zero] using
                  (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
                    (d := d) OS lgc xg (0 : Fin d → ℝ)
                    (fun i => ξ (Fin.succ i)) (ξ 0) hξ).symm
            have hkernel :=
              hrepr (ξ 0) (fun i => ξ (Fin.succ i)) (le_of_lt hξ)
            have hkernel' :
                osSemigroupGroupMatrixElement (d := d) OS lgc xg
                  (ξ 0) (fun i => ξ (Fin.succ i)) =
                ∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) ∂ν := by
              simpa [hξ] using hkernel
            have hlap :
                laplaceFourierKernel (d := d) ν ξ =
                  ∫ p : ℝ × (Fin d → ℝ),
                    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
                      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) ∂ν := by
              simp [laplaceFourierKernel, hξ]
            calc
              (if hξ : 0 < ξ 0 then
                @inner ℂ (OSHilbertSpace OS) _ xg
                  ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
                    ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xg))
              else 0) * ((h : SchwartzSpacetime d) ξ)
                  =
                osSemigroupGroupMatrixElement (d := d) OS lgc xg
                  (ξ 0) (fun i => ξ (Fin.succ i)) * ((h : SchwartzSpacetime d) ξ) := by
                    simp [hξ, hinner]
              _ =
                (∫ p : ℝ × (Fin d → ℝ),
                  Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
                    Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) ∂ν) *
                  ((h : SchwartzSpacetime d) ξ) := by rw [hkernel']
              _ = laplaceFourierKernel (d := d) ν ξ * ((h : SchwartzSpacetime d) ξ) := by
                    rw [hlap]
          · have hξ_not_mem :
                ξ ∉ tsupport (((h : positiveTimeCompactSupportSubmodule d) :
                  SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
              intro hmem
              exact hξ (h.property.1 hmem)
            have hξ_zero :
                ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ = 0 :=
              image_eq_zero_of_notMem_tsupport hξ_not_mem
            simp [hξ, hξ_zero]
    _ =
      ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν := by
        simpa [positiveTimeCompactSupportLaplaceSymbol_local] using
          (integral_laplaceFourierKernel_mul_eq_measure_integral_local
            (d := d) ν hsupp (h : SchwartzSpacetime d) h.property.1 h.property.2)
    _ =
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν := by
        rw [hν_supported]

/-- Fixed-control-measure family version of the compact-support one-point
spectral bridge.

For a fixed positive-time one-point pair `(f, g)`, the four diagonal measures
coming from polarization are independent of the reduced test `h`. Hence the
whole family of orbit pairings against positive-time compact-support tests is
already represented by one fixed supported finite measure `ρ` together with one
bounded measurable density `s`, independent of `h`. This is the right generic
off-diagonal infrastructure beneath the remaining VI.1 family-factorization
blocker. -/
theorem exists_supported_symbol_representation_positiveTimeOnePoint_family_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (f g : positiveTimeCompactSupportSubmodule d) :
    let Ff : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single 1
        (onePointToFin1CLM d (f : SchwartzSpacetime d) : SchwartzNPoint d 1)
        (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
          (f : SchwartzSpacetime d) f.property.1)
    let Fg : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single 1
        (onePointToFin1CLM d (g : SchwartzSpacetime d) : SchwartzNPoint d 1)
        (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
          (g : SchwartzSpacetime d) g.property.1)
    let xf : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Ff⟧)) : OSHilbertSpace OS))
    let xg : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Fg⟧)) : OSHilbertSpace OS))
    ∃ (ρ : Measure (ℝ × (Fin d → ℝ))) (_hρfin : IsFiniteMeasure ρ)
      (_hsuppρ : ρ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (s : (ℝ × (Fin d → ℝ)) → ℂ) (_hs_meas : AEStronglyMeasurable s ρ)
      (C : ℝ) (_hC : 0 ≤ C) (_hs_bound : ∀ᵐ p ∂ρ, ‖s p‖ ≤ C),
      ∀ h : positiveTimeCompactSupportSubmodule d,
        ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            @inner ℂ (OSHilbertSpace OS) _ xf
              ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xg))
          else 0) * ((h : SchwartzSpacetime d) ξ) =
          ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p * s p ∂ρ := by
  let Ff : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d (f : SchwartzSpacetime d) : SchwartzNPoint d 1)
      (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
        (f : SchwartzSpacetime d) f.property.1)
  let Fg : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d (g : SchwartzSpacetime d) : SchwartzNPoint d 1)
      (onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d)
        (g : SchwartzSpacetime d) g.property.1)
  let xf : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Ff⟧)) : OSHilbertSpace OS))
  let xg : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from (⟦Fg⟧)) : OSHilbertSpace OS))
  obtain ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
      hsupp₁, hsupp₂, hsupp₃, hsupp₄, horbit⟩ :=
    exists_polarized_measure_positiveTimeOnePoint_local
      (d := d) OS lgc f g
  let ρ : Measure (ℝ × (Fin d → ℝ)) :=
    polarizationControlMeasure_local ν₁ ν₂ ν₃ ν₄
  letI : IsFiniteMeasure ρ := by
    dsimp [ρ, polarizationControlMeasure_local]
    infer_instance
  let s : (ℝ × (Fin d → ℝ)) → ℂ :=
    polarizationControlDensity_local ν₁ ν₂ ν₃ ν₄
  have hs_meas : AEStronglyMeasurable s ρ := by
    simpa [s, ρ] using
      (aestronglyMeasurable_polarizationControlDensity_local
        (ν₁ := ν₁) (ν₂ := ν₂) (ν₃ := ν₃) (ν₄ := ν₄))
  have hs_bound : ∀ᵐ p ∂ρ, ‖s p‖ ≤ 1 := by
    simpa [s, ρ] using
      (ae_norm_polarizationControlDensity_le_one_local
        (ν₁ := ν₁) (ν₂ := ν₂) (ν₃ := ν₃) (ν₄ := ν₄))
  have hsuppρ : ρ (Set.prod (Set.Iio 0) Set.univ) = 0 := by
    simp [ρ, polarizationControlMeasure_local, hsupp₁, hsupp₂, hsupp₃, hsupp₄]
  refine ⟨ρ, inferInstance, hsuppρ, s, hs_meas, 1, by norm_num, hs_bound, ?_⟩
  intro h
  have hν₁_supported :
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁ =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁ := by
    simpa [mul_one] using
      (integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
        (d := d) (μ := ν₁) hsupp₁ h (fun _ => (1 : ℂ)))
  have hν₂_supported :
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂ =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂ := by
    simpa [mul_one] using
      (integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
        (d := d) (μ := ν₂) hsupp₂ h (fun _ => (1 : ℂ)))
  have hν₃_supported :
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃ =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃ := by
    simpa [mul_one] using
      (integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
        (d := d) (μ := ν₃) hsupp₃ h (fun _ => (1 : ℂ)))
  have hν₄_supported :
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄ =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄ := by
    simpa [mul_one] using
      (integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
        (d := d) (μ := ν₄) hsupp₄ h (fun _ => (1 : ℂ)))
  have horbit_h :=
    supported_symbol_formula_of_polarized_measure_positiveTimeOnePoint_local
      (d := d) OS lgc xf xg ν₁ ν₂ ν₃ ν₄ hsupp₁ hsupp₂ hsupp₃ hsupp₄ horbit h
  calc
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        @inner ℂ (OSHilbertSpace OS) _ xf
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xg))
      else 0) * ((h : SchwartzSpacetime d) ξ)
      =
    (1 / 4 : ℂ) *
      ((∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
        (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
        Complex.I * (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
        Complex.I * (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄)) := horbit_h
    _ =
      (1 / 4 : ℂ) *
        ((∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
          (∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
          Complex.I * (∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
          Complex.I * (∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄)) := by
        rw [← hν₁_supported, ← hν₂_supported, ← hν₃_supported, ← hν₄_supported]
    _ =
      ∫ p, (supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p * s p) *
        ↑((1 : ℝ)) ∂ρ := by
          symm
          simpa [s, ρ] using
            (integral_supported_symbol_mul_weight_eq_polarization_local
              (d := d) h ν₁ ν₂ ν₃ ν₄ (fun _ => (1 : ℝ))
              measurable_const (by intro p; norm_num) (by intro p; norm_num))
    _ = ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p * s p ∂ρ := by
          simp

/-- Per-probe diagonal supported-symbol formula for the translated product shell
attached to a real negative-time probe. This makes the four-diagonal spectral
package explicit before any later fixed-measure factorization step. -/
theorem exists_supported_symbol_diagonal_formula_translatedProductShell_negativeProbe_family_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    ∃ (ν₁ : Measure (ℝ × (Fin d → ℝ))) (_hν₁fin : IsFiniteMeasure ν₁)
      (ν₂ : Measure (ℝ × (Fin d → ℝ))) (_hν₂fin : IsFiniteMeasure ν₂)
      (ν₃ : Measure (ℝ × (Fin d → ℝ))) (_hν₃fin : IsFiniteMeasure ν₃)
      (ν₄ : Measure (ℝ × (Fin d → ℝ))) (_hν₄fin : IsFiniteMeasure ν₄)
      (_hsupp₁ : ν₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₂ : ν₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₃ : ν₃ (Set.prod (Set.Iio 0) Set.univ) = 0)
      (_hsupp₄ : ν₄ (Set.prod (Set.Iio 0) Set.univ) = 0),
      ∀ h : positiveTimeCompactSupportSubmodule d,
        ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift φ
                (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
          else 0) * ((h : SchwartzSpacetime d) ξ) =
        (1 / 4 : ℂ) *
          ((∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
            Complex.I *
              (∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
            Complex.I *
              (∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄)) := by
  let ψpt : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime φ,
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg,
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact⟩⟩
  obtain ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
      hsupp₁, hsupp₂, hsupp₃, hsupp₄, horbit⟩ :=
    exists_polarized_measure_positiveTimeOnePoint_local
      (d := d) OS lgc ψpt ψpt
  let ψ : SchwartzSpacetime d := reflectedSchwartzSpacetime φ
  let hφ_pos :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
  let hψ_pos :=
    onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d) ψ hψ_pos_time
  let xφ : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1))
      hφ_pos⟧) : OSHilbertSpace OS))
  let xψ : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
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
            hψ_pos⟧ : OSPreHilbertSpace OS) := by
    simpa [ψ, hφ_pos, hψ_pos_time, hψ_pos] using
      (mk_single_osConj_onePoint_eq_mk_single_reflected_of_real_local
        (d := d) OS φ hφ_real hφ_compact hφ_neg)
  have hx_eq : xφ = xψ := by
    exact congrArg (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS)) hx_eq_pre
  refine ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
    hsupp₁, hsupp₂, hsupp₃, hsupp₄, ?_⟩
  intro h
  letI : IsFiniteMeasure ν₁ := hν₁fin
  letI : IsFiniteMeasure ν₂ := hν₂fin
  letI : IsFiniteMeasure ν₃ := hν₃fin
  letI : IsFiniteMeasure ν₄ := hν₄fin
  have hν₁_supported :
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁ =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁ := by
    simpa [mul_one] using
      (integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
        (d := d) (μ := ν₁) hsupp₁ h (fun _ => (1 : ℂ)))
  have hν₂_supported :
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂ =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂ := by
    simpa [mul_one] using
      (integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
        (d := d) (μ := ν₂) hsupp₂ h (fun _ => (1 : ℂ)))
  have hν₃_supported :
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃ =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃ := by
    simpa [mul_one] using
      (integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
        (d := d) (μ := ν₃) hsupp₃ h (fun _ => (1 : ℂ)))
  have hν₄_supported :
      ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄ =
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄ := by
    simpa [mul_one] using
      (integral_supported_positiveTimeCompactSupportLaplaceSymbol_mul_eq_integral_local
        (d := d) (μ := ν₄) hsupp₄ h (fun _ => (1 : ℂ)))
  have horbit_h :=
    supported_symbol_formula_of_polarized_measure_positiveTimeOnePoint_local
      (d := d) OS lgc xψ xψ ν₁ ν₂ ν₃ ν₄ hsupp₁ hsupp₂ hsupp₃ hsupp₄ horbit h
  calc
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ
            (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
      else 0) * ((h : SchwartzSpacetime d) ξ)
      =
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        @inner ℂ (OSHilbertSpace OS) _ xψ
          ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
            ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xψ))
      else 0) * ((h : SchwartzSpacetime d) ξ) := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        by_cases hξ : 0 < ξ 0
        · have hinner :
            @inner ℂ (OSHilbertSpace OS) _ xψ
              ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
                ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xψ)) =
              osSemigroupGroupMatrixElement (d := d) OS lgc xψ
                (ξ 0) (fun i => ξ (Fin.succ i)) := by
              simpa [osSpatialTranslateHilbert_zero] using
                (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
                  (d := d) OS lgc xψ (0 : Fin d → ℝ)
                  (fun i => ξ (Fin.succ i)) (ξ 0) hξ).symm
          have hmat :
              osSemigroupGroupMatrixElement (d := d) OS lgc xψ
                (ξ 0) (fun i => ξ (Fin.succ i)) =
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift φ
                  (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ)))) := by
            calc
              osSemigroupGroupMatrixElement (d := d) OS lgc xψ
                  (ξ 0) (fun i => ξ (Fin.succ i))
                  =
                osSemigroupGroupMatrixElement (d := d) OS lgc xφ
                  (ξ 0) (fun i => ξ (Fin.succ i)) := by
                    simpa [hx_eq]
              _ =
                OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                  (twoPointProductLift φ
                    (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ)))) := by
                      simpa [xφ, hφ_pos] using
                        (osSemigroupGroupMatrixElement_eq_translatedProductShell_of_real_negative_probe_local
                          (d := d) OS lgc φ hφ_real hφ_compact hφ_neg ξ hξ)
          simp [hξ, hinner, hmat]
        · simp [hξ]
    _ =
      (1 / 4 : ℂ) *
        ((∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
          (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
          Complex.I * (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
          Complex.I * (∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄)) := horbit_h
    _ =
      (1 / 4 : ℂ) *
        ((∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
          (∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
          Complex.I * (∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
          Complex.I * (∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄)) := by
        rw [← hν₁_supported, ← hν₂_supported, ← hν₃_supported, ← hν₄_supported]

/-- Diagonal fixed-measure formula for the translated product shell attached to
a single real negative-time probe.

For a fixed probe `φ`, the whole family of positive-time translated
product-shell pairings against reduced tests `h` is already represented by one
fixed supported finite measure. This is the honest same-vector specialization
underneath the first VI.1 blocker, before any later across-`n` weighting step.
-/
theorem exists_supported_symbol_formula_translatedProductShell_negativeProbe_diagonal_family_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    ∃ (ν : Measure (ℝ × (Fin d → ℝ))) (_hνfin : IsFiniteMeasure ν)
      (_hsupp : ν (Set.prod (Set.Iio 0) Set.univ) = 0),
      ∀ h : positiveTimeCompactSupportSubmodule d,
        ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift φ
                (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
          else 0) * ((h : SchwartzSpacetime d) ξ) =
          ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν := by
  let ψpt : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime φ,
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg,
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) φ hφ_compact⟩⟩
  obtain ⟨ν, hνfin, hsupp, horbit⟩ :=
    exists_supported_symbol_formula_positiveTimeOnePoint_diagonal_family_local
      (d := d) OS lgc ψpt
  let ψ : SchwartzSpacetime d := reflectedSchwartzSpacetime φ
  let hφ_pos :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  let hψ_pos_time := reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg
  let hψ_pos :=
    onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d) ψ hψ_pos_time
  let xφ : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    ⟦PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1))
      hφ_pos⟧) : OSHilbertSpace OS))
  let xψ : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
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
            hψ_pos⟧ : OSPreHilbertSpace OS) := by
    simpa [ψ, hφ_pos, hψ_pos_time, hψ_pos] using
      (mk_single_osConj_onePoint_eq_mk_single_reflected_of_real_local
        (d := d) OS φ hφ_real hφ_compact hφ_neg)
  have hx_eq : xφ = xψ := by
    exact congrArg (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS)) hx_eq_pre
  refine ⟨ν, hνfin, hsupp, ?_⟩
  intro h
  calc
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift φ
            (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
      else 0) * ((h : SchwartzSpacetime d) ξ)
        =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          @inner ℂ (OSHilbertSpace OS) _ xψ
            ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
              ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xψ))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          by_cases hξ : 0 < ξ 0
          · have hinner :
              @inner ℂ (OSHilbertSpace OS) _ xψ
                ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ))
                  ((osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i))) xψ)) =
                osSemigroupGroupMatrixElement (d := d) OS lgc xψ
                  (ξ 0) (fun i => ξ (Fin.succ i)) := by
                simpa [osSpatialTranslateHilbert_zero] using
                  (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
                    (d := d) OS lgc xψ (0 : Fin d → ℝ)
                    (fun i => ξ (Fin.succ i)) (ξ 0) hξ).symm
            have hmat :
                osSemigroupGroupMatrixElement (d := d) OS lgc xψ
                  (ξ 0) (fun i => ξ (Fin.succ i)) =
                OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                  (twoPointProductLift φ
                    (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ)))) := by
              calc
                osSemigroupGroupMatrixElement (d := d) OS lgc xψ
                    (ξ 0) (fun i => ξ (Fin.succ i))
                    =
                  osSemigroupGroupMatrixElement (d := d) OS lgc xφ
                    (ξ 0) (fun i => ξ (Fin.succ i)) := by
                      simpa [hx_eq]
                _ =
                  OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                    (twoPointProductLift φ
                      (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ)))) := by
                        simpa [xφ, hφ_pos] using
                          (osSemigroupGroupMatrixElement_eq_translatedProductShell_of_real_negative_probe_local
                            (d := d) OS lgc φ hφ_real hφ_compact hφ_neg ξ hξ)
            simp [hξ, hinner, hmat]
          · simp [hξ]
    _ = ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν := by
        exact horbit h

/-! The remaining spectral seam now uses direct fixed measures `νₙ`, not
control-measure / density wrappers. The next sequence theorem packages exactly
that diagonal data and nothing heavier. -/

/-- Sequence-level direct fixed-measure formulas for translated product shells
attached to a negative approximate-identity sequence.

For each probe `φ_n`, the entire positive-time translated product-shell family
already has one fixed supported finite measure `ν_n`, independent of the
reduced test `h`. This keeps the support layer in the same diagonal-measure
currency as the surviving line-45 frontier theorem. -/
theorem exists_supported_symbol_formula_translatedProductShell_negativeApproxIdentity_family_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∃ ν_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (ν_seq n)) ∧
      (∀ n, ν_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
      (∀ n (h : positiveTimeCompactSupportSubmodule d),
        ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (φ_seq n)))))
          else 0) * ((h : SchwartzSpacetime d) ξ) =
          ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν_seq n)) := by
  classical
  have h_exists :
      ∀ n,
        ∃ (ν : Measure (ℝ × (Fin d → ℝ))) (_hνfin : IsFiniteMeasure ν)
          (_hsuppν : ν (Set.prod (Set.Iio 0) Set.univ) = 0),
          ∀ h : positiveTimeCompactSupportSubmodule d,
            ∫ ξ : SpacetimeDim d,
              (if hξ : 0 < ξ 0 then
                OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                  (twoPointProductLift (φ_seq n)
                    (SCV.translateSchwartz (-ξ)
                      (reflectedSchwartzSpacetime (φ_seq n)))))
              else 0) * ((h : SchwartzSpacetime d) ξ) =
              ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν := by
    intro n
    exact
      exists_supported_symbol_formula_translatedProductShell_negativeProbe_diagonal_family_local
        (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n)
  choose ν_seq hνfin hsuppν hrepr using h_exists
  exact ⟨ν_seq, hνfin, hsuppν, hrepr⟩

/-- Per-probe direct fixed-measure formulas on the raw spectral-symbol surface.

Each probe-dependent measure `μ_n` already acts on the whole reduced test
family through its own fixed supported finite measure `ν_n`, independent of the
reduced test `h`. This shows that the first live VI.1 blocker is no longer
about extracting a family representation for each `n`; the only missing content
is the across-`n` factorization through one common `ν` with the explicit
reflected-probe weights. -/
theorem exists_perProbe_supported_symbol_formula_family_of_fixed_target_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n)) :
    ∃ ν_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
      (∀ n, IsFiniteMeasure (ν_seq n)) ∧
      (∀ n, ν_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
      (∀ n (h : positiveTimeCompactSupportSubmodule d),
        ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(μ_seq n) =
          ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν_seq n)) := by
  obtain ⟨ν_seq, hνfin, hsuppν, hboundary⟩ :=
    exists_supported_symbol_formula_translatedProductShell_negativeApproxIdentity_family_local
      (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg
  refine ⟨ν_seq, hνfin, hsuppν, ?_⟩
  intro n h
  letI : IsFiniteMeasure (μ_seq n) := _hμfin n
  calc
    ∫ p, positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(μ_seq n)
      =
    ∫ ξ : SpacetimeDim d,
      k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
        (h : SchwartzSpacetime d) ξ := by
          symm
          exact integral_k2DifferenceKernel_real_mul_eq_measure_symbol_local
            (d := d) (μ := μ_seq n) (hsupp := hsupp n) h
    _ =
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift (φ_seq n)
            (SCV.translateSchwartz (-ξ)
              (reflectedSchwartzSpacetime (φ_seq n)))))
      else 0) * ((h : SchwartzSpacetime d) ξ) := by
        letI : IsFiniteMeasure (μ_seq n) := _hμfin n
        exact
          integral_k2DifferenceKernel_real_mul_eq_translatedProductShell_integral_local
            (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n)
            (μ_seq n) (hsupp n) (hμrepr n) h
    _ =
    ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν_seq n) := hboundary n h

/-- Sequence-level reduced boundary pairing formula for the VI.1 regularization
input. Each negative approximate-identity probe contributes a genuine
one-variable difference kernel whose pairing against a positive-time compactly
supported test is exactly the weighted translated product-shell boundary
integral. -/
theorem integral_translatedProductShell_boundary_eq_reduced_differenceKernel_pairing_of_negativeApproxIdentity_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (n : ℕ)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift (φ_seq n)
            (SCV.translateSchwartz (-ξ)
              (reflectedSchwartzSpacetime (φ_seq n)))))
      else 0) * ((h : SchwartzSpacetime d) ξ) =
    ∫ ξ : SpacetimeDim d,
      k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
        (h : SchwartzSpacetime d) ξ := by
  symm
  letI : IsFiniteMeasure (μ_seq n) := _hμfin n
  exact integral_k2DifferenceKernel_real_mul_eq_translatedProductShell_integral_local
    (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n)
    (μ_seq n) (hsupp n) (hμrepr n) h

/-- The honest real Euclidean kernel attached to the canonical `k = 2` probe
witness is uniformly bounded by the same positive-time contraction constant on
both time-ordering sectors. -/
theorem exists_k2TimeParametricKernel_real_bound_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    ∃ C_bd : ℝ, 0 < C_bd ∧
      ∀ x : NPointDomain d 2,
        ‖k2TimeParametricKernel_real_local (d := d) OS lgc φ hφ_compact hφ_neg x‖ ≤ C_bd := by
  let hφ_pos :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  let xφ : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        ⟦PositiveTimeBorchersSequence.single 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d φ : SchwartzNPoint d 1))
          hφ_pos⟧) : OSHilbertSpace OS))
  refine ⟨2 * ‖xφ‖ ^ 2 + 1, by positivity, ?_⟩
  intro x
  by_cases hx : x 0 0 < x 1 0
  · have hpos :=
      k2TimeParametricKernel_norm_le_of_pos_local
        (d := d) OS lgc φ hφ_real hφ_compact hφ_neg x hx
    simp [k2TimeParametricKernel_real_local, hx]
    linarith
  · by_cases hy : x 1 0 < x 0 0
    · have hswap :
          (swapTwoPoint_local x) 0 0 < (swapTwoPoint_local x) 1 0 := by
        simpa [swapTwoPoint_local] using hy
      have hpos :=
        k2TimeParametricKernel_norm_le_of_pos_local
          (d := d) OS lgc φ hφ_real hφ_compact hφ_neg (swapTwoPoint_local x) hswap
      simp [k2TimeParametricKernel_real_local, hx, hy]
      linarith
    · have hnonneg : 0 ≤ 2 * ‖xφ‖ ^ 2 + 1 := by positivity
      simpa [k2TimeParametricKernel_real_local, hx, hy] using hnonneg

/-- The honest piecewise real Euclidean kernel is a.e. strongly measurable. -/
theorem aestronglyMeasurable_k2TimeParametricKernel_real_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    AEStronglyMeasurable
      (k2TimeParametricKernel_real_local (d := d) OS lgc φ hφ_compact hφ_neg) volume := by
  let Spos : Set (NPointDomain d 2) := {x | x 0 0 < x 1 0}
  let Sneg : Set (NPointDomain d 2) := {x | x 1 0 < x 0 0}
  let F : NPointDomain d 2 → ℂ :=
    k2TimeParametricKernel (d := d)
      (k2ProbeWitness_local (d := d) OS lgc φ hφ_compact hφ_neg)
  let Fneg : NPointDomain d 2 → ℂ := fun x => F (swapTwoPoint_local x)
  have htime00_cont : Continuous fun x : NPointDomain d 2 => x 0 0 := by
    simpa using
      ((continuous_apply (0 : Fin (d + 1))).comp (continuous_apply (0 : Fin 2)))
  have htime10_cont : Continuous fun x : NPointDomain d 2 => x 1 0 := by
    simpa using
      ((continuous_apply (0 : Fin (d + 1))).comp (continuous_apply (1 : Fin 2)))
  have htime00 : Measurable fun x : NPointDomain d 2 => x 0 0 := htime00_cont.measurable
  have htime10 : Measurable fun x : NPointDomain d 2 => x 1 0 := htime10_cont.measurable
  have hSpos : MeasurableSet Spos := by
    change MeasurableSet {x : NPointDomain d 2 | x 0 0 < x 1 0}
    exact measurableSet_lt htime00 htime10
  have hSneg : MeasurableSet Sneg := by
    change MeasurableSet {x : NPointDomain d 2 | x 1 0 < x 0 0}
    exact measurableSet_lt htime10 htime00
  have hF : AEStronglyMeasurable (Spos.indicator F) volume := by
    rw [aestronglyMeasurable_indicator_iff hSpos]
    exact (continuousOn_k2TimeParametricKernel_of_pos_local
      (d := d) OS lgc φ hφ_compact hφ_neg).aestronglyMeasurable hSpos
  have hswap_cont : Continuous (swapTwoPoint_local (d := d)) := by
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa [swapTwoPoint_local] using (continuous_apply (1 : Fin 2))
    · simpa [swapTwoPoint_local] using (continuous_apply (0 : Fin 2))
  have hFneg_cont : ContinuousOn Fneg Sneg := by
    have hmaps : Set.MapsTo (swapTwoPoint_local (d := d)) Sneg Spos := by
      intro x hx
      simpa [Spos, Sneg, swapTwoPoint_local] using hx
    simpa [Fneg, F] using
      (continuousOn_k2TimeParametricKernel_of_pos_local
        (d := d) OS lgc φ hφ_compact hφ_neg).comp hswap_cont.continuousOn hmaps
  have hFneg : AEStronglyMeasurable (Sneg.indicator Fneg) volume := by
    rw [aestronglyMeasurable_indicator_iff hSneg]
    exact hFneg_cont.aestronglyMeasurable hSneg
  have hEq :
      k2TimeParametricKernel_real_local (d := d) OS lgc φ hφ_compact hφ_neg =
        fun x => Spos.indicator F x + Sneg.indicator Fneg x := by
    funext x
    by_cases hx : x 0 0 < x 1 0
    · have hnot : ¬ x 1 0 < x 0 0 := by linarith
      simp [k2TimeParametricKernel_real_local, Spos, Sneg, F, Fneg, hx, hnot]
    · by_cases hy : x 1 0 < x 0 0
      · simp [k2TimeParametricKernel_real_local, Spos, Sneg, F, Fneg, hx, hy]
      · simp [k2TimeParametricKernel_real_local, Spos, Sneg, F, Fneg, hx, hy]
  rw [hEq]
  exact hF.add hFneg

/-- The honest piecewise real Euclidean kernel already satisfies the constant-
bound kernel hypotheses needed for the later zero-diagonal CLM packaging. -/
theorem exists_k2TimeParametricKernel_real_constBound_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    ∃ (C_bd : ℝ) (hC : 0 < C_bd),
      AEStronglyMeasurable
        (k2TimeParametricKernel_real_local (d := d) OS lgc φ hφ_compact hφ_neg) volume ∧
      (∀ᵐ x : NPointDomain d 2 ∂volume,
        ‖k2TimeParametricKernel_real_local (d := d) OS lgc φ hφ_compact hφ_neg x‖ ≤ C_bd) := by
  obtain ⟨C_bd, hC, hbound⟩ :=
    exists_k2TimeParametricKernel_real_bound_local
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg
  refine ⟨C_bd, hC,
    aestronglyMeasurable_k2TimeParametricKernel_real_local
      (d := d) OS lgc φ hφ_compact hφ_neg, ?_⟩
  exact Filter.Eventually.of_forall hbound

/-! ### Remaining VI.1 / assembly frontier -/

/-- Constant/polynomial bound package for the honest piecewise real Euclidean
`k = 2` kernel attached to a fixed normalized negative-time probe. This support
theorem remains useful once the final VI.1 boundary-value identification has
chosen the correct limiting probe/kernel data. -/
theorem exists_k2_timeParametric_zeroDiagKernel_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0}) :
    ∃ (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd),
      AEStronglyMeasurable
        (k2TimeParametricKernel_real_local (d := d) OS lgc φ hφ_compact hφ_neg) volume ∧
      (∀ᵐ x : NPointDomain d 2 ∂volume,
        ‖k2TimeParametricKernel_real_local (d := d) OS lgc φ hφ_compact hφ_neg x‖ ≤
          C_bd * (1 + ‖x‖) ^ N) := by
  obtain ⟨C0, hC0, hK_meas, hK_bdd⟩ :=
    exists_k2TimeParametricKernel_real_constBound_package_local
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg
  refine ⟨|C0| + 1, 0, by positivity, hK_meas, ?_⟩
  exact OSReconstruction.ae_const_bound_to_poly_bound (d := d)
    (k2TimeParametricKernel_real_local (d := d) OS lgc φ hφ_compact hφ_neg)
    C0 hK_bdd

/-! ### Descended VI.1 regularizer packages -/

/-- The descended center-shear regularizer built from a normalized negative-time
probe and its reflected companion again has total integral `1`. This is the
natural one-variable normalized center cutoff attached to the VI.1
regularization sequence. -/
theorem integral_twoPointCenterShearDescent_reflected_negativeApproxIdentity_eq_one_local
    (φ : SchwartzSpacetime d)
    (hφ_int : ∫ x : SpacetimeDim d, φ x = 1) :
    ∫ ξ : SpacetimeDim d,
        OSReconstruction.twoPointCenterShearDescent (d := d) φ
          (reflectedSchwartzSpacetime φ) ξ = 1 := by
  rw [OSReconstruction.integral_twoPointCenterShearDescent_eq_mul]
  rw [reflectedSchwartzSpacetime_integral_eq_local, hφ_int]
  simp

/-- Translating the reflected right-slot probe simply translates its descended
one-variable center-shear representative. This is the exact covariance needed
to treat the VI.1 shell family as a translated regularizer on the reduced
positive-time side. -/
theorem twoPointCenterShearDescent_translated_reflected_eq_translated_local
    (φ : SchwartzSpacetime d)
    (ξ : SpacetimeDim d) :
    OSReconstruction.twoPointCenterShearDescent (d := d) φ
        (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ)) =
      SCV.translateSchwartz (-ξ)
        (OSReconstruction.twoPointCenterShearDescent (d := d) φ
          (reflectedSchwartzSpacetime φ)) := by
  simpa using
    (OSReconstruction.twoPointCenterShearDescent_translate_right
      (d := d) φ (reflectedSchwartzSpacetime φ) (-ξ))

/-- Sequence-level package for the descended one-variable VI.1 regularizer.

This records exactly the two facts the remaining sequence-limit theorem needs:
each descended cutoff is normalized, and translating the reflected right-slot
probe translates the descended cutoff in the same way. -/
theorem exists_k2_VI1_descended_center_package_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ))) :
    ∃ χ_seq : ℕ → SchwartzSpacetime d,
      (∀ n,
        χ_seq n =
          OSReconstruction.twoPointCenterDescent
            (twoPointProductLift (φ_seq n) (reflectedSchwartzSpacetime (φ_seq n)))) ∧
      (∀ n x, 0 ≤ (χ_seq n x).re) ∧
      (∀ n x, (χ_seq n x).im = 0) ∧
      (∀ n, ∫ ξ : SpacetimeDim d, χ_seq n ξ = 1) ∧
      (∀ n ξ,
        OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (SCV.translateSchwartz (-ξ)
              (reflectedSchwartzSpacetime (φ_seq n))) =
          SCV.translateSchwartz (-ξ) (χ_seq n)) ∧
      (∀ n,
        tsupport (χ_seq n : SpacetimeDim d → ℂ) ⊆
          Metric.closedBall (0 : SpacetimeDim d) (2 / (n + 1 : ℝ))) := by
  refine ⟨fun n => OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (φ_seq n)), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp [OSReconstruction.twoPointCenterShearDescent_eq]
  · intro n x
    exact
      (OSReconstruction.twoPointCenterShearDescent_re_nonneg_of_re_nonneg
        (d := d) (φ_seq n) (reflectedSchwartzSpacetime (φ_seq n))
        (hφ_real n)
        (by
          intro y
          simpa [reflectedSchwartzSpacetime,
            SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
            hφ_real n (timeReflection d y))
        (hφ_nonneg n)
        (by
          intro y
          simpa [reflectedSchwartzSpacetime,
            SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
            hφ_nonneg n (timeReflection d y))) x
  · intro n x
    exact
      (OSReconstruction.twoPointCenterShearDescent_im_eq_zero_of_im_eq_zero
        (d := d) (φ_seq n) (reflectedSchwartzSpacetime (φ_seq n))
        (hφ_real n)
        (by
          intro y
          simpa [reflectedSchwartzSpacetime,
            SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
            hφ_real n (timeReflection d y))) x
  · intro n
    exact integral_twoPointCenterShearDescent_reflected_negativeApproxIdentity_eq_one_local
      (d := d) (φ_seq n) (hφ_int n)
  · intro n ξ
    exact twoPointCenterShearDescent_translated_reflected_eq_translated_local
      (d := d) (φ_seq n) ξ
  · intro n
    have hrad : 0 ≤ (1 / (n + 1 : ℝ)) := by positivity
    have hreflect_ball :
        tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ) ⊆
          Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) :=
      reflectedSchwartzSpacetime_tsupport_ball (d := d) (φ_seq n) (hφ_ball n)
    have hclosed :=
      (OSReconstruction.twoPointCenterShearDescent_tsupport_subset_closedBall
        (d := d) (φ_seq n) (reflectedSchwartzSpacetime (φ_seq n))
        hrad hrad (hφ_ball n) hreflect_ball)
    have hrad_sum : ((n + 1 : ℝ))⁻¹ + ((n + 1 : ℝ))⁻¹ = 2 / (n + 1 : ℝ) := by
      have hne : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hne]
      ring
    simpa [hrad_sum] using hclosed

/-- The reflected negative approximate-identity probes already determine an
honest smoothing sequence inside the reduced positive-time compact-support
domain: convolving `h` with the reflected probe stays in the domain and
recovers `h` pointwise. This is the direct one-variable VI.1 smoothing surface,
kept separate from the later spectral-weight packaging. -/
theorem exists_reflected_negativeApproxIdentity_positiveTime_convolution_sequence_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ η_seq : ℕ → positiveTimeCompactSupportSubmodule d,
      (∀ n,
        η_seq n =
          positiveTimeCompactSupportConvolution
            (⟨reflectedSchwartzSpacetime (φ_seq n),
              ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                  (hφ_compact n)⟩⟩)
            h) ∧
      (∀ x : SpacetimeDim d,
        Filter.Tendsto
          (fun n => (((η_seq n : positiveTimeCompactSupportSubmodule d) :
            SchwartzSpacetime d) x))
          Filter.atTop
          (nhds (((h : positiveTimeCompactSupportSubmodule d) :
            SchwartzSpacetime d) x))) := by
  refine ⟨fun n =>
    positiveTimeCompactSupportConvolution
      (⟨reflectedSchwartzSpacetime (φ_seq n),
        ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
          reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
            (hφ_compact n)⟩⟩)
      h, ?_, ?_⟩
  · intro n
    rfl
  · intro x
    simpa using
      positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_apply_tendsto_self_local
        (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_ball h x

/-- Sequence-level OS-Hilbert orbit package for the reflected negative
approximate-identity boundary terms.

This is the direct VI.1 companion to the spectral packaging below: for each
probe `φ_n`, the translated product-shell boundary functional against `h` is
already an inner product against a Bochner-integrated two-step OS orbit built
from the reflected probe. -/
theorem exists_reflected_negativeApproxIdentity_boundary_orbit_sequence_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0}) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      ∃ v_seq : ℕ → OSHilbertSpace OS,
        ∀ n,
          let φ := φ_seq n
          let ψ := reflectedSchwartzSpacetime φ
          let xφ : OSHilbertSpace OS :=
            (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single 1
                    (SchwartzNPoint.osConj (d := d) (n := 1)
                      (onePointToFin1CLM d φ : SchwartzNPoint d 1))
                    (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                      (d := d) φ (hφ_compact n) (hφ_neg n))⟧)) : OSHilbertSpace OS))
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift φ (SCV.translateSchwartz (-ξ) ψ)))
            else 0) * ((h : SchwartzSpacetime d) ξ) =
            @inner ℂ (OSHilbertSpace OS) _ xφ (v_seq n) := by
  intro h
  refine ⟨fun n =>
    let φ := φ_seq n
    let ψ := reflectedSchwartzSpacetime φ
    let xψ : OSHilbertSpace OS :=
          (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single 1
                  (onePointToFin1CLM d ψ : SchwartzNPoint d 1)
              (onePointToFin1_tsupport_orderedPositiveTime_vi1_local
                (d := d) ψ
                (reflectedSchwartzSpacetime_tsupport_pos (d := d) φ (hφ_neg n)))⟧)) :
          OSHilbertSpace OS))
    let orbit := fun ξ : SpacetimeDim d =>
      (osSpatialTranslateHilbert (d := d) OS (fun i => ξ (Fin.succ i)))
        ((osTimeShiftHilbertComplex (d := d) OS lgc ((ξ 0 : ℝ) : ℂ)) xψ)
    ∫ ξ : SpacetimeDim d, ((h : SchwartzSpacetime d) ξ) • orbit ξ, ?_⟩
  intro n
  simpa using
    (integral_translatedProductShell_boundary_eq_inner_bochnerIntegral_reflected_orbit_local
      (d := d) OS lgc (φ_seq n) (hφ_compact n) (hφ_neg n) h)

/-- Schwartz spacetime test functions are globally Lipschitz, with a constant
controlled by the first Schwartz seminorm. This is the local VI.1 copy of the
support lemma from `K2BaseStep`, exposed here so the frontier file does not
depend on private declarations from the support layer. -/
theorem schwartz_lipschitz_bound_vi1_local
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

/-- The descended VI.1 regularizers inherit the shrinking-support property from
the original negative approximate identity sequence. Concretely, for every
Euclidean radius `δ > 0`, all sufficiently large descended cutoffs are
supported inside `ball(0, δ)`. -/
theorem eventually_tsupport_descended_center_package_subset_ball_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      tsupport
          ((OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n)) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) δ := by
  have hδ2 : 0 < δ / 2 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ2
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hrad : 0 ≤ (1 / (n + 1 : ℝ)) := by positivity
  have hreflect_ball :
      tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) :=
    reflectedSchwartzSpacetime_tsupport_ball (d := d) (φ_seq n) (hφ_ball n)
  have hclosed :
      tsupport
          ((OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n)) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) ⊆
        Metric.closedBall (0 : SpacetimeDim d) (2 / (n + 1 : ℝ)) := by
    have hclosed_raw :=
      (OSReconstruction.twoPointCenterShearDescent_tsupport_subset_closedBall
        (d := d) (φ_seq n) (reflectedSchwartzSpacetime (φ_seq n))
        hrad hrad (hφ_ball n) hreflect_ball)
    have hrad_sum : ((n + 1 : ℝ))⁻¹ + ((n + 1 : ℝ))⁻¹ = 2 / (n + 1 : ℝ) := by
      have hne : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hne]
      ring
    simpa [hrad_sum] using hclosed_raw
  intro x hx
  have hx_closed : x ∈ Metric.closedBall (0 : SpacetimeDim d) (2 / (n + 1 : ℝ)) :=
    hclosed hx
  have hsmall_half : 1 / (n + 1 : ℝ) < δ / 2 := by
    have hmono : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      have hNle : (N + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ hn
      exact one_div_le_one_div_of_le (by positivity) hNle
    exact lt_of_le_of_lt hmono hN
  have hsmall : 2 / (n + 1 : ℝ) < δ := by
    have hmul := mul_lt_mul_of_pos_left hsmall_half (by positivity : 0 < (2 : ℝ))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  rw [Metric.mem_ball]
  have hx_le : dist x 0 ≤ 2 / (n + 1 : ℝ) := by
    simpa [Metric.mem_closedBall] using hx_closed
  exact lt_of_le_of_lt hx_le hsmall

/-- Quantitative support consequence of the descended-center package: on the
shrinking center support, translating any fixed positive-time compact-support
test changes its value by at most a global Lipschitz constant times the support
radius `2/(n+1)`. This is the translation-error input for the direct VI.1
seminorm route. -/
theorem exists_descended_center_translation_error_bound_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n ξ u,
        u ∈ tsupport
          ((OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n)) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) →
        ‖(((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) (u + ξ) -
            ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ)‖ ≤
          C * (2 / (n + 1 : ℝ)) := by
  obtain ⟨χ_seq, hχ_seq_desc, hχ_seq_nonneg, hχ_seq_real, hχ_seq_int,
      hχ_seq_translate, hχ_seq_ball_closed⟩ :=
    exists_k2_VI1_descended_center_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
  obtain ⟨C, hC_pos, hLip⟩ :=
    schwartz_lipschitz_bound_vi1_local (d := d)
      (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))
  refine ⟨C, hC_pos, ?_⟩
  intro n ξ u hu
  have hu_desc : u ∈ tsupport (χ_seq n : SpacetimeDim d → ℂ) := by
    simpa [hχ_seq_desc n] using hu
  have hu_ball : u ∈ Metric.closedBall (0 : SpacetimeDim d) (2 / (n + 1 : ℝ)) := by
    exact hχ_seq_ball_closed n hu_desc
  have hu_norm : ‖u‖ ≤ 2 / (n + 1 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
  calc
    ‖(((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) (u + ξ) -
        ((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ)‖
      ≤ C * ‖(u + ξ) - ξ‖ := hLip (u + ξ) ξ
    _ = C * ‖u‖ := by
      congr 1
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ ≤ C * (2 / (n + 1 : ℝ)) := by
      gcongr

/-- Quantitative approximate-identity estimate for the descended VI.1
regularizers acting on translated positive-time compact-support tests.

Unlike the later `Tendsto` formulation, this gives an explicit uniform error
bound of size `O(1/(n+1))`, which is the direct VI.1 estimate one would want if
the route is pushed without the intermediate spectral-factorization detour. -/
theorem exists_descended_center_translate_uniform_error_bound_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n ξ,
        dist
            (∫ u : SpacetimeDim d,
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (φ_seq n))) u *
                  (SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ)
            ((h : SchwartzSpacetime d) ξ) ≤
          C * (2 / (n + 1 : ℝ)) := by
  obtain ⟨χ_seq, hχ_seq_desc, hχ_seq_nonneg, hχ_seq_real, hχ_seq_int,
      _hχ_seq_translate, hχ_seq_ball_closed⟩ :=
    exists_k2_VI1_descended_center_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
  obtain ⟨C, hC_pos, hLip⟩ :=
    schwartz_lipschitz_bound_vi1_local (d := d)
      (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))
  refine ⟨C, hC_pos, ?_⟩
  intro n ξ
  have hnorm_int : ∫ u : SpacetimeDim d, ‖χ_seq n u‖ = 1 := by
    have hnorm_re : ∀ u : SpacetimeDim d, ‖χ_seq n u‖ = (χ_seq n u).re := by
      intro u
      rw [← Complex.re_eq_norm.mpr ⟨hχ_seq_nonneg n u, (hχ_seq_real n u).symm⟩]
    simp_rw [hnorm_re]
    rw [show (fun u => (χ_seq n u).re) = (fun u => RCLike.re (χ_seq n u)) from rfl]
    rw [integral_re (SchwartzMap.integrable (χ_seq n))]
    exact congrArg Complex.re (hχ_seq_int n)
  have hbound :
      ∀ u : SpacetimeDim d,
        ‖χ_seq n u *
            ((SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ)‖ ≤
          (C * (2 / (n + 1 : ℝ))) * ‖χ_seq n u‖ := by
    intro u
    by_cases hu : u ∈ tsupport ((χ_seq n : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
    · have hu_ball : u ∈ Metric.closedBall (0 : SpacetimeDim d) (2 / (n + 1 : ℝ)) := by
        exact hχ_seq_ball_closed n hu
      have hu_norm : ‖u‖ ≤ 2 / (n + 1 : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
      have htrans :
          ‖(SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ‖ ≤
            C * (2 / (n + 1 : ℝ)) := by
        calc
          ‖(SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ‖
              =
            ‖(h : SchwartzSpacetime d) (ξ + -u) -
                (h : SchwartzSpacetime d) ξ‖ := by
                  simp [SCV.translateSchwartz_apply]
          _ ≤ C * ‖(ξ + -u) - ξ‖ := hLip (ξ + -u) ξ
          _ = C * ‖u‖ := by
                congr 1
                simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ ≤ C * (2 / (n + 1 : ℝ)) := by
                gcongr
      calc
        ‖χ_seq n u *
            ((SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ)‖
            =
          ‖χ_seq n u‖ *
            ‖(SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ‖ := by
                rw [norm_mul]
        _ ≤ ‖χ_seq n u‖ * (C * (2 / (n + 1 : ℝ))) := by
              gcongr
        _ = (C * (2 / (n + 1 : ℝ))) * ‖χ_seq n u‖ := by ring
    · have hu0 : χ_seq n u = 0 := by
        by_contra hu0
        exact hu (subset_tsupport _ (Function.mem_support.mpr hu0))
      simp [hu0]
  have hψ_cont :
      Continuous fun u : SpacetimeDim d =>
        (SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
          (h : SchwartzSpacetime d) ξ := by
    change Continuous (fun u : SpacetimeDim d =>
      (h : SchwartzSpacetime d) (ξ + -u) - (h : SchwartzSpacetime d) ξ)
    exact (((h : SchwartzSpacetime d).continuous.comp
      (continuous_const.add continuous_neg)).sub continuous_const)
  have hmeas :
      AEStronglyMeasurable
        (fun u : SpacetimeDim d =>
          χ_seq n u *
            ((SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ)) := by
    exact ((SchwartzMap.continuous (χ_seq n)).mul hψ_cont).aestronglyMeasurable
  have hIntDiff :
      Integrable
        (fun u : SpacetimeDim d =>
          χ_seq n u *
            ((SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ)) := by
    refine Integrable.mono'
      (((SchwartzMap.integrable (χ_seq n)).norm).const_mul (C * (2 / (n + 1 : ℝ))))
      hmeas ?_
    exact Filter.Eventually.of_forall hbound
  have hIntProd :
      Integrable
        (fun u : SpacetimeDim d =>
          χ_seq n u * (SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ) := by
    have hEq :
        (fun u : SpacetimeDim d =>
          χ_seq n u * (SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ) =
        fun u =>
          χ_seq n u *
            ((SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ) +
            ((h : SchwartzSpacetime d) ξ) * χ_seq n u := by
      funext u
      ring
    rw [hEq]
    exact hIntDiff.add ((SchwartzMap.integrable (χ_seq n)).const_mul ((h : SchwartzSpacetime d) ξ))
  have hEqInt :
      (∫ u : SpacetimeDim d,
        χ_seq n u * (SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ) -
          (h : SchwartzSpacetime d) ξ =
        ∫ u : SpacetimeDim d,
          χ_seq n u *
            ((SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ) := by
    calc
      (∫ u : SpacetimeDim d,
          χ_seq n u * (SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ) -
            (h : SchwartzSpacetime d) ξ
          =
        (∫ u : SpacetimeDim d,
            χ_seq n u * (SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ) -
          ∫ u : SpacetimeDim d, ((h : SchwartzSpacetime d) ξ) * χ_seq n u := by
              rw [MeasureTheory.integral_const_mul, hχ_seq_int n]
              ring
      _ =
        ∫ u : SpacetimeDim d,
          (χ_seq n u * (SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
            ((h : SchwartzSpacetime d) ξ) * χ_seq n u) := by
              rw [← MeasureTheory.integral_sub hIntProd
                ((SchwartzMap.integrable (χ_seq n)).const_mul ((h : SchwartzSpacetime d) ξ))]
      _ =
        ∫ u : SpacetimeDim d,
          χ_seq n u *
            ((SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ) := by
              congr with u
              ring
  calc
    dist
        (∫ u : SpacetimeDim d,
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n))) u *
              (SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ)
        ((h : SchwartzSpacetime d) ξ)
        =
      ‖(∫ u : SpacetimeDim d,
          χ_seq n u * (SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ) -
        (h : SchwartzSpacetime d) ξ‖ := by
          rw [dist_eq_norm]
          simp [hχ_seq_desc n]
    _ =
      ‖∫ u : SpacetimeDim d,
          χ_seq n u *
            ((SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ)‖ := by
            rw [hEqInt]
    _ ≤
      ∫ u : SpacetimeDim d,
        ‖χ_seq n u *
            ((SCV.translateSchwartz (-u) (h : SchwartzSpacetime d)) ξ -
              (h : SchwartzSpacetime d) ξ)‖ := by
            exact norm_integral_le_integral_norm _
    _ ≤
      ∫ u : SpacetimeDim d, (C * (2 / (n + 1 : ℝ))) * ‖χ_seq n u‖ := by
            apply MeasureTheory.integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
            · exact (((SchwartzMap.integrable (χ_seq n)).norm).const_mul
                (C * (2 / (n + 1 : ℝ))))
            · exact Filter.Eventually.of_forall hbound
    _ = (C * (2 / (n + 1 : ℝ))) * ∫ u : SpacetimeDim d, ‖χ_seq n u‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ = C * (2 / (n + 1 : ℝ)) := by
          simp [hnorm_int]

/-- A descended center-shear regularization sequence with real nonnegative mass
`1` and shrinking support is an honest approximate identity on the reduced
one-variable side. The support radius is `2/(n+1)` rather than `1/(n+1)`, but
the same continuity argument goes through unchanged. -/
theorem descended_center_package_integral_tendsto_of_continuousAt_zero_local
    (χ_seq : ℕ → SchwartzSpacetime d)
    (hχ_nonneg : ∀ n x, 0 ≤ (χ_seq n x).re)
    (hχ_real : ∀ n x, (χ_seq n x).im = 0)
    (hχ_int : ∀ n, ∫ x : SpacetimeDim d, χ_seq n x = 1)
    (hχ_support : ∀ n, tsupport (χ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.closedBall (0 : SpacetimeDim d) (2 / (n + 1 : ℝ)))
    {ψ : SpacetimeDim d → ℂ}
    (hψ_cont : Continuous ψ) :
    Filter.Tendsto (fun n => ∫ x : SpacetimeDim d, χ_seq n x * ψ x)
      Filter.atTop (nhds (ψ 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hψ_cont0 : ContinuousAt ψ 0 := hψ_cont.continuousAt
  rw [Metric.continuousAt_iff] at hψ_cont0
  obtain ⟨δ, hδpos, hδ⟩ := hψ_cont0 (ε / 2) hε2
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 2 / (n + 1 : ℝ) < δ := by
    have hδ2 : 0 < δ / 2 := by linarith
    rcases exists_nat_one_div_lt hδ2 with ⟨N, hN⟩
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hsmall_half : 1 / (n + 1 : ℝ) < δ / 2 := by
      have hmono : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
        have hNle : (N + 1 : ℝ) ≤ n + 1 := by
          exact_mod_cast Nat.succ_le_succ hn
        exact one_div_le_one_div_of_le (by positivity) hNle
      exact lt_of_le_of_lt hmono hN
    have hmul := mul_lt_mul_of_pos_left hsmall_half (by positivity : 0 < (2 : ℝ))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  filter_upwards [hsmall] with n hn
  have hnorm_int : ∫ x : SpacetimeDim d, ‖χ_seq n x‖ = 1 := by
    have hnorm_re : ∀ x : SpacetimeDim d, ‖χ_seq n x‖ = (χ_seq n x).re := by
      intro x
      rw [← Complex.re_eq_norm.mpr ⟨hχ_nonneg n x, (hχ_real n x).symm⟩]
    simp_rw [hnorm_re]
    rw [show (fun x => (χ_seq n x).re) = (fun x => RCLike.re (χ_seq n x)) from rfl]
    rw [integral_re (SchwartzMap.integrable (χ_seq n))]
    exact congrArg Complex.re (hχ_int n)
  have hbound : ∀ x : SpacetimeDim d,
      ‖χ_seq n x * (ψ x - ψ 0)‖ ≤ (ε / 2) * ‖χ_seq n x‖ := by
    intro x
    by_cases hx : x ∈ tsupport (χ_seq n : SpacetimeDim d → ℂ)
    · have hxball : x ∈ Metric.closedBall (0 : SpacetimeDim d) (2 / (n + 1 : ℝ)) := hχ_support n hx
      have hxdist : dist x 0 < δ := by
        have : dist x 0 ≤ 2 / (n + 1 : ℝ) := by
          simpa [Metric.mem_closedBall] using hxball
        exact lt_of_le_of_lt this hn
      have hψx : ‖ψ x - ψ 0‖ < ε / 2 := by
        simpa [dist_eq_norm] using hδ hxdist
      calc
        ‖χ_seq n x * (ψ x - ψ 0)‖ = ‖χ_seq n x‖ * ‖ψ x - ψ 0‖ := by
          rw [norm_mul]
        _ ≤ ‖χ_seq n x‖ * (ε / 2) := by
          gcongr
        _ = (ε / 2) * ‖χ_seq n x‖ := by ring
    · have hx0 : χ_seq n x = 0 := by
        by_contra hx0
        exact hx (subset_tsupport _ (Function.mem_support.mpr hx0))
      simp [hx0]
  have hmeas : AEStronglyMeasurable (fun x => χ_seq n x * (ψ x - ψ 0)) := by
    exact ((SchwartzMap.continuous (χ_seq n)).mul
      (hψ_cont.sub continuous_const)).aestronglyMeasurable
  have hIntDiff : Integrable (fun x : SpacetimeDim d => χ_seq n x * (ψ x - ψ 0)) := by
    refine Integrable.mono' (((SchwartzMap.integrable (χ_seq n)).norm).const_mul (ε / 2)) hmeas ?_
    exact Filter.Eventually.of_forall hbound
  have hIntProd : Integrable (fun x : SpacetimeDim d => χ_seq n x * ψ x) := by
    have hEq : (fun x : SpacetimeDim d => χ_seq n x * ψ x) =
        fun x => χ_seq n x * (ψ x - ψ 0) + (ψ 0) * χ_seq n x := by
      funext x
      ring
    rw [hEq]
    exact hIntDiff.add ((SchwartzMap.integrable (χ_seq n)).const_mul (ψ 0))
  have hEqInt :
      (∫ x : SpacetimeDim d, χ_seq n x * ψ x) - ψ 0 =
        ∫ x : SpacetimeDim d, χ_seq n x * (ψ x - ψ 0) := by
    calc
      (∫ x : SpacetimeDim d, χ_seq n x * ψ x) - ψ 0
          = (∫ x : SpacetimeDim d, χ_seq n x * ψ x) - ∫ x : SpacetimeDim d, (ψ 0) * χ_seq n x := by
              rw [MeasureTheory.integral_const_mul, hχ_int n]
              ring
      _ = ∫ x : SpacetimeDim d, ((χ_seq n x * ψ x) - (ψ 0) * χ_seq n x) := by
            rw [← MeasureTheory.integral_sub hIntProd ((SchwartzMap.integrable (χ_seq n)).const_mul (ψ 0))]
      _ = ∫ x : SpacetimeDim d, χ_seq n x * (ψ x - ψ 0) := by
            congr with x
            ring
  calc
    dist (∫ x : SpacetimeDim d, χ_seq n x * ψ x) (ψ 0)
        = ‖(∫ x : SpacetimeDim d, χ_seq n x * ψ x) - ψ 0‖ := by
            rw [dist_eq_norm]
    _ = ‖∫ x : SpacetimeDim d, χ_seq n x * (ψ x - ψ 0)‖ := by
          rw [hEqInt]
    _ ≤ ∫ x : SpacetimeDim d, ‖χ_seq n x * (ψ x - ψ 0)‖ := by
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ x : SpacetimeDim d, (ε / 2) * ‖χ_seq n x‖ := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact (((SchwartzMap.integrable (χ_seq n)).norm).const_mul (ε / 2))
          · exact Filter.Eventually.of_forall hbound
    _ = (ε / 2) * ∫ x : SpacetimeDim d, ‖χ_seq n x‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ = ε / 2 := by
          simp [hnorm_int]
    _ < ε := by
          linarith

/-- A positive-time compactly supported reduced test is uniformly separated from
the time-zero boundary by a strictly positive margin. -/
theorem exists_positive_time_margin_of_mem_positiveTimeCompactSupport_local
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ δ : ℝ, 0 < δ ∧
      tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) ⊆
        {x : SpacetimeDim d | δ < x 0} := by
  by_cases hempty :
      tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) = ∅
  · refine ⟨1, by positivity, ?_⟩
    simp [hempty]
  · let S := tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ)
    have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr (by simpa [S] using hempty)
    have hS_compact : IsCompact S := by
      simpa [S] using h.property.2.isCompact
    obtain ⟨x₀, hx₀_mem, hx₀_min⟩ :=
      hS_compact.exists_isMinOn hS_nonempty (continuous_apply (0 : Fin (d + 1))).continuousOn
    have hx₀_pos : 0 < x₀ 0 := by
      simpa [S] using h.property.1 hx₀_mem
    refine ⟨x₀ 0 / 2, by linarith, ?_⟩
    intro x hx
    have hxmin : x₀ 0 ≤ x 0 := isMinOn_iff.mp hx₀_min x hx
    show x₀ 0 / 2 < x 0
    linarith

/-- If a Schwartz test is supported in a small Euclidean ball and we translate
it by a vector whose time coordinate is larger than the ball radius, the
translated support lies entirely in the positive-time half-space. -/
theorem translateSchwartz_tsupport_subset_positive_of_ball_and_margin_local
    (χ : SchwartzSpacetime d)
    {δ : ℝ} (hδ : 0 < δ)
    (hχ_ball : tsupport (χ : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) δ)
    {ξ : SpacetimeDim d} (hξ : δ < ξ 0) :
    tsupport ((SCV.translateSchwartz (-ξ) χ : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | 0 < x 0} := by
  intro x hx
  have hx_pre :
      x + (-ξ) ∈ tsupport (χ : SpacetimeDim d → ℂ) := by
    exact tsupport_comp_subset_preimage (χ : SpacetimeDim d → ℂ)
      (f := fun y : SpacetimeDim d => y + (-ξ))
      (Homeomorph.addRight (-ξ)).continuous hx
  have hx_ball : x + (-ξ) ∈ Metric.ball (0 : SpacetimeDim d) δ := hχ_ball hx_pre
  have hnorm : ‖x + (-ξ)‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx_ball
  have hcoord :
      |x 0 - ξ 0| < δ := by
    have hcoord_norm : ‖(x + (-ξ)) 0‖ < δ :=
      lt_of_le_of_lt (norm_le_pi_norm _ 0) hnorm
    simpa [Real.norm_eq_abs, sub_eq_add_neg] using hcoord_norm
  have hlower : ξ 0 - δ < x 0 := by
    have hleft : -δ < x 0 - ξ 0 := (abs_lt.mp hcoord).1
    linarith
  have hmargin : 0 < ξ 0 - δ := by
    linarith
  show 0 < x 0
  linarith

/-- For every positive-time compact-support test `h`, the translated descended
VI.1 regularizers are eventually positive-time supported over the whole support
of `h`. This is the support-side input needed to turn the descended one-variable
cutoffs into honest reduced positive-time test functions in the remaining VI.1
limit argument. -/
theorem eventually_translated_descended_center_package_subset_positive_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ ξ ∈ tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ),
        tsupport
            ((SCV.translateSchwartz (-ξ)
                (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                  (reflectedSchwartzSpacetime (φ_seq n))) : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ) ⊆
          {x : SpacetimeDim d | 0 < x 0} := by
  obtain ⟨δ, hδ_pos, hmargin⟩ :=
    exists_positive_time_margin_of_mem_positiveTimeCompactSupport_local (d := d) h
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        tsupport
            ((OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (φ_seq n)) : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ) ⊆
          Metric.ball (0 : SpacetimeDim d) δ :=
    eventually_tsupport_descended_center_package_subset_ball_local
      (d := d) φ_seq hφ_ball hδ_pos
  filter_upwards [hevent] with n hn ξ hξ
  exact translateSchwartz_tsupport_subset_positive_of_ball_and_margin_local
    (d := d)
    (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (φ_seq n)))
    hδ_pos hn (hmargin hξ)

/-- The descended VI.1 regularizers form an honest approximate identity on the
reduced one-variable Schwartz space: pairing them against any continuous test
function recovers the value at the origin. -/
theorem descended_center_approxIdentity_integral_tendsto_of_continuousAt_zero_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    {ψ : SpacetimeDim d → ℂ}
    (hψ_cont : Continuous ψ) :
    Filter.Tendsto
      (fun n =>
        ∫ ξ : SpacetimeDim d,
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n))) ξ * ψ ξ)
      Filter.atTop
      (𝓝 (ψ 0)) := by
  obtain ⟨χ_seq, hχ_seq_desc, hχ_seq_nonneg, hχ_seq_real, hχ_seq_int, _,
      _hχ_seq_ball_closed⟩ :=
    exists_k2_VI1_descended_center_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
  have hrewrite :
      (fun n =>
        ∫ ξ : SpacetimeDim d,
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n))) ξ * ψ ξ) =
      (fun n => ∫ ξ : SpacetimeDim d, χ_seq n ξ * ψ ξ) := by
    funext n
    simp [hχ_seq_desc n]
  rw [hrewrite]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hψ_cont0 : ContinuousAt ψ 0 := hψ_cont.continuousAt
  rw [Metric.continuousAt_iff] at hψ_cont0
  obtain ⟨δ, hδpos, hδ⟩ := hψ_cont0 (ε / 2) hε2
  have hsmall :
      ∀ᶠ n : ℕ in Filter.atTop,
        tsupport ((χ_seq n : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          Metric.ball (0 : SpacetimeDim d) δ := by
    have hsmall_raw :=
      eventually_tsupport_descended_center_package_subset_ball_local
        (d := d) φ_seq hφ_ball hδpos
    filter_upwards [hsmall_raw] with n hn
    simpa [hχ_seq_desc n] using hn
  filter_upwards [hsmall] with n hn
  have hnorm_int : ∫ x : SpacetimeDim d, ‖χ_seq n x‖ = 1 := by
    have hnorm_re : ∀ x : SpacetimeDim d, ‖χ_seq n x‖ = (χ_seq n x).re := by
      intro x
      rw [← Complex.re_eq_norm.mpr ⟨hχ_seq_nonneg n x, (hχ_seq_real n x).symm⟩]
    simp_rw [hnorm_re]
    rw [show (fun x => (χ_seq n x).re) = (fun x => RCLike.re (χ_seq n x)) from rfl]
    rw [integral_re (SchwartzMap.integrable (χ_seq n))]
    exact congrArg Complex.re (hχ_seq_int n)
  have hbound :
      ∀ x : SpacetimeDim d,
        ‖χ_seq n x * (ψ x - ψ 0)‖ ≤ (ε / 2) * ‖χ_seq n x‖ := by
    intro x
    by_cases hx : x ∈ tsupport ((χ_seq n : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
    · have hxball : x ∈ Metric.ball (0 : SpacetimeDim d) δ := hn hx
      have hxdist : dist x 0 < δ := by
        simpa [Metric.mem_ball] using hxball
      have hψx : ‖ψ x - ψ 0‖ < ε / 2 := by
        simpa [dist_eq_norm] using hδ hxdist
      calc
        ‖χ_seq n x * (ψ x - ψ 0)‖ = ‖χ_seq n x‖ * ‖ψ x - ψ 0‖ := by
          rw [norm_mul]
        _ ≤ ‖χ_seq n x‖ * (ε / 2) := by
          gcongr
        _ = (ε / 2) * ‖χ_seq n x‖ := by ring
    · have hx0 : χ_seq n x = 0 := by
        by_contra hx0
        exact hx (subset_tsupport _ (Function.mem_support.mpr hx0))
      simp [hx0]
  have hmeas : AEStronglyMeasurable (fun x => χ_seq n x * (ψ x - ψ 0)) := by
    exact ((SchwartzMap.continuous (χ_seq n)).mul
      (hψ_cont.sub continuous_const)).aestronglyMeasurable
  have hIntDiff : Integrable (fun x : SpacetimeDim d => χ_seq n x * (ψ x - ψ 0)) := by
    refine Integrable.mono' (((SchwartzMap.integrable (χ_seq n)).norm).const_mul (ε / 2)) hmeas ?_
    exact Filter.Eventually.of_forall hbound
  have hIntProd : Integrable (fun x : SpacetimeDim d => χ_seq n x * ψ x) := by
    have hEq : (fun x : SpacetimeDim d => χ_seq n x * ψ x) =
        fun x => χ_seq n x * (ψ x - ψ 0) + (ψ 0) * χ_seq n x := by
      funext x
      ring
    rw [hEq]
    exact hIntDiff.add ((SchwartzMap.integrable (χ_seq n)).const_mul (ψ 0))
  have hEqInt :
      (∫ x : SpacetimeDim d, χ_seq n x * ψ x) - ψ 0 =
        ∫ x : SpacetimeDim d, χ_seq n x * (ψ x - ψ 0) := by
    calc
      (∫ x : SpacetimeDim d, χ_seq n x * ψ x) - ψ 0
          = (∫ x : SpacetimeDim d, χ_seq n x * ψ x) -
              ∫ x : SpacetimeDim d, (ψ 0) * χ_seq n x := by
                rw [MeasureTheory.integral_const_mul, hχ_seq_int n]
                ring
      _ = ∫ x : SpacetimeDim d, ((χ_seq n x * ψ x) - (ψ 0) * χ_seq n x) := by
            rw [← MeasureTheory.integral_sub hIntProd
              ((SchwartzMap.integrable (χ_seq n)).const_mul (ψ 0))]
      _ = ∫ x : SpacetimeDim d, χ_seq n x * (ψ x - ψ 0) := by
            congr with x
            ring
  calc
    dist (∫ x : SpacetimeDim d, χ_seq n x * ψ x) (ψ 0)
        = ‖(∫ x : SpacetimeDim d, χ_seq n x * ψ x) - ψ 0‖ := by
            rw [dist_eq_norm]
    _ = ‖∫ x : SpacetimeDim d, χ_seq n x * (ψ x - ψ 0)‖ := by
          rw [hEqInt]
    _ ≤ ∫ x : SpacetimeDim d, ‖χ_seq n x * (ψ x - ψ 0)‖ := by
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ x : SpacetimeDim d, (ε / 2) * ‖χ_seq n x‖ := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact (((SchwartzMap.integrable (χ_seq n)).norm).const_mul (ε / 2))
          · exact Filter.Eventually.of_forall hbound
    _ = (ε / 2) * ∫ x : SpacetimeDim d, ‖χ_seq n x‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ = ε / 2 := by
          simp [hnorm_int]
    _ < ε := by
          linarith

/-- The descended VI.1 regularizers act as an honest approximate identity on
translated Schwartz tests, pointwise at every spacetime point. This is the
reduced one-variable analogue of the reflected-probe convolution regularization
lemma from `K2BaseStep`, but phrased directly for the descended center
sequence. -/
theorem descended_center_translate_tendsto_self_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (g : SchwartzSpacetime d)
    (x : SpacetimeDim d) :
    Filter.Tendsto
      (fun n =>
        ∫ ξ : SpacetimeDim d,
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n))) ξ *
              (SCV.translateSchwartz (-ξ) g) x)
      Filter.atTop
      (𝓝 (g x)) := by
  let ψ : SpacetimeDim d → ℂ := fun ξ => (SCV.translateSchwartz (-ξ) g) x
  have hψ_cont : Continuous ψ := by
    change Continuous (fun ξ : SpacetimeDim d => g (x + -ξ))
    exact g.continuous.comp (continuous_const.add continuous_neg)
  have hmain :=
    descended_center_approxIdentity_integral_tendsto_of_continuousAt_zero_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball hψ_cont
  simpa [ψ, SCV.translateSchwartz_apply] using hmain

/-- Translating a normalized center cutoff preserves its total integral. -/
theorem integral_translateSchwartz_eq_one_of_integral_eq_one_local
    (χ : SchwartzSpacetime d)
    (hχ : ∫ x : SpacetimeDim d, χ x = 1)
    (ξ : SpacetimeDim d) :
    ∫ u : SpacetimeDim d, SCV.translateSchwartz (-ξ) χ u = 1 := by
  have htrans :
      ∫ u : SpacetimeDim d, SCV.translateSchwartz (-ξ) χ u =
        ∫ u : SpacetimeDim d, χ u := by
    have htrans_raw :=
      congrArg (fun L : SchwartzSpacetime d →L[ℂ] ℂ => L χ)
      (OSReconstruction.integralCLM_translation_invariant (m := d + 1) (-ξ))
    simpa [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply] using htrans_raw
  exact htrans.trans hχ

/-- Normalized-center independence on translated descended VI.1 regularizers. -/
theorem schwingerDifferencePositiveCLM_eq_of_translated_descended_center_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d)
    (hχ : ∫ x : SpacetimeDim d, χ x = 1)
    (ξ : SpacetimeDim d)
    (h : positiveTimeCompactSupportSubmodule d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift (SCV.translateSchwartz (-ξ) χ)
          (h : SchwartzSpacetime d))) =
      (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h := by
  have hχ_trans :
      ∫ u : SpacetimeDim d, SCV.translateSchwartz (-ξ) χ u = 1 :=
    integral_translateSchwartz_eq_one_of_integral_eq_one_local
      (d := d) χ hχ ξ
  exact schwingerDifferencePositiveCLM_eq_of_normalized_center_local
    (d := d) OS χ₀ hχ₀ (SCV.translateSchwartz (-ξ) χ) hχ_trans h

/-- The descended VI.1 center package may be used as a normalized center test in
the reduced positive-time Schwinger functional, uniformly in the translation
parameter. This packages the normalization part of the remaining VI.1 argument
so the first `sorry` only has to prove the actual boundary-limit comparison. -/
theorem schwingerDifferencePositiveCLM_eq_of_descended_center_package_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (n : ℕ) (ξ : SpacetimeDim d)
    (h : positiveTimeCompactSupportSubmodule d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift
          (SCV.translateSchwartz (-ξ)
            (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n))))
          (h : SchwartzSpacetime d))) =
      (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h := by
  obtain ⟨χ_seq, hχ_seq_desc, hχ_seq_nonneg, hχ_seq_real, hχ_seq_int,
      hχ_seq_translate, hχ_seq_ball⟩ :=
    exists_k2_VI1_descended_center_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
  simpa [hχ_seq_desc n] using
    schwingerDifferencePositiveCLM_eq_of_translated_descended_center_local
      (d := d) OS χ₀ hχ₀ (χ_seq n) (hχ_seq_int n) ξ h

/-- Honest OS II VI.1 boundary-limit theorem for the `k = 2` route.

This is the sequence-level statement the OS paper actually uses: starting from
a shrinking normalized negative approximate identity and the per-probe
positive-time shell package, the regularized translated product-shell boundary
functionals converge to the reduced Schwinger positive CLM. This replaces the
earlier too-strong fixed-probe equality surface. -/
theorem integral_translatedProductShell_boundary_eq_probe_pairing_descended_center_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
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
            else 0) * ((h : SchwartzSpacetime d) ξ))
    (n : ℕ) (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
      (if hξ : 0 < ξ 0 then
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift (φ_seq n)
            (SCV.translateSchwartz (-ξ)
              (reflectedSchwartzSpacetime (φ_seq n)))))
      else 0) * ((h : SchwartzSpacetime d) ξ) =
    ∫ x : NPointDomain d 2,
      k2TimeParametricKernel (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
        twoPointDifferenceLift
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n)))
          (h : SchwartzSpacetime d) x := by
  obtain ⟨χ_seq, hχ_seq_desc, hχ_seq_nonneg, hχ_seq_real, hχ_seq_int,
      hχ_seq_translate, hχ_seq_ball⟩ :=
    exists_k2_VI1_descended_center_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
  have hχn_int :
      ∫ u : SpacetimeDim d,
        OSReconstruction.twoPointCenterDescent
          (twoPointProductLift (φ_seq n) (reflectedSchwartzSpacetime (φ_seq n))) u = 1 := by
    simpa [hχ_seq_desc n] using hχ_seq_int n
  simpa [hχn_int, hχ_seq_desc n, one_mul] using
    (hpair n (χ_seq n) h).symm

/-- On the descended normalized-center shell, the reduced one-variable pairing
and the original probe pairing agree exactly. This packages the shell
bookkeeping needed in the first VI.1 limit theorem, leaving only the genuine
boundary-limit argument there. -/
theorem integral_k2DifferenceKernel_real_eq_probe_pairing_descended_center_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
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
            else 0) * ((h : SchwartzSpacetime d) ξ))
    (n : ℕ)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
      k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
        (h : SchwartzSpacetime d) ξ =
    ∫ x : NPointDomain d 2,
      k2TimeParametricKernel (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
        twoPointDifferenceLift
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n)))
          (h : SchwartzSpacetime d) x := by
  calc
    ∫ ξ : SpacetimeDim d,
      k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
        (h : SchwartzSpacetime d) ξ
      =
        ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (φ_seq n)))))
          else 0) * ((h : SchwartzSpacetime d) ξ) := by
            symm
            exact
              integral_translatedProductShell_boundary_eq_reduced_differenceKernel_pairing_of_negativeApproxIdentity_local
                (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg μ_seq _hμfin hsupp hμrepr n h
    _ =
    ∫ x : NPointDomain d 2,
      k2TimeParametricKernel (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
        twoPointDifferenceLift
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n)))
          (h : SchwartzSpacetime d) x := by
      simpa using
      integral_translatedProductShell_boundary_eq_probe_pairing_descended_center_local
        (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
        hφ_compact hφ_neg hpair n h

/-- The descended-center shell bookkeeping may be collapsed to any fixed
normalized center test.

Indeed, the probe pairing already depends on the center variable only through
its total integral, while the descended shell and the fixed normalized center
both have integral `1`. So the reduced one-variable pairing is exactly the same
as pairing the probe witness against the single fixed shell
`twoPointDifferenceLift χ₀ h`. This is the sharper direct OS surface for the
remaining VI.1 convergence theorem. -/
theorem integral_k2DifferenceKernel_real_eq_probe_pairing_fixed_normalized_center_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
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
            else 0) * ((h : SchwartzSpacetime d) ξ))
    (n : ℕ)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∫ ξ : SpacetimeDim d,
      k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
        (h : SchwartzSpacetime d) ξ =
    ∫ x : NPointDomain d 2,
      k2TimeParametricKernel (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
        twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
  have hred_to_boundary :
      ∫ ξ : SpacetimeDim d,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
          (h : SchwartzSpacetime d) ξ =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift (φ_seq n)
              (SCV.translateSchwartz (-ξ)
                (reflectedSchwartzSpacetime (φ_seq n)))))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
    calc
      ∫ ξ : SpacetimeDim d,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
          (h : SchwartzSpacetime d) ξ
        =
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
          twoPointDifferenceLift
            (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n)))
            (h : SchwartzSpacetime d) x := by
          exact integral_k2DifferenceKernel_real_eq_probe_pairing_descended_center_local
            (d := d) OS lgc φ_seq hφ_nonneg hφ_int hφ_ball hφ_real hφ_compact hφ_neg
            μ_seq _hμfin hsupp hμrepr hpair n h
      _ =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift (φ_seq n)
              (SCV.translateSchwartz (-ξ)
                (reflectedSchwartzSpacetime (φ_seq n)))))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
          symm
          exact integral_translatedProductShell_boundary_eq_probe_pairing_descended_center_local
            (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
            hφ_compact hφ_neg hpair n h
  have hfixed_to_boundary :
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
          twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x =
      ∫ ξ : SpacetimeDim d,
        (if hξ : 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift (φ_seq n)
              (SCV.translateSchwartz (-ξ)
                (reflectedSchwartzSpacetime (φ_seq n)))))
        else 0) * ((h : SchwartzSpacetime d) ξ) := by
    simpa [hχ₀, one_mul] using hpair n χ₀ h
  exact hred_to_boundary.trans hfixed_to_boundary.symm

/-- Pre-limit descended-center package for the reduced `k = 2` VI.1 theorem.

This packages exactly the already-proved data sitting underneath the first
remaining `sorry`:
- the descended normalized center sequence `χ_n`,
- identification of the reduced one-variable kernel pairing with the descended
  probe pairing,
- and the exact Schwinger target value on the same descended shell.

With this package available, the remaining open theorem is honestly just the
VI.1 convergence step on the descended shell. -/
theorem exists_k2_VI1_descended_reduced_pairing_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
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
            else 0) * ((h : SchwartzSpacetime d) ξ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      ∃ χ_seq : ℕ → SchwartzSpacetime d,
        (∀ n,
          ∫ ξ : SpacetimeDim d,
            k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
              (h : SchwartzSpacetime d) ξ =
          ∫ x : NPointDomain d 2,
            k2TimeParametricKernel (d := d)
                (k2ProbeWitness_local (d := d) OS lgc
                  (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
              twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x) ∧
        (∀ n,
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d))) =
            (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
              (d := d) OS χ₀) h) := by
  intro h
  obtain ⟨χ_seq, hχ_seq_desc, hχ_seq_nonneg, hχ_seq_real, hχ_seq_int,
      _hχ_seq_translate, _hχ_seq_ball⟩ :=
    exists_k2_VI1_descended_center_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
  refine ⟨χ_seq, ?_, ?_⟩
  · intro n
    simpa [hχ_seq_desc n] using
      integral_k2DifferenceKernel_real_eq_probe_pairing_descended_center_local
        (d := d) OS lgc φ_seq hφ_nonneg hφ_int hφ_ball hφ_real hφ_compact hφ_neg
        μ_seq _hμfin hsupp hμrepr hpair n h
  · intro n
    exact schwingerDifferencePositiveCLM_eq_of_normalized_center_local
      (d := d) OS χ₀ hχ₀ (χ_seq n) (hχ_seq_int n) h

/-- Pre-limit descended-center package on the explicit spectral-symbol surface.

This strengthens the previous reduced pairing package by rewriting the same
descended probe pairing directly as an integral of the concrete Laplace-Fourier
test symbol attached to `h` against the probe-dependent measure `μ_n`. With
this package available, the first remaining VI.1 blocker is transparently a
fixed-measure factorization problem for `μ_n`, not a hidden kernel/Fubini
problem. -/
theorem exists_k2_VI1_descended_measure_symbol_package_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
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
            else 0) * ((h : SchwartzSpacetime d) ξ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      ∃ χ_seq : ℕ → SchwartzSpacetime d,
        (∀ n,
          ∫ x : NPointDomain d 2,
            k2TimeParametricKernel (d := d)
                (k2ProbeWitness_local (d := d) OS lgc
                  (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
              twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x =
          ∫ p : ℝ × (Fin d → ℝ),
            positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(μ_seq n)) ∧
        (∀ n,
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d))) =
            (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
              (d := d) OS χ₀) h) := by
  intro h
  obtain ⟨χ_seq, hpair_probe, htarget_descended⟩ :=
    exists_k2_VI1_descended_reduced_pairing_package_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball μ_seq _hμfin hsupp hμrepr hpair h
  refine ⟨χ_seq, ?_, htarget_descended⟩
  intro n
  calc
    ∫ x : NPointDomain d 2,
      k2TimeParametricKernel (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
        twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x
        =
      ∫ ξ : SpacetimeDim d,
        k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
          (h : SchwartzSpacetime d) ξ := by
            symm
            exact hpair_probe n
    _ =
      ∫ p : ℝ × (Fin d → ℝ),
        positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(μ_seq n) := by
          letI : IsFiniteMeasure (μ_seq n) := _hμfin n
          exact integral_k2DifferenceKernel_real_mul_eq_measure_symbol_local
            (d := d) (μ := μ_seq n) (hsupp := hsupp n) h

/-- Per-probe diagonal supported-symbol package on the descended-shell surface.

This isolates the already-provable four-diagonal extraction for each fixed probe
`φ_n`: after descending to the normalized center shell, each probe pairing is
already a polarization combination of four supported symbol integrals. The
remaining first VI.1 blocker is therefore only the fixed-measure factorization
problem across `n`, not the per-probe diagonalization. -/
theorem exists_perProbe_diagonal_supported_symbol_sequences_of_probe_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n)) :
    ∀ (h : positiveTimeCompactSupportSubmodule d)
      (χ_seq : ℕ → SchwartzSpacetime d),
      (∀ n,
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
            (h : SchwartzSpacetime d) ξ =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d)
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
            twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x) →
      ∃ ν₁_seq ν₂_seq ν₃_seq ν₄_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
        (∀ n, IsFiniteMeasure (ν₁_seq n)) ∧
        (∀ n, IsFiniteMeasure (ν₂_seq n)) ∧
        (∀ n, IsFiniteMeasure (ν₃_seq n)) ∧
        (∀ n, IsFiniteMeasure (ν₄_seq n)) ∧
        (∀ n, ν₁_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
        (∀ n, ν₂_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
        (∀ n, ν₃_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
        (∀ n, ν₄_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
        (∀ n,
          ∫ x : NPointDomain d 2,
            k2TimeParametricKernel (d := d)
                (k2ProbeWitness_local (d := d) OS lgc
                  (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
              twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x =
            (1 / 4 : ℂ) *
              ((∫ p,
                  supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν₁_seq n)) -
                (∫ p,
                  supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν₂_seq n)) -
                Complex.I *
                  (∫ p,
                    supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν₃_seq n)) +
                Complex.I *
                  (∫ p,
                    supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν₄_seq n)))) := by
  intro h χ_seq hpair_probe
  have h_exists :
      ∀ n,
        ∃ (ν₁ : Measure (ℝ × (Fin d → ℝ))) (_hν₁fin : IsFiniteMeasure ν₁)
          (ν₂ : Measure (ℝ × (Fin d → ℝ))) (_hν₂fin : IsFiniteMeasure ν₂)
          (ν₃ : Measure (ℝ × (Fin d → ℝ))) (_hν₃fin : IsFiniteMeasure ν₃)
          (ν₄ : Measure (ℝ × (Fin d → ℝ))) (_hν₄fin : IsFiniteMeasure ν₄)
          (_hsupp₁ : ν₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
          (_hsupp₂ : ν₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
          (_hsupp₃ : ν₃ (Set.prod (Set.Iio 0) Set.univ) = 0)
          (_hsupp₄ : ν₄ (Set.prod (Set.Iio 0) Set.univ) = 0),
          ∫ x : NPointDomain d 2,
            k2TimeParametricKernel (d := d)
                (k2ProbeWitness_local (d := d) OS lgc
                  (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
              twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x =
            (1 / 4 : ℂ) *
              ((∫ p,
                  supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
                (∫ p,
                  supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
                Complex.I *
                  (∫ p,
                    supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
                Complex.I *
                  (∫ p,
                    supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄)) := by
    intro n
    obtain ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
        hsupp₁, hsupp₂, hsupp₃, hsupp₄, hdiag_supported⟩ :=
      exists_supported_symbol_diagonal_formula_translatedProductShell_negativeProbe_family_local
        (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n)
    letI : IsFiniteMeasure ν₁ := hν₁fin
    letI : IsFiniteMeasure ν₂ := hν₂fin
    letI : IsFiniteMeasure ν₃ := hν₃fin
    letI : IsFiniteMeasure ν₄ := hν₄fin
    refine ⟨ν₁, hν₁fin, ν₂, hν₂fin, ν₃, hν₃fin, ν₄, hν₄fin,
      hsupp₁, hsupp₂, hsupp₃, hsupp₄, ?_⟩
    calc
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d)
            (k2ProbeWitness_local (d := d) OS lgc
              (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
          twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x
          =
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
            (h : SchwartzSpacetime d) ξ := by
              symm
              exact hpair_probe n
      _ =
        ∫ ξ : SpacetimeDim d,
          (if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (φ_seq n)))))
          else 0) * ((h : SchwartzSpacetime d) ξ) := by
            symm
            exact
              integral_translatedProductShell_boundary_eq_reduced_differenceKernel_pairing_of_negativeApproxIdentity_local
                (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg μ_seq _hμfin
                hsupp hμrepr n h
      _ =
        (1 / 4 : ℂ) *
          ((∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
            (∫ p,
              supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
            Complex.I *
              (∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
            Complex.I *
              (∫ p,
                supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄)) := hdiag_supported h
  choose ν₁_seq hν₁fin ν₂_seq hν₂fin ν₃_seq hν₃fin ν₄_seq hν₄fin
    hsupp₁ hsupp₂ hsupp₃ hsupp₄ hpair_diag using h_exists
  exact ⟨ν₁_seq, ν₂_seq, ν₃_seq, ν₄_seq,
    hν₁fin, hν₂fin, hν₃fin, hν₄fin,
    hsupp₁, hsupp₂, hsupp₃, hsupp₄, hpair_diag⟩

/-- Per-probe diagonal supported-symbol package on the descended-shell surface.

This isolates the already-provable four-diagonal extraction for each fixed probe
`φ_n`: after descending to the normalized center shell, each probe pairing is
already a polarization combination of four supported symbol integrals. The
remaining first VI.1 blocker is therefore only the fixed-measure factorization
problem across `n`, not the per-probe diagonalization. -/
theorem exists_perProbe_diagonal_supported_symbol_package_of_descended_center_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
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
            else 0) * ((h : SchwartzSpacetime d) ξ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      ∃ χ_seq : ℕ → SchwartzSpacetime d,
        (∀ n,
          ∃ (ν₁ : Measure (ℝ × (Fin d → ℝ))) (_hν₁fin : IsFiniteMeasure ν₁)
            (ν₂ : Measure (ℝ × (Fin d → ℝ))) (_hν₂fin : IsFiniteMeasure ν₂)
            (ν₃ : Measure (ℝ × (Fin d → ℝ))) (_hν₃fin : IsFiniteMeasure ν₃)
            (ν₄ : Measure (ℝ × (Fin d → ℝ))) (_hν₄fin : IsFiniteMeasure ν₄)
            (_hsupp₁ : ν₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
            (_hsupp₂ : ν₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
            (_hsupp₃ : ν₃ (Set.prod (Set.Iio 0) Set.univ) = 0)
            (_hsupp₄ : ν₄ (Set.prod (Set.Iio 0) Set.univ) = 0),
            ∫ x : NPointDomain d 2,
              k2TimeParametricKernel (d := d)
                  (k2ProbeWitness_local (d := d) OS lgc
                    (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
                twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x =
              (1 / 4 : ℂ) *
                ((∫ p,
                    supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₁) -
                  (∫ p,
                    supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₂) -
                  Complex.I *
                    (∫ p,
                      supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₃) +
                  Complex.I *
                    (∫ p,
                      supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂ν₄))) ∧
        (∀ n,
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d))) =
            (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
              (d := d) OS χ₀) h) := by
  intro h
  obtain ⟨χ_seq, hpair_probe, htarget_descended⟩ :=
    exists_k2_VI1_descended_reduced_pairing_package_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball μ_seq _hμfin hsupp hμrepr hpair h
  obtain ⟨ν₁_seq, ν₂_seq, ν₃_seq, ν₄_seq, hν₁fin, hν₂fin, hν₃fin, hν₄fin,
      hsupp₁, hsupp₂, hsupp₃, hsupp₄, hpair_diag⟩ :=
    exists_perProbe_diagonal_supported_symbol_sequences_of_probe_pairing_local
      (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg μ_seq _hμfin hsupp
      hμrepr h χ_seq hpair_probe
  refine ⟨χ_seq, ?_, htarget_descended⟩
  intro n
  exact ⟨ν₁_seq n, hν₁fin n, ν₂_seq n, hν₂fin n, ν₃_seq n, hν₃fin n,
    ν₄_seq n, hν₄fin n, hsupp₁ n, hsupp₂ n, hsupp₃ n, hsupp₄ n, hpair_diag n⟩

/-- Sequence-valued per-probe diagonal package on the descended-shell surface.

This is just the `choose`-packaged version of
`exists_perProbe_diagonal_supported_symbol_package_of_descended_center_local`.
It turns the nested `∀ n, ∃ ...` diagonal measures into honest sequences
`ν₁_seq, …, ν₄_seq`, so the remaining first VI.1 blocker can focus on the
fixed-measure factorization question across `n` rather than on choice
bookkeeping. -/
theorem exists_perProbe_diagonal_supported_symbol_sequences_of_descended_center_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (μ_seq : ℕ → Measure (ℝ × (Fin d → ℝ)))
    (_hμfin : ∀ n, IsFiniteMeasure (μ_seq n))
    (hsupp : ∀ n, μ_seq n (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμrepr : ∀ n (t : ℝ) (a : Fin d → ℝ), 0 < t →
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n))
    (hpair : ∀ n (χ : SchwartzSpacetime d) (h : positiveTimeCompactSupportSubmodule d),
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
            else 0) * ((h : SchwartzSpacetime d) ξ)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      ∃ χ_seq : ℕ → SchwartzSpacetime d,
        ∃ ν₁_seq ν₂_seq ν₃_seq ν₄_seq : ℕ → Measure (ℝ × (Fin d → ℝ)),
          (∀ n, IsFiniteMeasure (ν₁_seq n)) ∧
          (∀ n, IsFiniteMeasure (ν₂_seq n)) ∧
          (∀ n, IsFiniteMeasure (ν₃_seq n)) ∧
          (∀ n, IsFiniteMeasure (ν₄_seq n)) ∧
          (∀ n, ν₁_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
          (∀ n, ν₂_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
          (∀ n, ν₃_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
          (∀ n, ν₄_seq n (Set.prod (Set.Iio 0) Set.univ) = 0) ∧
          (∀ n,
            ∫ x : NPointDomain d 2,
              k2TimeParametricKernel (d := d)
                  (k2ProbeWitness_local (d := d) OS lgc
                    (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
                twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x =
              (1 / 4 : ℂ) *
                ((∫ p,
                    supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν₁_seq n)) -
                  (∫ p,
                    supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν₂_seq n)) -
                  Complex.I *
                    (∫ p,
                      supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν₃_seq n)) +
                  Complex.I *
                    (∫ p,
                      supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p ∂(ν₄_seq n)))) ∧
          (∀ n,
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d))) =
              (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
                (d := d) OS χ₀) h) := by
  intro h
  obtain ⟨χ_seq, hpair_diag_seq, htarget_descended⟩ :=
    exists_perProbe_diagonal_supported_symbol_package_of_descended_center_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball μ_seq _hμfin hsupp hμrepr hpair h
  choose ν₁_seq hν₁fin ν₂_seq hν₂fin ν₃_seq hν₃fin ν₄_seq hν₄fin
    hsupp₁ hsupp₂ hsupp₃ hsupp₄ hpair_diag using hpair_diag_seq
  exact ⟨χ_seq, ν₁_seq, ν₂_seq, ν₃_seq, ν₄_seq,
    hν₁fin, hν₂fin, hν₃fin, hν₄fin,
    hsupp₁, hsupp₂, hsupp₃, hsupp₄, hpair_diag, htarget_descended⟩


end
