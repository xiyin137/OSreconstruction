/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1Support

/-!
# OS to Wightman `k = 2` VI.1 Frontier

This file now contains only the surviving OS II Section VI.1 `k = 2` frontier:
the common-measure/common-density spectral seam behind the probe limit, the
limit wrappers above it, and the final distributional assembly theorem.

All proved support infrastructure has been moved to `OSToWightmanK2VI1Support.lean` so that the hard `sorry`s stay on a small, readable theorem surface.
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

/-- Honest remaining OS II VI.1 spectral factorization seam.

For each fixed positive-time test `h`, the per-probe pairings are already known
to admit per-`n` supported-symbol representations. The real remaining content
is to factor those per-probe families through one common supported positive-
energy control measure `ρ`, one bounded measurable density `s`, and the explicit
reflected approximate-identity weights. Once that common factorization exists,
the actual convergence is immediate from the proved weighted DCT layer in the
support file. -/
private theorem exists_supported_symbol_weighted_measure_representation_of_perProbe_family_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
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
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂(μ_seq n)) :
    ∀ h : positiveTimeCompactSupportSubmodule d,
      ∃ (ρ : Measure (ℝ × (Fin d → ℝ))) (_hρfin : IsFiniteMeasure ρ)
        (s : (ℝ × (Fin d → ℝ)) → ℂ) (C : ℝ)
        (w_seq : ℕ → (ℝ × (Fin d → ℝ)) → ℝ),
        ρ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
        AEStronglyMeasurable s ρ ∧
        0 ≤ C ∧
        (∀ᵐ p ∂ρ, ‖s p‖ ≤ C) ∧
        (∀ n p, 0 ≤ w_seq n p) ∧
        (∀ n p, w_seq n p ≤ 1) ∧
        (∀ n, Measurable (w_seq n)) ∧
        (∀ p, Filter.Tendsto (fun n => w_seq n p) Filter.atTop (𝓝 1)) ∧
        (∀ n,
          ∫ ξ : SpacetimeDim d,
            k2DifferenceKernel_real_local (μ_seq n) ξ *
              (h : SchwartzSpacetime d) ξ =
            ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
              s p * ↑(w_seq n p) ∂ρ) ∧
        ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h =
            ∫ p, supported_positiveTimeCompactSupportLaplaceSymbol_local (d := d) h p *
              s p ∂ρ) := by
  /-
  Honest remaining spectral VI.1 content:

  the support file proves that each probe-dependent measure `μ_n` already has
  its own supported-symbol family representation. What is still open is the
  across-`n` factorization through one common `ρ` and one common density `s`
  against the explicit reflected-probe weights.
  -/
  sorry

private theorem k2DifferenceKernel_real_pairing_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local
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
      Filter.Tendsto
        (fun n =>
          ∫ ξ : SpacetimeDim d,
            k2DifferenceKernel_real_local (μ_seq n) ξ *
              (h : SchwartzSpacetime d) ξ)
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) := by
  intro h
  obtain ⟨ρ, hρfin, s, C, w_seq, hsuppρ, hs_meas, hC, hs_bound,
      hw_nonneg, hw_le, hw_meas, hw_tendsto, hrepr, htarget⟩ :=
    exists_supported_symbol_weighted_measure_representation_of_perProbe_family_local
      OS lgc χ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_ball
      μ_seq _hμfin hsupp hμrepr h
  letI : IsFiniteMeasure ρ := hρfin
  exact
    tendsto_to_schwingerDifferencePositive_of_supported_symbol_density_representation_local
      (d := d) OS χ₀ h ρ
      w_seq
      hw_le hw_nonneg hw_meas hw_tendsto
      s hs_meas C hC hs_bound
      (fun n =>
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (μ_seq n) ξ *
            (h : SchwartzSpacetime d) ξ)
      hrepr htarget

private theorem translatedProductShell_boundary_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local
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
      Filter.Tendsto
        (fun n =>
          ∫ ξ : SpacetimeDim d,
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ))
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) := by
  intro h
  have hred :=
    k2DifferenceKernel_real_pairing_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local
      OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball μ_seq _hμfin hsupp hμrepr hpair h
  refine Filter.Tendsto.congr' ?_ hred
  filter_upwards with n
  exact
    integral_translatedProductShell_boundary_eq_reduced_differenceKernel_pairing_of_negativeApproxIdentity_local
      OS lgc φ_seq hφ_real hφ_compact hφ_neg μ_seq _hμfin hsupp hμrepr n h |>.symm

/-- Route-independent final payoff: once an honest Euclidean two-point kernel
has the correct sector formulas, measurable polynomial bounds, and agreement
with `OS.S 2` on the flat-origin difference-shell generators, reproduction on
all of `ZeroDiagonalSchwartz d 2` is purely formal. This packages the last
non-VI.1 bookkeeping step so the remaining assembly theorem only has to produce
the limiting witness/kernel data. -/
private theorem k2_distributional_reproduction_of_flatOrigin_shell_agreement_local
    (OS : OsterwalderSchraderAxioms d)
    (K : NPointDomain d 2 → ℂ)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hShell :
      ∀ (χ h : SchwartzSpacetime d)
        (hzero : ∀ k : ℕ, iteratedFDeriv ℝ k (h : SpacetimeDim d → ℂ) 0 = 0),
        OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound
            (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)))
    (f : ZeroDiagonalSchwartz d 2) :
    OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x) := by
  have hCLM :
      OSReconstruction.twoPointZeroDiagonalKernelCLM (d := d) K hK_meas C_bd N hC hK_bound =
        OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2 :=
    zeroDiagKernelCLM_eq_schwinger_of_flatOrigin_differenceShell_agreement
      (d := d) OS K hK_meas C_bd N hC hK_bound hShell
  have happly :=
    congrArg (fun L : ZeroDiagonalSchwartz d 2 →L[ℂ] ℂ => L f) hCLM
  simpa [OSReconstruction.twoPointZeroDiagonalKernelCLM_apply] using happly.symm

private theorem exists_k2_timeParametric_distributional_assembly
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) (K : NPointDomain d 2 → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ x : NPointDomain d 2, x 0 0 < x 1 0 →
        K x = k2TimeParametricKernel (d := d) G x) ∧
      (∀ x : NPointDomain d 2, x 1 0 < x 0 0 →
        K x = k2TimeParametricKernel (d := d) G
          (fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i))) ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x)) := by
  /-
  Honest remaining assembly step after the VI.1 refactor:

  * obtain the shrinking negative approximate-identity sequence and its
    per-probe shell package from `exists_k2_VI1_regularization_input_local`;
  * use
    `translatedProductShell_boundary_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local`
    to identify the reduced boundary functional on the positive-time edge;
  * choose the resulting honest Euclidean kernel/witness pair `(G, K)` coming
    from the OS II VI.1 limit construction, not from a single fixed probe;
  * discharge the final reproduction clause through
    `k2_distributional_reproduction_of_flatOrigin_shell_agreement_local`.
  -/
  sorry

/-- The `k = 2` time-parametric base step on the honest OS route.

The previous kernel / difference-lift transport chain has been removed from the
critical path. The remaining gap is now exactly the OS-faithful semigroup /
distributional assembly theorem. -/
theorem schwinger_continuation_base_step_timeParametric_k2
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ) (K : NPointDomain d 2 → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ x : NPointDomain d 2, x 0 0 < x 1 0 →
        K x = k2TimeParametricKernel (d := d) G x) ∧
      (∀ x : NPointDomain d 2, x 1 0 < x 0 0 →
        K x = k2TimeParametricKernel (d := d) G
          (fun i => x ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) i))) ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x)) := by
  exact exists_k2_timeParametric_distributional_assembly OS lgc

end
