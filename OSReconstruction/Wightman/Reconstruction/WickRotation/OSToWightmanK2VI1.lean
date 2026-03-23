/- 
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2BaseStep

/-!
# OS to Wightman `k = 2` VI.1 Frontier

This file isolates the remaining OS II Section VI.1 regularization /
boundary-identification frontier for the honest `k = 2` base step.

`OSToWightmanK2BaseStep.lean` now serves as the proved support layer:
semigroup witnesses, Bochner data, positive-time shell identities, and the
route-independent density extension theorem all live there. The only remaining
`k = 2` reconstruction gaps stay here so that the support file does not keep
growing while the VI.1 work remains open.
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

/-- Sequence-level OS II VI.1 regularization input for the active `k = 2`
frontier.

This packages a shrinking normalized negative approximate identity together
with the per-probe semigroup/Bochner shell data already proved in the support
file. The remaining VI.1 work in this file should start from this sequence
package, not from a single fixed probe. -/
private theorem exists_k2_VI1_regularization_input_local
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
private def k2DifferenceKernel_real_local
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
private theorem k2TimeParametricKernel_real_eq_twoPointDifferenceKernel_local
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
private theorem integral_k2DifferenceKernel_real_mul_eq_translatedProductShell_integral_local
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

/-- The honest real Euclidean kernel attached to the canonical `k = 2` probe
witness is uniformly bounded by the same positive-time contraction constant on
both time-ordering sectors. -/
private theorem exists_k2TimeParametricKernel_real_bound_local
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
private theorem aestronglyMeasurable_k2TimeParametricKernel_real_local
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
private theorem exists_k2TimeParametricKernel_real_constBound_package_local
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
private theorem exists_k2_timeParametric_zeroDiagKernel_package_local
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

/-- Honest OS II VI.1 boundary-limit theorem for the `k = 2` route.

This is the sequence-level statement the OS paper actually uses: starting from
a shrinking normalized negative approximate identity and the per-probe
positive-time shell package, the regularized translated product-shell boundary
functionals converge to the reduced Schwinger positive CLM. This replaces the
earlier too-strong fixed-probe equality surface. -/
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
    (hhol : ∀ n,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness
        (k2ProbeWitness_local (d := d) OS lgc
          (φ_seq n) (hφ_compact n) (hφ_neg n)))
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
    (hkernel : ∀ n (x : NPointDomain d 2), x 0 0 < x 1 0 →
      k2TimeParametricKernel (d := d)
          (k2ProbeWitness_local (d := d) OS lgc
            (φ_seq n) (hφ_compact n) (hφ_neg n)) x =
        laplaceFourierKernel (d := d) (μ_seq n) (fun i => x 1 i - x 0 i))
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
  /-
  Honest remaining OS II VI.1 step:

  * regularize the reduced boundary object with the shrinking negative
    approximate identity sequence `φ_seq`;
  * use the VI.1 mean-value / positivity estimates to control the resulting
    boundary functionals;
  * prove those regularized boundary functionals converge to the reduced
    Schwinger positive CLM, which is independent of the normalized center test
    by `schwingerDifferencePositiveCLM_eq_of_normalized_center_local`.
  -/
  sorry

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
  * apply the route-independent zero-diagonal kernel CLM density theorem to
    obtain reproduction on all `ZeroDiagonalSchwartz d 2`.
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
  exact exists_k2_timeParametric_distributional_assembly (d := d) OS lgc

end
