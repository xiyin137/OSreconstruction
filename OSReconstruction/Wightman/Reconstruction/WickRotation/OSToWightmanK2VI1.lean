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

/-- The reflected companions of the shrinking negative approximate-identity
sequence already produce honest real spectral weights in `[0,1]` converging to
`1` pointwise on the nonnegative-energy spectral side. This is the exact input
needed if the remaining VI.1 limit is completed by dominated convergence over a
fixed spectral measure, rather than by a direct shell estimate. -/
private theorem reflected_negativeApproxIdentity_fourierLaplace_weight_package_local
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

/-- Dominated-convergence wrapper for fixed finite spectral measures weighted by
approximate-identity factors in `[0,1]`. This is the exact scalar measure-limit
step one needs once the remaining VI.1 argument is reduced to a fixed spectral
measure with probe-dependent weights. -/
private theorem weighted_measure_tendsto_of_approx_identity_local
    (ρ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure ρ]
    (w_seq : ℕ → (ℝ × (Fin d → ℝ)) → ℝ)
    (hw_le : ∀ n p, w_seq n p ≤ 1)
    (hw_nonneg : ∀ n p, 0 ≤ w_seq n p)
    (hw_meas : ∀ n, Measurable (w_seq n))
    (hw_tendsto : ∀ p, Filter.Tendsto (fun n => w_seq n p) Filter.atTop (𝓝 1)) :
    ∀ f : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℂ,
      Filter.Tendsto
        (fun n => ∫ p, f p * ↑(w_seq n p) ∂ρ)
        Filter.atTop
        (𝓝 (∫ p, f p ∂ρ)) := by
  intro f
  rw [show (fun p => f p) = (fun p => f p * (1 : ℂ)) from by
    ext p
    simp]
  apply MeasureTheory.tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun n =>
      f.continuous.aestronglyMeasurable.mul
        ((measurable_ofReal.comp (hw_meas n)).aestronglyMeasurable)
  · refine ⟨‖f‖, Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun p => ?_⟩
    simp only [norm_mul, Complex.norm_real]
    calc
      ‖f p‖ * ‖w_seq n p‖
          ≤ ‖f‖ * ‖w_seq n p‖ := by
            gcongr
            exact f.norm_coe_le_norm p
      _ ≤ ‖f‖ * 1 := by
            gcongr
            rw [Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [hw_nonneg n p], hw_le n p⟩
      _ = ‖f‖ := by simp
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

/-- Sequence-level reduced boundary pairing formula for the VI.1 regularization
input. Each negative approximate-identity probe contributes a genuine
one-variable difference kernel whose pairing against a positive-time compactly
supported test is exactly the weighted translated product-shell boundary
integral. -/
private theorem integral_translatedProductShell_boundary_eq_reduced_differenceKernel_pairing_of_negativeApproxIdentity_local
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

/-! ### Descended VI.1 regularizer packages -/

/-- The descended center-shear regularizer built from a normalized negative-time
probe and its reflected companion again has total integral `1`. This is the
natural one-variable normalized center cutoff attached to the VI.1
regularization sequence. -/
private theorem integral_twoPointCenterShearDescent_reflected_negativeApproxIdentity_eq_one_local
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
private theorem twoPointCenterShearDescent_translated_reflected_eq_translated_local
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
private theorem exists_k2_VI1_descended_center_package_local
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

/-- Schwartz spacetime test functions are globally Lipschitz, with a constant
controlled by the first Schwartz seminorm. This is the local VI.1 copy of the
support lemma from `K2BaseStep`, exposed here so the frontier file does not
depend on private declarations from the support layer. -/
private theorem schwartz_lipschitz_bound_vi1_local
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
private theorem eventually_tsupport_descended_center_package_subset_ball_local
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
private theorem exists_descended_center_translation_error_bound_local
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

/-- A descended center-shear regularization sequence with real nonnegative mass
`1` and shrinking support is an honest approximate identity on the reduced
one-variable side. The support radius is `2/(n+1)` rather than `1/(n+1)`, but
the same continuity argument goes through unchanged. -/
private theorem descended_center_package_integral_tendsto_of_continuousAt_zero_local
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
private theorem exists_positive_time_margin_of_mem_positiveTimeCompactSupport_local
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
private theorem translateSchwartz_tsupport_subset_positive_of_ball_and_margin_local
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
private theorem eventually_translated_descended_center_package_subset_positive_local
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
private theorem descended_center_approxIdentity_integral_tendsto_of_continuousAt_zero_local
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
private theorem descended_center_translate_tendsto_self_local
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
private theorem integral_translateSchwartz_eq_one_of_integral_eq_one_local
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
private theorem schwingerDifferencePositiveCLM_eq_of_translated_descended_center_local
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
private theorem schwingerDifferencePositiveCLM_eq_of_descended_center_package_local
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
private theorem integral_translatedProductShell_boundary_eq_probe_pairing_descended_center_local
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
private theorem integral_k2DifferenceKernel_real_eq_probe_pairing_descended_center_local
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
            k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
              (h : SchwartzSpacetime d) ξ)
        Filter.atTop
        (𝓝 ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h)) := by
  intro h
  obtain ⟨χ_seq, hχ_seq_desc, hχ_seq_nonneg, hχ_seq_real, hχ_seq_int,
      hχ_seq_translate, hχ_seq_ball⟩ :=
    exists_k2_VI1_descended_center_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
  have hcenter :
      ∀ n ξ,
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift (SCV.translateSchwartz (-ξ) (χ_seq n))
              (h : SchwartzSpacetime d))) =
          (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
            (d := d) OS χ₀) h := by
    intro n ξ
    simpa [hχ_seq_desc n] using
      schwingerDifferencePositiveCLM_eq_of_descended_center_package_local
        (d := d) OS χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_ball n ξ h
  have hpair_descended :
      ∀ n,
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
            twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x := by
    intro n
    simpa [hχ_seq_desc n] using
      integral_translatedProductShell_boundary_eq_probe_pairing_descended_center_local
        (d := d) OS lgc φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
        hφ_compact hφ_neg hpair n h
  have hpair_reduced :
      ∀ n,
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
    intro n
    exact
      integral_translatedProductShell_boundary_eq_reduced_differenceKernel_pairing_of_negativeApproxIdentity_local
        (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg μ_seq _hμfin hsupp hμrepr n h
  have hpair_probe :
      ∀ n,
        ∫ ξ : SpacetimeDim d,
          k2DifferenceKernel_real_local (d := d) (μ_seq n) ξ *
            (h : SchwartzSpacetime d) ξ =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d)
              (k2ProbeWitness_local (d := d) OS lgc
                (φ_seq n) (hφ_compact n) (hφ_neg n)) x *
            twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d) x := by
    intro n
    simpa [hχ_seq_desc n] using
      integral_k2DifferenceKernel_real_eq_probe_pairing_descended_center_local
        (d := d) OS lgc φ_seq hφ_nonneg hφ_int hφ_ball hφ_real hφ_compact hφ_neg
        μ_seq _hμfin hsupp hμrepr hpair n h
  have htarget_descended :
      ∀ n,
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift (χ_seq n) (h : SchwartzSpacetime d))) =
          (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
            (d := d) OS χ₀) h := by
    intro n
    have htrans0 := hcenter n (0 : SpacetimeDim d)
    have hleft0 : SCV.translateSchwartz (0 : SpacetimeDim d) (χ_seq n) = χ_seq n := by
      ext x
      simp [SCV.translateSchwartz_apply]
    simpa [hleft0] using htrans0
  /-
  Honest remaining OS II VI.1 step:

  * regularize the reduced boundary object with the shrinking negative
    approximate identity sequence `φ_seq`;
  * work directly on the honest reduced one-variable surface given by the
    pairings `∫ k2DifferenceKernel_real_local (μ_seq n) * h`;
  * keep the descended normalized center sequence `χ_seq` and the exact
    Schwinger value on the same descended shell available through
    `hpair_probe` and `htarget_descended`;
  * use the VI.1 mean-value / positivity estimates to show that difference
    tends to `0`.
  -/
  sorry

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
  intro h
  have hred :=
    k2DifferenceKernel_real_pairing_tendsto_schwingerDifferencePositive_of_negativeApproxIdentity_local
      (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg
      hφ_ball μ_seq _hμfin hhol hsupp hμrepr hkernel hpair h
  refine Filter.Tendsto.congr' ?_ hred
  filter_upwards with n
  exact
    integral_translatedProductShell_boundary_eq_reduced_differenceKernel_pairing_of_negativeApproxIdentity_local
      (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg μ_seq _hμfin hsupp hμrepr n h |>.symm

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
  exact exists_k2_timeParametric_distributional_assembly (d := d) OS lgc

end
