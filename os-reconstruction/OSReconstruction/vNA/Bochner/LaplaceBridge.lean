/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace BochnerLaplaceBridge

/-- The logarithmic change-of-variables map used to convert spectral parameters `λ ∈ (0, 1]`
to Laplace parameters `u = -log λ ∈ [0, ∞)`. -/
def negLogMap : ℝ → ℝ := fun s => -Real.log s

theorem negLogMap_measurable : Measurable negLogMap := by
  exact Real.measurable_log.neg

/-- Push a finite measure on `ℝ` forward under `λ ↦ -log λ` after discarding the zero atom.

This is the honest change-of-variables bridge for bounded positive operators: a spectral measure
may have mass at `λ = 0`, and that mass cannot be sent through `-log`. For positive exponents
the zero atom contributes nothing to `λ^t`, so it is removed first. -/
def laplaceMeasurePos (μ : Measure ℝ) : Measure ℝ :=
  (μ.restrict (Set.Ioi 0)).map negLogMap

instance laplaceMeasurePos_isFinite (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (laplaceMeasurePos μ) := by
  unfold laplaceMeasurePos
  infer_instance

theorem rpow_eq_exp_neg_negLogMap (s : ℝ) (hs : 0 < s) (t : ℝ) :
    s ^ t = Real.exp (-t * negLogMap s) := by
  unfold negLogMap
  rw [Real.rpow_def_of_pos hs]
  congr 1
  ring

/-- For `t > 0`, a finite measure on `[0, ∞)` yields the same scalar integral whether written as
`∫ λ^t dμ(λ)` or, after deleting the zero atom and substituting `λ = exp(-u)`, as a Laplace
integral `∫ exp(-tu) dν(u)`.

The hypothesis `μ(Iio 0) = 0` excludes genuinely negative spectral mass; the zero atom is removed
inside `laplaceMeasurePos`. -/
theorem spectralIntegral_eq_laplace_restrictZero
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp_nonneg : μ (Set.Iio 0) = 0)
    (t : ℝ) (ht : 0 < t)
    (_hint : Integrable (fun s => s ^ t) μ) :
    ∫ s, s ^ t ∂μ =
      ∫ u, Real.exp (-t * u) ∂(laplaceMeasurePos μ) := by
  unfold laplaceMeasurePos
  have hmeasExp : AEStronglyMeasurable (fun u : ℝ => Real.exp (-t * u))
      ((μ.restrict (Set.Ioi 0)).map negLogMap) := by
    have hcont : Continuous (fun u : ℝ => Real.exp (-t * u)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  rw [MeasureTheory.integral_map negLogMap_measurable.aemeasurable hmeasExp]
  have hposEq :
      ∀ᵐ s ∂(μ.restrict (Set.Ioi 0)), Real.exp (-t * negLogMap s) = s ^ t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with s hs
    exact (rpow_eq_exp_neg_negLogMap s hs t).symm
  rw [integral_congr_ae hposEq]
  conv_rhs => rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  have hae_nonneg : ∀ᵐ s ∂μ, 0 ≤ s := by
    rw [ae_iff]
    simpa [Set.compl_setOf, not_le] using hsupp_nonneg
  filter_upwards [hae_nonneg] with s hs
  by_cases hpos : 0 < s
  · simp [Set.indicator_of_mem, hpos]
  · have hs0 : s = 0 := by
      exact le_antisymm (le_of_not_gt hpos) hs
    subst hs0
    simp [Real.zero_rpow ht.ne']

/-- If `μ` is supported in `[0, 1]`, then the pushed-forward measure `laplaceMeasurePos μ`
is supported in `[0, ∞)`. -/
theorem laplaceMeasurePos_nonnegSupport
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp_le_one : μ (Set.Ioi 1) = 0) :
    laplaceMeasurePos μ (Set.Iio 0) = 0 := by
  unfold laplaceMeasurePos
  rw [Measure.map_apply negLogMap_measurable measurableSet_Iio]
  rw [Measure.restrict_apply' measurableSet_Ioi]
  have hpre :
      negLogMap ⁻¹' Set.Iio 0 ∩ Set.Ioi 0 = Set.Ioi 1 := by
    ext s
    constructor
    · intro hs
      rcases hs with ⟨hsneglog, hspos⟩
      simp only [Set.mem_preimage, Set.mem_Iio, negLogMap, neg_lt_zero] at hsneglog
      have hgt : 1 < Real.exp (Real.log s) := Real.one_lt_exp_iff.2 hsneglog
      simpa [Real.exp_log hspos] using hgt
    · intro hs
      constructor
      · simp only [Set.mem_preimage, Set.mem_Iio, negLogMap, neg_lt_zero]
        exact Real.log_pos hs
      · simpa using (lt_trans zero_lt_one hs : 0 < s)
  rw [hpre, hsupp_le_one]

end BochnerLaplaceBridge
