/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Moments.ComplexMGF
import OSReconstruction.SCV.Osgood

/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/


















open MeasureTheory Filter Set Complex Real
open scoped Topology ProbabilityTheory

noncomputable section

namespace SCV

private theorem integrable_exp_mul_of_lt_zero_of_nonnegSupport
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Set.Iio 0) = 0) {x : ℝ} (hx : x < 0) :
    Integrable (fun t : ℝ => Real.exp (x * t)) μ := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (x * t)) μ := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
    simp
  refine hconst.mono' hmeas ?_
  have hae : ∀ᵐ (t : ℝ) ∂μ, 0 ≤ t := by
    rw [ae_iff]
    simp only [not_le]
    exact hsupp
  filter_upwards [hae] with t ht
  have hxt : x * t ≤ 0 := by nlinarith
  have hexp : Real.exp (x * t) ≤ 1 := Real.exp_le_one_iff.mpr hxt
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using hexp

private theorem neg_mem_interior_integrableExpSet_id_of_nonnegSupport
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Set.Iio 0) = 0) {x : ℝ} (hx : x < 0) :
    x ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset (isOpen_Iio.mem_nhds hx) ?_
  intro y hy
  change Integrable (fun t : ℝ => Real.exp (y * t)) μ
  exact integrable_exp_mul_of_lt_zero_of_nonnegSupport μ hsupp hy

/-- The scalar Laplace transform of a finite measure supported in `[0,∞)` is
    holomorphic on the right half-plane. -/
theorem laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hsupp : μ (Set.Iio 0) = 0) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∫ t : ℝ, Complex.exp (-z * (t : ℂ)) ∂μ)
      {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  have hz' : (-z).re ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
    have hzneg : (-z).re < 0 := by
      simp only [Complex.neg_re]
      linarith
    exact neg_mem_interior_integrableExpSet_id_of_nonnegSupport μ hsupp hzneg
  have hbase :
      HasDerivAt (ProbabilityTheory.complexMGF id μ)
        (μ[fun t ↦ t * Complex.exp ((-z) * (t : ℂ))]) (-z) :=
    ProbabilityTheory.hasDerivAt_complexMGF (X := id) (μ := μ) hz'
  have hcomp :
      HasDerivAt (fun w : ℂ => ProbabilityTheory.complexMGF id μ (-w))
        (μ[fun t ↦ t * Complex.exp ((-z) * (t : ℂ))] * (-1)) z := by
    simpa using hbase.comp z (hasDerivAt_neg z)
  simpa [ProbabilityTheory.complexMGF, mul_assoc]
    using hcomp.differentiableAt.differentiableWithinAt

end SCV
