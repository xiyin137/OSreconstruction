/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform
import OSReconstruction.SCV.PaleyWiener
import OSReconstruction.Mathlib429Compat
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section

open scoped Topology FourierTransform
open Set MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]



omit [NeZero d] in
/-- A Schwartz function supported on the Section-4.3 positive-energy region
vanishes when one time coordinate is negative. -/
theorem section43NPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time_of_support_positiveEnergy
    {n : ℕ}
    (F : SchwartzNPoint d n)
    (hF_supp :
      tsupport (F : NPointDomain d n → ℂ) ⊆
        section43PositiveEnergyRegion d n)
    (r : Fin n) (t : Fin n → ℝ)
    (η : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    nPointTimeSpatialSchwartzCLE (d := d) (n := n) F
      (Function.update t r s, η) = 0 := by
  have hnot_region :
      (nPointTimeSpatialCLE (d := d) n).symm (Function.update t r s, η) ∉
        section43PositiveEnergyRegion d n := by
    intro hmem
    have htime : 0 ≤
        (((nPointTimeSpatialCLE (d := d) n).symm
          (Function.update t r s, η)) r 0) := hmem r
    have hEq :
        (((nPointTimeSpatialCLE (d := d) n).symm
          (Function.update t r s, η)) r 0) = s := by
      simp [nPointTimeSpatialCLE]
    linarith
  have hnot_supp :
      (nPointTimeSpatialCLE (d := d) n).symm (Function.update t r s, η) ∉
        tsupport (F : NPointDomain d n → ℂ) := by
    intro hx
    exact hnot_region (hF_supp hx)
  change F ((nPointTimeSpatialCLE (d := d) n).symm
    (Function.update t r s, η)) = 0
  simpa using image_eq_zero_of_notMem_tsupport hnot_supp

omit [NeZero d] in
/-- Negative time in one chosen coordinate forces the partial spatial Fourier
transform to vanish for any input supported in the Section-4.3 positive-energy
region. -/
theorem section43PartialFourierSpatial_fun_eq_zero_of_neg_time_of_support_positiveEnergy
    {n : ℕ}
    (F : SchwartzNPoint d n)
    (hF_supp :
      tsupport (F : NPointDomain d n → ℂ) ⊆
        section43PositiveEnergyRegion d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    partialFourierSpatial_fun (d := d) (n := n) F
      (Function.update t r s, ξ) = 0 := by
  rw [partialFourierSpatial_fun_eq_integral]
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards with η
  simp [section43NPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time_of_support_positiveEnergy
    (F := F) hF_supp (r := r) (t := t) (η := η) hs]

theorem section43ComplexLaplaceTransform_integrable_of_nonneg_re
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    (s : ℂ) (hs : 0 ≤ s.re) :
    Integrable (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * f t) := by
  apply MeasureTheory.Integrable.mono f.integrable
  · exact ((Complex.continuous_exp.comp
        ((continuous_const : Continuous (fun _ : ℝ => -s)).mul Complex.continuous_ofReal)).mul
        f.continuous).aestronglyMeasurable
  · filter_upwards with t
    simp only [norm_mul, Complex.norm_exp]
    by_cases ht : (f : ℝ → ℂ) t = 0
    · simp [ht]
    · have ht_supp : t ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ ht
      have ht_nonneg : 0 ≤ t := Set.mem_Ici.mp (hf_supp ht_supp)
      have hre : (-s * (t : ℂ)).re = -(s.re * t) := by
        simp [Complex.mul_re]
      rw [hre]
      have hexp : Real.exp (-(s.re * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      exact mul_le_of_le_one_left (norm_nonneg _) hexp

end OSReconstruction
