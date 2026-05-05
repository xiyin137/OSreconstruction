/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.EuclideanWeylFrechet
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Euclidean Weyl Bump Infrastructure

This file contains the normalized compact bump package for the local Euclidean
Weyl route.  It deliberately stops before the radial Poisson/right-inverse
theorem: that is the next genuine analytic layer.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter
open scoped LineDeriv

namespace SCV

/-- The explicit unnormalized radial bump used in the Euclidean Weyl proof. -/
noncomputable def euclideanWeylRawBumpReal
    {ι : Type*} [Fintype ι]
    (ε : ℝ) : EuclideanSpace ℝ ι → ℝ :=
  fun x =>
    (ContDiffBumpBase.ofInnerProductSpace (EuclideanSpace ℝ ι)).toFun 2
      ((2 / ε) • x)

theorem euclideanWeylRawBumpReal_contDiff
    {ι : Type*} [Fintype ι]
    (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanWeylRawBumpReal (ι := ι) ε) := by
  let base := ContDiffBumpBase.ofInnerProductSpace (EuclideanSpace ℝ ι)
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry base.toFun)
      (Set.Ioi (1 : ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ ι))) :=
    base.smooth
  have hg : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ ι => ((2 : ℝ), (2 / ε) • x)) := by
    fun_prop
  have hmaps : ∀ x : EuclideanSpace ℝ ι,
      ((2 : ℝ), (2 / ε) • x) ∈
        Set.Ioi (1 : ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ ι)) := by
    intro x
    simp
  have hcomp := hs.comp_contDiff hg hmaps
  simpa [euclideanWeylRawBumpReal, base, Function.uncurry] using hcomp

theorem euclideanWeylRawBumpReal_nonneg
    {ι : Type*} [Fintype ι]
    (ε : ℝ) (x : EuclideanSpace ℝ ι) :
    0 ≤ euclideanWeylRawBumpReal ε x := by
  unfold euclideanWeylRawBumpReal
  exact
    ((ContDiffBumpBase.ofInnerProductSpace (EuclideanSpace ℝ ι)).mem_Icc 2
      ((2 / ε) • x)).1

theorem euclideanWeylRawBumpReal_apply
    {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
    euclideanWeylRawBumpReal ε x =
      Real.smoothTransition (2 - 2 * (‖x‖ / ε)) := by
  simp [euclideanWeylRawBumpReal, ContDiffBumpBase.ofInnerProductSpace,
    norm_smul, Real.norm_eq_abs, abs_of_pos hε, div_eq_mul_inv]
  ring_nf

theorem euclideanWeylRawBumpReal_support
    {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) :
    Function.support (euclideanWeylRawBumpReal (ι := ι) ε) =
      Metric.ball (0 : EuclideanSpace ℝ ι) ε := by
  let E := EuclideanSpace ℝ ι
  have hbase :
      Function.support ((ContDiffBumpBase.ofInnerProductSpace E).toFun 2) =
        Metric.ball (0 : E) 2 := by
    exact (ContDiffBumpBase.ofInnerProductSpace E).support 2 (by norm_num)
  ext x
  have hxmem : euclideanWeylRawBumpReal ε x ≠ 0 ↔
      (2 / ε) • x ∈
        Function.support ((ContDiffBumpBase.ofInnerProductSpace E).toFun 2) := by
    simp [euclideanWeylRawBumpReal, E, Function.mem_support]
  rw [Function.mem_support, hxmem, hbase]
  simp [Metric.mem_ball, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  constructor <;> intro h
  · have hmul := mul_lt_mul_of_pos_right h (by positivity : 0 < ε / 2)
    field_simp [hε.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  · have h2ε : 0 < 2 / ε := by positivity
    have hmul := mul_lt_mul_of_pos_left h h2ε
    field_simp [hε.ne'] at hmul ⊢
    linarith

theorem euclideanWeylRawBumpReal_hasCompactSupport
    {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (euclideanWeylRawBumpReal (ι := ι) ε) := by
  rw [HasCompactSupport]
  rw [tsupport, euclideanWeylRawBumpReal_support hε]
  rw [closure_ball _ hε.ne']
  exact isCompact_closedBall _ _

theorem euclideanWeylRawBumpReal_integrable
    {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (euclideanWeylRawBumpReal (ι := ι) ε) := by
  exact ((euclideanWeylRawBumpReal_contDiff (ι := ι) ε).continuous).integrable_of_hasCompactSupport
    (euclideanWeylRawBumpReal_hasCompactSupport hε)

theorem euclideanWeylRawBumpReal_integral_pos
    {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) :
    0 < ∫ x : EuclideanSpace ℝ ι, euclideanWeylRawBumpReal ε x := by
  refine (integral_pos_iff_support_of_nonneg
    (euclideanWeylRawBumpReal_nonneg ε)
    (euclideanWeylRawBumpReal_integrable hε)).mpr ?_
  rw [euclideanWeylRawBumpReal_support hε]
  exact measure_ball_pos volume (0 : EuclideanSpace ℝ ι) hε

/-- The real normalization denominator for the raw Euclidean Weyl bump. -/
noncomputable def euclideanWeylRawIntegralReal
    {ι : Type*} [Fintype ι] (ε : ℝ) : ℝ :=
  ∫ x : EuclideanSpace ℝ ι, euclideanWeylRawBumpReal ε x

theorem euclideanWeylRawIntegralReal_pos
    {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) :
    0 < euclideanWeylRawIntegralReal (ι := ι) ε := by
  simpa [euclideanWeylRawIntegralReal] using
    euclideanWeylRawBumpReal_integral_pos (ι := ι) hε

theorem euclideanWeylRawIntegralReal_scale
    {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) :
    euclideanWeylRawIntegralReal (ι := ι) ε =
      ε ^ Fintype.card ι * euclideanWeylRawIntegralReal (ι := ι) 1 := by
  let E := EuclideanSpace ℝ ι
  have hraw : ∀ x : E,
      euclideanWeylRawBumpReal ε x =
        euclideanWeylRawBumpReal (ι := ι) 1 (ε⁻¹ • x) := by
    intro x
    rw [euclideanWeylRawBumpReal_apply (ι := ι) hε x,
      euclideanWeylRawBumpReal_apply (ι := ι) zero_lt_one (ε⁻¹ • x)]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hε, div_eq_mul_inv]
    ring_nf
  have hscale := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (μ := (volume : Measure E))
    (f := fun x : E => euclideanWeylRawBumpReal (ι := ι) 1 x)
    (R := ε) hε.le
  calc
    euclideanWeylRawIntegralReal (ι := ι) ε
        = ∫ x : E, euclideanWeylRawBumpReal (ι := ι) 1 (ε⁻¹ • x) := by
          simp [euclideanWeylRawIntegralReal, E, hraw]
    _ = ε ^ Module.finrank ℝ E *
          ∫ x : E, euclideanWeylRawBumpReal (ι := ι) 1 x := by
          simpa [smul_eq_mul] using hscale
    _ = ε ^ Fintype.card ι * euclideanWeylRawIntegralReal (ι := ι) 1 := by
          simp [euclideanWeylRawIntegralReal, E, finrank_euclideanSpace]

/-- The fixed scalar profile underlying the explicit Euclidean Weyl bump. -/
noncomputable def euclideanWeylBaseProfile (r : ℝ) : ℂ :=
  (Real.smoothTransition (2 - 2 * |r|) : ℂ)

theorem euclideanWeylBaseProfile_eq_zero_of_one_le_abs
    {r : ℝ} (hr : 1 ≤ |r|) :
    euclideanWeylBaseProfile r = 0 := by
  change ((Real.smoothTransition (2 - 2 * |r|) : ℝ) : ℂ) = 0
  rw [Real.smoothTransition.zero_of_nonpos]
  · norm_num
  · linarith

theorem euclideanWeylBaseProfile_eq_one_of_abs_le_half
    {r : ℝ} (hr : |r| ≤ 1 / 2) :
    euclideanWeylBaseProfile r = 1 := by
  change ((Real.smoothTransition (2 - 2 * |r|) : ℝ) : ℂ) = 1
  rw [Real.smoothTransition.one_of_one_le]
  · norm_num
  · linarith

/-- The one-dimensional weighted raw radial mass for the fixed Weyl profile. -/
noncomputable def euclideanWeylWeightedRawMass
    (N : ℕ) (ε : ℝ) : ℂ :=
  ∫ r in Set.Ioi 0,
    ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylBaseProfile (r / ε)

theorem euclideanWeylWeightedRawMass_scale
    {N : ℕ} (hNpos : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    euclideanWeylWeightedRawMass N ε =
      (((ε ^ N : ℝ) : ℂ)) * euclideanWeylWeightedRawMass N 1 := by
  let H : ℝ → ℂ :=
    fun r => ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylBaseProfile r
  have harg : ∀ x : ℝ, x / ε = ε⁻¹ * x := by
    intro x
    ring_nf
  have hpow : ∀ x : ℝ,
      ((x ^ (N - 1) : ℝ) : ℂ) * euclideanWeylBaseProfile (x / ε) =
        (((ε ^ (N - 1) : ℝ) : ℂ)) * H (ε⁻¹ * x) := by
    intro x
    simp [H, harg x]
    have hrhs :
        (ε : ℂ) ^ (N - 1) *
            (((ε : ℂ)⁻¹ * (x : ℂ)) ^ (N - 1) *
              euclideanWeylBaseProfile (ε⁻¹ * x)) =
          (x : ℂ) ^ (N - 1) * euclideanWeylBaseProfile (ε⁻¹ * x) := by
      calc
        (ε : ℂ) ^ (N - 1) *
            (((ε : ℂ)⁻¹ * (x : ℂ)) ^ (N - 1) *
              euclideanWeylBaseProfile (ε⁻¹ * x))
            = ((ε : ℂ) ^ (N - 1) * ((ε : ℂ)⁻¹) ^ (N - 1)) *
                ((x : ℂ) ^ (N - 1) * euclideanWeylBaseProfile (ε⁻¹ * x)) := by
              rw [mul_pow]
              ring
        _ = (x : ℂ) ^ (N - 1) * euclideanWeylBaseProfile (ε⁻¹ * x) := by
              have hunit :
                  (ε : ℂ) ^ (N - 1) * ((ε : ℂ)⁻¹) ^ (N - 1) = 1 := by
                rw [← mul_pow, mul_inv_cancel₀
                  (Complex.ofReal_ne_zero.mpr hε.ne'), one_pow]
              rw [hunit, one_mul]
    rw [hrhs]
  have hsubst := MeasureTheory.integral_comp_mul_left_Ioi
    (g := H) (a := 0) (b := ε⁻¹) (inv_pos.mpr hε)
  have hsubst' :
      (∫ x in Set.Ioi 0, H (ε⁻¹ * x)) =
        (ε : ℂ) * ∫ x in Set.Ioi 0, H x := by
    simpa [smul_eq_mul, hε.ne'] using hsubst
  calc
    euclideanWeylWeightedRawMass N ε
        = ∫ x in Set.Ioi 0,
            (((ε ^ (N - 1) : ℝ) : ℂ)) * H (ε⁻¹ * x) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact hpow x
    _ = (((ε ^ (N - 1) : ℝ) : ℂ)) *
          ∫ x in Set.Ioi 0, H (ε⁻¹ * x) := by
          simpa using
            (MeasureTheory.integral_const_mul
              (μ := (volume.restrict (Set.Ioi (0 : ℝ))))
              (((ε ^ (N - 1) : ℝ) : ℂ))
              (fun x : ℝ => H (ε⁻¹ * x)))
    _ = (((ε ^ (N - 1) : ℝ) : ℂ)) *
          ((ε : ℂ) * ∫ x in Set.Ioi 0, H x) := by
          rw [hsubst']
    _ = (((ε ^ N : ℝ) : ℂ)) * euclideanWeylWeightedRawMass N 1 := by
          simp [euclideanWeylWeightedRawMass, H]
          have hcoeff :
              (ε : ℂ) ^ (N - 1) * (ε : ℂ) = (ε : ℂ) ^ N := by
            rw [mul_comm]
            rw [← pow_succ', Nat.sub_add_cancel hNpos]
          rw [← mul_assoc, hcoeff]

/-- The normalized scalar profile for radius `ε`. -/
noncomputable def euclideanWeylNormalizedProfile
    {ι : Type*} [Fintype ι] (ε : ℝ) : ℝ → ℂ :=
  fun r =>
    (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) *
      euclideanWeylBaseProfile (r / ε)

theorem euclideanWeylNormalizedProfile_eq_zero_of_epsilon_le_abs
    {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) {r : ℝ}
    (hr : ε ≤ |r|) :
    euclideanWeylNormalizedProfile (ι := ι) ε r = 0 := by
  have hbase : euclideanWeylBaseProfile (r / ε) = 0 := by
    apply euclideanWeylBaseProfile_eq_zero_of_one_le_abs
    rw [abs_div, abs_of_pos hε]
    exact (one_le_div hε).2 hr
  simp [euclideanWeylNormalizedProfile, hbase]

theorem euclideanWeylNormalizedProfile_support_subset
    {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    Function.support (euclideanWeylNormalizedProfile (ι := ι) ε) ⊆
      Set.Icc (-ε) ε := by
  intro r hr
  by_contra hnot
  have hcase : r < -ε ∨ ε < r := by
    rw [Set.mem_Icc] at hnot
    by_cases hleft : -ε ≤ r
    · right
      exact lt_of_not_ge (fun hright => hnot ⟨hleft, hright⟩)
    · left
      exact lt_of_not_ge hleft
  have hεabs : ε ≤ |r| := by
    rcases hcase with hlt | hgt
    · have hrneg : r < 0 := by linarith
      rw [abs_of_neg hrneg]
      linarith
    · have hrnonneg : 0 ≤ r := by linarith
      rw [abs_of_nonneg hrnonneg]
      linarith
  rw [Function.mem_support] at hr
  exact hr (euclideanWeylNormalizedProfile_eq_zero_of_epsilon_le_abs hε hεabs)

theorem euclideanWeylNormalizedProfile_eq_plateau_of_abs_le_half_epsilon
    {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) {r : ℝ}
    (hr : |r| ≤ ε / 2) :
    euclideanWeylNormalizedProfile (ι := ι) ε r =
      (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) := by
  have hbase : euclideanWeylBaseProfile (r / ε) = 1 := by
    apply euclideanWeylBaseProfile_eq_one_of_abs_le_half
    rw [abs_div, abs_of_pos hε]
    have hr' : |r| ≤ (1 / 2) * ε := by linarith
    exact (div_le_iff₀ hε).2 hr'
  simp [euclideanWeylNormalizedProfile, hbase]

theorem euclideanWeylNormalizedProfile_contDiff
    {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanWeylNormalizedProfile (ι := ι) ε) := by
  let e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single (0 : Fin 1) 1
  have hline : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => r • e) := by
    fun_prop
  have hraw : ContDiff ℝ (⊤ : ℕ∞)
      (fun r : ℝ => euclideanWeylRawBumpReal (ι := Fin 1) ε (r • e)) := by
    exact (euclideanWeylRawBumpReal_contDiff (ι := Fin 1) ε).comp hline
  have hbase : (fun r : ℝ => euclideanWeylBaseProfile (r / ε)) =
      fun r : ℝ =>
        ((euclideanWeylRawBumpReal (ι := Fin 1) ε (r • e) : ℝ) : ℂ) := by
    funext r
    rw [euclideanWeylRawBumpReal_apply (ι := Fin 1) hε]
    simp [euclideanWeylBaseProfile, e, abs_div, abs_of_pos hε,
      norm_smul, Real.norm_eq_abs]
  have hbase_cd : ContDiff ℝ (⊤ : ℕ∞)
      (fun r : ℝ => euclideanWeylBaseProfile (r / ε)) := by
    rw [hbase]
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp hraw
  exact contDiff_const.mul hbase_cd

theorem euclideanWeylWeightedNormalizedProfile_integrable
    {ι : Type*} [Fintype ι] (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun r : ℝ =>
      ((r ^ (N - 1) : ℝ) : ℂ) *
        euclideanWeylNormalizedProfile (ι := ι) ε r) := by
  have hcont_weight : Continuous (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ)) := by
    fun_prop
  have hcont_profile : Continuous (euclideanWeylNormalizedProfile (ι := ι) ε) :=
    (euclideanWeylNormalizedProfile_contDiff (ι := ι) hε).continuous
  have hcont : Continuous (fun r : ℝ =>
      ((r ^ (N - 1) : ℝ) : ℂ) *
        euclideanWeylNormalizedProfile (ι := ι) ε r) :=
    hcont_weight.mul hcont_profile
  have hcompact : HasCompactSupport (fun r : ℝ =>
      ((r ^ (N - 1) : ℝ) : ℂ) *
        euclideanWeylNormalizedProfile (ι := ι) ε r) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Set.Icc (-ε) ε))
    intro r hr
    have hprofile_mem :
        r ∈ Function.support (euclideanWeylNormalizedProfile (ι := ι) ε) := by
      rw [Function.mem_support] at hr ⊢
      intro hzero
      apply hr
      simp [hzero]
    exact euclideanWeylNormalizedProfile_support_subset hε hprofile_mem
  exact hcont.integrable_of_hasCompactSupport hcompact

theorem euclideanWeylBump_weightedMass_eq_const
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ε : ℝ} (hε : 0 < ε) :
    ∫ r in Set.Ioi 0,
      ((r ^ (Fintype.card ι - 1) : ℝ) : ℂ) *
        euclideanWeylNormalizedProfile (ι := ι) ε r =
    (((euclideanWeylRawIntegralReal (ι := ι) 1 : ℝ) : ℂ)⁻¹) *
      euclideanWeylWeightedRawMass (Fintype.card ι) 1 := by
  let N := Fintype.card ι
  have hNpos : 0 < N := Fintype.card_pos_iff.mpr inferInstance
  have hIscale :
      euclideanWeylRawIntegralReal (ι := ι) ε =
        ε ^ N * euclideanWeylRawIntegralReal (ι := ι) 1 := by
    simpa [N] using euclideanWeylRawIntegralReal_scale (ι := ι) hε
  have hWscale := euclideanWeylWeightedRawMass_scale (N := N) hNpos hε
  have hconst :
      (∫ r in Set.Ioi 0,
        ((r ^ (N - 1) : ℝ) : ℂ) *
          euclideanWeylNormalizedProfile (ι := ι) ε r) =
        (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) *
          euclideanWeylWeightedRawMass N ε := by
    calc
      (∫ r in Set.Ioi 0,
        ((r ^ (N - 1) : ℝ) : ℂ) *
          euclideanWeylNormalizedProfile (ι := ι) ε r)
          = ∫ r in Set.Ioi 0,
              (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) *
                (((r ^ (N - 1) : ℝ) : ℂ) *
                  euclideanWeylBaseProfile (r / ε)) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro r hr
            simp [euclideanWeylNormalizedProfile]
            ring
      _ = (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) *
            ∫ r in Set.Ioi 0,
              ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylBaseProfile (r / ε) := by
            simpa using
              (MeasureTheory.integral_const_mul
                (μ := (volume.restrict (Set.Ioi (0 : ℝ))))
                ((((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹))
                (fun r : ℝ =>
                  ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylBaseProfile (r / ε)))
      _ = (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) *
            euclideanWeylWeightedRawMass N ε := by
            simp [euclideanWeylWeightedRawMass]
  rw [show Fintype.card ι = N from rfl]
  rw [hconst]
  rw [hWscale]
  rw [hIscale]
  have hpow_ne : ((ε ^ N : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero N hε.ne'
  have hI1_ne : (((euclideanWeylRawIntegralReal (ι := ι) 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (euclideanWeylRawIntegralReal_pos (ι := ι) zero_lt_one).ne'
  simp only [Complex.ofReal_mul]
  field_simp [hpow_ne, hI1_ne]

/-- The scalar radial profile of a difference of two normalized Weyl bumps. -/
noncomputable def euclideanWeylBumpSubProfile
    {ι : Type*} [Fintype ι]
    (ε δ : ℝ) : ℝ → ℂ :=
  fun r =>
    euclideanWeylNormalizedProfile (ι := ι) ε r -
      euclideanWeylNormalizedProfile (ι := ι) δ r

theorem euclideanWeylBumpSubProfile_contDiff
    {ι : Type*} [Fintype ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanWeylBumpSubProfile (ι := ι) ε δ) := by
  exact (euclideanWeylNormalizedProfile_contDiff (ι := ι) hε).sub
    (euclideanWeylNormalizedProfile_contDiff (ι := ι) hδ)

theorem euclideanWeylBumpSubProfile_eq_zero_of_max_le_abs
    {ι : Type*} [Fintype ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {r : ℝ}
    (hr : max ε δ ≤ |r|) :
    euclideanWeylBumpSubProfile (ι := ι) ε δ r = 0 := by
  have hεr : ε ≤ |r| := le_trans (le_max_left ε δ) hr
  have hδr : δ ≤ |r| := le_trans (le_max_right ε δ) hr
  simp [euclideanWeylBumpSubProfile,
    euclideanWeylNormalizedProfile_eq_zero_of_epsilon_le_abs hε hεr,
    euclideanWeylNormalizedProfile_eq_zero_of_epsilon_le_abs hδ hδr]

theorem euclideanWeylBumpSubProfile_support_subset
    {ι : Type*} [Fintype ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Function.support (euclideanWeylBumpSubProfile (ι := ι) ε δ) ⊆
      Set.Icc (-(max ε δ)) (max ε δ) := by
  intro r hr
  let R := max ε δ
  have hRpos : 0 < R := lt_of_lt_of_le hε (le_max_left ε δ)
  by_contra hnot
  have hcase : r < -R ∨ R < r := by
    rw [Set.mem_Icc] at hnot
    by_cases hleft : -R ≤ r
    · right
      exact lt_of_not_ge (fun hright => hnot ⟨hleft, hright⟩)
    · left
      exact lt_of_not_ge hleft
  have hRabs : R ≤ |r| := by
    rcases hcase with hlt | hgt
    · have hrneg : r < 0 := by linarith
      rw [abs_of_neg hrneg]
      linarith
    · have hrnonneg : 0 ≤ r := by linarith
      rw [abs_of_nonneg hrnonneg]
      linarith
  rw [Function.mem_support] at hr
  exact hr (euclideanWeylBumpSubProfile_eq_zero_of_max_le_abs hε hδ hRabs)

theorem euclideanWeylBumpSubProfile_eq_plateau_of_abs_le_half_min
    {ι : Type*} [Fintype ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {r : ℝ}
    (hr : |r| ≤ min ε δ / 2) :
    euclideanWeylBumpSubProfile (ι := ι) ε δ r =
      (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) -
        (((euclideanWeylRawIntegralReal (ι := ι) δ : ℝ) : ℂ)⁻¹) := by
  have hεhalf : |r| ≤ ε / 2 := by
    have hmin : min ε δ ≤ ε := min_le_left ε δ
    linarith
  have hδhalf : |r| ≤ δ / 2 := by
    have hmin : min ε δ ≤ δ := min_le_right ε δ
    linarith
  simp [euclideanWeylBumpSubProfile,
    euclideanWeylNormalizedProfile_eq_plateau_of_abs_le_half_epsilon hε hεhalf,
    euclideanWeylNormalizedProfile_eq_plateau_of_abs_le_half_epsilon hδ hδhalf]

theorem euclideanWeylBumpSubProfile_exists_plateau
    {ι : Type*} [Fintype ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ η : ℝ, ∃ c : ℂ, 0 < η ∧
      ∀ r ∈ Set.Icc 0 η,
        euclideanWeylBumpSubProfile (ι := ι) ε δ r = c := by
  refine ⟨min ε δ / 2,
    (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) -
      (((euclideanWeylRawIntegralReal (ι := ι) δ : ℝ) : ℂ)⁻¹), ?_, ?_⟩
  · positivity
  · intro r hr
    have hr_abs : |r| ≤ min ε δ / 2 := by
      rw [abs_of_nonneg hr.1]
      exact hr.2
    exact euclideanWeylBumpSubProfile_eq_plateau_of_abs_le_half_min hε hδ hr_abs

theorem euclideanWeylBumpSubProfile_weightedMass_eq_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∫ r in Set.Ioi 0,
      ((r ^ (Fintype.card ι - 1) : ℝ) : ℂ) *
        euclideanWeylBumpSubProfile (ι := ι) ε δ r = 0 := by
  let N := Fintype.card ι
  let fε : ℝ → ℂ := fun r =>
    ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylNormalizedProfile (ι := ι) ε r
  let fδ : ℝ → ℂ := fun r =>
    ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylNormalizedProfile (ι := ι) δ r
  have hrewrite :
      (∫ r in Set.Ioi 0,
        ((r ^ (N - 1) : ℝ) : ℂ) *
          euclideanWeylBumpSubProfile (ι := ι) ε δ r) =
        ∫ r in Set.Ioi 0, fε r - fδ r := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp [fε, fδ, euclideanWeylBumpSubProfile]
    ring
  rw [show Fintype.card ι = N from rfl]
  rw [hrewrite]
  rw [MeasureTheory.integral_sub]
  · rw [show (∫ r in Set.Ioi 0, fε r) =
        ∫ r in Set.Ioi 0,
          ((r ^ (Fintype.card ι - 1) : ℝ) : ℂ) *
            euclideanWeylNormalizedProfile (ι := ι) ε r by rfl]
    rw [show (∫ r in Set.Ioi 0, fδ r) =
        ∫ r in Set.Ioi 0,
          ((r ^ (Fintype.card ι - 1) : ℝ) : ℂ) *
            euclideanWeylNormalizedProfile (ι := ι) δ r by rfl]
    rw [euclideanWeylBump_weightedMass_eq_const (ι := ι) hε,
      euclideanWeylBump_weightedMass_eq_const (ι := ι) hδ]
    simp
  · exact (euclideanWeylWeightedNormalizedProfile_integrable
      (ι := ι) N hε).integrableOn
  · exact (euclideanWeylWeightedNormalizedProfile_integrable
      (ι := ι) N hδ).integrableOn

/-- A normalized compact radial Euclidean bump with support in `closedBall 0 ε`. -/
noncomputable def euclideanWeylBump
    {ι : Type*} [Fintype ι]
    (ε : ℝ) (hε : 0 < ε) :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ := by
  let E := EuclideanSpace ℝ ι
  let I : ℝ := ∫ x : E, euclideanWeylRawBumpReal ε x
  let f : E → ℂ := fun x => ((euclideanWeylRawBumpReal ε x / I : ℝ) : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp
      ((euclideanWeylRawBumpReal_contDiff (ι := ι) ε).div_const I)
  have hf_compact : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : E) ε)
    intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall]
    have hxraw : euclideanWeylRawBumpReal ε x ≠ 0 := by
      intro hzero
      apply hx
      simp [f, hzero]
    have hxin : x ∈ Function.support (euclideanWeylRawBumpReal (ι := ι) ε) := by
      simpa [Function.mem_support] using hxraw
    rw [euclideanWeylRawBumpReal_support (ι := ι) hε] at hxin
    exact le_of_lt (by simpa [Metric.mem_ball] using hxin)
  exact hf_compact.toSchwartzMap hf_smooth

@[simp]
theorem euclideanWeylBump_apply
    {ι : Type*} [Fintype ι]
    (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
    euclideanWeylBump ε hε x =
      ((euclideanWeylRawBumpReal ε x /
        (∫ y : EuclideanSpace ℝ ι, euclideanWeylRawBumpReal ε y) : ℝ) : ℂ) := by
  simp [euclideanWeylBump]

theorem euclideanWeylBump_raw_profile
    {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
    euclideanWeylBump ε hε x =
      euclideanWeylNormalizedProfile (ι := ι) ε ‖x‖ := by
  rw [euclideanWeylBump_apply, euclideanWeylRawBumpReal_apply hε]
  simp [euclideanWeylNormalizedProfile, euclideanWeylBaseProfile,
    euclideanWeylRawIntegralReal,
    abs_of_nonneg (div_nonneg (norm_nonneg x) hε.le)]
  ring

theorem euclideanWeylBump_eq_of_norm_eq
    {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε)
    {x y : EuclideanSpace ℝ ι} (hxy : ‖x‖ = ‖y‖) :
    euclideanWeylBump ε hε x = euclideanWeylBump ε hε y := by
  rw [euclideanWeylBump_raw_profile hε x,
    euclideanWeylBump_raw_profile hε y, hxy]

theorem euclideanWeylBump_sub_eq_of_norm_eq
    {ι : Type*} [Fintype ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {x y : EuclideanSpace ℝ ι} (hxy : ‖x‖ = ‖y‖) :
    ((euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
      SchwartzMap (EuclideanSpace ℝ ι) ℂ) x) =
    ((euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
      SchwartzMap (EuclideanSpace ℝ ι) ℂ) y) := by
  simp [euclideanWeylBump_eq_of_norm_eq hε hxy,
    euclideanWeylBump_eq_of_norm_eq hδ hxy]

theorem euclideanWeylBumpSubProfile_norm_eq_bump_sub
    {ι : Type*} [Fintype ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (x : EuclideanSpace ℝ ι) :
    euclideanWeylBumpSubProfile (ι := ι) ε δ ‖x‖ =
      (euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
        SchwartzMap (EuclideanSpace ℝ ι) ℂ) x := by
  simp [euclideanWeylBumpSubProfile,
    euclideanWeylBump_raw_profile hε x,
    euclideanWeylBump_raw_profile hδ x]

theorem euclideanWeylBumpSubProfile_spec
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanWeylBumpSubProfile (ι := ι) ε δ) ∧
    Function.support (euclideanWeylBumpSubProfile (ι := ι) ε δ) ⊆
      Set.Icc (-(max ε δ)) (max ε δ) ∧
    (∃ η : ℝ, ∃ c : ℂ, 0 < η ∧
      ∀ r ∈ Set.Icc 0 η,
        euclideanWeylBumpSubProfile (ι := ι) ε δ r = c) ∧
    (∀ x : EuclideanSpace ℝ ι,
      euclideanWeylBumpSubProfile (ι := ι) ε δ ‖x‖ =
        (euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
          SchwartzMap (EuclideanSpace ℝ ι) ℂ) x) ∧
    (∫ r in Set.Ioi 0,
      ((r ^ (Fintype.card ι - 1) : ℝ) : ℂ) *
        euclideanWeylBumpSubProfile (ι := ι) ε δ r) = 0 := by
  refine ⟨euclideanWeylBumpSubProfile_contDiff hε hδ,
    euclideanWeylBumpSubProfile_support_subset hε hδ,
    euclideanWeylBumpSubProfile_exists_plateau hε hδ,
    ?_, euclideanWeylBumpSubProfile_weightedMass_eq_zero hε hδ⟩
  intro x
  exact euclideanWeylBumpSubProfile_norm_eq_bump_sub hε hδ x

/-- The Euclidean Weyl bump is real nonnegative. -/
theorem euclideanWeylBump_nonneg_re
    {ι : Type*} [Fintype ι]
    (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
    0 ≤ (euclideanWeylBump ε hε x).re := by
  rw [euclideanWeylBump_apply]
  simp only [Complex.ofReal_re]
  exact div_nonneg
    (euclideanWeylRawBumpReal_nonneg ε x)
    (le_of_lt (euclideanWeylRawBumpReal_integral_pos hε))

/-- The Euclidean Weyl bump has real values. -/
theorem euclideanWeylBump_im_eq_zero
    {ι : Type*} [Fintype ι]
    (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
    (euclideanWeylBump ε hε x).im = 0 := by
  rw [euclideanWeylBump_apply]
  simp

/-- The Euclidean Weyl bump is normalized to have integral one. -/
theorem euclideanWeylBump_normalized
    {ι : Type*} [Fintype ι]
    (ε : ℝ) (hε : 0 < ε) :
    ∫ x : EuclideanSpace ℝ ι, euclideanWeylBump ε hε x = 1 := by
  let E := EuclideanSpace ℝ ι
  have hb_apply : ∀ x : E,
      euclideanWeylBump ε hε x =
        ((euclideanWeylRawBumpReal ε x /
          (∫ y : E, euclideanWeylRawBumpReal ε y) : ℝ) : ℂ) := by
    intro x
    simp [euclideanWeylBump, E]
  rw [show (∫ x : E, euclideanWeylBump ε hε x) =
      ∫ x : E,
        ((euclideanWeylRawBumpReal ε x /
          (∫ y : E, euclideanWeylRawBumpReal ε y) : ℝ) : ℂ) by
    simp_rw [hb_apply]]
  rw [integral_complex_ofReal, MeasureTheory.integral_div]
  exact_mod_cast div_self (euclideanWeylRawBumpReal_integral_pos (ι := ι) hε).ne'

/-- The Euclidean Weyl bump has topological support in `closedBall 0 ε`. -/
theorem euclideanWeylBump_support
    {ι : Type*} [Fintype ι]
    (ε : ℝ) (hε : 0 < ε) :
    tsupport (euclideanWeylBump ε hε :
      EuclideanSpace ℝ ι → ℂ) ⊆ Metric.closedBall 0 ε := by
  let E := EuclideanSpace ℝ ι
  have hsupp :
      Function.support (euclideanWeylBump ε hε : E → ℂ) =
        Function.support (euclideanWeylRawBumpReal (ι := ι) ε) := by
    ext x
    rw [Function.mem_support, Function.mem_support, euclideanWeylBump_apply]
    have hI : (∫ y : E, euclideanWeylRawBumpReal ε y) ≠ 0 :=
      (euclideanWeylRawBumpReal_integral_pos (ι := ι) hε).ne'
    constructor
    · intro hbump hraw
      apply hbump
      simp [hraw]
    · intro hraw hbump
      apply hraw
      have hbump_real :
          euclideanWeylRawBumpReal ε x /
              (∫ y : E, euclideanWeylRawBumpReal ε y) = 0 := by
        exact_mod_cast hbump
      rw [div_eq_zero_iff] at hbump_real
      exact hbump_real.resolve_right hI
  rw [tsupport, hsupp, ← tsupport]
  intro x hx
  rw [tsupport, euclideanWeylRawBumpReal_support (ι := ι) hε,
    closure_ball _ hε.ne'] at hx
  simpa [E] using hx

/-- The difference of two normalized Euclidean Weyl bumps has integral zero. -/
theorem euclideanWeylBump_sub_integral_eq_zero
    {ι : Type*} [Fintype ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∫ x : EuclideanSpace ℝ ι,
      (euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
        SchwartzMap (EuclideanSpace ℝ ι) ℂ) x = 0 := by
  change ∫ x : EuclideanSpace ℝ ι,
    euclideanWeylBump ε hε x - euclideanWeylBump δ hδ x = 0
  rw [MeasureTheory.integral_sub]
  · rw [euclideanWeylBump_normalized ε hε, euclideanWeylBump_normalized δ hδ]
    simp
  · exact SchwartzMap.integrable (euclideanWeylBump ε hε)
  · exact SchwartzMap.integrable (euclideanWeylBump δ hδ)

/-- The support of a difference of two Euclidean Weyl bumps is contained in the
larger closed ball. -/
theorem euclideanWeylBump_sub_support
    {ι : Type*} [Fintype ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    tsupport ((euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
      SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
      EuclideanSpace ℝ ι → ℂ) ⊆ Metric.closedBall 0 (max ε δ) := by
  intro x hx
  have hx' := tsupport_sub
    (euclideanWeylBump ε hε : EuclideanSpace ℝ ι → ℂ)
    (euclideanWeylBump δ hδ : EuclideanSpace ℝ ι → ℂ) hx
  rcases hx' with hxε | hxδ
  · have hxε' := euclideanWeylBump_support ε hε hxε
    rw [Metric.mem_closedBall] at hxε' ⊢
    exact le_trans hxε' (le_max_left _ _)
  · have hxδ' := euclideanWeylBump_support δ hδ hxδ
    rw [Metric.mem_closedBall] at hxδ' ⊢
    exact le_trans hxδ' (le_max_right _ _)

/-- A difference of two Euclidean Weyl bumps is compactly supported. -/
theorem euclideanWeylBump_sub_hasCompactSupport
    {ι : Type*} [Fintype ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    HasCompactSupport (((euclideanWeylBump ε hε - euclideanWeylBump δ hδ :
      SchwartzMap (EuclideanSpace ℝ ι) ℂ) : EuclideanSpace ℝ ι → ℂ)) := by
  exact IsCompact.of_isClosed_subset
    (isCompact_closedBall (0 : EuclideanSpace ℝ ι) (max ε δ))
    (isClosed_tsupport _)
    (euclideanWeylBump_sub_support hε hδ)

end SCV
