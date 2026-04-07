import OSReconstruction.Wightman.SchwartzTensorProduct
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/

/-!
# Slice Integrals of Schwartz Functions

This file contains the compact-support slice-integral theorem used in the
multi-dimensional induction behind the zero-mean decomposition on Schwartz
space.
-/

noncomputable section

open scoped SchwartzMap Topology
open MeasureTheory SchwartzMap LineDeriv

namespace OSReconstruction

/-- Insert a tail vector into `Fin (n+1) → ℝ` with zero head coordinate. This
is the linear part of the map `y ↦ Fin.cons x y`. -/
noncomputable def tailInsertCLM (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    Fin.cases
      (0 : (Fin n → ℝ) →L[ℝ] ℝ)
      (fun i => ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i)
      j

@[simp] theorem tailInsertCLM_apply {n : ℕ} (y : Fin n → ℝ) :
    tailInsertCLM n y = Fin.cons 0 y := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [tailInsertCLM]
  · intro i
    simp [tailInsertCLM]

theorem tailInsertCLM_opNorm_le (n : ℕ) :
    ‖tailInsertCLM n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul, tailInsertCLM_apply]
    have htail :
        ‖(Fin.cons 0 y : Fin (n + 1) → ℝ)‖ ≤ ‖y‖ := by
      simp only [Pi.norm_def]
      exact_mod_cast Finset.sup_le fun b _ =>
        Fin.cases
          (by simp)
          (fun i => Finset.le_sup (f := fun j : Fin n => ‖y j‖₊) (Finset.mem_univ i))
          b
    exact htail

/-- Integrate out the head coordinate of a Schwartz function on `ℝ × ℝ^n`,
viewed as `Fin (n+1) → ℝ`. This is the raw pointwise slice integral needed for
the multi-dimensional Poincare induction. -/
def sliceIntegralRaw {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) : V :=
  ∫ x : ℝ, F (Fin.cons x y)

@[simp] theorem sliceIntegralRaw_prependField {n : ℕ}
    (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n → ℝ) ℂ) (y : Fin n → ℝ) :
    sliceIntegralRaw (φ.prependField g) y =
      (∫ x : ℝ, φ x) * g y := by
  simp only [sliceIntegralRaw, SchwartzMap.prependField_apply]
  exact MeasureTheory.integral_mul_const (g y) (fun x => φ x)

/-- Fubini for the raw slice integral. Integrating first in the head variable
and then in the tail variables recovers the full integral on `Fin (n+1) → ℝ`.
-/
theorem integral_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    ∫ y : Fin n → ℝ, sliceIntegralRaw F y =
      ∫ z : Fin (n + 1) → ℝ, F z := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp :
      MeasureTheory.MeasurePreserving e
        (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))) := by
    simpa [e] using
      (MeasureTheory.volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0)
  have hF_int :
      Integrable (fun z : Fin (n + 1) → ℝ => F z)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ)) := by
    simpa using
      (SchwartzMap.integrable
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ))) F)
  have hpair_int :
      Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))) := by
    have hiff :=
      (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding
        (g := fun z : Fin (n + 1) → ℝ => F z))
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hiff.2 hF_int
  calc
    ∫ y : Fin n → ℝ, sliceIntegralRaw F y
        = ∫ y : Fin n → ℝ, ∫ x : ℝ, F (Fin.cons x y) := by
            simp [sliceIntegralRaw]
    _ = ∫ p : ℝ × (Fin n → ℝ), F (Fin.cons p.1 p.2) := by
          symm
          exact MeasureTheory.integral_prod_symm
            (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2)) hpair_int
    _ = ∫ z : Fin (n + 1) → ℝ, F z := by
          simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using
            (hmp.symm.integral_comp'
              (f := e.symm) (g := fun z : Fin (n + 1) → ℝ => F z))

/-- Zeroth-order Schwartz decay for the raw slice integral: integrating out the
head coordinate loses two powers of decay in that coordinate, but preserves
arbitrary polynomial decay in the tail variables. This is the first genuine
estimate needed for the multi-dimensional induction. -/
theorem exists_one_add_norm_pow_mul_sliceIntegralRaw_le {n k : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ),
        (1 + ‖y‖) ^ k * ‖sliceIntegralRaw F y‖ ≤
          C * ((Finset.Iic (k + 2, 0)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F := by
  let C0 : ℝ := ∫ x : ℝ, (1 + x ^ 2)⁻¹
  let C : ℝ := (2 : ℝ) ^ (k + 2) * C0
  refine ⟨C, by positivity, ?_⟩
  intro F y
  let S : ℝ := ((Finset.Iic (k + 2, 0)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F
  let zfun : ℝ → Fin (n + 1) → ℝ := fun x j => Fin.cases x y j
  have hS_nonneg : 0 ≤ S := by positivity
  have hC0_int :
      Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    simpa using integrable_inv_one_add_sq
  have hbound_point :
      ∀ x : ℝ,
        (1 + ‖y‖) ^ k * ‖F (fun j : Fin (n + 1) => Fin.cases x y j)‖ ≤
          ((2 : ℝ) ^ (k + 2) * S) * (1 + x ^ 2)⁻¹ := by
    intro x
    let z : Fin (n + 1) → ℝ := zfun x
    have hhead : ‖x‖ ≤ ‖z‖ := by
      simpa [z] using (norm_le_pi_norm z 0)
    have htail : ‖y‖ ≤ ‖z‖ := by
      calc
        ‖y‖ = ‖tailCLM n z‖ := by
          simp [tailCLM_apply, zfun, z]
        _ ≤ ‖tailCLM n (E := ℝ)‖ * ‖z‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖z‖ := by
          gcongr
          exact tailCLM_opNorm_le (E := ℝ) n
        _ = ‖z‖ := by ring
    have hprod :
        (1 + ‖y‖) ^ k * (1 + ‖x‖) ^ 2 ≤ (1 + ‖z‖) ^ (k + 2) := by
      calc
        (1 + ‖y‖) ^ k * (1 + ‖x‖) ^ 2
            ≤ (1 + ‖z‖) ^ k * (1 + ‖z‖) ^ 2 := by
              gcongr
        _ = (1 + ‖z‖) ^ (k + 2) := by
              rw [← pow_add]
    have hseminorm :
        (1 + ‖z‖) ^ (k + 2) * ‖F z‖ ≤
          (2 : ℝ) ^ (k + 2) * S := by
      simpa [S] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := ℝ) (m := (k + 2, 0)) (k := k + 2) (n := 0)
          le_rfl le_rfl F z)
    have hx_pos : 0 < (1 + ‖x‖) ^ (2 : ℕ) := by positivity
    have hx_nonneg : 0 ≤ (1 + ‖x‖) ^ (2 : ℕ) := by positivity
    have hmain :
        (1 + ‖y‖) ^ k * ‖F z‖ ≤
          ((2 : ℝ) ^ (k + 2) * S) / (1 + ‖x‖) ^ (2 : ℕ) := by
      refine (le_div_iff₀ hx_pos).2 ?_
      calc
        ((1 + ‖y‖) ^ k * ‖F z‖) * (1 + ‖x‖) ^ (2 : ℕ)
            = ((1 + ‖y‖) ^ k * (1 + ‖x‖) ^ (2 : ℕ)) * ‖F z‖ := by ring
        _ ≤ (1 + ‖z‖) ^ (k + 2) * ‖F z‖ := by
              gcongr
        _ ≤ (2 : ℝ) ^ (k + 2) * S := hseminorm
    have hsq : 1 + x ^ 2 ≤ (1 + ‖x‖) ^ (2 : ℕ) := by
      calc
        1 + x ^ 2 ≤ 1 + 2 * |x| + x ^ 2 := by
          nlinarith [abs_nonneg x]
        _ = 1 + 2 * |x| + |x| ^ 2 := by rw [sq_abs]
        _ = (1 + |x|) ^ (2 : ℕ) := by ring
        _ = (1 + ‖x‖) ^ (2 : ℕ) := by rw [Real.norm_eq_abs]
    have hsq_inv : ((1 + ‖x‖) ^ (2 : ℕ))⁻¹ ≤ (1 + x ^ 2)⁻¹ := by
      have hpos1 : 0 < 1 + x ^ 2 := by positivity
      simpa [one_div] using (one_div_le_one_div_of_le hpos1 hsq)
    calc
      (1 + ‖y‖) ^ k * ‖F z‖
          ≤ ((2 : ℝ) ^ (k + 2) * S) * (((1 + ‖x‖) ^ (2 : ℕ))⁻¹) := by
            simpa [one_div, div_eq_mul_inv] using hmain
      _ ≤ ((2 : ℝ) ^ (k + 2) * S) * (1 + x ^ 2)⁻¹ := by
            gcongr
  have hnorm :
      ‖sliceIntegralRaw F y‖ ≤ ∫ x : ℝ, ‖F (zfun x)‖ := by
    simpa [sliceIntegralRaw] using
      (norm_integral_le_integral_norm (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (f := fun x : ℝ => F (zfun x)))
  have hmajor_integrable :
      Integrable
        (fun x : ℝ => ((2 : ℝ) ^ (k + 2) * S) * (1 + x ^ 2)⁻¹)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hC0_int.const_mul ((2 : ℝ) ^ (k + 2) * S)
  have hzfun_cont : Continuous zfun := by
    classical
    refine continuous_pi ?_
    intro j
    induction j using Fin.cases with
    | zero =>
        simpa [zfun] using (continuous_id : Continuous fun a : ℝ => a)
    | succ i =>
        simpa [zfun] using (continuous_const : Continuous fun _ : ℝ => y i)
  have hlower_integrable :
      Integrable (fun x : ℝ => (1 + ‖y‖) ^ k * ‖F (zfun x)‖)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    refine hmajor_integrable.mono' ?_ ?_
    · exact (continuous_const.mul ((F.continuous.comp hzfun_cont).norm)).aestronglyMeasurable
    · filter_upwards [Filter.Eventually.of_forall hbound_point] with x hx
      have hnonneg : 0 ≤ (1 + ‖y‖) ^ k * ‖F (zfun x)‖ := by positivity
      have hy1_nonneg : 0 ≤ 1 + ‖y‖ := by positivity
      simpa [zfun, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hy1_nonneg] using hx
  calc
    (1 + ‖y‖) ^ k * ‖sliceIntegralRaw F y‖
        ≤ (1 + ‖y‖) ^ k * ∫ x : ℝ, ‖F (zfun x)‖ := by
            gcongr
    _ = ∫ x : ℝ, (1 + ‖y‖) ^ k * ‖F (zfun x)‖ := by
          rw [← integral_const_mul]
    _ ≤ ∫ x : ℝ, ((2 : ℝ) ^ (k + 2) * S) * (1 + x ^ 2)⁻¹ := by
          refine MeasureTheory.integral_mono_ae hlower_integrable hmajor_integrable ?_
          exact Filter.Eventually.of_forall hbound_point
    _ = C * S := by
          rw [MeasureTheory.integral_const_mul]
          rw [show (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ k * 4 by
            rw [pow_add]
            norm_num]
          simp [C, C0, S]
          ring

/-- Pointwise `x`-decay for a fixed tail slice. This is the basic majorant used
for integrability of the slice map. -/
theorem norm_sliceSection_le_inv_one_add_sq {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) (x : ℝ) :
    ‖F (Fin.cons x y)‖ ≤
      ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
  let S : ℝ := ((Finset.Iic (2, 0)).sup
    (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F
  have hhead : ‖x‖ ≤ ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by
    simpa using (norm_le_pi_norm (Fin.cons x y : Fin (n + 1) → ℝ) 0)
  have hseminorm :
      (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) * ‖F (Fin.cons x y)‖
        ≤ (2 : ℝ) ^ (2 : ℕ) * S := by
    simpa [S] using
      (SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℝ) (m := (2, 0)) (k := 2) (n := 0)
        le_rfl le_rfl F (Fin.cons x y))
  have hx_pos : 0 < (1 + ‖x‖) ^ (2 : ℕ) := by positivity
  have hmain :
      ‖F (Fin.cons x y)‖ ≤ ((2 : ℝ) ^ (2 : ℕ) * S) / (1 + ‖x‖) ^ (2 : ℕ) := by
    refine (le_div_iff₀ hx_pos).2 ?_
    calc
      ‖F (Fin.cons x y)‖ * (1 + ‖x‖) ^ (2 : ℕ)
          ≤ ‖F (Fin.cons x y)‖ * (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) := by
            gcongr
      _ = (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) * ‖F (Fin.cons x y)‖ := by ring
      _ ≤ (2 : ℝ) ^ (2 : ℕ) * S := hseminorm
  have hsq : 1 + x ^ 2 ≤ (1 + ‖x‖) ^ (2 : ℕ) := by
    calc
      1 + x ^ 2 ≤ 1 + 2 * |x| + x ^ 2 := by nlinarith [abs_nonneg x]
      _ = 1 + 2 * |x| + |x| ^ 2 := by rw [sq_abs]
      _ = (1 + |x|) ^ (2 : ℕ) := by ring
      _ = (1 + ‖x‖) ^ (2 : ℕ) := by rw [Real.norm_eq_abs]
  have hsq_inv : ((1 + ‖x‖) ^ (2 : ℕ))⁻¹ ≤ (1 + x ^ 2)⁻¹ := by
    have hpos1 : 0 < 1 + x ^ 2 := by positivity
    simpa [one_div] using (one_div_le_one_div_of_le hpos1 hsq)
  calc
    ‖F (Fin.cons x y)‖
        ≤ ((2 : ℝ) ^ (2 : ℕ) * S) * (((1 + ‖x‖) ^ (2 : ℕ))⁻¹) := by
          simpa [one_div, div_eq_mul_inv] using hmain
    _ ≤ ((2 : ℝ) ^ (2 : ℕ) * S) * (1 + x ^ 2)⁻¹ := by
          gcongr
    _ = ((4 : ℝ) * S) * (1 + x ^ 2)⁻¹ := by norm_num
    _ = ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
          simp [S]

/-- The slice map `y ↦ F (x,y)` is differentiable in the tail variable, with
derivative obtained by composing the ambient Fréchet derivative with the tail
inclusion. -/
theorem hasFDerivAt_sliceSection {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (x : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt
      (fun y' : Fin n → ℝ => F (Fin.cons x y'))
      (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
        (tailInsertCLM n))
      y := by
  let c : Fin (n + 1) → ℝ := Fin.cons x 0
  have hinner :
      HasFDerivAt
        (fun y' : Fin n → ℝ => tailInsertCLM n y' + c)
        (tailInsertCLM n) y := by
    simpa [c, tailInsertCLM_apply, add_comm, add_left_comm, add_assoc]
      using (tailInsertCLM n).hasFDerivAt.add_const c
  have hfun :
      (fun y' : Fin n → ℝ => tailInsertCLM n y' + c) =
        (fun y' : Fin n → ℝ => (Fin.cons x y' : Fin (n + 1) → ℝ)) := by
    funext y'
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [c, tailInsertCLM_apply]
    · intro i
      simp [c, tailInsertCLM_apply]
  have hpt : (Fin.cons 0 y : Fin (n + 1) → ℝ) + c = Fin.cons x y := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [c]
    · intro i
      simp [c]
  have hcons : ∀ y' : Fin n → ℝ, (Fin.cons 0 y' : Fin (n + 1) → ℝ) + c = Fin.cons x y' := by
    intro y'
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [c]
    · intro i
      simp [c]
  simpa [Function.comp, tailInsertCLM_apply, c, hcons, hpt] using
    (F.differentiableAt.hasFDerivAt.comp y hinner)

/-- Pointwise `x`-decay for the first tail derivative of a slice. This is the
majorant needed for the first differentiation-under-integral step. -/
theorem norm_fderiv_fullSlice_le_inv_one_add_sq {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) (x : ℝ) :
    ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ ≤
      ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
  let S : ℝ := ((Finset.Iic (2, 1)).sup
    (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F
  have hhead : ‖x‖ ≤ ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by
    simpa using (norm_le_pi_norm (Fin.cons x y : Fin (n + 1) → ℝ) 0)
  have hseminorm :
      (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) *
        ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖
          ≤ (2 : ℝ) ^ (2 : ℕ) * S := by
    simpa [S] using
      (SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℝ) (m := (2, 1)) (k := 2) (n := 1)
        le_rfl le_rfl F (Fin.cons x y))
  have hx_pos : 0 < (1 + ‖x‖) ^ (2 : ℕ) := by positivity
  have hmain :
      ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖
        ≤ ((2 : ℝ) ^ (2 : ℕ) * S) / (1 + ‖x‖) ^ (2 : ℕ) := by
    refine (le_div_iff₀ hx_pos).2 ?_
    calc
      ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ * (1 + ‖x‖) ^ (2 : ℕ)
          ≤ ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ *
            (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) := by
              gcongr
      _ = (1 + ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖) ^ (2 : ℕ) *
            ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ := by ring
      _ ≤ (2 : ℝ) ^ (2 : ℕ) * S := hseminorm
  have hsq : 1 + x ^ 2 ≤ (1 + ‖x‖) ^ (2 : ℕ) := by
    calc
      1 + x ^ 2 ≤ 1 + 2 * |x| + x ^ 2 := by nlinarith [abs_nonneg x]
      _ = 1 + 2 * |x| + |x| ^ 2 := by rw [sq_abs]
      _ = (1 + |x|) ^ (2 : ℕ) := by ring
      _ = (1 + ‖x‖) ^ (2 : ℕ) := by rw [Real.norm_eq_abs]
  have hsq_inv : ((1 + ‖x‖) ^ (2 : ℕ))⁻¹ ≤ (1 + x ^ 2)⁻¹ := by
    have hpos1 : 0 < 1 + x ^ 2 := by positivity
    simpa [one_div] using (one_div_le_one_div_of_le hpos1 hsq)
  calc
    ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖
        ≤ ((2 : ℝ) ^ (2 : ℕ) * S) * (((1 + ‖x‖) ^ (2 : ℕ))⁻¹) := by
          simpa [one_div, div_eq_mul_inv] using hmain
    _ ≤ ((2 : ℝ) ^ (2 : ℕ) * S) * (1 + x ^ 2)⁻¹ := by
          gcongr
    _ = ((4 : ℝ) * S) * (1 + x ^ 2)⁻¹ := by norm_num
    _ = ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
          simp [S]

/-- Pointwise `x`-decay for the first tail derivative of a slice. This is the
majorant needed for the first differentiation-under-integral step. -/
theorem norm_fderiv_sliceSection_le_inv_one_add_sq {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) (x : ℝ) :
    ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
        (tailInsertCLM n))‖ ≤
      ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
  have hcomp :
      ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
          (tailInsertCLM n))‖
        ≤ ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ *
          ‖tailInsertCLM n‖ := by
    exact ContinuousLinearMap.opNorm_comp_le _ _
  calc
    ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
        (tailInsertCLM n))‖
        ≤ ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ * ‖tailInsertCLM n‖ := hcomp
    _ ≤ ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ * 1 := by
          gcongr
          exact tailInsertCLM_opNorm_le n
    _ = ‖fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)‖ := by ring
    _ ≤ ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹ := by
          exact norm_fderiv_fullSlice_le_inv_one_add_sq F y x

/-- First differentiation-under-integral step for the raw slice map. -/
theorem hasFDerivAt_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) :
    HasFDerivAt
      (sliceIntegralRaw F)
      (∫ x : ℝ,
        (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
          (tailInsertCLM n)))
      y := by
  let bound0 : ℝ → ℝ := fun x =>
    ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹
  let bound1 : ℝ → ℝ := fun x =>
    ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹
  have hs : (Set.univ : Set (Fin n → ℝ)) ∈ nhds y := Filter.univ_mem
  have hF_meas :
      ∀ᶠ y' in nhds y,
        AEStronglyMeasurable
          (fun x : ℝ => F (Fin.cons x y'))
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro y'
    have hcont : Continuous fun x : ℝ => F (Fin.cons x y') := by
      have hpath : Continuous fun x : ℝ => (Fin.cons x y' : Fin (n + 1) → ℝ) := by
        classical
        refine continuous_pi ?_
        intro j
        refine Fin.cases ?_ ?_ j
        · simpa using (continuous_id : Continuous fun x : ℝ => x)
        · intro i
          simpa using (continuous_const : Continuous fun _ : ℝ => y' i)
      exact F.continuous.comp hpath
    exact hcont.aestronglyMeasurable
  have hF_int :
      Integrable (fun x : ℝ => F (Fin.cons x y))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have hbound_int :
        Integrable (fun x : ℝ => bound0 x)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [bound0, mul_comm, mul_left_comm, mul_assoc] using
        integrable_inv_one_add_sq.const_mul
          ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F)
    refine hbound_int.mono' ?_ ?_
    · exact (F.continuous.comp <| by
          classical
          refine continuous_pi ?_
          intro j
          refine Fin.cases ?_ ?_ j
          · simpa using (continuous_id : Continuous fun x : ℝ => x)
          · intro i
            simpa using (continuous_const : Continuous fun _ : ℝ => y i)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (norm_sliceSection_le_inv_one_add_sq F y)
  have hF'_meas :
      AEStronglyMeasurable
        (fun x : ℝ =>
          (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
            (tailInsertCLM n)))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have hpath : Continuous fun x : ℝ => (Fin.cons x y : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun x : ℝ => x)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    have hcont :
        Continuous
          (fun x : ℝ =>
            (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
              (tailInsertCLM n))) := by
      exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
    exact hcont.aestronglyMeasurable
  have h_bound :
      ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
              (tailInsertCLM n))‖ ≤ bound1 x := by
    exact Filter.Eventually.of_forall (fun x y' _ => by
      simpa [bound1] using norm_fderiv_sliceSection_le_inv_one_add_sq F y' x)
  have h_bound_all :
      ∀ x : ℝ, ∀ y' : Fin n → ℝ,
        ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
            (tailInsertCLM n))‖ ≤ bound1 x := by
    intro x y'
    simpa [bound1] using norm_fderiv_sliceSection_le_inv_one_add_sq F y' x
  have h_bound' :
      ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
              (tailInsertCLM n))‖ ≤ bound1 x := by
    exact Filter.Eventually.of_forall (fun x y' _ => h_bound_all x y')
  have h_bound_int :
      Integrable bound1 (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    simpa [bound1, mul_comm, mul_left_comm, mul_assoc] using
      integrable_inv_one_add_sq.const_mul
        ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F)
  have h_diff :
      ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          HasFDerivAt
            (fun y'' : Fin n → ℝ => F (Fin.cons x y''))
            ((((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
              (tailInsertCLM n)))
            y' := by
    exact Filter.Eventually.of_forall
      (fun x y' _ => hasFDerivAt_sliceSection F x y')
  simpa [sliceIntegralRaw] using
    (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (s := (Set.univ : Set (Fin n → ℝ)))
      (x₀ := y)
      (F := fun y' x => F (Fin.cons x y'))
      (F' := fun y' x =>
        (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
          (tailInsertCLM n)))
      hs hF_meas hF_int hF'_meas h_bound' h_bound_int h_diff)

theorem fderiv_sliceIntegralRaw_eq {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) :
    fderiv ℝ (sliceIntegralRaw F) y =
      (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y).comp
        (tailInsertCLM n) := by
  let φ : ℝ → (Fin (n + 1) → ℝ) →L[ℝ] V := fun x =>
    fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)
  have hφ_cont : Continuous φ := by
    have hpath : Continuous fun x : ℝ => (Fin.cons x y : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun x : ℝ => x)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    simpa [φ] using (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath)
  have hφ_int : Integrable φ (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have hbound_int :
        Integrable
          (fun x : ℝ =>
            ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        integrable_inv_one_add_sq.const_mul
          ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F)
    refine hbound_int.mono' hφ_cont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (norm_fderiv_fullSlice_le_inv_one_add_sq F y)
  calc
    fderiv ℝ (sliceIntegralRaw F) y
        = ∫ x : ℝ,
            (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
              (tailInsertCLM n)) := by
              exact (hasFDerivAt_sliceIntegralRaw F y).fderiv
    _ = (∫ x : ℝ, φ x).comp (tailInsertCLM n) := by
          let L :
              ((Fin (n + 1) → ℝ) →L[ℝ] V) →L[ℝ] ((Fin n → ℝ) →L[ℝ] V) :=
            (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n + 1) → ℝ) V).flip
              (tailInsertCLM n)
          have hL : ∀ A : ((Fin (n + 1) → ℝ) →L[ℝ] V), L A = A.comp (tailInsertCLM n) := by
            intro A
            simp [L, ContinuousLinearMap.compL_apply]
          have hcomp :
              (fun x : ℝ =>
                (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
                  (tailInsertCLM n))) =
              fun x : ℝ => L (φ x) := by
            funext x
            simp [φ, hL]
          rw [hcomp, ContinuousLinearMap.integral_comp_comm L hφ_int]
          simp [hL]
    _ = (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y).comp
          (tailInsertCLM n) := by
          simp [sliceIntegralRaw, φ, SchwartzMap.fderivCLM_apply]

theorem continuous_fderiv_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    Continuous (fderiv ℝ (sliceIntegralRaw F)) := by
  let L :
      ((Fin (n + 1) → ℝ) →L[ℝ] V) →L[ℝ] ((Fin n → ℝ) →L[ℝ] V) :=
    (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n + 1) → ℝ) V).flip (tailInsertCLM n)
  have hslice :
      Continuous (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro y
    exact (hasFDerivAt_sliceIntegralRaw
      (V := (Fin (n + 1) → ℝ) →L[ℝ] V)
      (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y).continuousAt
  have hEq :
      fderiv ℝ (sliceIntegralRaw F) =
        fun y =>
          L (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y) := by
    funext y
    simp [L, fderiv_sliceIntegralRaw_eq, ContinuousLinearMap.compL_apply]
  rw [hEq]
  exact L.continuous.comp hslice

theorem contDiff_one_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    ContDiff ℝ 1 (sliceIntegralRaw F) := by
  rw [contDiff_one_iff_fderiv]
  constructor
  · intro y
    exact (hasFDerivAt_sliceIntegralRaw F y).differentiableAt
  · exact continuous_fderiv_sliceIntegralRaw F

theorem sliceIntegralRaw_eq_zero_of_outside_closedBall {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) {R : ℝ}
    (hF : tsupport F ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) R)
    {y : Fin n → ℝ}
    (hy : y ∉ Metric.closedBall (0 : Fin n → ℝ) R) :
    sliceIntegralRaw F y = 0 := by
  have hy_gt : R < ‖y‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm, not_le] using hy
  rw [sliceIntegralRaw]
  refine integral_eq_zero_of_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have hnorm_le : ‖y‖ ≤ ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by
    calc
      ‖y‖ = ‖tailCLM n (E := ℝ) (Fin.cons x y)‖ := by
        simp [tailCLM_apply]
      _ ≤ ‖tailCLM n (E := ℝ)‖ * ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by
        gcongr
        exact tailCLM_opNorm_le (E := ℝ) n
      _ = ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ := by ring
  have hz_not_mem : (Fin.cons x y : Fin (n + 1) → ℝ) ∉ tsupport F := by
    intro hz
    have hball := hF hz
    have hnorm_ball : ‖(Fin.cons x y : Fin (n + 1) → ℝ)‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hball
    exact not_lt_of_ge (le_trans hnorm_le hnorm_ball) hy_gt
  simpa using image_eq_zero_of_notMem_tsupport hz_not_mem

theorem hasCompactSupport_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (hF : HasCompactSupport F) :
    HasCompactSupport (sliceIntegralRaw F) := by
  rcases hF.isCompact.isBounded.subset_closedBall (0 : Fin (n + 1) → ℝ) with ⟨R, hR⟩
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℝ) R) ?_
  intro y hy
  by_contra hyR
  exact hy <|
    sliceIntegralRaw_eq_zero_of_outside_closedBall
      (F := F) (hF := hR) hyR

theorem contDiff_nat_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (m : ℕ) (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    ContDiff ℝ m (sliceIntegralRaw F) := by
  induction m generalizing n V F with
  | zero =>
      exact contDiff_zero.2 <|
        continuous_iff_continuousAt.2 fun y => (hasFDerivAt_sliceIntegralRaw F y).continuousAt
  | succ m ihm =>
      exact (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := m) (f := sliceIntegralRaw F)).2 <|
      let L :
          ((Fin (n + 1) → ℝ) →L[ℝ] V) →L[ℝ] ((Fin n → ℝ) →L[ℝ] V) :=
        (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n + 1) → ℝ) V).flip
          (tailInsertCLM n)
      by
        refine ⟨fun y => ∫ x : ℝ, (fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)).comp
            (tailInsertCLM n), ?_, ?_⟩
        · have hslice :
              ContDiff ℝ m
                (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F)) :=
            ihm (F := SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F)
          have hEq :
              (fun y => ∫ x : ℝ, (fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)).comp
                  (tailInsertCLM n)) =
                fun y => L (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y) := by
            funext y
            calc
              (∫ x : ℝ, (fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)).comp
                  (tailInsertCLM n))
                  = fderiv ℝ (sliceIntegralRaw F) y := by
                      symm
                      exact (hasFDerivAt_sliceIntegralRaw F y).fderiv
              _ = L (sliceIntegralRaw (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y) := by
                    simpa [L] using fderiv_sliceIntegralRaw_eq (F := F) y
          rw [hEq]
          exact L.contDiff.comp hslice
        · intro y
          exact hasFDerivAt_sliceIntegralRaw F y

theorem contDiff_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    ContDiff ℝ (⊤ : ℕ∞) (sliceIntegralRaw F) := by
  rw [contDiff_infty]
  intro m
  exact contDiff_nat_sliceIntegralRaw m F

/-- The `(-∞, 0]` slice integral as a function of the tail variable. This is
the lower-half-line analogue of `sliceIntegralRaw`, and is one half of the
fiberwise antiderivative decomposition used in the two-point factorization
route. -/
def iicZeroSlice {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) : V :=
  ∫ t in Set.Iic (0 : ℝ), F (Fin.cons t y)

/-- The `(-∞, 0]` slice integral is Fréchet differentiable in the tail
variable, with derivative obtained by integrating the ambient derivative
composed with `tailInsertCLM`. This is the restricted-measure version of
`hasFDerivAt_sliceIntegralRaw`. -/
theorem hasFDerivAt_iicZeroSlice {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) :
    HasFDerivAt
      (iicZeroSlice F)
      (∫ x in Set.Iic (0 : ℝ),
        (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
          (tailInsertCLM n)))
      y := by
  let μ : Measure ℝ := MeasureTheory.volume.restrict (Set.Iic (0 : ℝ))
  let bound0 : ℝ → ℝ := fun x =>
    ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹
  let bound1 : ℝ → ℝ := fun x =>
    ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹
  have hs : (Set.univ : Set (Fin n → ℝ)) ∈ nhds y := Filter.univ_mem
  have hF_meas :
      ∀ᶠ y' in nhds y,
        AEStronglyMeasurable (fun x : ℝ => F (Fin.cons x y')) μ := by
    refine Filter.Eventually.of_forall ?_
    intro y'
    have hcont : Continuous fun x : ℝ => F (Fin.cons x y') := by
      have hpath : Continuous fun x : ℝ => (Fin.cons x y' : Fin (n + 1) → ℝ) := by
        classical
        refine continuous_pi ?_
        intro j
        refine Fin.cases ?_ ?_ j
        · simpa using (continuous_id : Continuous fun x : ℝ => x)
        · intro i
          simpa using (continuous_const : Continuous fun _ : ℝ => y' i)
      exact F.continuous.comp hpath
    exact hcont.aestronglyMeasurable.restrict
  have hF_int :
      Integrable (fun x : ℝ => F (Fin.cons x y)) μ := by
    have hbound_int :
        Integrable (fun x : ℝ => bound0 x) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [bound0, mul_comm, mul_left_comm, mul_assoc] using
        integrable_inv_one_add_sq.const_mul
          ((4 : ℝ) * ((Finset.Iic (2, 0)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F)
    have hbound_int' : Integrable (fun x : ℝ => bound0 x) μ := hbound_int.restrict
    refine hbound_int'.mono' ?_ ?_
    · exact ((F.continuous.comp <| by
            classical
            refine continuous_pi ?_
            intro j
            refine Fin.cases ?_ ?_ j
            · simpa using (continuous_id : Continuous fun x : ℝ => x)
            · intro i
              simpa using (continuous_const : Continuous fun _ : ℝ => y i)).aestronglyMeasurable).restrict
    · exact Filter.Eventually.of_forall (norm_sliceSection_le_inv_one_add_sq F y)
  have hF'_meas :
      AEStronglyMeasurable
        (fun x : ℝ =>
          (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
            (tailInsertCLM n)))
        μ := by
    have hpath : Continuous fun x : ℝ => (Fin.cons x y : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun x : ℝ => x)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    have hcont :
        Continuous
          (fun x : ℝ =>
            (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
              (tailInsertCLM n))) := by
      exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
    exact hcont.aestronglyMeasurable.restrict
  have h_bound :
      ∀ᵐ x ∂μ,
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
              (tailInsertCLM n))‖ ≤ bound1 x := by
    exact Filter.Eventually.of_forall (fun x y' _ => by
      simpa [bound1] using norm_fderiv_sliceSection_le_inv_one_add_sq F y' x)
  have h_bound_int :
      Integrable bound1 μ := by
    have hbase :
        Integrable bound1 (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [bound1, mul_comm, mul_left_comm, mul_assoc] using
        integrable_inv_one_add_sq.const_mul
          ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F)
    exact hbase.restrict
  have h_diff :
      ∀ᵐ x ∂μ,
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          HasFDerivAt
            (fun y'' : Fin n → ℝ => F (Fin.cons x y''))
            ((((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
              (tailInsertCLM n)))
            y' := by
    exact Filter.Eventually.of_forall
      (fun x y' _ => hasFDerivAt_sliceSection F x y')
  simpa [iicZeroSlice, μ] using
    (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := μ)
      (s := (Set.univ : Set (Fin n → ℝ)))
      (x₀ := y)
      (F := fun y' x => F (Fin.cons x y'))
      (F' := fun y' x =>
        (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y'))).comp
          (tailInsertCLM n)))
      hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff)

theorem fderiv_iicZeroSlice_eq {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) :
    fderiv ℝ (iicZeroSlice F) y =
      (∫ x in Set.Iic (0 : ℝ),
        fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)).comp
          (tailInsertCLM n) := by
  let μ : Measure ℝ := MeasureTheory.volume.restrict (Set.Iic (0 : ℝ))
  let φ : ℝ → (Fin (n + 1) → ℝ) →L[ℝ] V := fun x =>
    fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)
  have hφ_cont : Continuous φ := by
    have hpath : Continuous fun x : ℝ => (Fin.cons x y : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun x : ℝ => x)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    simpa [φ] using (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath)
  have hφ_int : Integrable φ μ := by
    have hbound_int :
        Integrable
          (fun x : ℝ =>
            ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        integrable_inv_one_add_sq.const_mul
          ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F)
    have hbound_int' :
        Integrable
          (fun x : ℝ =>
            ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹)
          μ := hbound_int.restrict
    refine hbound_int'.mono' hφ_cont.aestronglyMeasurable.restrict ?_
    exact Filter.Eventually.of_forall (norm_fderiv_fullSlice_le_inv_one_add_sq F y)
  calc
    fderiv ℝ (iicZeroSlice F) y
        = ∫ x in Set.Iic (0 : ℝ),
            (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
              (tailInsertCLM n)) := by
              exact (hasFDerivAt_iicZeroSlice F y).fderiv
    _ = (∫ x, φ x ∂μ).comp (tailInsertCLM n) := by
          let L :
              ((Fin (n + 1) → ℝ) →L[ℝ] V) →L[ℝ] ((Fin n → ℝ) →L[ℝ] V) :=
            (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n + 1) → ℝ) V).flip
              (tailInsertCLM n)
          have hL :
              ∀ A : ((Fin (n + 1) → ℝ) →L[ℝ] V), L A = A.comp (tailInsertCLM n) := by
            intro A
            simp [L, ContinuousLinearMap.compL_apply]
          have hcomp :
              (fun x : ℝ =>
                (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
                  (tailInsertCLM n))) =
              fun x : ℝ => L (φ x) := by
            funext x
            simp [φ, hL]
          rw [show ∫ x in Set.Iic (0 : ℝ),
                (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y))).comp
                  (tailInsertCLM n)) = ∫ x, (fun x : ℝ => L (φ x)) x ∂μ by
                simp [μ, hcomp]]
          rw [ContinuousLinearMap.integral_comp_comm L hφ_int]
          simp [hL, μ]
    _ = (∫ x in Set.Iic (0 : ℝ),
          fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)).comp
            (tailInsertCLM n) := by
          simp [μ, φ]

theorem contDiff_nat_iicZeroSlice {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (m : ℕ) (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    ContDiff ℝ m (iicZeroSlice F) := by
  induction m generalizing n V F with
  | zero =>
      exact contDiff_zero.2 <|
        continuous_iff_continuousAt.2 fun y => (hasFDerivAt_iicZeroSlice F y).continuousAt
  | succ m ihm =>
      exact (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := m) (f := iicZeroSlice F)).2 <|
      let L :
          ((Fin (n + 1) → ℝ) →L[ℝ] V) →L[ℝ] ((Fin n → ℝ) →L[ℝ] V) :=
        (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n + 1) → ℝ) V).flip
          (tailInsertCLM n)
      by
        refine ⟨fun y => ∫ x in Set.Iic (0 : ℝ),
            (fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)).comp (tailInsertCLM n), ?_, ?_⟩
        · have hslice :
              ContDiff ℝ m
                (iicZeroSlice (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F)) :=
            ihm (F := SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F)
          have hEq :
              (fun y => ∫ x in Set.Iic (0 : ℝ),
                  (fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)).comp
                    (tailInsertCLM n)) =
                fun y =>
                  L (iicZeroSlice (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y) := by
            funext y
            let φ : ℝ → (Fin (n + 1) → ℝ) →L[ℝ] V := fun x =>
              fderiv ℝ (F : (Fin (n + 1) → ℝ) → V) (Fin.cons x y)
            have hφ_cont : Continuous φ := by
              have hpath : Continuous fun x : ℝ => (Fin.cons x y : Fin (n + 1) → ℝ) := by
                classical
                refine continuous_pi ?_
                intro j
                refine Fin.cases ?_ ?_ j
                · simpa using (continuous_id : Continuous fun x : ℝ => x)
                · intro i
                  simpa using (continuous_const : Continuous fun _ : ℝ => y i)
              simpa [φ] using (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath)
            have hφ_int :
                Integrable φ (MeasureTheory.volume.restrict (Set.Iic (0 : ℝ))) := by
              have hbound_int :
                  Integrable
                    (fun x : ℝ =>
                      ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
                        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹)
                    (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  integrable_inv_one_add_sq.const_mul
                    ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
                      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F)
              have hbound_int' :
                  Integrable
                    (fun x : ℝ =>
                      ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
                        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F) * (1 + x ^ 2)⁻¹)
                    (MeasureTheory.volume.restrict (Set.Iic (0 : ℝ))) := hbound_int.restrict
              refine hbound_int'.mono' hφ_cont.aestronglyMeasurable.restrict ?_
              exact Filter.Eventually.of_forall (norm_fderiv_fullSlice_le_inv_one_add_sq F y)
            change ∫ x, L (φ x) ∂(MeasureTheory.volume.restrict (Set.Iic (0 : ℝ))) =
              L (∫ x, φ x ∂(MeasureTheory.volume.restrict (Set.Iic (0 : ℝ))))
            rw [ContinuousLinearMap.integral_comp_comm L hφ_int]
          rw [hEq]
          exact L.contDiff.comp hslice
        · intro y
          exact hasFDerivAt_iicZeroSlice F y

/-- The `(-∞, 0]` slice is smooth in the tail variable. -/
theorem contDiff_iicZeroSlice {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    ContDiff ℝ (⊤ : ℕ∞) (iicZeroSlice F) := by
  rw [contDiff_infty]
  intro m
  exact contDiff_nat_iicZeroSlice m F

/-- The raw slice map is itself Schwartz. This is the genuine induction
ingredient used in the multi-dimensional zero-mean decomposition. -/
theorem decay_sliceIntegralRaw {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (k m : ℕ) :
    ∃ C : ℝ, ∀ y : Fin n → ℝ,
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (sliceIntegralRaw F) y‖ ≤ C := by
  induction m generalizing V n F with
  | zero =>
      obtain ⟨C0, hC0_nonneg, hC0⟩ :=
        exists_one_add_norm_pow_mul_sliceIntegralRaw_le (n := n) (k := k) (V := V)
      let C : ℝ :=
        C0 * ((Finset.Iic (k + 2, 0)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F
      refine ⟨C, ?_⟩
      intro y
      calc
        ‖y‖ ^ k * ‖iteratedFDeriv ℝ 0 (sliceIntegralRaw F) y‖
            = ‖y‖ ^ k * ‖sliceIntegralRaw F y‖ := by
                rw [norm_iteratedFDeriv_zero]
        _ ≤ (1 + ‖y‖) ^ k * ‖sliceIntegralRaw F y‖ := by
              have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
              have hy_le : ‖y‖ ≤ 1 + ‖y‖ := by linarith
              exact mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ hy_nonneg hy_le k) (norm_nonneg _)
        _ ≤ C0 * ((Finset.Iic (k + 2, 0)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) V)) F := hC0 F y
        _ = C := by rfl
  | succ m ihm =>
      let F' : SchwartzMap (Fin (n + 1) → ℝ) ((Fin (n + 1) → ℝ) →L[ℝ] V) :=
        SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F
      have hIH := ihm (V := (Fin (n + 1) → ℝ) →L[ℝ] V) (n := n) (F := F')
      obtain ⟨C, hC⟩ := hIH
      let L :
          ((Fin (n + 1) → ℝ) →L[ℝ] V) →L[ℝ] ((Fin n → ℝ) →L[ℝ] V) :=
        (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin (n + 1) → ℝ) V).flip
          (tailInsertCLM n)
      let C' : ℝ := ‖L‖ * C
      refine ⟨C', ?_⟩
      intro y
      have hEq :
          fderiv ℝ (sliceIntegralRaw F) =
            fun y =>
              L (sliceIntegralRaw
                (SchwartzMap.fderivCLM ℝ (Fin (n + 1) → ℝ) V F) y) := by
        funext y'
        simp [L, fderiv_sliceIntegralRaw_eq, ContinuousLinearMap.compL_apply]
      calc
        ‖y‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) (sliceIntegralRaw F) y‖
            = ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fderiv ℝ (sliceIntegralRaw F)) y‖ := by
                rw [norm_iteratedFDeriv_fderiv]
        _ = ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (L ∘ sliceIntegralRaw F') y‖ := by
              have hcompEq : (fun y => L (sliceIntegralRaw F' y)) = L ∘ sliceIntegralRaw F' := rfl
              rw [hEq, hcompEq]
        _ ≤ ‖y‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ m (sliceIntegralRaw F') y‖) := by
              gcongr
              exact L.norm_iteratedFDeriv_comp_left
                ((contDiff_sliceIntegralRaw F').contDiffAt) (by exact_mod_cast le_top)
        _ = ‖L‖ * (‖y‖ ^ k * ‖iteratedFDeriv ℝ m (sliceIntegralRaw F') y‖) := by
              ring
        _ ≤ ‖L‖ * C := by
              gcongr
              exact hC y
        _ = C' := by rfl

/-- Integrating out the head coordinate preserves the Schwartz class. -/
noncomputable def sliceIntegral {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) :
    SchwartzMap (Fin n → ℝ) V where
  toFun := sliceIntegralRaw F
  smooth' := contDiff_sliceIntegralRaw F
  decay' := decay_sliceIntegralRaw F

@[simp] theorem sliceIntegral_apply {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (Fin (n + 1) → ℝ) V) (y : Fin n → ℝ) :
    sliceIntegral F y = sliceIntegralRaw F y := rfl

theorem integral_sliceIntegral {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))
        (sliceIntegral F)
      =
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ))) F := by
  simp [SchwartzMap.integralCLM_apply, integral_sliceIntegralRaw]

/-- For a fixed tail variable, the head slice of a Schwartz function is
integrable on `ℝ`. This is the basic analytic input for the fiberwise
antiderivative construction. -/
theorem integrable_sliceSection {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (y : Fin n → ℝ) :
    Integrable (fun x : ℝ => F (Fin.cons x y))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  let C : ℝ :=
    (4 : ℝ) * ((Finset.Iic (2, 0)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F
  have hmajor_int :
      Integrable (fun x : ℝ => C * (1 + x ^ 2)⁻¹)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    simpa [C, mul_comm, mul_left_comm, mul_assoc] using
      (integrable_inv_one_add_sq.const_mul C)
  have hcons_cont : Continuous (fun x : ℝ => (Fin.cons x y : Fin (n + 1) → ℝ)) := by
    classical
    refine continuous_pi ?_
    intro j
    refine Fin.cases ?_ ?_ j
    · simpa using (continuous_id : Continuous fun x : ℝ => x)
    · intro i
      simpa using (continuous_const : Continuous fun _ : ℝ => y i)
  refine hmajor_int.mono' ?_ ?_
  · exact (F.continuous.comp hcons_cont).aestronglyMeasurable
  · filter_upwards [Filter.Eventually.of_forall
      (norm_sliceSection_le_inv_one_add_sq (F := F) (y := y))] with x hx
    exact hx

theorem sliceIntegral_smul {n : ℕ}
    (c : ℂ) (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    sliceIntegral (c • F) = c • sliceIntegral F := by
  ext y
  simp only [sliceIntegral_apply, sliceIntegralRaw]
  change ∫ x : ℝ, c * F (Fin.cons x y) = c * ∫ x : ℝ, F (Fin.cons x y)
  exact MeasureTheory.integral_const_mul c _

@[simp] theorem sliceIntegral_prependField {n : ℕ}
    (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n → ℝ) ℂ) :
    sliceIntegral (φ.prependField g) =
      (∫ x : ℝ, φ x) • g := by
  ext y
  simp [sliceIntegral_apply, sliceIntegralRaw_prependField, smul_eq_mul]

@[simp] theorem sliceIntegral_prependField_eq_self {n : ℕ}
    (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n → ℝ) ℂ)
    (hφ : ∫ x : ℝ, φ x = 1) :
    sliceIntegral (φ.prependField g) = g := by
  rw [sliceIntegral_prependField, hφ, one_smul]

/-- The improper integral over `(-∞, x]` has derivative equal to the integrand,
for continuous integrable functions. This is the scalar FTC input needed for the
head-direction derivative of the fiberwise antiderivative. -/
theorem hasDerivAt_integral_Iic {f : ℝ → ℂ}
    (hf_cont : Continuous f)
    (hf_int : Integrable f (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (a : ℝ) :
    HasDerivAt (fun x => ∫ t in Set.Iic x, f t) (f a) a := by
  have hsplit :
      ∀ x : ℝ,
        ∫ t in Set.Iic x, f t
          = (∫ t in (0 : ℝ)..x, f t) + ∫ t in Set.Iic (0 : ℝ), f t := by
    intro x
    have hIic_x :
        Filter.Tendsto (fun r => ∫ t in r..x, f t) Filter.atBot
          (nhds (∫ t in Set.Iic x, f t)) :=
      intervalIntegral_tendsto_integral_Iic x hf_int.integrableOn Filter.tendsto_id
    have hIic_zero :
        Filter.Tendsto (fun r => ∫ t in r..(0 : ℝ), f t) Filter.atBot
          (nhds (∫ t in Set.Iic (0 : ℝ), f t)) :=
      intervalIntegral_tendsto_integral_Iic 0 hf_int.integrableOn Filter.tendsto_id
    have hadd :
        ∀ r : ℝ,
          ∫ t in r..x, f t =
            (∫ t in r..(0 : ℝ), f t) + ∫ t in (0 : ℝ)..x, f t := by
      intro r
      exact (intervalIntegral.integral_add_adjacent_intervals
        hf_int.intervalIntegrable hf_int.intervalIntegrable).symm
    have hlim :=
      hIic_zero.add_const (∫ t in (0 : ℝ)..x, f t)
    have heq_lim :
        Filter.Tendsto (fun r => ∫ t in r..x, f t) Filter.atBot
          (nhds ((∫ t in Set.Iic (0 : ℝ), f t) + ∫ t in (0 : ℝ)..x, f t)) :=
      Filter.Tendsto.congr' (Filter.Eventually.of_forall fun r => (hadd r).symm) hlim
    rw [tendsto_nhds_unique hIic_x heq_lim, add_comm]
  have heq :
      (fun x => ∫ t in Set.Iic x, f t)
        = fun x => (∫ t in (0 : ℝ)..x, f t) + ∫ t in Set.Iic (0 : ℝ), f t := by
    funext x
    exact hsplit x
  rw [heq]
  have hinterval :
      HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, f t) (f a) a :=
    intervalIntegral.integral_hasDerivAt_right
      hf_int.intervalIntegrable
      (hf_cont.measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
      hf_cont.continuousAt
  let c : ℂ := ∫ t in Set.Iic (0 : ℝ), f t
  have hsum :
      HasDerivAt
        (fun x => (∫ t in (0 : ℝ)..x, f t) + c)
        (f a) a := by
    simpa [c] using hinterval.add_const c
  simpa [c] using hsum

/-- The variable-limit interval piece of the head antiderivative construction. -/
def intervalPiece {n : ℕ} (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (v : Fin (n + 1) → ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..(v 0), F (Fin.cons t (Fin.tail v))

/-- In the head direction, the interval piece differentiates to the original
Schwartz function by the one-variable FTC. -/
theorem hasDerivAt_intervalPiece_head {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (v : Fin (n + 1) → ℝ) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, F (Fin.cons t (Fin.tail v)))
      (F v) (v 0) := by
  set y : Fin n → ℝ := Fin.tail v
  have hcont : Continuous (fun t : ℝ => F (Fin.cons t y)) := by
    exact F.continuous.comp (continuous_pi fun j =>
      Fin.cases continuous_id (fun _ => continuous_const) j)
  have hFTC : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, F (Fin.cons t y))
      (F (Fin.cons (v 0) y)) (v 0) :=
    intervalIntegral.integral_hasDerivAt_right
      (integrable_sliceSection F y).intervalIntegrable
      (hcont.measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
      hcont.continuousAt
  rwa [show F (Fin.cons (v 0) y) = F v from congr_arg F (Fin.cons_self_tail v)] at hFTC

/-- For fixed upper limit `a`, the interval piece is Fréchet differentiable in
the tail variables, with derivative obtained by integrating the ambient
derivative composed with `tailInsertCLM`. -/
theorem hasFDerivAt_intervalPiece_tailFixed {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (a : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt
      (fun y' : Fin n → ℝ => ∫ t in (0 : ℝ)..a, F (Fin.cons t y'))
      (∫ t in (0 : ℝ)..a,
        (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y))).comp
          (tailInsertCLM n)))
      y := by
  let bound1 : ℝ → ℝ := fun x =>
    ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * (1 + x ^ 2)⁻¹
  have hs : (Set.univ : Set (Fin n → ℝ)) ∈ nhds y := Filter.univ_mem
  have hF_meas :
      ∀ᶠ y' in nhds y,
        AEStronglyMeasurable (fun t : ℝ => F (Fin.cons t y'))
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) a)) := by
    refine Filter.Eventually.of_forall ?_
    intro y'
    have hcont : Continuous (fun t : ℝ => F (Fin.cons t y')) := by
      have hpath : Continuous fun t : ℝ => (Fin.cons t y' : Fin (n + 1) → ℝ) := by
        classical
        refine continuous_pi ?_
        intro j
        refine Fin.cases ?_ ?_ j
        · simpa using (continuous_id : Continuous fun t : ℝ => t)
        · intro i
          simpa using (continuous_const : Continuous fun _ : ℝ => y' i)
      exact F.continuous.comp hpath
    exact hcont.aestronglyMeasurable.restrict
  have hF_int :
      IntervalIntegrable (fun t : ℝ => F (Fin.cons t y)) MeasureTheory.volume (0 : ℝ) a := by
    exact (integrable_sliceSection F y).intervalIntegrable
  have hF'_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y))).comp
            (tailInsertCLM n)))
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) a)) := by
    have hpath : Continuous fun t : ℝ => (Fin.cons t y : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun t : ℝ => t)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    have hcont :
        Continuous
          (fun t : ℝ =>
            (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y))).comp
              (tailInsertCLM n))) := by
      exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
    exact hcont.aestronglyMeasurable.restrict
  have h_bound :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) a)),
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y'))).comp
              (tailInsertCLM n))‖ ≤ bound1 t := by
    exact Filter.Eventually.of_forall (fun t y' _ => by
      simpa [bound1] using norm_fderiv_sliceSection_le_inv_one_add_sq F y' t)
  have h_bound_int :
      IntervalIntegrable bound1 MeasureTheory.volume (0 : ℝ) a := by
    exact (integrable_inv_one_add_sq.const_mul
      ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F)).intervalIntegrable
  have h_diff :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) a)),
        ∀ y' ∈ (Set.univ : Set (Fin n → ℝ)),
          HasFDerivAt
            (fun y'' : Fin n → ℝ => F (Fin.cons t y''))
            ((((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y'))).comp
              (tailInsertCLM n)))
            y' := by
    exact Filter.Eventually.of_forall
      (fun t y' _ => hasFDerivAt_sliceSection F t y')
  exact
    (hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (μ := MeasureTheory.volume)
      (s := (Set.univ : Set (Fin n → ℝ)))
      (x₀ := y)
      (F := fun y' t => F (Fin.cons t y'))
      (F' := fun y' t =>
        (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t y'))).comp
          (tailInsertCLM n)))
      (a := (0 : ℝ)) (b := a)
      hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff)

/-- Splitting the interval piece at a base point `a`. This is the clean
algebraic decomposition behind the product-space derivative proof. -/
theorem intervalPiece_split_at {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (a x : ℝ) (y : Fin n → ℝ) :
    (∫ t in (0 : ℝ)..x, F (Fin.cons t y)) =
      (∫ t in (0 : ℝ)..a, F (Fin.cons t y)) +
      ∫ t in a..x, F (Fin.cons t y) := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    (integrable_sliceSection F y).intervalIntegrable
    (integrable_sliceSection F y).intervalIntegrable).symm

/-- The fixed-interval tail piece is Fréchet differentiable on the product
space; its derivative only sees the tail variable. -/
theorem hasFDerivAt_intervalPiece_tailFixed_prod {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (a : ℝ) (p : ℝ × (Fin n → ℝ)) :
    HasFDerivAt
      (fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..a, F (Fin.cons t q.2))
      ((∫ t in (0 : ℝ)..a,
          (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t p.2))).comp
            (tailInsertCLM n))).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))
      p := by
  simpa using
    (hasFDerivAt_intervalPiece_tailFixed F a p.2).comp p hasFDerivAt_snd

/-- The fixed-tail moving-endpoint piece is Fréchet differentiable on the
product space; its derivative only sees the head variable. -/
theorem hasFDerivAt_intervalPiece_headFixed_prod {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (p : ℝ × (Fin n → ℝ)) :
    HasFDerivAt
      (fun q : ℝ × (Fin n → ℝ) => ∫ t in p.1..q.1, F (Fin.cons t p.2))
      ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight
        (F (Fin.cons p.1 p.2)))
      p := by
  have hcont : Continuous (fun t : ℝ => F (Fin.cons t p.2)) := by
    have hpath : Continuous fun t : ℝ => (Fin.cons t p.2 : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun t : ℝ => t)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => p.2 i)
    exact F.continuous.comp hpath
  have hhead :
      HasDerivAt (fun x : ℝ => ∫ t in p.1..x, F (Fin.cons t p.2))
        (F (Fin.cons p.1 p.2)) p.1 := by
    exact intervalIntegral.integral_hasDerivAt_right
      (integrable_sliceSection F p.2).intervalIntegrable
      (hcont.measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
      hcont.continuousAt
  have hfst :
      HasFDerivAt
        (fun q : ℝ × (Fin n → ℝ) => q.1)
        (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))
        p := hasFDerivAt_fst
  simpa using hhead.hasFDerivAt.comp p hfst

/-- The remaining error term after splitting the interval piece into the
fixed-interval tail piece and the fixed-tail moving-endpoint piece. This is the
only nonlinear interaction still missing in the joint product-space derivative. -/
def intervalPieceShortTailError {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (p q : ℝ × (Fin n → ℝ)) : ℂ :=
  ∫ t in p.1..q.1, (F (Fin.cons t q.2) - F (Fin.cons t p.2))

/-- Exact product-space decomposition of the interval piece around a base point
`p = (a, y)`. The first term has only tail variation, the second only head
variation, and the third is the genuine mixed error term. -/
theorem intervalPiece_prod_split {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (p q : ℝ × (Fin n → ℝ)) :
    ∫ t in (0 : ℝ)..q.1, F (Fin.cons t q.2) =
      (∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
      (∫ t in p.1..q.1, F (Fin.cons t p.2)) +
      intervalPieceShortTailError F p q := by
  rw [intervalPieceShortTailError]
  have hp_int :
      IntervalIntegrable (fun t : ℝ => F (Fin.cons t p.2)) MeasureTheory.volume p.1 q.1 := by
    exact (integrable_sliceSection F p.2).intervalIntegrable
  have hq_int :
      IntervalIntegrable (fun t : ℝ => F (Fin.cons t q.2)) MeasureTheory.volume p.1 q.1 := by
    exact (integrable_sliceSection F q.2).intervalIntegrable
  have hsub_int :
      IntervalIntegrable
        (fun t : ℝ => F (Fin.cons t q.2) - F (Fin.cons t p.2)) MeasureTheory.volume p.1 q.1 := by
    exact hq_int.sub hp_int
  calc
    ∫ t in (0 : ℝ)..q.1, F (Fin.cons t q.2)
        = (∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
            ∫ t in p.1..q.1, F (Fin.cons t q.2) := by
              exact intervalPiece_split_at F p.1 q.1 q.2
    _ =
        (∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
          ((∫ t in p.1..q.1, F (Fin.cons t p.2)) +
            ∫ t in p.1..q.1, (F (Fin.cons t q.2) - F (Fin.cons t p.2))) := by
              congr 1
              calc
                ∫ t in p.1..q.1, F (Fin.cons t q.2)
                    = ∫ t in p.1..q.1,
                        (F (Fin.cons t p.2) +
                          (F (Fin.cons t q.2) - F (Fin.cons t p.2))) := by
                            refine intervalIntegral.integral_congr_ae ?_
                            exact Filter.Eventually.of_forall (fun t _ => by ring)
                _ =
                    (∫ t in p.1..q.1, F (Fin.cons t p.2)) +
                    ∫ t in p.1..q.1, (F (Fin.cons t q.2) - F (Fin.cons t p.2)) := by
                      exact intervalIntegral.integral_add hp_int hsub_int
    _ =
        (∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
          (∫ t in p.1..q.1, F (Fin.cons t p.2)) +
          ∫ t in p.1..q.1, (F (Fin.cons t q.2) - F (Fin.cons t p.2)) := by
            ring_nf

/-- The mixed short-tail error is quadratic in the head/tail increments: its
norm is bounded by a global Schwartz seminorm constant times
`|q₀ - p₀| * ‖q_tail - p_tail‖`. -/
theorem norm_intervalPieceShortTailError_le {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (p q : ℝ × (Fin n → ℝ)) :
    ‖intervalPieceShortTailError F p q‖ ≤
      (((4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖q.2 - p.2‖) *
        |q.1 - p.1| := by
  rw [intervalPieceShortTailError]
  let C : ℝ :=
    ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖q.2 - p.2‖
  have hmain :
      ‖∫ t in p.1..q.1, (F (Fin.cons t q.2) - F (Fin.cons t p.2))‖ ≤
        C * |q.1 - p.1| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    have hdiff :
        ∀ z : Fin n → ℝ, DifferentiableAt ℝ (fun y' : Fin n → ℝ => F (Fin.cons t y')) z := by
      intro z
      exact (hasFDerivAt_sliceSection F t z).differentiableAt
    have hbound :
        ∀ z : Fin n → ℝ,
          ‖fderiv ℝ (fun y' : Fin n → ℝ => F (Fin.cons t y')) z‖ ≤
            (4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F := by
      intro z
      calc
        ‖fderiv ℝ (fun y' : Fin n → ℝ => F (Fin.cons t y')) z‖
            = ‖(((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t z))).comp
                (tailInsertCLM n))‖ := by
                  simpa using congrArg norm (hasFDerivAt_sliceSection F t z).fderiv
        _ ≤ ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * (1 + t ^ 2)⁻¹ := by
              simpa using norm_fderiv_sliceSection_le_inv_one_add_sq F z t
        _ ≤ (4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F := by
              have hone : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
              have hinv : (1 + t ^ 2)⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hone
              have hCnonneg :
                  0 ≤ (4 : ℝ) * ((Finset.Iic (2, 1)).sup
                    (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F := by
                positivity
              have hm := mul_le_mul_of_nonneg_left hinv hCnonneg
              simpa using hm
    have hmv :
        ‖F (Fin.cons t q.2) - F (Fin.cons t p.2)‖ ≤
          ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖q.2 - p.2‖ := by
      simpa using
        (Convex.norm_image_sub_le_of_norm_fderiv_le
          (s := (Set.univ : Set (Fin n → ℝ)))
          (f := fun y' : Fin n → ℝ => F (Fin.cons t y'))
          (x := p.2) (y := q.2)
          (fun z _ => hdiff z)
          (fun z _ => hbound z)
          convex_univ (by simp) (by simp))
    simpa [C] using hmv
  simpa [C, mul_assoc, mul_left_comm, mul_comm] using hmain

/-- The mixed short-tail error has zero Fréchet derivative at the base point.
This is the key nonlinear remainder estimate behind the full derivative of the
interval piece. -/
theorem hasFDerivAt_intervalPieceShortTailError {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (p : ℝ × (Fin n → ℝ)) :
    HasFDerivAt (intervalPieceShortTailError F p)
      (0 : (ℝ × (Fin n → ℝ)) →L[ℝ] ℂ) p := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hp0 : intervalPieceShortTailError F p p = 0 := by
    simp [intervalPieceShortTailError]
  have hbig :
      (fun h : ℝ × (Fin n → ℝ) => intervalPieceShortTailError F p (p + h)) =O[𝓝 0]
        fun h : ℝ × (Fin n → ℝ) => ‖h‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound
      ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) ?_
    refine Filter.Eventually.of_forall ?_
    intro h
    have hbase := norm_intervalPieceShortTailError_le F p (p + h)
    have hfst : |h.1| ≤ ‖h‖ := by
      calc
        |h.1| = ‖h.1‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖h‖ := by
          calc
            ‖h.1‖ = ‖ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ) h‖ := by rfl
            _ ≤ ‖ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)‖ * ‖h‖ := by
                  exact ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖h‖ := by
                  gcongr
                  exact ContinuousLinearMap.norm_fst_le ℝ ℝ (Fin n → ℝ)
            _ = ‖h‖ := by ring
    have hsnd : ‖h.2‖ ≤ ‖h‖ := by
      calc
        ‖h.2‖ = ‖ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ) h‖ := by rfl
        _ ≤ ‖ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)‖ * ‖h‖ := by
              exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖h‖ := by
              gcongr
              exact ContinuousLinearMap.norm_snd_le ℝ ℝ (Fin n → ℝ)
        _ = ‖h‖ := by ring
    have hCnonneg :
        0 ≤ (4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F := by
      positivity
    have hprod :
        (((4 : ℝ) * ((Finset.Iic (2, 1)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖h.2‖) * |h.1| ≤
          ((4 : ℝ) * ((Finset.Iic (2, 1)).sup
            (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖h‖ ^ 2 := by
      have hmul :
          ‖h.2‖ * |h.1| ≤ ‖h‖ * ‖h‖ := by
        exact mul_le_mul hsnd hfst (abs_nonneg _) (norm_nonneg _)
      have hleft := mul_le_mul_of_nonneg_left hmul hCnonneg
      simpa [pow_two, mul_assoc] using hleft
    have hsimp :
        ‖intervalPieceShortTailError F p (p + h)‖ ≤
          (((4 : ℝ) * ((Finset.Iic (2, 1)).sup
              (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F) * ‖h.2‖) * |h.1| := by
      simpa [Prod.fst_add, Prod.snd_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbase
    refine hsimp.trans ?_
    refine hprod.trans ?_
    have hsq_nonneg : 0 ≤ ‖h‖ ^ 2 := by positivity
    simp [Real.norm_of_nonneg hsq_nonneg]
  have hsmall :
      (fun h : ℝ × (Fin n → ℝ) =>
        intervalPieceShortTailError F p (p + h) - intervalPieceShortTailError F p p) =o[𝓝 0]
          fun h : ℝ × (Fin n → ℝ) => h := by
    simpa [hp0] using
      hbig.trans_isLittleO
        (Asymptotics.isLittleO_norm_pow_id (E' := ℝ × (Fin n → ℝ)) one_lt_two)
  simpa using hsmall

/-- The head/tail coordinate map on `Fin (n+1) → ℝ`. -/
noncomputable def headTailCLM (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
  (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0).prod
    (tailCLM n (E := ℝ))

@[simp] theorem headTailCLM_apply {n : ℕ} (v : Fin (n + 1) → ℝ) :
    headTailCLM n v = (v 0, Fin.tail v) := rfl

/-- Product-space Fréchet derivative of the interval piece. This is the clean
assembly of the head FTC term, the tail DCT term, and the zero-derivative mixed
error. -/
theorem hasFDerivAt_intervalPiece_prod {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (p : ℝ × (Fin n → ℝ)) :
    HasFDerivAt
      (fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..q.1, F (Fin.cons t q.2))
      (((∫ t in (0 : ℝ)..p.1,
          (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t p.2))).comp
            (tailInsertCLM n))).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))) +
        ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight
          (F (Fin.cons p.1 p.2))))
      p := by
  have hsplit :
      (fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..q.1, F (Fin.cons t q.2)) =
        (fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
        (fun q : ℝ × (Fin n → ℝ) => ∫ t in p.1..q.1, F (Fin.cons t p.2)) +
        intervalPieceShortTailError F p := by
    funext q
    simpa [Pi.add_apply, add_assoc] using intervalPiece_prod_split F p q
  have htail := hasFDerivAt_intervalPiece_tailFixed_prod F p.1 p
  have hhead := hasFDerivAt_intervalPiece_headFixed_prod F p
  have herr := hasFDerivAt_intervalPieceShortTailError F p
  have hsum :
      HasFDerivAt
        ((fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..p.1, F (Fin.cons t q.2)) +
          (fun q : ℝ × (Fin n → ℝ) => ∫ t in p.1..q.1, F (Fin.cons t p.2)) +
          intervalPieceShortTailError F p)
        ((((∫ t in (0 : ℝ)..p.1,
            (((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t p.2))).comp
              (tailInsertCLM n))).comp
            (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))) +
          ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight
            (F (Fin.cons p.1 p.2)))) +
          (0 : (ℝ × (Fin n → ℝ)) →L[ℝ] ℂ))
        p := by
    exact (htail.add hhead).add herr
  simpa [hsplit, add_assoc] using hsum

/-- The interval piece is C^1 (combining FTC for head + DCT for tail).
This is the key HasFDerivAt step. -/
theorem hasFDerivAt_intervalPiece {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (v : Fin (n + 1) → ℝ) :
    HasFDerivAt (intervalPiece F)
      (ContinuousLinearMap.smulRight
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0) (F v) +
       (∫ t in (0 : ℝ)..(v 0),
          ((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail v))).comp
            (tailInsertCLM n))).comp (tailCLM n (E := ℝ)))
       v := by
  have hprod := hasFDerivAt_intervalPiece_prod F (headTailCLM n v)
  have hcomp :
      HasFDerivAt (fun w : Fin (n + 1) → ℝ => headTailCLM n w) (headTailCLM n) v := by
    simpa using (headTailCLM n).hasFDerivAt
  have h := hprod.comp v hcomp
  let Ltail : (Fin n → ℝ) →L[ℝ] ℂ :=
    ∫ t in (0 : ℝ)..(v 0),
      ((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail v))).comp
        (tailInsertCLM n))
  let LprodComp : (Fin (n + 1) → ℝ) →L[ℝ] ℂ :=
    ((Ltail.comp (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))).comp (headTailCLM n)) +
      (((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight
        (F (Fin.cons (v 0) (Fin.tail v)))).comp (headTailCLM n))
  let Ltarget : (Fin (n + 1) → ℝ) →L[ℝ] ℂ :=
    ContinuousLinearMap.smulRight
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0) (F v) +
      Ltail.comp (tailCLM n (E := ℝ))
  have h' :
      HasFDerivAt
        ((fun q : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..q.1, F (Fin.cons t q.2)) ∘ headTailCLM n)
        LprodComp
        v := by
    simpa [LprodComp, Ltail, headTailCLM_apply, Fin.cons_self_tail] using h
  have hL : LprodComp = Ltarget := by
    ext w
    simp [LprodComp, Ltarget, Ltail, headTailCLM, tailCLM_apply,
      ContinuousLinearMap.comp_apply, Fin.cons_self_tail, add_comm]
  simpa [intervalPiece, Ltarget, hL] using h'

/-- The interval piece is C^∞. Proof by induction on derivative order:
- Head derivative of intervalPiece F = F (Schwartz, hence C^∞)
- Tail derivative of intervalPiece F = intervalPiece (fderivCLM F) ∘ tailInsertCLM
  (same structure, apply IH)
- Combined: C^{m+1} from C^m of both derivatives. -/
theorem contDiff_intervalPiece {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (intervalPiece F) := by
  rw [contDiff_infty]
  intro m
  induction m generalizing F with
  | zero =>
      exact contDiff_zero.2 <|
        continuous_iff_continuousAt.2 fun x => (hasFDerivAt_intervalPiece F x).continuousAt
  | succ m ih =>
      simpa using
        (contDiff_succ_iff_fderiv_apply
          (𝕜 := ℝ) (D := Fin (n + 1) → ℝ)
          (n := (m : ℕ∞)) (f := intervalPiece F)).2 <|
          ⟨fun x => (hasFDerivAt_intervalPiece F x).differentiableAt, by simp,
            fun y => by
              let ytail : Fin (n + 1) → ℝ := tailInsertCLM n (tailCLM n y)
              let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ := lineDerivOp ytail F
              have hEq :
                  (fun x : Fin (n + 1) → ℝ => (fderiv ℝ (intervalPiece F) x) y) =
                    fun x : Fin (n + 1) → ℝ =>
                      (y 0 : ℝ) • F x + intervalPiece dF x := by
                funext x
                let φ : ℝ → (Fin n → ℝ) →L[ℝ] ℂ := fun t =>
                  ((fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail x))).comp
                    (tailInsertCLM n))
                have hφ_cont :
                    Continuous φ := by
                  have hpath : Continuous fun t : ℝ => (Fin.cons t (Fin.tail x) : Fin (n + 1) → ℝ) := by
                    classical
                    refine continuous_pi ?_
                    intro j
                    refine Fin.cases ?_ ?_ j
                    · simpa using (continuous_id : Continuous fun t : ℝ => t)
                    · intro i
                      simpa using (continuous_const : Continuous fun _ : ℝ => Fin.tail x i)
                  simpa [φ] using
                    (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
                have hφ_int :
                    IntervalIntegrable φ MeasureTheory.volume (0 : ℝ) (x 0) := by
                  exact hφ_cont.intervalIntegrable _ _
                rw [(hasFDerivAt_intervalPiece F x).fderiv]
                calc
                  ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0).smulRight (F x) +
                      ((∫ t in (0 : ℝ)..(x 0), φ t).comp (tailCLM n (E := ℝ)))) y
                      = (y 0 : ℝ) • F x + (∫ t in (0 : ℝ)..(x 0), φ t) (Fin.tail y) := by
                          simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
                            ContinuousLinearMap.add_apply, ContinuousLinearMap.proj_apply,
                            tailCLM_apply]
                          congr 1
                  _ = (y 0 : ℝ) • F x + ∫ t in (0 : ℝ)..(x 0), (φ t) (Fin.tail y) := by
                          rw [ContinuousLinearMap.intervalIntegral_apply hφ_int (Fin.tail y)]
                  _ = (y 0 : ℝ) • F x + intervalPiece dF x := by
                          simp [intervalPiece, ytail, dF, φ, SchwartzMap.lineDerivOp_apply_eq_fderiv,
                            tailInsertCLM_apply]
                          have htailfun : (fun i => y i.succ) = Fin.tail y := by
                            ext i
                            rfl
                          rw [htailfun]
              simpa [hEq] using ((F.smooth m).const_smul (y 0)).add (ih dF)⟩

/-- Fiberwise antiderivative along the head coordinate. For fixed tail variables,
integrate the head slice over `(-∞, x₀]`. This is the raw construction behind
the multi-dimensional Schwartz Poincare lemma. -/
def fiberwiseAntiderivRaw {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    (Fin (n + 1) → ℝ) → ℂ :=
  fun v => ∫ t in Set.Iic (v 0), F (Fin.cons t (Fin.tail v))

/-- The raw head antiderivative splits into the variable-limit interval piece
plus the fixed `(-∞, 0]` slice. -/
theorem fiberwiseAntiderivRaw_eq_interval_add_iic {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (v : Fin (n + 1) → ℝ) :
    fiberwiseAntiderivRaw F v =
      intervalPiece F v + iicZeroSlice F (Fin.tail v) := by
  set y : Fin n → ℝ := Fin.tail v
  rw [fiberwiseAntiderivRaw, intervalPiece, iicZeroSlice]
  change ∫ t in Set.Iic (v 0), F (Fin.cons t y) =
    (∫ t in (0 : ℝ)..(v 0), F (Fin.cons t y)) +
      ∫ t in Set.Iic (0 : ℝ), F (Fin.cons t y)
  have hf_int := integrable_sliceSection F y
  have hIic_v0 :
      Filter.Tendsto (fun r => ∫ t in r..(v 0), F (Fin.cons t y)) Filter.atBot
        (nhds (∫ t in Set.Iic (v 0), F (Fin.cons t y))) :=
    intervalIntegral_tendsto_integral_Iic (v 0) hf_int.integrableOn Filter.tendsto_id
  have hIic_0 :
      Filter.Tendsto (fun r => ∫ t in r..(0 : ℝ), F (Fin.cons t y)) Filter.atBot
        (nhds (∫ t in Set.Iic (0 : ℝ), F (Fin.cons t y))) :=
    intervalIntegral_tendsto_integral_Iic 0 hf_int.integrableOn Filter.tendsto_id
  have hadd : ∀ r : ℝ,
      ∫ t in r..(v 0), F (Fin.cons t y) =
        (∫ t in r..(0 : ℝ), F (Fin.cons t y)) + ∫ t in (0 : ℝ)..(v 0), F (Fin.cons t y) :=
    fun r => (intervalIntegral.integral_add_adjacent_intervals
      hf_int.intervalIntegrable hf_int.intervalIntegrable).symm
  have hlim := hIic_0.add_const (∫ t in (0 : ℝ)..(v 0), F (Fin.cons t y))
  have heq_lim :
      Filter.Tendsto (fun r => ∫ t in r..(v 0), F (Fin.cons t y)) Filter.atBot
        (nhds ((∫ t in Set.Iic (0 : ℝ), F (Fin.cons t y)) +
               ∫ t in (0 : ℝ)..(v 0), F (Fin.cons t y))) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall fun r => (hadd r).symm) hlim
  rw [tendsto_nhds_unique hIic_v0 heq_lim, add_comm]

/-- Differentiating the raw fiberwise antiderivative in the head direction
recovers the original Schwartz function. -/
theorem lineDeriv_fiberwiseAntiderivRaw {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (v : Fin (n + 1) → ℝ) :
    lineDeriv ℝ (fiberwiseAntiderivRaw F) v (Pi.single 0 1) = F v := by
  set e0 : Fin (n + 1) → ℝ := Pi.single 0 1 with he0
  set y : Fin n → ℝ := Fin.tail v with hy
  set G : ℝ → ℂ := fun s => F (Fin.cons s y) with hG
  have hG_cont : Continuous G := by
    rw [hG]
    have hcons_cont : Continuous (fun s : ℝ => (Fin.cons s y : Fin (n + 1) → ℝ)) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun s : ℝ => s)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => y i)
    exact F.continuous.comp hcons_cont
  have hG_int : Integrable G (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    rw [hG]
    simpa [hy] using integrable_sliceSection (F := F) (y := Fin.tail v)
  have hFTC : HasDerivAt (fun x => ∫ s in Set.Iic x, G s) (G (v 0)) (v 0) :=
    hasDerivAt_integral_Iic hG_cont hG_int (v 0)
  have hcomp : HasDerivAt (fun t => ∫ s in Set.Iic (v 0 + t), G s) (G (v 0)) 0 := by
    have hFTC' : HasDerivAt (fun x => ∫ s in Set.Iic x, G s) (G (v 0)) (v 0 + 0) := by
      simpa using hFTC
    simpa using hFTC'.comp_const_add (v 0) 0
  have heq :
      ∀ t : ℝ,
        fiberwiseAntiderivRaw F (v + t • e0)
          = ∫ s in Set.Iic (v 0 + t), G s := by
    intro t
    rw [fiberwiseAntiderivRaw, hG]
    have hhead : (v + t • e0) 0 = v 0 + t := by
      simp [e0, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, mul_one]
    have htail :
        Fin.tail (v + t • e0) = y := by
      ext i
      simp [Fin.tail, e0, hy, Pi.add_apply, Pi.smul_apply]
    rw [hhead, htail]
  have hline : HasLineDerivAt ℝ (fiberwiseAntiderivRaw F) (G (v 0)) v e0 := by
    show HasDerivAt (fun t => fiberwiseAntiderivRaw F (v + t • e0)) (G (v 0)) 0
    have hfun :
        (fun t => fiberwiseAntiderivRaw F (v + t • e0))
          = fun t => ∫ s in Set.Iic (v 0 + t), G s := by
      funext t
      exact heq t
    rw [hfun]
    exact hcomp
  rw [hline.lineDeriv]
  simp [hG, hy, Fin.cons_self_tail]

/-- If a Schwartz function has compact support and each head slice has integral
zero, then the raw fiberwise antiderivative is compactly supported as well. -/
theorem hasCompactSupport_fiberwiseAntiderivRaw {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF : HasCompactSupport F)
    (hzero :
      ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0) :
    HasCompactSupport (fiberwiseAntiderivRaw F) := by
  rcases hF.isCompact.isBounded.subset_closedBall (0 : Fin (n + 1) → ℝ) with ⟨R, hR⟩
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin (n + 1) → ℝ) R) ?_
  intro v hv
  by_contra hvR
  have hv_gt : R < ‖v‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm, not_le] using hvR
  have hhead_or_tail : R < ‖v 0‖ ∨ R < ‖Fin.tail v‖ := by
    by_contra hsplit
    push_neg at hsplit
    have hcoord : ∀ j : Fin (n + 1), ‖v j‖ ≤ R := by
      intro j
      refine Fin.cases ?_ ?_ j
      · exact hsplit.1
      · intro i
        exact le_trans (norm_le_pi_norm (Fin.tail v) i) hsplit.2
    have hv_le : ‖v‖ ≤ R := by
      have hRnonneg : 0 ≤ R := le_trans (norm_nonneg _) (hcoord 0)
      exact (pi_norm_le_iff_of_nonneg hRnonneg).2 hcoord
    exact not_lt_of_ge hv_le hv_gt
  cases hhead_or_tail with
  | inr htail =>
      have hzero_slice :
          fiberwiseAntiderivRaw F v = 0 := by
        rw [fiberwiseAntiderivRaw, ← MeasureTheory.integral_indicator measurableSet_Iic]
        have hind :
            Set.indicator (Set.Iic (v 0))
              (fun t : ℝ => F (Fin.cons t (Fin.tail v))) = 0 := by
          funext t
          by_cases ht : t ∈ Set.Iic (v 0)
          · have hnorm_gt :
                R < ‖Fin.cons t (Fin.tail v)‖ := by
              calc
                R < ‖Fin.tail v‖ := htail
                _ ≤ ‖Fin.cons t (Fin.tail v)‖ := by
                    calc
                      ‖Fin.tail v‖ = ‖tailCLM n (E := ℝ) (Fin.cons t (Fin.tail v))‖ := by
                          simp [tailCLM_apply]
                      _ ≤ ‖tailCLM n (E := ℝ)‖ * ‖Fin.cons t (Fin.tail v)‖ := by
                          exact ContinuousLinearMap.le_opNorm _ _
                      _ ≤ 1 * ‖Fin.cons t (Fin.tail v)‖ := by
                          gcongr
                          exact tailCLM_opNorm_le (E := ℝ) n
                      _ = ‖Fin.cons t (Fin.tail v)‖ := by ring
            have hnot : (Fin.cons t (Fin.tail v) : Fin (n + 1) → ℝ) ∉ tsupport F := by
              intro htF
              have hball : ‖Fin.cons t (Fin.tail v)‖ ≤ R := by
                simpa [Metric.mem_closedBall, dist_eq_norm] using hR htF
              exact not_lt_of_ge hball hnorm_gt
            simp [ht, image_eq_zero_of_notMem_tsupport hnot]
          · simp [ht]
        rw [hind]
        simp
      exact hv hzero_slice
  | inl hhead =>
      by_cases hhead_pos : R < v 0
      · have hEq :
            fiberwiseAntiderivRaw F v = ∫ t : ℝ, F (Fin.cons t (Fin.tail v)) := by
          rw [fiberwiseAntiderivRaw, ← MeasureTheory.integral_indicator measurableSet_Iic]
          refine MeasureTheory.integral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro t
          by_cases ht : t ∈ Set.Iic (v 0)
          · simp [ht]
          · have ht_gt : v 0 < t := by simpa [Set.mem_Iic, not_le] using ht
            have hnorm_gt :
                R < ‖Fin.cons t (Fin.tail v)‖ := by
              have hRt : R < ‖t‖ := by
                by_cases ht_nonneg : 0 ≤ t
                · calc
                    R < t := by linarith [hhead_pos, ht_gt]
                    _ = ‖t‖ := by simp [Real.norm_of_nonneg ht_nonneg]
                · have ht_neg : t < 0 := lt_of_not_ge ht_nonneg
                  have hRneg : R < 0 := by linarith [hhead_pos, ht_gt, ht_neg]
                  exact lt_of_lt_of_le hRneg (norm_nonneg _)
              exact lt_of_lt_of_le hRt <|
                by simpa using
                  (norm_le_pi_norm (Fin.cons t (Fin.tail v) : Fin (n + 1) → ℝ) 0)
            have hnot : (Fin.cons t (Fin.tail v) : Fin (n + 1) → ℝ) ∉ tsupport F := by
              intro htF
              have hball : ‖Fin.cons t (Fin.tail v)‖ ≤ R := by
                simpa [Metric.mem_closedBall, dist_eq_norm] using hR htF
              exact not_lt_of_ge hball hnorm_gt
            simp [ht, image_eq_zero_of_notMem_tsupport hnot]
        have hv0 : fiberwiseAntiderivRaw F v = 0 := by
          rw [hEq, hzero]
        exact hv hv0
      · have hhead_neg : v 0 < -R := by
          have hv0neg : v 0 < 0 := by
            by_contra hv0nonneg
            have hv0nonneg' : 0 ≤ v 0 := le_of_not_gt hv0nonneg
            have : R < v 0 := by
              calc
                R < ‖v 0‖ := hhead
                _ = v 0 := by simp [Real.norm_of_nonneg hv0nonneg']
            exact hhead_pos this
          have hnorm : ‖v 0‖ = -v 0 := by
            simp [Real.norm_of_nonpos (le_of_lt hv0neg)]
          linarith [hhead]
        have hzero_slice :
            fiberwiseAntiderivRaw F v = 0 := by
          rw [fiberwiseAntiderivRaw, ← MeasureTheory.integral_indicator measurableSet_Iic]
          have hind :
              Set.indicator (Set.Iic (v 0))
                (fun t : ℝ => F (Fin.cons t (Fin.tail v))) = 0 := by
            funext t
            by_cases ht : t ∈ Set.Iic (v 0)
            · have ht_le : t ≤ v 0 := by simpa [Set.mem_Iic] using ht
              have ht_neg : t < -R := by linarith
              have hnorm_gt :
                  R < ‖Fin.cons t (Fin.tail v)‖ := by
                have ht_nonpos : t ≤ 0 := by linarith
                calc
                  R < -t := by linarith
                  _ = ‖t‖ := by simp [Real.norm_of_nonpos ht_nonpos]
                  _ ≤ ‖Fin.cons t (Fin.tail v)‖ := by
                      simpa using (norm_le_pi_norm (Fin.cons t (Fin.tail v) : Fin (n + 1) → ℝ) 0)
              have hnot : (Fin.cons t (Fin.tail v) : Fin (n + 1) → ℝ) ∉ tsupport F := by
                intro htF
                have hball : ‖Fin.cons t (Fin.tail v)‖ ≤ R := by
                  simpa [Metric.mem_closedBall, dist_eq_norm] using hR htF
                exact not_lt_of_ge hball hnorm_gt
              simp [ht, image_eq_zero_of_notMem_tsupport hnot]
            · simp [ht]
          rw [hind]
          simp
        exact hv hzero_slice

/-- The zero-slice condition is preserved by differentiating in a pure tail
direction. This is the parameter-preservation input needed for the eventual
decay induction on the fiberwise antiderivative. -/
theorem zeroSlice_lineDerivOp_tailInsert {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0)
    (w : Fin n → ℝ) :
    ∀ y : Fin n → ℝ,
      ∫ t : ℝ, (∂_{tailInsertCLM n w} F) (Fin.cons t y) = 0 := by
  intro y
  have hzeroFun : sliceIntegralRaw F = 0 := by
    ext y'
    exact hzero y'
  have hline_zero : lineDeriv ℝ (sliceIntegralRaw F) y w = 0 := by
    rw [hzeroFun]
    change lineDeriv ℝ (fun _ : Fin n → ℝ => (0 : ℂ)) y w = 0
    rw [((hasFDerivAt_const (0 : ℂ) y).hasLineDerivAt w).lineDeriv]
    simp
  have hline_formula :
      lineDeriv ℝ (sliceIntegralRaw F) y w =
        sliceIntegralRaw (∂_{tailInsertCLM n w} F) y := by
    have h_int :
        Integrable
          (fun x : ℝ =>
            (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons x y)).comp (tailInsertCLM n))
          volume := by
      let C : ℝ :=
        (4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F
      have hmajor_int :
          Integrable (fun x : ℝ => C * (1 + x ^ 2)⁻¹)
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        simpa [C, mul_comm, mul_left_comm, mul_assoc] using
          (integrable_inv_one_add_sq.const_mul C)
      have hpath : Continuous fun x : ℝ => (Fin.cons x y : Fin (n + 1) → ℝ) := by
        classical
        refine continuous_pi ?_
        intro j
        refine Fin.cases ?_ ?_ j
        · simpa using (continuous_id : Continuous fun x : ℝ => x)
        · intro i
          simpa using (continuous_const : Continuous fun _ : ℝ => y i)
      have hcont :
          Continuous
            (fun x : ℝ =>
              (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons x y)).comp (tailInsertCLM n)) := by
        exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
      refine hmajor_int.mono' hcont.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall (fun x =>
        (norm_fderiv_sliceSection_le_inv_one_add_sq F y x).trans_eq (by simp [C]))
    rw [((hasFDerivAt_sliceIntegralRaw F y).hasLineDerivAt w).lineDeriv]
    rw [ContinuousLinearMap.integral_apply h_int]
    simp [sliceIntegralRaw, SchwartzMap.lineDerivOp_apply_eq_fderiv, tailInsertCLM_apply]
  rw [hline_formula] at hline_zero
  simpa [sliceIntegralRaw] using hline_zero

/-! ## Fiberwise antiderivative decay and Schwartz packaging -/

/-- Evaluating the derivative of the fixed `(-∞, 0]` slice piece on a pure tail
vector gives the same slice piece for the tail-differentiated Schwartz map. -/
theorem fderiv_iicZeroSlice_comp_tail_tailInsert_eq {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x : Fin (n + 1) → ℝ) (w : Fin n → ℝ) :
    fderiv ℝ (fun z : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail z)) x (tailInsertCLM n w) =
      iicZeroSlice (∂_{tailInsertCLM n w} F) (Fin.tail x) := by
  have hcomp := (hasFDerivAt_iicZeroSlice F (Fin.tail x)).comp x
    ((tailCLM n (E := ℝ)).hasFDerivAt)
  have h_int :
      Integrable
        (fun t : ℝ =>
          (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail x))).comp
            (tailInsertCLM n))
        (MeasureTheory.volume.restrict (Set.Iic (0 : ℝ))) := by
    let C : ℝ :=
      (4 : ℝ) * ((Finset.Iic (2, 1)).sup
        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F
    have hmajor_int :
        Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [C, mul_comm, mul_left_comm, mul_assoc] using
        (integrable_inv_one_add_sq.const_mul C)
    have hpath : Continuous fun t : ℝ => (Fin.cons t (Fin.tail x) : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun t : ℝ => t)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => Fin.tail x i)
    have hcont :
        Continuous
          (fun t : ℝ =>
            (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail x))).comp
              (tailInsertCLM n)) := by
      exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
    refine hmajor_int.restrict.mono' hcont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun t =>
      (norm_fderiv_sliceSection_le_inv_one_add_sq F (Fin.tail x) t).trans_eq (by simp [C]))
  change (fderiv ℝ (iicZeroSlice F ∘ Fin.tail) x) (tailInsertCLM n w) =
      iicZeroSlice (∂_{tailInsertCLM n w} F) (Fin.tail x)
  rw [hcomp.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.integral_apply h_int]
  simp [iicZeroSlice, SchwartzMap.lineDerivOp_apply_eq_fderiv, tailInsertCLM_apply,
    tailCLM_apply]

/-- Evaluating the derivative of the variable-limit interval piece on a pure
tail vector gives the interval piece for the tail-differentiated Schwartz map. -/
theorem fderiv_intervalPiece_tailInsert_eq {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x : Fin (n + 1) → ℝ) (w : Fin n → ℝ) :
    fderiv ℝ (intervalPiece F) x (tailInsertCLM n w) =
      intervalPiece (∂_{tailInsertCLM n w} F) x := by
  let v : Fin (n + 1) → ℝ := tailInsertCLM n w
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ := ∂_{v} F
  have hv0 : v 0 = 0 := by simp [v, tailInsertCLM_apply]
  have htail : Fin.tail v = w := by
    ext i
    simp [v, tailInsertCLM_apply]
  rw [(hasFDerivAt_intervalPiece F x).fderiv]
  let φ : ℝ → (Fin n → ℝ) →L[ℝ] ℂ := fun t =>
    (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail x))).comp
      (tailInsertCLM n)
  calc
    (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0).smulRight (F x)) +
        ((∫ t in (0 : ℝ)..(x 0), φ t).comp (tailCLM n (E := ℝ)))) v
        = (((∫ t in (0 : ℝ)..(x 0), φ t).comp (tailCLM n (E := ℝ))) v) := by
            simp [ContinuousLinearMap.smulRight_apply, hv0]
    _ = (∫ t in (0 : ℝ)..(x 0), φ t) w := by
          rw [ContinuousLinearMap.comp_apply]
          simpa [tailCLM_apply] using congrArg (fun u => (∫ t in (0 : ℝ)..(x 0), φ t) u) htail
    _ = intervalPiece dF x := by
          rw [ContinuousLinearMap.intervalIntegral_apply]
          · simp [intervalPiece, dF, v, φ, SchwartzMap.lineDerivOp_apply_eq_fderiv,
              tailInsertCLM_apply]
          ·
            have hpath : Continuous fun t : ℝ => (Fin.cons t (Fin.tail x) : Fin (n + 1) → ℝ) := by
              classical
              refine continuous_pi ?_
              intro j
              refine Fin.cases ?_ ?_ j
              · simpa using (continuous_id : Continuous fun t : ℝ => t)
              · intro i
                simpa using (continuous_const : Continuous fun _ : ℝ => Fin.tail x i)
            have hcont : Continuous φ := by
              exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
            exact hcont.intervalIntegrable _ _

theorem head_tail_decomposition_sliceIntegral {n : ℕ} (y : Fin (n + 1) → ℝ) :
    y = (y 0) • ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ) +
      tailInsertCLM n (tailCLM n y) := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [tailInsertCLM_apply]
  · intro i
    simp [tailInsertCLM_apply, tailCLM_apply]

/-- Evaluating the derivative of the fixed `(-∞, 0]` slice piece on an
arbitrary direction depends only on the tail component of that direction. -/
theorem fderiv_iicZeroSlice_comp_tail_apply {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x y : Fin (n + 1) → ℝ) :
    fderiv ℝ (fun z : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail z)) x y =
      iicZeroSlice
        (∂_{(tailInsertCLM n (tailCLM n y) : Fin (n + 1) → ℝ)} F) (Fin.tail x) := by
  have hcomp :=
    (hasFDerivAt_iicZeroSlice F (Fin.tail x)).comp x
      ((tailCLM n (E := ℝ)).hasFDerivAt)
  have hsame :
      fderiv ℝ (fun z : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail z)) x y =
        fderiv ℝ (fun z : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail z)) x
          (tailInsertCLM n (tailCLM n y)) := by
    simpa [Function.comp, ContinuousLinearMap.comp_apply, tailCLM_apply] using
      congrArg
        (fun L : (Fin (n + 1) → ℝ) →L[ℝ] ℂ => L y = L (tailInsertCLM n (tailCLM n y)))
        hcomp.fderiv
  rw [hsame]
  simpa using
    fderiv_iicZeroSlice_comp_tail_tailInsert_eq F x (tailCLM n y)

/-- The fiberwise antiderivative is smooth. -/
theorem contDiff_fiberwiseAntiderivRaw {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fiberwiseAntiderivRaw F) := by
  have hdecomp : fiberwiseAntiderivRaw F =
      fun v => intervalPiece F v + iicZeroSlice F (Fin.tail v) := by
    ext v
    exact fiberwiseAntiderivRaw_eq_interval_add_iic F v
  rw [hdecomp]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (intervalPiece F) := contDiff_intervalPiece F
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail v)) := by
    exact (contDiff_iicZeroSlice F).comp (tailCLM n (E := ℝ)).contDiff
  exact h1.add h2

/-- The raw fiberwise antiderivative has the expected head-plus-tail derivative
formula: the head component gives the FTC term `F`, while the tail component is
again a fiberwise antiderivative of the corresponding line derivative of `F`. -/
theorem fderiv_fiberwiseAntiderivRaw_apply {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x y : Fin (n + 1) → ℝ) :
    fderiv ℝ (fiberwiseAntiderivRaw F) x y =
      (y 0 : ℝ) • F x +
        fiberwiseAntiderivRaw
          (∂_{(tailInsertCLM n (tailCLM n y) : Fin (n + 1) → ℝ)} F) x := by
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    ∂_{(tailInsertCLM n (tailCLM n y) : Fin (n + 1) → ℝ)} F
  have hdecomp :
      fiberwiseAntiderivRaw F =
        fun z : Fin (n + 1) → ℝ => intervalPiece F z + iicZeroSlice F (Fin.tail z) := by
    funext z
    exact fiberwiseAntiderivRaw_eq_interval_add_iic F z
  have hsum :=
    (hasFDerivAt_intervalPiece F x).add
      ((hasFDerivAt_iicZeroSlice F (Fin.tail x)).comp x
        ((tailCLM n (E := ℝ)).hasFDerivAt))
  calc
    fderiv ℝ (fiberwiseAntiderivRaw F) x y
        = fderiv ℝ (fun z : Fin (n + 1) → ℝ => intervalPiece F z + iicZeroSlice F (Fin.tail z)) x y := by
            rw [hdecomp]
    _ = (y 0 : ℝ) • F x + intervalPiece dF x + iicZeroSlice dF (Fin.tail x) := by
            have hfun :
                (fun z : Fin (n + 1) → ℝ => intervalPiece F z + iicZeroSlice F (Fin.tail z)) =
                  (intervalPiece F) + (iicZeroSlice F ∘ Fin.tail) := rfl
            rw [hfun]
            have hsum_eval :
                (fderiv ℝ ((intervalPiece F) + (iicZeroSlice F ∘ Fin.tail)) x) y =
                  (y 0 : ℝ) • F x +
                    (((∫ t in (0 : ℝ)..(x 0),
                        (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                          (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                        (Fin.tail y)) +
                      (∫ t in Set.Iic (0 : ℝ),
                        (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                          (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                        (Fin.tail y)) := by
              simpa [Function.comp, add_assoc] using
                congrArg (fun L : (Fin (n + 1) → ℝ) →L[ℝ] ℂ => L y) hsum.fderiv
            have htail_eval :
                (((∫ t in (0 : ℝ)..(x 0),
                    (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                      (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                    (Fin.tail y)) +
                  (∫ t in Set.Iic (0 : ℝ),
                    (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                      (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                    (Fin.tail y)) =
                  intervalPiece dF x + iicZeroSlice dF (Fin.tail x) := by
              have hinterval :
                  (∫ t in (0 : ℝ)..(x 0),
                      (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                        (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                    (Fin.tail y) =
                    intervalPiece dF x := by
                have hraw := fderiv_intervalPiece_tailInsert_eq F x (tailCLM n y)
                rw [(hasFDerivAt_intervalPiece F x).fderiv] at hraw
                simpa [dF, ContinuousLinearMap.smulRight_apply,
                  ContinuousLinearMap.comp_apply, tailCLM_apply, tailInsertCLM_apply] using hraw
              have hiic :
                  (∫ t in Set.Iic (0 : ℝ),
                      (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                        (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                    (Fin.tail y) =
                    iicZeroSlice dF (Fin.tail x) := by
                have hcompTail :=
                  (hasFDerivAt_iicZeroSlice F (Fin.tail x)).comp x
                    ((tailCLM n (E := ℝ)).hasFDerivAt)
                have hexpl :
                    fderiv ℝ (fun z : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail z)) x y =
                      (∫ t in Set.Iic (0 : ℝ),
                          (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                            (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                        (Fin.tail y) := by
                  change (fderiv ℝ (iicZeroSlice F ∘ Fin.tail) x) y = _
                  rw [hcompTail.fderiv, ContinuousLinearMap.comp_apply, tailCLM_apply]
                  rfl
                exact hexpl.symm.trans (fderiv_iicZeroSlice_comp_tail_apply F x y)
              rw [hinterval, hiic]
            exact hsum_eval.trans <|
              by simpa [add_assoc] using
                congrArg (fun z : ℂ => (y 0 : ℝ) • F x + z) htail_eval
    _ = (y 0 : ℝ) • F x + fiberwiseAntiderivRaw dF x := by
            simpa [intervalPiece, iicZeroSlice, add_assoc] using
              congrArg (fun z : ℂ => (y 0 : ℝ) • F x + z)
                (fiberwiseAntiderivRaw_eq_interval_add_iic dF x).symm

/-- The tail representation: the zero-slice antiderivative can also be written
as an integral over the complementary upper tail. -/
theorem fiberwiseAntiderivRaw_eq_neg_ioi {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0)
    (v : Fin (n + 1) → ℝ) :
    fiberwiseAntiderivRaw F v = -(∫ t in Set.Ioi (v 0), F (Fin.cons t (Fin.tail v))) := by
  set y := Fin.tail v
  rw [fiberwiseAntiderivRaw]
  have hf_int := integrable_sliceSection F y
  have hsplit :
      ∫ t in Set.Iic (v 0), F (Fin.cons t y) =
        (∫ t : ℝ, F (Fin.cons t y)) - ∫ t in Set.Ioi (v 0), F (Fin.cons t y) := by
    have h := integral_add_compl (s := Set.Iic (v 0)) measurableSet_Iic hf_int
    rw [show (Set.Iic (v 0))ᶜ = Set.Ioi (v 0) by ext t; simp] at h
    linear_combination h
  rw [hsplit, hzero y, zero_sub]

/-- Zeroth-order decay for the raw fiberwise antiderivative. -/
theorem exists_norm_pow_mul_fiberwiseAntiderivRaw_le {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0)
    (k : ℕ) :
    ∃ C : ℝ, ∀ v : Fin (n + 1) → ℝ,
      ‖v‖ ^ k * ‖fiberwiseAntiderivRaw F v‖ ≤ C := by
  let S : ℝ := ((Finset.Iic (k + 2, 0)).sup
    (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F
  let M : ℝ := (2 : ℝ) ^ (k + 2) * S
  let C : ℝ := ∫ t : ℝ, M * (1 + t ^ 2)⁻¹
  refine ⟨C, ?_⟩
  intro v
  set y := Fin.tail v
  let zfun : ℝ → Fin (n + 1) → ℝ := fun t => Fin.cons t y
  have hmajor_point :
      ∀ t : ℝ, ‖zfun t‖ ^ k * ‖F (zfun t)‖ ≤ M * (1 + t ^ 2)⁻¹ := by
    intro t
    let z : Fin (n + 1) → ℝ := zfun t
    have hseminorm :
        (1 + ‖z‖) ^ (k + 2) * ‖F z‖ ≤ M := by
      simpa [M, S, z] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := ℝ) (m := (k + 2, 0)) (k := k + 2) (n := 0)
          le_rfl le_rfl F z)
    have hmain :
        ‖z‖ ^ k * ‖F z‖ ≤ M / (1 + ‖z‖) ^ (2 : ℕ) := by
      have hpow : ‖z‖ ^ k ≤ (1 + ‖z‖) ^ k := by
        have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg _
        have hz_le : ‖z‖ ≤ 1 + ‖z‖ := by linarith
        exact pow_le_pow_left₀ hz_nonneg hz_le k
      have hden_pos : 0 < (1 + ‖z‖) ^ (2 : ℕ) := by positivity
      refine (le_div_iff₀ hden_pos).2 ?_
      calc
        (‖z‖ ^ k * ‖F z‖) * (1 + ‖z‖) ^ (2 : ℕ)
            = (‖z‖ ^ k * (1 + ‖z‖) ^ (2 : ℕ)) * ‖F z‖ := by ring
        _ ≤ ((1 + ‖z‖) ^ k * (1 + ‖z‖) ^ (2 : ℕ)) * ‖F z‖ := by
              gcongr
        _ = (1 + ‖z‖) ^ (k + 2) * ‖F z‖ := by
              rw [← pow_add]
        _ ≤ M := hseminorm
    have hhead : ‖t‖ ≤ ‖z‖ := by
      simpa [z] using (norm_le_pi_norm z 0)
    have hsq : 1 + t ^ 2 ≤ (1 + ‖z‖) ^ (2 : ℕ) := by
      calc
        1 + t ^ 2 = 1 + ‖t‖ ^ 2 := by
              rw [Real.norm_eq_abs, sq_abs]
        _ ≤ 1 + 2 * ‖z‖ + ‖z‖ ^ 2 := by
              nlinarith [norm_nonneg t, hhead]
        _ = (1 + ‖z‖) ^ (2 : ℕ) := by ring
    have hsq_inv : ((1 + ‖z‖) ^ (2 : ℕ))⁻¹ ≤ (1 + t ^ 2)⁻¹ := by
      have hpos : 0 < 1 + t ^ 2 := by positivity
      simpa [one_div] using (one_div_le_one_div_of_le hpos hsq)
    calc
      ‖zfun t‖ ^ k * ‖F (zfun t)‖ = ‖z‖ ^ k * ‖F z‖ := by rfl
      _ ≤ M * (((1 + ‖z‖) ^ (2 : ℕ))⁻¹) := by
            simpa [one_div, div_eq_mul_inv] using hmain
      _ ≤ M * (1 + t ^ 2)⁻¹ := by
            gcongr
  have hmajor_integrable :
      Integrable (fun t : ℝ => M * (1 + t ^ 2)⁻¹)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    simpa [M, mul_comm, mul_left_comm, mul_assoc] using
      integrable_inv_one_add_sq.const_mul M
  have hmajor_nonneg : ∀ t : ℝ, 0 ≤ M * (1 + t ^ 2)⁻¹ := by
    intro t
    positivity
  by_cases hv0_nonneg : 0 ≤ v 0
  · have hrepr := fiberwiseAntiderivRaw_eq_neg_ioi F hzero v
    have hnorm_int : IntegrableOn (fun t : ℝ => ‖F (zfun t)‖) (Set.Ioi (v 0)) volume := by
      simpa [y, zfun] using (integrable_sliceSection F y).norm.integrableOn
    have hleft_int :
        IntegrableOn (fun t : ℝ => ‖v‖ ^ k * ‖F (zfun t)‖) (Set.Ioi (v 0)) volume := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnorm_int.const_mul (‖v‖ ^ k)
    have hright_int :
        IntegrableOn (fun t : ℝ => M * (1 + t ^ 2)⁻¹) (Set.Ioi (v 0)) volume := by
      exact hmajor_integrable.integrableOn
    have hdom :
        ∀ t ∈ Set.Ioi (v 0), ‖v‖ ^ k * ‖F (zfun t)‖ ≤ M * (1 + t ^ 2)⁻¹ := by
      intro t ht
      have ht0 : 0 ≤ t := le_trans hv0_nonneg (le_of_lt ht)
      have hcoord : ∀ j : Fin (n + 1), ‖v j‖ ≤ ‖zfun t‖ := by
        intro j
        refine Fin.cases ?_ ?_ j
        · calc
            ‖v 0‖ = v 0 := by simp [Real.norm_of_nonneg hv0_nonneg]
            _ ≤ t := le_of_lt ht
            _ = ‖t‖ := by simp [Real.norm_of_nonneg ht0]
            _ ≤ ‖zfun t‖ := by simpa [zfun] using (norm_le_pi_norm (zfun t) 0)
        · intro i
          calc
            ‖v i.succ‖ = ‖y i‖ := by
              change ‖v i.succ‖ = ‖v i.succ‖
              rfl
            _ ≤ ‖y‖ := by simpa using (norm_le_pi_norm y i)
            _ = ‖tailCLM n (E := ℝ) (zfun t)‖ := by simp [tailCLM_apply, zfun, y]
            _ ≤ ‖tailCLM n (E := ℝ)‖ * ‖zfun t‖ := by
                exact ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖zfun t‖ := by
                gcongr
                exact tailCLM_opNorm_le (E := ℝ) n
            _ = ‖zfun t‖ := by ring
      have hv_le : ‖v‖ ≤ ‖zfun t‖ := by
        exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hcoord
      have hpow : ‖v‖ ^ k ≤ ‖zfun t‖ ^ k := by
        exact pow_le_pow_left₀ (norm_nonneg _) hv_le k
      calc
        ‖v‖ ^ k * ‖F (zfun t)‖ ≤ ‖zfun t‖ ^ k * ‖F (zfun t)‖ := by
              gcongr
        _ ≤ M * (1 + t ^ 2)⁻¹ := hmajor_point t
    calc
      ‖v‖ ^ k * ‖fiberwiseAntiderivRaw F v‖
          = ‖v‖ ^ k * ‖∫ t in Set.Ioi (v 0), F (zfun t)‖ := by
              rw [hrepr, norm_neg]
      _ ≤ ‖v‖ ^ k * ∫ t in Set.Ioi (v 0), ‖F (zfun t)‖ := by
            gcongr
            simpa using
              (norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi (v 0)))
                (f := fun t : ℝ => F (zfun t)))
      _ = ∫ t in Set.Ioi (v 0), ‖v‖ ^ k * ‖F (zfun t)‖ := by
            rw [← integral_const_mul]
      _ ≤ ∫ t in Set.Ioi (v 0), M * (1 + t ^ 2)⁻¹ := by
            exact setIntegral_mono_on hleft_int hright_int measurableSet_Ioi hdom
      _ ≤ ∫ t : ℝ, M * (1 + t ^ 2)⁻¹ := by
            exact setIntegral_le_integral
              (hfi := hmajor_integrable)
              (hf := Filter.Eventually.of_forall hmajor_nonneg)
      _ = C := by rfl
  · have hv0_nonpos : v 0 ≤ 0 := le_of_not_ge hv0_nonneg
    have hnorm_int : IntegrableOn (fun t : ℝ => ‖F (zfun t)‖) (Set.Iic (v 0)) volume := by
      simpa [y, zfun] using (integrable_sliceSection F y).norm.integrableOn
    have hleft_int :
        IntegrableOn (fun t : ℝ => ‖v‖ ^ k * ‖F (zfun t)‖) (Set.Iic (v 0)) volume := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnorm_int.const_mul (‖v‖ ^ k)
    have hright_int :
        IntegrableOn (fun t : ℝ => M * (1 + t ^ 2)⁻¹) (Set.Iic (v 0)) volume := by
      exact hmajor_integrable.integrableOn
    have hdom :
        ∀ t ∈ Set.Iic (v 0), ‖v‖ ^ k * ‖F (zfun t)‖ ≤ M * (1 + t ^ 2)⁻¹ := by
      intro t ht
      have htv : t ≤ v 0 := by simpa using ht
      have ht_nonpos : t ≤ 0 := le_trans htv hv0_nonpos
      have hcoord : ∀ j : Fin (n + 1), ‖v j‖ ≤ ‖zfun t‖ := by
        intro j
        refine Fin.cases ?_ ?_ j
        · calc
            ‖v 0‖ = -v 0 := by simp [Real.norm_of_nonpos hv0_nonpos]
            _ ≤ -t := by linarith
            _ = ‖t‖ := by simp [Real.norm_of_nonpos ht_nonpos]
            _ ≤ ‖zfun t‖ := by simpa [zfun] using (norm_le_pi_norm (zfun t) 0)
        · intro i
          calc
            ‖v i.succ‖ = ‖y i‖ := by
              change ‖v i.succ‖ = ‖v i.succ‖
              rfl
            _ ≤ ‖y‖ := by simpa using (norm_le_pi_norm y i)
            _ = ‖tailCLM n (E := ℝ) (zfun t)‖ := by simp [tailCLM_apply, zfun, y]
            _ ≤ ‖tailCLM n (E := ℝ)‖ * ‖zfun t‖ := by
                exact ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖zfun t‖ := by
                gcongr
                exact tailCLM_opNorm_le (E := ℝ) n
            _ = ‖zfun t‖ := by ring
      have hv_le : ‖v‖ ≤ ‖zfun t‖ := by
        exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hcoord
      have hpow : ‖v‖ ^ k ≤ ‖zfun t‖ ^ k := by
        exact pow_le_pow_left₀ (norm_nonneg _) hv_le k
      calc
        ‖v‖ ^ k * ‖F (zfun t)‖ ≤ ‖zfun t‖ ^ k * ‖F (zfun t)‖ := by
              gcongr
        _ ≤ M * (1 + t ^ 2)⁻¹ := hmajor_point t
    calc
      ‖v‖ ^ k * ‖fiberwiseAntiderivRaw F v‖
          = ‖v‖ ^ k * ‖∫ t in Set.Iic (v 0), F (zfun t)‖ := by
              simp [fiberwiseAntiderivRaw, y, zfun]
      _ ≤ ‖v‖ ^ k * ∫ t in Set.Iic (v 0), ‖F (zfun t)‖ := by
            gcongr
            simpa using
              (norm_integral_le_integral_norm (μ := volume.restrict (Set.Iic (v 0)))
                (f := fun t : ℝ => F (zfun t)))
      _ = ∫ t in Set.Iic (v 0), ‖v‖ ^ k * ‖F (zfun t)‖ := by
            rw [← integral_const_mul]
      _ ≤ ∫ t in Set.Iic (v 0), M * (1 + t ^ 2)⁻¹ := by
            exact setIntegral_mono_on hleft_int hright_int measurableSet_Iic hdom
      _ ≤ ∫ t : ℝ, M * (1 + t ^ 2)⁻¹ := by
            exact setIntegral_le_integral
              (hfi := hmajor_integrable)
              (hf := Filter.Eventually.of_forall hmajor_nonneg)
      _ = C := by rfl

/-- Linearity of `fiberwiseAntiderivRaw` in the Schwartz argument. -/
theorem fiberwiseAntiderivRaw_add {n : ℕ}
    (F G : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (v : Fin (n + 1) → ℝ) :
    fiberwiseAntiderivRaw (F + G) v =
      fiberwiseAntiderivRaw F v + fiberwiseAntiderivRaw G v := by
  simp [fiberwiseAntiderivRaw, SchwartzMap.add_apply]
  rw [← MeasureTheory.integral_add
    (integrable_sliceSection F (Fin.tail v)).integrableOn
    (integrable_sliceSection G (Fin.tail v)).integrableOn]

/-- Scalar linearity of `fiberwiseAntiderivRaw`. -/
theorem fiberwiseAntiderivRaw_smul {n : ℕ}
    (c : ℝ) (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (v : Fin (n + 1) → ℝ) :
    fiberwiseAntiderivRaw (c • F) v =
      c • fiberwiseAntiderivRaw F v := by
  simp only [fiberwiseAntiderivRaw, SchwartzMap.smul_apply]
  exact MeasureTheory.integral_smul c _

/-- Linearity of `fiberwiseAntiderivRaw` over finite sums. -/
theorem fiberwiseAntiderivRaw_finset_sum {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (v : Fin (n + 1) → ℝ) :
    fiberwiseAntiderivRaw (s.sum f) v =
      s.sum (fun i => fiberwiseAntiderivRaw (f i) v) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    simp [fiberwiseAntiderivRaw, SchwartzMap.zero_apply, MeasureTheory.integral_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [fiberwiseAntiderivRaw_add, ih]

/-- Basis decomposition of the Fréchet derivative of `fiberwiseAntiderivRaw`. -/
theorem fderiv_fiberwiseAntiderivRaw_eq_sum {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (x : Fin (n + 1) → ℝ) :
    fderiv ℝ (fiberwiseAntiderivRaw F) x =
      ContinuousLinearMap.smulRight
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0) (F x) +
      Finset.univ.sum (fun i : Fin n =>
        ContinuousLinearMap.smulRight
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) i.succ)
          (fiberwiseAntiderivRaw (∂_{(tailInsertCLM n (Pi.single i (1 : ℝ)))} F) x)) := by
  ext h
  rw [fderiv_fiberwiseAntiderivRaw_apply F x h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  congr 1
  have htail : tailCLM n h = Finset.univ.sum
      (fun i : Fin n => (h i.succ : ℝ) • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    ext j; simp [tailCLM_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ]
  have hdir : tailInsertCLM n (tailCLM n h) =
      Finset.univ.sum (fun i : Fin n =>
        (h i.succ : ℝ) • (tailInsertCLM n (Pi.single i (1 : ℝ)) : Fin (n + 1) → ℝ)) := by
    rw [htail]; simp [map_sum]
  have hext : ∂_{(tailInsertCLM n (tailCLM n h) : Fin (n + 1) → ℝ)} F =
      Finset.univ.sum (fun i : Fin n =>
        (h i.succ) • ∂_{(tailInsertCLM n (Pi.single i (1 : ℝ)) : Fin (n + 1) → ℝ)} F) := by
    ext v
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [hdir, map_sum]
    simp only [ContinuousLinearMap.map_smul]
    have hsum_coe : ∀ (s : Finset (Fin n))
        (f : Fin n → SchwartzMap (Fin (n + 1) → ℝ) ℂ) (w : Fin (n + 1) → ℝ),
        (s.sum f) w = s.sum (fun i => (f i) w) := by
      intro s f w
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih => simp [Finset.sum_insert ha, SchwartzMap.add_apply, ih]
    rw [hsum_coe]
    simp only [SchwartzMap.smul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hclm_sum : ∀ (s : Finset (Fin n))
      (f : Fin n → (Fin (n + 1) → ℝ) →L[ℝ] ℂ) (w : Fin (n + 1) → ℝ),
      (s.sum f) w = s.sum (fun i => (f i) w) := by
    intro s f w
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      simp [Finset.sum_insert ha, ContinuousLinearMap.add_apply, ih]
  rw [hclm_sum]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  rw [hext, fiberwiseAntiderivRaw_finset_sum, show Finset.univ.sum
    (fun i : Fin n => fiberwiseAntiderivRaw ((h i.succ) • ∂_{(tailInsertCLM n
      (Pi.single i (1 : ℝ)) : Fin (n + 1) → ℝ)} F) x) = Finset.univ.sum
    (fun i : Fin n => (h i.succ) • fiberwiseAntiderivRaw (∂_{(tailInsertCLM n
      (Pi.single i (1 : ℝ)) : Fin (n + 1) → ℝ)} F) x)
    from Finset.sum_congr rfl (fun i _ => fiberwiseAntiderivRaw_smul _ _ _)]
  rfl

/-- Full Schwartz decay for the raw fiberwise antiderivative under the
zero-slice condition. -/
theorem decay_fiberwiseAntiderivRaw {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0)
    (k p : ℕ) :
    ∃ C : ℝ, ∀ v : Fin (n + 1) → ℝ,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ p (fiberwiseAntiderivRaw F) v‖ ≤ C := by
  induction p generalizing n F with
  | zero =>
      obtain ⟨C, hC⟩ := exists_norm_pow_mul_fiberwiseAntiderivRaw_le F hzero k
      exact ⟨C, fun v => by rw [norm_iteratedFDeriv_zero]; exact hC v⟩
  | succ p ihp =>
      obtain ⟨C_head, hC_head⟩ := F.decay' k p
      have hIH : ∀ i : Fin n, ∃ C_i : ℝ, ∀ v : Fin (n + 1) → ℝ,
          ‖v‖ ^ k * ‖iteratedFDeriv ℝ p
            (fiberwiseAntiderivRaw (∂_{(tailInsertCLM n (Pi.single i (1 : ℝ)))} F)) v‖ ≤ C_i :=
        fun i => ihp _ (zeroSlice_lineDerivOp_tailInsert F hzero (Pi.single i 1))
      choose C_tail hC_tail using hIH
      let L₀ : ℂ →L[ℝ] ((Fin (n + 1) → ℝ) →L[ℝ] ℂ) :=
        ContinuousLinearMap.smulRightL ℝ (Fin (n + 1) → ℝ) ℂ
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0)
      let Lᵢ : Fin n → (ℂ →L[ℝ] ((Fin (n + 1) → ℝ) →L[ℝ] ℂ)) := fun i =>
        ContinuousLinearMap.smulRightL ℝ (Fin (n + 1) → ℝ) ℂ
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) i.succ)
      let fᵢ : Fin n → ((Fin (n + 1) → ℝ) → ℂ) := fun i =>
        fiberwiseAntiderivRaw (∂_{(tailInsertCLM n (Pi.single i (1 : ℝ)))} F)
      have hF_cd : ContDiff ℝ p (F : (Fin (n + 1) → ℝ) → ℂ) := F.smooth p
      have hfᵢ_cd : ∀ i : Fin n, ContDiff ℝ p (fᵢ i) := fun i => by
        exact (contDiff_infty.mp (contDiff_fiberwiseAntiderivRaw _)) p
      have hfderiv_fun : fderiv ℝ (fiberwiseAntiderivRaw F) =
          (fun v => L₀ (F v)) + (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v))) := by
        funext v; exact fderiv_fiberwiseAntiderivRaw_eq_sum F v
      have hA_cd : ContDiff ℝ p (fun v => L₀ (F v)) := L₀.contDiff.comp hF_cd
      have hB_cd : ContDiff ℝ p
          (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v))) :=
        ContDiff.sum (fun i _ => (Lᵢ i).contDiff.comp (hfᵢ_cd i))
      have hstep4_head : ∀ v, ‖iteratedFDeriv ℝ p (fun v => L₀ (F v)) v‖ ≤
          ‖L₀‖ * ‖iteratedFDeriv ℝ p (F : (Fin (n + 1) → ℝ) → ℂ) v‖ :=
        fun v => L₀.norm_iteratedFDeriv_comp_left hF_cd.contDiffAt le_rfl
      have hstep4_tail : ∀ v,
          ‖iteratedFDeriv ℝ p (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v))) v‖ ≤
          Finset.univ.sum (fun i => ‖Lᵢ i‖ * ‖iteratedFDeriv ℝ p (fᵢ i) v‖) := by
        intro v
        set_option synthInstance.maxHeartbeats 40000 in
        have hsum_eq : iteratedFDeriv ℝ p
            (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v))) v =
            Finset.univ.sum (fun i =>
              iteratedFDeriv ℝ p (fun v => Lᵢ i (fᵢ i v)) v) := by
          have key := congr_fun (iteratedFDeriv_sum (𝕜 := ℝ) (i := p)
            (f := fun (j : Fin n) (v : Fin (n + 1) → ℝ) => Lᵢ j (fᵢ j v))
            (u := Finset.univ)
            (fun j _ => (Lᵢ j).contDiff.comp (hfᵢ_cd j))) v
          rw [show (fun v => ∑ i : Fin n, (Lᵢ i) (fᵢ i v)) =
            (fun x => ∑ j : Fin n, (fun j v => Lᵢ j (fᵢ j v)) j x) from rfl]
          rw [key]
          simp only [Finset.sum_apply]
        rw [hsum_eq]
        calc ‖Finset.univ.sum (fun i =>
                iteratedFDeriv ℝ p (fun v => Lᵢ i (fᵢ i v)) v)‖
            ≤ Finset.univ.sum (fun i =>
                ‖iteratedFDeriv ℝ p (fun v => Lᵢ i (fᵢ i v)) v‖) := norm_sum_le _ _
          _ ≤ Finset.univ.sum (fun i =>
                ‖Lᵢ i‖ * ‖iteratedFDeriv ℝ p (fᵢ i) v‖) :=
              Finset.sum_le_sum (fun i _ =>
                (Lᵢ i).norm_iteratedFDeriv_comp_left (hfᵢ_cd i).contDiffAt le_rfl)
      let C_total := ‖L₀‖ * C_head + Finset.univ.sum (fun i => ‖Lᵢ i‖ * C_tail i)
      refine ⟨C_total, fun v => ?_⟩
      calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ (p + 1) (fiberwiseAntiderivRaw F) v‖
          = ‖v‖ ^ k * ‖iteratedFDeriv ℝ p (fderiv ℝ (fiberwiseAntiderivRaw F)) v‖ := by
            rw [norm_iteratedFDeriv_fderiv (𝕜 := ℝ)]
        _ = ‖v‖ ^ k * ‖iteratedFDeriv ℝ p ((fun v => L₀ (F v)) +
              (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v)))) v‖ := by
            congr 2
            exact congr_fun (congr_arg (iteratedFDeriv ℝ p) hfderiv_fun) v
        _ ≤ ‖v‖ ^ k * (‖iteratedFDeriv ℝ p (fun v => L₀ (F v)) v‖ +
              ‖iteratedFDeriv ℝ p (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v))) v‖) := by
            gcongr
            rw [iteratedFDeriv_add hA_cd hB_cd]
            exact norm_add_le _ _
        _ ≤ ‖v‖ ^ k * (‖L₀‖ * ‖iteratedFDeriv ℝ p (F : (Fin (n + 1) → ℝ) → ℂ) v‖ +
              Finset.univ.sum (fun i => ‖Lᵢ i‖ * ‖iteratedFDeriv ℝ p (fᵢ i) v‖)) :=
            mul_le_mul_of_nonneg_left (add_le_add (hstep4_head v) (hstep4_tail v)) (by positivity)
        _ = ‖L₀‖ * (‖v‖ ^ k * ‖iteratedFDeriv ℝ p (F : (Fin (n + 1) → ℝ) → ℂ) v‖) +
              Finset.univ.sum (fun i =>
                ‖Lᵢ i‖ * (‖v‖ ^ k * ‖iteratedFDeriv ℝ p (fᵢ i) v‖)) := by
            rw [mul_add, Finset.mul_sum]
            congr 1
            · ring
            · apply Finset.sum_congr rfl
              intro i _
              ring
        _ ≤ ‖L₀‖ * C_head + Finset.univ.sum (fun i => ‖Lᵢ i‖ * C_tail i) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left (hC_head v) (norm_nonneg L₀)
            · exact Finset.sum_le_sum (fun i _ =>
                mul_le_mul_of_nonneg_left (hC_tail i v) (norm_nonneg (Lᵢ i)))

/-- The Schwartz fiberwise antiderivative obtained from the raw one under the
zero-slice condition. -/
noncomputable def fiberwiseAntideriv {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0) :
    SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
  SchwartzMap.mk (fiberwiseAntiderivRaw F)
    (contDiff_fiberwiseAntiderivRaw F)
    (decay_fiberwiseAntiderivRaw F hzero)

/-- Differentiating the Schwartz antiderivative in the head direction recovers
the original Schwartz function. -/
theorem lineDeriv_fiberwiseAntideriv {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0)
    (v : Fin (n + 1) → ℝ) :
    lineDeriv ℝ (⇑(fiberwiseAntideriv F hzero)) v (Pi.single 0 1) = F v :=
  lineDeriv_fiberwiseAntiderivRaw F v

end OSReconstruction
