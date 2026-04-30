/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.EuclideanWeylBump
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Radial Poisson Infrastructure for the Euclidean Weyl Route

This file contains the finite-interval radial ODE substrate for the compact
radial Poisson primitive used in the local Euclidean Weyl proof.  It starts
with the radial mass and primitive profiles and proves the FTC and algebraic
facts needed before the genuine Laplacian calculation.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter intervalIntegral
open scoped LineDeriv

namespace SCV

/-- The scalar radial Laplacian profile expression
`a''(r) + (N - 1) / r * a'(r)`.  This is used only away from `r = 0`;
the origin is handled separately by the checked quadratic profile theorem. -/
noncomputable def radialProfileLaplacian
    (N : ℕ) (a : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv (deriv a) r +
    (((((N - 1 : ℕ) : ℝ) / r : ℝ) : ℂ) * deriv a r)

/-- The weighted radial mass appearing in the radial Poisson ODE. -/
noncomputable def radialMass (N : ℕ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ s in (0)..r, ((s ^ (N - 1) : ℝ) : ℂ) * F s

/-- The radial derivative candidate `A'(r) = r^(1-N) ∫_0^r s^(N-1) F(s) ds`. -/
noncomputable def radialPrimitiveDeriv
    (N : ℕ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  if r = 0 then 0
  else (((r ^ (N - 1) : ℝ) : ℂ)⁻¹) * radialMass N F r

/-- The radial primitive normalized to vanish at the outer radius `R`. -/
noncomputable def radialPrimitiveProfile
    (N : ℕ) (F : ℝ → ℂ) (R r : ℝ) : ℂ :=
  -∫ t in r..R, radialPrimitiveDeriv N F t

@[simp]
theorem radialMass_zero (N : ℕ) (F : ℝ → ℂ) :
    radialMass N F 0 = 0 := by
  simp [radialMass]

@[simp]
theorem radialPrimitiveDeriv_zero (N : ℕ) (F : ℝ → ℂ) :
    radialPrimitiveDeriv N F 0 = 0 := by
  simp [radialPrimitiveDeriv]

@[simp]
theorem radialPrimitiveProfile_self (N : ℕ) (F : ℝ → ℂ) (R : ℝ) :
    radialPrimitiveProfile N F R R = 0 := by
  simp [radialPrimitiveProfile]

theorem deriv_radialMass
    {N : ℕ} {F : ℝ → ℂ}
    (hF_cont : Continuous F) :
    ∀ r ∈ Set.Ioi 0,
      deriv (radialMass N F) r =
        ((r ^ (N - 1) : ℝ) : ℂ) * F r := by
  intro r hr
  have hcont : Continuous (fun s : ℝ => ((s ^ (N - 1) : ℝ) : ℂ) * F s) := by
    have hpow : Continuous (fun s : ℝ => ((s ^ (N - 1) : ℝ) : ℂ)) := by
      fun_prop
    exact hpow.mul hF_cont
  change deriv (fun u : ℝ =>
      ∫ s in (0)..u, ((s ^ (N - 1) : ℝ) : ℂ) * F s) r =
    ((r ^ (N - 1) : ℝ) : ℂ) * F r
  exact Continuous.deriv_integral _ hcont 0 r

theorem hasDerivAt_radialMass
    {N : ℕ} {F : ℝ → ℂ}
    (hF_cont : Continuous F) (r : ℝ) :
    HasDerivAt (radialMass N F)
      (((r ^ (N - 1) : ℝ) : ℂ) * F r) r := by
  have hcont : Continuous (fun s : ℝ => ((s ^ (N - 1) : ℝ) : ℂ) * F s) := by
    have hpow : Continuous (fun s : ℝ => ((s ^ (N - 1) : ℝ) : ℂ)) := by
      fun_prop
    exact hpow.mul hF_cont
  change HasDerivAt (fun u : ℝ =>
      ∫ s in (0)..u, ((s ^ (N - 1) : ℝ) : ℂ) * F s)
    (((r ^ (N - 1) : ℝ) : ℂ) * F r) r
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 r)
    (hcont.measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
    hcont.continuousAt

theorem radialMass_eq_weightedMass_of_support
    {N : ℕ} {F : ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hweight_int :
      IntegrableOn
        (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ) * F r)
        (Set.Ioi 0) volume)
    (hF_support : Function.support F ⊆ Set.Icc (-R) R) :
    radialMass N F R =
      ∫ r in Set.Ioi 0, ((r ^ (N - 1) : ℝ) : ℂ) * F r := by
  let G : ℝ → ℂ := fun r => ((r ^ (N - 1) : ℝ) : ℂ) * F r
  have htail_zero : (∫ r in Set.Ioi R, G r) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    have hF_zero : F r = 0 := by
      by_contra hne
      have hmem : r ∈ Function.support F := by
        rw [Function.mem_support]
        exact hne
      have hbound := hF_support hmem
      exact (not_le_of_gt hr) hbound.2
    simp [G, hF_zero]
  have hsplit :
      (∫ r in (0 : ℝ)..R, G r) + ∫ r in Set.Ioi R, G r =
        ∫ r in Set.Ioi 0, G r := by
    exact intervalIntegral.integral_interval_add_Ioi
      hweight_int
      (hweight_int.mono_set (Ioi_subset_Ioi hR))
  rw [radialMass]
  change (∫ r in (0 : ℝ)..R, G r) = ∫ r in Set.Ioi 0, G r
  rw [← hsplit, htail_zero, add_zero]

theorem radialMass_eq_const_near_zero
    {N : ℕ} (hNpos : 0 < N) {F : ℝ → ℂ} {η r : ℝ} {c : ℂ}
    (hη : 0 < η)
    (hr_nonneg : 0 ≤ r) (hr_le : r ≤ η)
    (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
    radialMass N F r =
      c * (((r ^ N : ℝ) : ℂ) / (N : ℂ)) := by
  have hcongr :
      (∫ s in (0)..r, ((s ^ (N - 1) : ℝ) : ℂ) * F s) =
        ∫ s in (0)..r, c * ((s ^ (N - 1) : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsIcc : s ∈ Set.Icc 0 η := by
      rw [Set.mem_uIcc] at hs
      rw [Set.mem_Icc]
      rcases hs with ⟨hs0, hsr⟩ | ⟨hsr, hs0⟩
      · exact ⟨hs0, le_trans hsr hr_le⟩
      · exact ⟨by linarith, by linarith⟩
    simp [hF_zero s hsIcc, mul_comm]
  rw [radialMass, hcongr]
  rw [show (∫ s in (0)..r, c * ((s ^ (N - 1) : ℝ) : ℂ)) =
      c * ∫ s in (0)..r, ((s ^ (N - 1) : ℝ) : ℂ) by
    exact intervalIntegral.integral_const_mul c
      (fun s : ℝ => ((s ^ (N - 1) : ℝ) : ℂ))]
  rw [show (∫ s in (0)..r, ((s ^ (N - 1) : ℝ) : ℂ)) =
      (((r ^ N : ℝ) : ℂ) / (N : ℂ)) by
    calc
      (∫ s in (0)..r, ((s ^ (N - 1) : ℝ) : ℂ))
          = (((∫ s in (0)..r, (s ^ (N - 1) : ℝ)) : ℝ) : ℂ) := by
              rw [intervalIntegral.integral_of_le hr_nonneg,
                intervalIntegral.integral_of_le hr_nonneg]
              exact integral_complex_ofReal
      _ = (((r ^ N : ℝ) : ℂ) / (N : ℂ)) := by
              rw [integral_pow]
              have hN : (N - 1 + 1 : ℕ) = N := Nat.sub_add_cancel hNpos
              rw [hN]
              have hz : (0 : ℝ) ^ N = 0 := zero_pow hNpos.ne'
              rw [hz, sub_zero]
              have hden : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
                exact_mod_cast hN
              rw [hden]
              norm_cast]

theorem radialPrimitiveDeriv_eq_inv_mul
    {N : ℕ} {F : ℝ → ℂ} {r : ℝ} (hr : r ≠ 0) :
    radialPrimitiveDeriv N F r =
      (((r ^ (N - 1) : ℝ) : ℂ)⁻¹) * radialMass N F r := by
  simp [radialPrimitiveDeriv, hr]

theorem radialPrimitiveDeriv_mul_power_eq_radialMass
    {N : ℕ} {F : ℝ → ℂ} {r : ℝ} (hr : r ≠ 0) :
    ((r ^ (N - 1) : ℝ) : ℂ) * radialPrimitiveDeriv N F r =
      radialMass N F r := by
  rw [radialPrimitiveDeriv_eq_inv_mul hr]
  have hpow_ne : ((r ^ (N - 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero (N - 1) hr
  field_simp [hpow_ne]

theorem radialPrimitiveDeriv_eq_linear_near_zero
    {N : ℕ} (hNpos : 0 < N) {F : ℝ → ℂ} {η r : ℝ} {c : ℂ}
    (hη : 0 < η)
    (hr_pos : 0 < r) (hr_le : r ≤ η)
    (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
    radialPrimitiveDeriv N F r =
      c * (((r : ℝ) : ℂ) / (N : ℂ)) := by
  rw [radialPrimitiveDeriv_eq_inv_mul hr_pos.ne']
  rw [radialMass_eq_const_near_zero hNpos hη hr_pos.le hr_le hF_zero]
  have hrC_ne : ((r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hr_pos.ne'
  have hN_ne : (N : ℂ) ≠ 0 := by
    exact_mod_cast hNpos.ne'
  have hpow : ((r ^ N : ℝ) : ℂ) = (r : ℂ) ^ N := by
    norm_cast
  have hpow_pred : ((r ^ (N - 1) : ℝ) : ℂ) = (r : ℂ) ^ (N - 1) := by
    norm_cast
  rw [hpow]
  rw [hpow_pred]
  have hNsucc : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
  field_simp [hrC_ne, hN_ne]
  calc
    c * (r : ℂ) ^ N = c * ((r : ℂ) ^ (N - 1) * r) := by
      rw [← pow_succ, hNsucc]
    _ = c * (r : ℂ) ^ (N - 1) * r := by ring
    _ = (r : ℂ) ^ (N - 1) * c * r := by ring

theorem radialPrimitiveProfile_eq_quadratic_near_zero
    {N : ℕ} (hNpos : 0 < N) {F : ℝ → ℂ} {R η : ℝ} {c : ℂ}
    (hη : 0 < η) (hηR : η ≤ R)
    (hprim_int_tail :
      IntervalIntegrable (radialPrimitiveDeriv N F) volume η R)
    (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
    ∃ C : ℂ,
      ∀ r ∈ Set.Icc 0 η,
        radialPrimitiveProfile N F R r =
          C + (c / (2 * (N : ℂ))) * (((r ^ 2 : ℝ) : ℂ)) := by
  let K : ℂ := c / (2 * (N : ℂ))
  have _hR_nonneg : 0 ≤ R := le_trans hη.le hηR
  refine ⟨-(∫ t in η..R, radialPrimitiveDeriv N F t) -
      K * (((η ^ 2 : ℝ) : ℂ)), ?_⟩
  intro r hr
  rcases hr with ⟨hr_nonneg, hr_le⟩
  have hN_ne : (N : ℂ) ≠ 0 := by
    exact_mod_cast hNpos.ne'
  have hlin_cont :
      Continuous (fun t : ℝ => c * (((t : ℝ) : ℂ) / (N : ℂ))) := by
    fun_prop
  have hlin_int :
      IntervalIntegrable
        (fun t : ℝ => c * (((t : ℝ) : ℂ) / (N : ℂ))) volume r η :=
    hlin_cont.intervalIntegrable r η
  have hlin_eq_deriv :
      EqOn
        (fun t : ℝ => c * (((t : ℝ) : ℂ) / (N : ℂ)))
        (radialPrimitiveDeriv N F) (Set.uIoc r η) := by
    intro t ht
    have htIoc : t ∈ Set.Ioc r η := by
      simpa [uIoc_of_le hr_le] using ht
    exact (radialPrimitiveDeriv_eq_linear_near_zero hNpos hη
      (lt_of_le_of_lt hr_nonneg htIoc.1) htIoc.2 hF_zero).symm
  have hprim_int_rη :
      IntervalIntegrable (radialPrimitiveDeriv N F) volume r η :=
    hlin_int.congr hlin_eq_deriv
  have hsplit :
      (∫ t in r..R, radialPrimitiveDeriv N F t) =
        (∫ t in r..η, radialPrimitiveDeriv N F t) +
          ∫ t in η..R, radialPrimitiveDeriv N F t := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      hprim_int_rη hprim_int_tail).symm
  have hderiv_integral :
      (∫ t in r..η, radialPrimitiveDeriv N F t) =
        K * (((η ^ 2 : ℝ) : ℂ)) -
          K * (((r ^ 2 : ℝ) : ℂ)) := by
    have hcongr :
        (∫ t in r..η, radialPrimitiveDeriv N F t) =
          ∫ t in r..η, c * (((t : ℝ) : ℂ) / (N : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.mem_uIcc] at ht
      have htIcc : t ∈ Set.Icc 0 η := by
        rw [Set.mem_Icc]
        rcases ht with ⟨hrt, htη⟩ | ⟨hηt, htr⟩
        · exact ⟨le_trans hr_nonneg hrt, htη⟩
        · exact ⟨by linarith, by linarith⟩
      by_cases ht_zero : t = 0
      · subst t
        simp
      · have ht_nonneg : 0 ≤ t := htIcc.1
        have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht_zero)
        exact radialPrimitiveDeriv_eq_linear_near_zero hNpos hη
          ht_pos htIcc.2 hF_zero
    rw [hcongr]
    have hlinear_rewrite :
        (fun t : ℝ => c * (((t : ℝ) : ℂ) / (N : ℂ))) =
          fun t : ℝ => (c / (N : ℂ)) * ((t : ℝ) : ℂ) := by
      funext t
      field_simp [hN_ne]
    rw [hlinear_rewrite]
    rw [show (∫ t in r..η, (c / (N : ℂ)) * ((t : ℝ) : ℂ)) =
        (c / (N : ℂ)) * ∫ t in r..η, ((t : ℝ) : ℂ) by
      exact intervalIntegral.integral_const_mul (c / (N : ℂ))
        (fun t : ℝ => ((t : ℝ) : ℂ))]
    rw [show (∫ t in r..η, ((t : ℝ) : ℂ)) =
        (((∫ t in r..η, t) : ℝ) : ℂ) by
      rw [intervalIntegral.integral_of_le hr_le,
        intervalIntegral.integral_of_le hr_le]
      exact integral_complex_ofReal]
    rw [integral_id]
    simp [K]
    field_simp [hN_ne]
  calc
    radialPrimitiveProfile N F R r
        = -∫ t in r..R, radialPrimitiveDeriv N F t := by
            rfl
    _ = -((∫ t in r..η, radialPrimitiveDeriv N F t) +
          ∫ t in η..R, radialPrimitiveDeriv N F t) := by
            rw [hsplit]
    _ = (-(∫ t in η..R, radialPrimitiveDeriv N F t) -
          K * (((η ^ 2 : ℝ) : ℂ))) +
          K * (((r ^ 2 : ℝ) : ℂ)) := by
            rw [hderiv_integral]
            ring
    _ = (-(∫ t in η..R, radialPrimitiveDeriv N F t) -
          K * (((η ^ 2 : ℝ) : ℂ))) +
          (c / (2 * (N : ℂ))) * (((r ^ 2 : ℝ) : ℂ)) := by
            simp [K]

theorem deriv_radialPrimitiveDeriv
    {N : ℕ} (hNpos : 0 < N) {F : ℝ → ℂ}
    (hF_cont : Continuous F) :
    ∀ r ∈ Set.Ioi 0,
      deriv (radialPrimitiveDeriv N F) r +
        (((((N - 1 : ℕ) : ℝ) / r : ℝ) : ℂ) *
          radialPrimitiveDeriv N F r) = F r := by
  intro r hr
  have hr_pos : 0 < r := hr
  let p : ℝ → ℝ := fun x => x ^ (N - 1)
  let p' : ℝ := ((N - 1 : ℕ) : ℝ) * r ^ (N - 1 - 1)
  have hp : HasDerivAt p p' r := by
    simpa [p, p'] using (hasDerivAt_pow (N - 1) r)
  have hp_ne : p r ≠ 0 := by
    simp [p, hr_pos.ne']
  have hpinv : HasDerivAt (fun x : ℝ => (p x)⁻¹)
      (-p' / (p r) ^ 2) r := by
    simpa using hp.inv hp_ne
  have hpinvC : HasDerivAt (fun x : ℝ => (((p x)⁻¹ : ℝ) : ℂ))
      (((-p' / (p r) ^ 2 : ℝ) : ℂ)) r := by
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r hpinv
  have hmass := hasDerivAt_radialMass (N := N) hF_cont r
  have hraw : HasDerivAt
      (fun x : ℝ => (((p x)⁻¹ : ℝ) : ℂ) * radialMass N F x)
      (((-p' / (p r) ^ 2 : ℝ) : ℂ) * radialMass N F r +
        (((p r)⁻¹ : ℝ) : ℂ) * (((r ^ (N - 1) : ℝ) : ℂ) * F r)) r := by
    simpa [p] using hpinvC.mul hmass
  have hlocal : radialPrimitiveDeriv N F =ᶠ[𝓝 r]
      fun x : ℝ => (((p x)⁻¹ : ℝ) : ℂ) * radialMass N F x := by
    filter_upwards [Ioi_mem_nhds hr_pos] with x hx
    ·
      have hx_pos : 0 < x := hx
      rw [radialPrimitiveDeriv_eq_inv_mul (N := N) (F := F) hx_pos.ne']
      simp [p]
  have hA := hraw.congr_of_eventuallyEq hlocal
  have hp_log : p' = (((N - 1 : ℕ) : ℝ) / r) * p r := by
    dsimp [p, p']
    rcases N with _ | N
    · cases hNpos
    rcases N with _ | k
    · norm_num
    · have hr_ne : r ≠ 0 := hr_pos.ne'
      norm_num
      field_simp [hr_ne]
      ring
  have hA_value : radialPrimitiveDeriv N F r =
      (((p r)⁻¹ : ℝ) : ℂ) * radialMass N F r := by
    rw [radialPrimitiveDeriv_eq_inv_mul (N := N) (F := F) hr_pos.ne']
    simp [p]
  rw [hA.deriv, hA_value, hp_log]
  dsimp [p] at hp_ne ⊢
  have hr_ne : r ≠ 0 := hr_pos.ne'
  field_simp [hp_ne, hr_ne]
  have hpow_cancel :
      ((1 / r ^ (N - 1) : ℝ) : ℂ) * ((r ^ (N - 1) : ℝ) : ℂ) = 1 := by
    have hpow_ne : r ^ (N - 1) ≠ 0 := pow_ne_zero (N - 1) hr_ne
    norm_cast
    field_simp [hpow_ne]
  rw [hpow_cancel]
  have hcoeff :
      (((-(((N - 1 : ℕ) : ℝ) / (r * r ^ (N - 1))) : ℝ) : ℂ)) =
        -(((1 / r ^ (N - 1) : ℝ) : ℂ) *
          (((((N - 1 : ℕ) : ℝ) / r) : ℝ) : ℂ)) := by
    have hpow_ne : r ^ (N - 1) ≠ 0 := pow_ne_zero (N - 1) hr_ne
    norm_cast
    field_simp [hr_ne, hpow_ne]
  rw [hcoeff]
  ring

theorem continuousAt_radialPrimitiveDeriv_of_pos
    {N : ℕ} {F : ℝ → ℂ}
    (hF_cont : Continuous F) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (radialPrimitiveDeriv N F) r := by
  let G : ℝ → ℂ :=
    fun x => (((x ^ (N - 1) : ℝ) : ℂ)⁻¹) * radialMass N F x
  have hmass_cont : ContinuousAt (radialMass N F) r :=
    (hasDerivAt_radialMass (N := N) hF_cont r).continuousAt
  have hpow_cont :
      ContinuousAt (fun x : ℝ => ((x ^ (N - 1) : ℝ) : ℂ)) r := by
    fun_prop
  have hpow_ne : ((r ^ (N - 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero (N - 1) hr.ne'
  have hinv_cont :
      ContinuousAt (fun x : ℝ => (((x ^ (N - 1) : ℝ) : ℂ)⁻¹)) r :=
    hpow_cont.inv₀ hpow_ne
  have hG_cont : ContinuousAt G r := hinv_cont.mul hmass_cont
  have hlocal : radialPrimitiveDeriv N F =ᶠ[𝓝 r] G := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact radialPrimitiveDeriv_eq_inv_mul (N := N) (F := F) hx.ne'
  exact hG_cont.congr_of_eventuallyEq hlocal

theorem intervalIntegrable_radialPrimitiveDeriv_of_pos
    {N : ℕ} {F : ℝ → ℂ}
    (hF_cont : Continuous F) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (radialPrimitiveDeriv N F) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro x hx
  have hxpos : 0 < x := by
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨hax, _⟩ | ⟨hbx, _⟩
    · exact lt_of_lt_of_le ha hax
    · exact lt_of_lt_of_le hb hbx
  exact (continuousAt_radialPrimitiveDeriv_of_pos hF_cont hxpos).continuousWithinAt

theorem hasDerivAt_radialPrimitiveProfile_of_pos
    {N : ℕ} {F : ℝ → ℂ} {R r : ℝ}
    (hF_cont : Continuous F)
    (hprim_int :
      IntervalIntegrable (radialPrimitiveDeriv N F) volume r R)
    (hr : 0 < r) :
    HasDerivAt (fun u : ℝ => radialPrimitiveProfile N F R u)
      (radialPrimitiveDeriv N F r) r := by
  have hB_cont : ContinuousAt (radialPrimitiveDeriv N F) r :=
    continuousAt_radialPrimitiveDeriv_of_pos hF_cont hr
  have hB_meas :
      StronglyMeasurableAtFilter (radialPrimitiveDeriv N F) (𝓝 r) volume :=
    (ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioi 0) isOpen_Ioi
      (fun x hx => continuousAt_radialPrimitiveDeriv_of_pos (N := N) hF_cont hx)) r hr
  have hbase : HasDerivAt
      (fun u : ℝ => ∫ t in u..R, radialPrimitiveDeriv N F t)
      (-(radialPrimitiveDeriv N F r)) r := by
    exact intervalIntegral.integral_hasDerivAt_left hprim_int hB_meas hB_cont
  simpa [radialPrimitiveProfile] using hbase.neg

theorem deriv_radialPrimitiveProfile_of_pos
    {N : ℕ} {F : ℝ → ℂ} {R r : ℝ}
    (hF_cont : Continuous F)
    (hprim_int :
      IntervalIntegrable (radialPrimitiveDeriv N F) volume r R)
    (hr : 0 < r) :
    deriv (fun u : ℝ => radialPrimitiveProfile N F R u) r =
      radialPrimitiveDeriv N F r :=
  (hasDerivAt_radialPrimitiveProfile_of_pos hF_cont hprim_int hr).deriv

theorem radialProfileLaplacian_radialPrimitiveProfile_of_pos
    {N : ℕ} (hNpos : 0 < N) {F : ℝ → ℂ} {R : ℝ}
    (hF_cont : Continuous F)
    (hprim_int_pos :
      ∀ u ∈ Set.Ioi 0,
        IntervalIntegrable (radialPrimitiveDeriv N F) volume u R) :
    ∀ r ∈ Set.Ioi 0,
      radialProfileLaplacian N
          (fun u : ℝ => radialPrimitiveProfile N F R u) r = F r := by
  intro r hr
  have hr_pos : 0 < r := hr
  have hfirst :
      deriv (fun u : ℝ => radialPrimitiveProfile N F R u) r =
        radialPrimitiveDeriv N F r :=
    deriv_radialPrimitiveProfile_of_pos hF_cont (hprim_int_pos r hr) hr_pos
  have hderiv_eventual :
      (fun u : ℝ =>
          deriv (fun s : ℝ => radialPrimitiveProfile N F R s) u) =ᶠ[𝓝 r]
        radialPrimitiveDeriv N F := by
    filter_upwards [Ioi_mem_nhds hr_pos] with u hu
    exact deriv_radialPrimitiveProfile_of_pos hF_cont (hprim_int_pos u hu) hu
  have hsecond :
      deriv
          (fun u : ℝ =>
            deriv (fun s : ℝ => radialPrimitiveProfile N F R s) u) r =
        deriv (radialPrimitiveDeriv N F) r :=
    hderiv_eventual.deriv_eq
  rw [radialProfileLaplacian, hsecond, hfirst]
  exact deriv_radialPrimitiveDeriv hNpos hF_cont r hr

theorem radialProfileLaplacian_radialPrimitiveProfile_of_pos_of_R_pos
    {N : ℕ} (hNpos : 0 < N) {F : ℝ → ℂ} {R : ℝ}
    (hF_cont : Continuous F) (hRpos : 0 < R) :
    ∀ r ∈ Set.Ioi 0,
      radialProfileLaplacian N
          (fun u : ℝ => radialPrimitiveProfile N F R u) r = F r := by
  exact radialProfileLaplacian_radialPrimitiveProfile_of_pos hNpos hF_cont
    (fun u hu =>
      intervalIntegrable_radialPrimitiveDeriv_of_pos hF_cont hu hRpos)

/-- Away from the origin, the radial derivative profile is `C¹` when the
source profile is smooth. -/
theorem contDiffOn_radialPrimitiveDeriv_of_smooth
    {N : ℕ} {F : ℝ → ℂ} (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiffOn ℝ (1 : ℕ) (radialPrimitiveDeriv N F) (Set.Ioi 0) := by
  let G : ℝ → ℂ := fun r =>
    (((r ^ (N - 1) : ℝ) : ℂ)⁻¹) * radialMass N F r
  have hmass : ContDiffOn ℝ (1 : ℕ) (radialMass N F) (Set.Ioi 0) := by
    rw [show ((1 : ℕ) : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 by rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    constructor
    · intro r _hr
      have hdiff : DifferentiableAt ℝ (radialMass N F) r :=
        (hasDerivAt_radialMass (N := N) hF_smooth.continuous r).differentiableAt
      exact hdiff.differentiableWithinAt
    · constructor
      · intro h
        cases h
      · have hpow_real : ContDiffOn ℝ (0 : ℕ)
            (fun r : ℝ => r ^ (N - 1)) (Set.Ioi 0) := by
          fun_prop
        have hpow_complex : ContDiffOn ℝ (0 : ℕ)
            (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ)) (Set.Ioi 0) := by
          simpa [Function.comp_def] using
            Complex.ofRealCLM.contDiff.comp_contDiffOn hpow_real
        have hintegrand : ContDiffOn ℝ (0 : ℕ)
            (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ) * F r)
            (Set.Ioi 0) :=
          hpow_complex.mul
            ((hF_smooth.of_le (by norm_num :
              ((0 : ℕ) : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffOn)
        exact hintegrand.congr fun r hr =>
          deriv_radialMass (N := N) hF_smooth.continuous r hr
  have hG : ContDiffOn ℝ (1 : ℕ) G (Set.Ioi 0) := by
    have hpow_real : ContDiffOn ℝ (1 : ℕ)
        (fun r : ℝ => r ^ (N - 1)) (Set.Ioi 0) := by
      fun_prop
    have hpow_complex : ContDiffOn ℝ (1 : ℕ)
        (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ)) (Set.Ioi 0) := by
      simpa [Function.comp_def] using
        Complex.ofRealCLM.contDiff.comp_contDiffOn hpow_real
    have hpow_ne : ∀ r ∈ Set.Ioi 0,
        ((r ^ (N - 1) : ℝ) : ℂ) ≠ 0 := by
      intro r hr
      have hr_pos : 0 < r := hr
      exact_mod_cast pow_ne_zero (N - 1) hr_pos.ne'
    have hinv : ContDiffOn ℝ (1 : ℕ)
        (fun r : ℝ => (((r ^ (N - 1) : ℝ) : ℂ)⁻¹)) (Set.Ioi 0) :=
      hpow_complex.inv hpow_ne
    exact hinv.mul hmass
  refine hG.congr ?_
  intro r hr
  exact radialPrimitiveDeriv_eq_inv_mul (N := N) (F := F) hr.ne'

/-- The radial primitive profile is `C²` on the positive half-line. -/
theorem contDiffOn_radialPrimitiveProfile_of_pos
    {N : ℕ} {F : ℝ → ℂ} {R : ℝ}
    (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F) (hRpos : 0 < R) :
    ContDiffOn ℝ (2 : ℕ)
      (fun r : ℝ => radialPrimitiveProfile N F R r) (Set.Ioi 0) := by
  rw [show ((2 : ℕ) : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  constructor
  · intro r hr
    exact (hasDerivAt_radialPrimitiveProfile_of_pos (N := N) (F := F) (R := R)
      hF_smooth.continuous
      (intervalIntegrable_radialPrimitiveDeriv_of_pos hF_smooth.continuous hr hRpos)
      hr).differentiableAt.differentiableWithinAt
  · constructor
    · intro h
      cases h
    · exact (contDiffOn_radialPrimitiveDeriv_of_smooth (N := N)
        hF_smooth).congr fun r hr =>
          (deriv_radialPrimitiveProfile_of_pos (N := N) (F := F) (R := R)
            hF_smooth.continuous
            (intervalIntegrable_radialPrimitiveDeriv_of_pos hF_smooth.continuous hr hRpos)
            hr)

/-- Away from the origin, the radial derivative profile is smooth when the
source profile is smooth. -/
theorem contDiffOn_radialPrimitiveDeriv_of_smooth_infty
    {N : ℕ} {F : ℝ → ℂ} (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (radialPrimitiveDeriv N F) (Set.Ioi 0) := by
  let G : ℝ → ℂ := fun r =>
    (((r ^ (N - 1) : ℝ) : ℂ)⁻¹) * radialMass N F r
  have hmass : ContDiffOn ℝ (⊤ : ℕ∞) (radialMass N F) (Set.Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    constructor
    · intro r _hr
      have hdiff : DifferentiableAt ℝ (radialMass N F) r :=
        (hasDerivAt_radialMass (N := N) hF_smooth.continuous r).differentiableAt
      exact hdiff.differentiableWithinAt
    · have hpow_real : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun r : ℝ => r ^ (N - 1)) (Set.Ioi 0) := by
        fun_prop
      have hpow_complex : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ)) (Set.Ioi 0) := by
        simpa [Function.comp_def] using
          Complex.ofRealCLM.contDiff.comp_contDiffOn hpow_real
      have hintegrand : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ) * F r)
          (Set.Ioi 0) :=
        hpow_complex.mul hF_smooth.contDiffOn
      exact hintegrand.congr fun r hr =>
        deriv_radialMass (N := N) hF_smooth.continuous r hr
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G (Set.Ioi 0) := by
    have hpow_real : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun r : ℝ => r ^ (N - 1)) (Set.Ioi 0) := by
      fun_prop
    have hpow_complex : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ)) (Set.Ioi 0) := by
      simpa [Function.comp_def] using
        Complex.ofRealCLM.contDiff.comp_contDiffOn hpow_real
    have hpow_ne : ∀ r ∈ Set.Ioi 0,
        ((r ^ (N - 1) : ℝ) : ℂ) ≠ 0 := by
      intro r hr
      have hr_pos : 0 < r := hr
      exact_mod_cast pow_ne_zero (N - 1) hr_pos.ne'
    have hinv : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun r : ℝ => (((r ^ (N - 1) : ℝ) : ℂ)⁻¹)) (Set.Ioi 0) :=
      hpow_complex.inv hpow_ne
    exact hinv.mul hmass
  refine hG.congr ?_
  intro r hr
  exact radialPrimitiveDeriv_eq_inv_mul (N := N) (F := F) hr.ne'

/-- The radial primitive profile is smooth on the positive half-line. -/
theorem contDiffOn_radialPrimitiveProfile_of_pos_infty
    {N : ℕ} {F : ℝ → ℂ} {R : ℝ}
    (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F) (hRpos : 0 < R) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun r : ℝ => radialPrimitiveProfile N F R r) (Set.Ioi 0) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  constructor
  · intro r hr
    exact (hasDerivAt_radialPrimitiveProfile_of_pos (N := N) (F := F) (R := R)
      hF_smooth.continuous
      (intervalIntegrable_radialPrimitiveDeriv_of_pos hF_smooth.continuous hr hRpos)
      hr).differentiableAt.differentiableWithinAt
  · exact (contDiffOn_radialPrimitiveDeriv_of_smooth_infty (N := N)
      hF_smooth).congr fun r hr =>
        deriv_radialPrimitiveProfile_of_pos (N := N) (F := F) (R := R)
          hF_smooth.continuous
          (intervalIntegrable_radialPrimitiveDeriv_of_pos hF_smooth.continuous hr hRpos)
          hr

theorem radialPrimitiveProfile_eventually_quadratic_norm_near_zero
    {ι : Type*} [Fintype ι]
    {N : ℕ} (hNpos : 0 < N) {F : ℝ → ℂ} {R η : ℝ} {c : ℂ}
    (hη : 0 < η) (hηR : η ≤ R)
    (hprim_int_tail :
      IntervalIntegrable (radialPrimitiveDeriv N F) volume η R)
    (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
    ∃ C : ℂ, ∀ᶠ x : EuclideanSpace ℝ ι in 𝓝 0,
      radialPrimitiveProfile N F R ‖x‖ =
        C + (c / (2 * (N : ℂ))) * (((‖x‖ ^ 2 : ℝ) : ℂ)) := by
  rcases radialPrimitiveProfile_eq_quadratic_near_zero hNpos hη hηR
      hprim_int_tail hF_zero with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ ι) hη] with x hx
  have hnorm_lt : ‖x‖ < η := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  exact hC ‖x‖ ⟨norm_nonneg x, hnorm_lt.le⟩

/-- The squared Euclidean norm has constant Laplacian `2 * dim`. -/
theorem laplacian_norm_sq_real
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    Laplacian.laplacian (fun y : EuclideanSpace ℝ ι => ‖y‖ ^ 2) x =
      (2 * Fintype.card ι : ℝ) := by
  calc
    Laplacian.laplacian (fun y : EuclideanSpace ℝ ι => ‖y‖ ^ 2) x =
        ∑ i, (iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ ι => ‖y‖ ^ 2) x)
            ![(EuclideanSpace.basisFun ι ℝ) i,
              (EuclideanSpace.basisFun ι ℝ) i] := by
      exact congrFun
        (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
          (fun y : EuclideanSpace ℝ ι => ‖y‖ ^ 2)
          (EuclideanSpace.basisFun ι ℝ)) x
    _ = (2 * Fintype.card ι : ℝ) := by
      let e : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.basisFun ι ℝ i
      have hfd : fderiv ℝ (2 • ⇑(innerSL ℝ (E := EuclideanSpace ℝ ι))) x =
          2 • (innerSL ℝ) := by
        change fderiv ℝ (⇑(2 • (innerSL ℝ (E := EuclideanSpace ℝ ι)))) x =
          2 • (innerSL ℝ)
        simpa using ContinuousLinearMap.fderiv (𝕜 := ℝ)
          (2 • (innerSL ℝ (E := EuclideanSpace ℝ ι)))
      have hterm : ∀ i : ι,
          (iteratedFDeriv ℝ 2
              (fun y : EuclideanSpace ℝ ι => ‖y‖ ^ 2) x) ![e i, e i] = 2 := by
        intro i
        rw [iteratedFDeriv_two_apply, fderiv_norm_sq]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have hfd_apply := congrArg (fun L => (L (e i)) (e i)) hfd
        refine hfd_apply.trans ?_
        exact
          (show ((2 • (innerSL ℝ (E := EuclideanSpace ℝ ι)))
              ((EuclideanSpace.basisFun ι ℝ) i))
              ((EuclideanSpace.basisFun ι ℝ) i) = (2 : ℝ) by
            simp [(EuclideanSpace.basisFun ι ℝ).norm_eq_one])
      calc
        (∑ i, (iteratedFDeriv ℝ 2
              (fun y : EuclideanSpace ℝ ι => ‖y‖ ^ 2) x)
                ![(EuclideanSpace.basisFun ι ℝ) i,
                  (EuclideanSpace.basisFun ι ℝ) i])
            = ∑ _i : ι, (2 : ℝ) := by
              apply Finset.sum_congr rfl
              intro i _
              simpa [e] using hterm i
        _ = (2 * Fintype.card ι : ℝ) := by
              simp [mul_comm]

/-- The quadratic germ supplied by the radial primitive has the expected
Euclidean Laplacian. -/
theorem laplacian_quadratic_norm_complex
    {ι : Type*} [Fintype ι]
    (C K : ℂ) (x : EuclideanSpace ℝ ι) :
    Laplacian.laplacian
        (fun y : EuclideanSpace ℝ ι =>
          C + K * (((‖y‖ ^ 2 : ℝ) : ℂ))) x =
      K * ((2 * Fintype.card ι : ℝ) : ℂ) := by
  have hsmooth : ContDiffAt ℝ 2
      (fun y : EuclideanSpace ℝ ι => ‖y‖ ^ 2) x :=
    contDiffAt_id.norm_sq ℝ
  have hofReal :
      Laplacian.laplacian
          (fun y : EuclideanSpace ℝ ι => (((‖y‖ ^ 2 : ℝ) : ℂ))) x =
        (((2 * Fintype.card ι : ℝ) : ℂ)) := by
    simpa [Function.comp_def, laplacian_norm_sq_real (ι := ι) x] using
      hsmooth.laplacian_CLM_comp_left (l := Complex.ofRealCLM)
  have hcomplex_smooth : ContDiffAt ℝ 2
      (fun y : EuclideanSpace ℝ ι => (((‖y‖ ^ 2 : ℝ) : ℂ))) x :=
    (Complex.ofRealCLM.contDiff.of_le le_top).contDiffAt.comp x
      ((contDiffAt_id.norm_sq ℝ).of_le le_top)
  have hmul :
      Laplacian.laplacian
          (fun y : EuclideanSpace ℝ ι => K * (((‖y‖ ^ 2 : ℝ) : ℂ))) x =
        K * (((2 * Fintype.card ι : ℝ) : ℂ)) := by
    have hmul_raw :=
      InnerProductSpace.laplacian_smul (𝕜 := ℂ)
        (f := fun y : EuclideanSpace ℝ ι => (((‖y‖ ^ 2 : ℝ) : ℂ))) K
        hcomplex_smooth
    have hfun :
        (fun y : EuclideanSpace ℝ ι => K * (((‖y‖ ^ 2 : ℝ) : ℂ))) =
          K • (fun y : EuclideanSpace ℝ ι => (((‖y‖ ^ 2 : ℝ) : ℂ))) := by
      ext y
      simp [smul_eq_mul]
    rw [hfun, hmul_raw, hofReal]
    simp [smul_eq_mul]
  have hmul_smooth : ContDiffAt ℝ 2
      (fun y : EuclideanSpace ℝ ι => K * (((‖y‖ ^ 2 : ℝ) : ℂ))) x := by
    simpa [smul_eq_mul] using hcomplex_smooth.const_smul K
  have hconst_smooth : ContDiffAt ℝ 2
      (fun _ : EuclideanSpace ℝ ι => C) x :=
    contDiffAt_const
  have hadd := hconst_smooth.laplacian_add hmul_smooth
  have hfun :
      (fun y : EuclideanSpace ℝ ι =>
        C + K * (((‖y‖ ^ 2 : ℝ) : ℂ))) =
        (fun _ : EuclideanSpace ℝ ι => C) +
          fun y => K * (((‖y‖ ^ 2 : ℝ) : ℂ)) := by
    ext y
    simp
  rw [hfun, hadd, hmul]
  simp

/-- A nonzero point in `EuclideanSpace ℝ ι` forces the coordinate type to have
positive cardinality. -/
theorem euclidean_card_pos_of_ne_zero
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
    0 < Fintype.card ι := by
  by_contra h
  have hcard : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos h
  have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
  haveI := hempty
  exact hx (Subsingleton.elim x 0)

/-- The real cast of `card - 1` agrees with subtracting one whenever an
off-origin point exists. -/
theorem nat_cast_card_sub_one_of_ne_zero
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
    (((Fintype.card ι - 1 : ℕ) : ℝ) =
      (Fintype.card ι : ℝ) - 1) := by
  exact Nat.cast_pred (euclidean_card_pos_of_ne_zero hx)

/-- The squared radial first-derivative coefficients sum to one away from the
origin. -/
theorem sum_coord_sq_div_norm_sq_eq_one
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
    (∑ i : ι, (x i / ‖x‖)^2) = (1 : ℝ) := by
  have hnorm_ne : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
  have hnorm_sq : ‖x‖ ^ 2 = ∑ i : ι, (x i)^2 := by
    simpa [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x)
  calc
    (∑ i : ι, (x i / ‖x‖)^2)
        = (∑ i : ι, (x i)^2) / ‖x‖^2 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i _
            field_simp [hnorm_ne]
    _ = 1 := by
            rw [← hnorm_sq]
            field_simp [hnorm_ne]

/-- Complex-valued version of the squared radial first-derivative coefficient
sum. -/
theorem sum_complex_coord_sq_div_norm_sq_eq_one
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
    (∑ i : ι, (((x i / ‖x‖ : ℝ) : ℂ)^2)) = (1 : ℂ) := by
  exact_mod_cast (sum_coord_sq_div_norm_sq_eq_one (ι := ι) hx)

/-- The trace of the off-origin norm Hessian is `(dim - 1) / ‖x‖`. -/
theorem sum_radial_norm_hessian_coeff
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
    (∑ i : ι, (1 / ‖x‖ - (x i)^2 / ‖x‖^3)) =
      ((Fintype.card ι : ℝ) - 1) / ‖x‖ := by
  have hnorm_ne : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
  have hnorm_sq : ‖x‖ ^ 2 = ∑ i : ι, (x i)^2 := by
    simpa [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x)
  calc
    (∑ i : ι, (1 / ‖x‖ - (x i)^2 / ‖x‖^3))
        = (Fintype.card ι : ℝ) / ‖x‖ -
            (∑ i : ι, (x i)^2) / ‖x‖^3 := by
            rw [Finset.sum_sub_distrib]
            rw [Finset.sum_const, Finset.card_univ]
            rw [Finset.sum_div]
            simp [div_eq_mul_inv]
    _ = ((Fintype.card ι : ℝ) - 1) / ‖x‖ := by
            rw [← hnorm_sq]
            field_simp [hnorm_ne]

/-- Complex-valued version of the trace of the off-origin norm Hessian. -/
theorem sum_complex_radial_norm_hessian_coeff
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
    (∑ i : ι,
      (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ))) =
      ((((Fintype.card ι : ℝ) - 1) / ‖x‖ : ℝ) : ℂ) := by
  exact_mod_cast (sum_radial_norm_hessian_coeff (ι := ι) hx)

/-- The norm has Frechet derivative `v ↦ ⟪x, v⟫ / ‖x‖` away from the origin. -/
theorem hasFDerivAt_norm_off_origin
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
    HasFDerivAt
      (fun y : EuclideanSpace ℝ ι => ‖y‖)
      ((‖x‖⁻¹ : ℝ) • innerSL ℝ x) x := by
  have hsq : HasFDerivAt
      (fun y : EuclideanSpace ℝ ι => ‖y‖ ^ 2)
      (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hsq_ne : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_pos_iff.mpr hx).ne'
  have hsqrt := hsq.sqrt hsq_ne
  have hcoeff : (1 / (2 * √(‖x‖ ^ 2)) : ℝ) • (2 • innerSL ℝ x) =
      (‖x‖⁻¹ : ℝ) • innerSL ℝ x := by
    rw [Real.sqrt_sq (norm_nonneg x)]
    ext v
    simp
    field_simp [(norm_pos_iff.mpr hx).ne']
  convert hsqrt using 1
  · ext y
    rw [Real.sqrt_sq (norm_nonneg y)]
  · exact hcoeff.symm

/-- Coordinate form of the first derivative of the norm in an orthonormal
basis direction. -/
theorem fderiv_norm_basisFun_off_origin
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) (i : ι) :
    fderiv ℝ (fun y : EuclideanSpace ℝ ι => ‖y‖) x
        ((EuclideanSpace.basisFun ι ℝ) i) =
      x i / ‖x‖ := by
  rw [(hasFDerivAt_norm_off_origin hx).fderiv]
  simp [div_eq_mul_inv, smul_eq_mul]
  ring

/-- The coordinate derivative of `y_i / ‖y‖` in the same basis direction. -/
theorem fderiv_coord_div_norm_basisFun
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) (i : ι) :
    fderiv ℝ (fun y : EuclideanSpace ℝ ι => y i / ‖y‖) x
        ((EuclideanSpace.basisFun ι ℝ) i) =
      1 / ‖x‖ - (x i)^2 / ‖x‖^3 := by
  let e : EuclideanSpace ℝ ι := (EuclideanSpace.basisFun ι ℝ) i
  have hecoord : e i = (1 : ℝ) := by
    have hinner : inner ℝ ((EuclideanSpace.basisFun ι ℝ) i) e = e i :=
      EuclideanSpace.basisFun_inner (𝕜 := ℝ) (ι := ι) e i
    rw [← hinner]
    simp [e, (EuclideanSpace.basisFun ι ℝ).norm_eq_one]
  have hnorm_ne : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
  have hcoord : HasFDerivAt (fun y : EuclideanSpace ℝ ι => y i)
      ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : ι => ℝ) i :
          EuclideanSpace ℝ ι →L[ℝ] ℝ)) x := by
    exact (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : ι => ℝ) i).hasFDerivAt
  have hnorm := hasFDerivAt_norm_off_origin hx
  have hinv_norm : HasFDerivAt (fun y : EuclideanSpace ℝ ι => (‖y‖)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ ℝ (‖x‖)⁻¹ (‖x‖)⁻¹).comp
        ((‖x‖⁻¹ : ℝ) • innerSL ℝ x)) x := by
    exact (hasFDerivAt_inv' (𝕜 := ℝ) hnorm_ne).comp x hnorm
  have hprod := hcoord.mul hinv_norm
  rw [show (fun y : EuclideanSpace ℝ ι => y i / ‖y‖) =
      ((fun y : EuclideanSpace ℝ ι => y i) * fun y => (‖y‖)⁻¹) by
    ext y
    rw [Pi.mul_apply, div_eq_mul_inv]]
  rw [hprod.fderiv]
  simp [e, hecoord, ContinuousLinearMap.mulLeftRight_apply]
  field_simp [hnorm_ne]
  ring

/-- The coordinate quotient `y_i / ‖y‖` is differentiable away from the
origin. -/
theorem differentiableAt_coord_div_norm_off_origin
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) (i : ι) :
    DifferentiableAt ℝ (fun y : EuclideanSpace ℝ ι => y i / ‖y‖) x := by
  have hnorm_ne : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
  have hcoord : HasFDerivAt (fun y : EuclideanSpace ℝ ι => y i)
      ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : ι => ℝ) i :
          EuclideanSpace ℝ ι →L[ℝ] ℝ)) x := by
    exact (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : ι => ℝ) i).hasFDerivAt
  have hnorm := hasFDerivAt_norm_off_origin hx
  have hinv_norm : HasFDerivAt (fun y : EuclideanSpace ℝ ι => (‖y‖)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ ℝ (‖x‖)⁻¹ (‖x‖)⁻¹).comp
        ((‖x‖⁻¹ : ℝ) • innerSL ℝ x)) x := by
    exact (hasFDerivAt_inv' (𝕜 := ℝ) hnorm_ne).comp x hnorm
  have hprod := hcoord.mul hinv_norm
  have hfun : (fun y : EuclideanSpace ℝ ι => y i / ‖y‖) =
      ((fun y : EuclideanSpace ℝ ι => y i) * fun y => (‖y‖)⁻¹) := by
    ext y
    rw [Pi.mul_apply, div_eq_mul_inv]
  rw [hfun]
  exact hprod.differentiableAt

/-- Complex-valued coordinate quotient derivative in the same basis
direction. -/
theorem fderiv_complex_coord_div_norm_basisFun
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) (i : ι) :
    fderiv ℝ (fun y : EuclideanSpace ℝ ι => (((y i / ‖y‖ : ℝ) : ℂ))) x
        ((EuclideanSpace.basisFun ι ℝ) i) =
      (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ)) := by
  have hreal_diff := differentiableAt_coord_div_norm_off_origin hx i
  have hreal_has := hreal_diff.hasFDerivAt
  have hcomplex_has := Complex.ofRealCLM.hasFDerivAt.comp x hreal_has
  change fderiv ℝ (Complex.ofRealCLM ∘
      fun y : EuclideanSpace ℝ ι => y i / ‖y‖) x
        ((EuclideanSpace.basisFun ι ℝ) i) =
      (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ))
  rw [hcomplex_has.fderiv]
  simp [fderiv_coord_div_norm_basisFun hx i]

/-- Off the origin, the diagonal entries of the Hessian of the Euclidean norm
are the standard radial coefficients. -/
theorem iteratedFDeriv_norm_basisFun_basisFun_off_origin
    {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) (i : ι) :
    iteratedFDeriv ℝ 2
        (fun y : EuclideanSpace ℝ ι => ‖y‖) x
        ![(EuclideanSpace.basisFun ι ℝ) i,
          (EuclideanSpace.basisFun ι ℝ) i] =
      1 / ‖x‖ - (x i)^2 / ‖x‖^3 := by
  let e : EuclideanSpace ℝ ι := (EuclideanSpace.basisFun ι ℝ) i
  have hnorm_smooth : ContDiffAt ℝ (2 : ℕ)
      (fun y : EuclideanSpace ℝ ι => ‖y‖) x :=
    contDiffAt_norm ℝ hx
  have hfd_diff : DifferentiableAt ℝ
      (fderiv ℝ (fun y : EuclideanSpace ℝ ι => ‖y‖)) x := by
    have hfd_smooth : ContDiffAt ℝ (1 : ℕ)
        (fderiv ℝ (fun y : EuclideanSpace ℝ ι => ‖y‖)) x :=
      hnorm_smooth.fderiv_right (m := 1) (by norm_num)
    exact hfd_smooth.differentiableAt (by norm_num)
  have h_eval :
      fderiv ℝ (fun y : EuclideanSpace ℝ ι =>
          fderiv ℝ (fun z : EuclideanSpace ℝ ι => ‖z‖) y e) x =
        (ContinuousLinearMap.apply ℝ ℝ e).comp
          (fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ ι => ‖z‖)) x) := by
    change fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ e) ∘
        fun y : EuclideanSpace ℝ ι =>
          fderiv ℝ (fun z : EuclideanSpace ℝ ι => ‖z‖) y) x =
      (ContinuousLinearMap.apply ℝ ℝ e).comp
        (fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ ι => ‖z‖)) x)
    rw [fderiv_comp (x := x)
      (g := (ContinuousLinearMap.apply ℝ ℝ e))
      (f := fun y : EuclideanSpace ℝ ι =>
        fderiv ℝ (fun z : EuclideanSpace ℝ ι => ‖z‖) y)]
    · rw [ContinuousLinearMap.fderiv]
    · exact (ContinuousLinearMap.apply ℝ ℝ e).differentiableAt
    · exact hfd_diff
  have hlocal : (fun y : EuclideanSpace ℝ ι =>
          fderiv ℝ (fun z : EuclideanSpace ℝ ι => ‖z‖) y e) =ᶠ[𝓝 x]
        (fun y : EuclideanSpace ℝ ι => y i / ‖y‖) := by
    filter_upwards [compl_singleton_mem_nhds hx] with y hy
    simp [e, fderiv_norm_basisFun_off_origin hy i]
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ ι => ‖y‖)) x e e = _
  have hscalar := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hlocal
  calc
    fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ ι => ‖y‖)) x e e
        = fderiv ℝ (fun y : EuclideanSpace ℝ ι =>
            fderiv ℝ (fun z : EuclideanSpace ℝ ι => ‖z‖) y e) x e := by
            have happly :=
              congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ => L e) h_eval
            simpa using happly.symm
    _ = fderiv ℝ (fun y : EuclideanSpace ℝ ι => y i / ‖y‖) x e := by
            exact congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ => L e) hscalar
    _ = 1 / ‖x‖ - (x i)^2 / ‖x‖^3 := by
            simpa [e] using fderiv_coord_div_norm_basisFun hx i

private theorem real_smul_smul_complex_mul (r s : ℝ) (z : ℂ) :
    r • s • z = z * (s : ℂ) * (r : ℂ) := by
  rw [Complex.real_smul (x := s) (z := z)]
  rw [Complex.real_smul (x := r) (z := (s : ℂ) * z)]
  ring

/-- First coordinate derivative of a scalar profile composed with the Euclidean
norm. -/
theorem fderiv_radial_comp_basisFun_off_origin
    {ι : Type*} [Fintype ι]
    {a : ℝ → ℂ} {x : EuclideanSpace ℝ ι}
    (hx : x ≠ 0) (ha : DifferentiableAt ℝ a ‖x‖) (i : ι) :
    fderiv ℝ (fun y : EuclideanSpace ℝ ι => a ‖y‖) x
        ((EuclideanSpace.basisFun ι ℝ) i) =
      deriv a ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ)) := by
  have hnorm := hasFDerivAt_norm_off_origin hx
  have ha_deriv : HasDerivAt a (deriv a ‖x‖) ‖x‖ := ha.hasDerivAt
  have hcomp := ha_deriv.hasFDerivAt.comp x hnorm
  change fderiv ℝ (a ∘ norm) x ((EuclideanSpace.basisFun ι ℝ) i) =
    deriv a ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ))
  rw [hcomp.fderiv]
  simp [div_eq_mul_inv]
  calc
    ‖x‖⁻¹ • x i • deriv a ‖x‖ =
        deriv a ‖x‖ * ↑(x i) * ↑(‖x‖⁻¹) :=
          real_smul_smul_complex_mul (r := ‖x‖⁻¹) (s := x i) (z := deriv a ‖x‖)
    _ = deriv a ‖x‖ * ↑(x i) * (↑‖x‖)⁻¹ := by
          norm_num
    _ = deriv a ‖x‖ * (↑(x i) * (↑‖x‖)⁻¹) := by
          ring

/-- First coordinate derivative of `deriv a ∘ ‖·‖`.  This is the `a'' * ρ'`
term used in the off-origin radial Hessian calculation. -/
theorem fderiv_deriv_radial_comp_basisFun_off_origin
    {ι : Type*} [Fintype ι]
    {a : ℝ → ℂ} {x : EuclideanSpace ℝ ι}
    (hx : x ≠ 0) (hda : DifferentiableAt ℝ (deriv a) ‖x‖) (i : ι) :
    fderiv ℝ (fun y : EuclideanSpace ℝ ι => deriv a ‖y‖) x
        ((EuclideanSpace.basisFun ι ℝ) i) =
      deriv (deriv a) ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ)) := by
  have hnorm := hasFDerivAt_norm_off_origin hx
  have hda_deriv : HasDerivAt (deriv a) (deriv (deriv a) ‖x‖) ‖x‖ :=
    hda.hasDerivAt
  have hcomp := hda_deriv.hasFDerivAt.comp x hnorm
  change fderiv ℝ (deriv a ∘ norm) x ((EuclideanSpace.basisFun ι ℝ) i) =
    deriv (deriv a) ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ))
  rw [hcomp.fderiv]
  simp [div_eq_mul_inv]
  calc
    ‖x‖⁻¹ • x i • deriv (deriv a) ‖x‖ =
        deriv (deriv a) ‖x‖ * ↑(x i) * ↑(‖x‖⁻¹) :=
          real_smul_smul_complex_mul
            (r := ‖x‖⁻¹) (s := x i) (z := deriv (deriv a) ‖x‖)
    _ = deriv (deriv a) ‖x‖ * ↑(x i) * (↑‖x‖)⁻¹ := by
          norm_num
    _ = deriv (deriv a) ‖x‖ * (↑(x i) * (↑‖x‖)⁻¹) := by
          ring

/-- Product-rule form of the off-origin radial chain rule after the first
coordinate derivative has been rewritten as `a'(‖y‖) * y_i / ‖y‖`. -/
theorem fderiv_radial_chain_product_basisFun
    {ι : Type*} [Fintype ι]
    {a : ℝ → ℂ} {x : EuclideanSpace ℝ ι}
    (hx : x ≠ 0) (hda : DifferentiableAt ℝ (deriv a) ‖x‖) (i : ι) :
    fderiv ℝ (fun y : EuclideanSpace ℝ ι =>
        deriv a ‖y‖ * (((y i / ‖y‖ : ℝ) : ℂ))) x
        ((EuclideanSpace.basisFun ι ℝ) i) =
      deriv (deriv a) ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ)^2) +
        deriv a ‖x‖ *
          (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ)) := by
  let e : EuclideanSpace ℝ ι := (EuclideanSpace.basisFun ι ℝ) i
  have hg_diff : DifferentiableAt ℝ
      (fun y : EuclideanSpace ℝ ι => deriv a ‖y‖) x := by
    have hnorm := hasFDerivAt_norm_off_origin hx
    have hda_deriv : HasDerivAt (deriv a) (deriv (deriv a) ‖x‖) ‖x‖ :=
      hda.hasDerivAt
    exact (hda_deriv.hasFDerivAt.comp x hnorm).differentiableAt
  have hq_real_diff := differentiableAt_coord_div_norm_off_origin hx i
  have hq_diff : DifferentiableAt ℝ
      (fun y : EuclideanSpace ℝ ι => (((y i / ‖y‖ : ℝ) : ℂ))) x := by
    exact Complex.ofRealCLM.differentiableAt.comp x hq_real_diff
  change fderiv ℝ ((fun y : EuclideanSpace ℝ ι => deriv a ‖y‖) *
      fun y : EuclideanSpace ℝ ι => (((y i / ‖y‖ : ℝ) : ℂ))) x e = _
  have hmul := fderiv_mul hg_diff hq_diff
  have hmul_apply := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℂ => L e) hmul
  change (fun L : EuclideanSpace ℝ ι →L[ℝ] ℂ => L e)
      (fderiv ℝ ((fun y : EuclideanSpace ℝ ι => deriv a ‖y‖) *
        fun y : EuclideanSpace ℝ ι => (((y i / ‖y‖ : ℝ) : ℂ))) x) = _
  calc
    (fun L : EuclideanSpace ℝ ι →L[ℝ] ℂ => L e)
        (fderiv ℝ ((fun y : EuclideanSpace ℝ ι => deriv a ‖y‖) *
          fun y : EuclideanSpace ℝ ι => (((y i / ‖y‖ : ℝ) : ℂ))) x)
        =
          (fun L : EuclideanSpace ℝ ι →L[ℝ] ℂ => L e)
            (deriv a ‖x‖ •
                fderiv ℝ (fun y : EuclideanSpace ℝ ι =>
                  (((y i / ‖y‖ : ℝ) : ℂ))) x +
              (((x i / ‖x‖ : ℝ) : ℂ)) •
                fderiv ℝ (fun y : EuclideanSpace ℝ ι => deriv a ‖y‖) x) := hmul_apply
    _ = deriv (deriv a) ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ)^2) +
          deriv a ‖x‖ *
            (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ)) := by
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
          rw [fderiv_deriv_radial_comp_basisFun_off_origin hx hda i]
          rw [fderiv_complex_coord_div_norm_basisFun hx i]
          simp [smul_eq_mul]
          ring

/-- A `C^2` one-variable profile has differentiable first derivative. -/
theorem differentiableAt_deriv_of_contDiffAt_two
    {a : ℝ → ℂ} {r : ℝ} (ha : ContDiffAt ℝ (2 : ℕ) a r) :
    DifferentiableAt ℝ (deriv a) r := by
  have hfderiv_smooth : ContDiffAt ℝ (1 : ℕ) (fderiv ℝ a) r :=
    ha.fderiv_right (m := 1) (by norm_num)
  have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ a) r :=
    hfderiv_smooth.differentiableAt (by norm_num)
  have happly_diff : DifferentiableAt ℝ
      (fun s : ℝ => (fderiv ℝ a s) (1 : ℝ)) r :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).differentiableAt.comp r hfderiv_diff
  have hderiv_eq : (fun s : ℝ => (fderiv ℝ a s) (1 : ℝ)) = deriv a := by
    funext s
    rw [fderiv_eq_smul_deriv (𝕜 := ℝ) (f := a) (x := s) (y := (1 : ℝ))]
    simp
  simpa [hderiv_eq]

/-- Near an off-origin point, the first coordinate derivative of `a ∘ ‖·‖`
has the expected radial form. -/
theorem eventually_fderiv_radial_comp_basisFun_eq
    {ι : Type*} [Fintype ι]
    {a : ℝ → ℂ} {x : EuclideanSpace ℝ ι}
    (hx : x ≠ 0) (ha : ContDiffAt ℝ (2 : ℕ) a ‖x‖) (i : ι) :
    (fun y : EuclideanSpace ℝ ι =>
        fderiv ℝ (fun z : EuclideanSpace ℝ ι => a ‖z‖) y
          ((EuclideanSpace.basisFun ι ℝ) i)) =ᶠ[𝓝 x]
      (fun y : EuclideanSpace ℝ ι =>
        deriv a ‖y‖ * (((y i / ‖y‖ : ℝ) : ℂ))) := by
  have ha_event : ∀ᶠ r in 𝓝 ‖x‖, DifferentiableAt ℝ a r := by
    exact (ha.eventually (by norm_num)).mono fun r hr =>
      hr.differentiableAt (by norm_num)
  have ha_y_event : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ a ‖y‖ :=
    continuous_norm.continuousAt.tendsto.eventually ha_event
  filter_upwards [compl_singleton_mem_nhds hx, ha_y_event] with y hy hya
  exact fderiv_radial_comp_basisFun_off_origin hy hya i

/-- Diagonal coordinate form of the off-origin second chain rule for radial
profiles. -/
theorem iteratedFDeriv_radial_comp_basisFun_basisFun
    {ι : Type*} [Fintype ι]
    {a : ℝ → ℂ} {x : EuclideanSpace ℝ ι}
    (hx : x ≠ 0) (ha : ContDiffAt ℝ (2 : ℕ) a ‖x‖) (i : ι) :
    iteratedFDeriv ℝ 2
        (fun y : EuclideanSpace ℝ ι => a ‖y‖) x
        ![(EuclideanSpace.basisFun ι ℝ) i,
          (EuclideanSpace.basisFun ι ℝ) i] =
      deriv (deriv a) ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ)^2) +
        deriv a ‖x‖ *
          (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ)) := by
  let e : EuclideanSpace ℝ ι := (EuclideanSpace.basisFun ι ℝ) i
  have hlocal := eventually_fderiv_radial_comp_basisFun_eq hx ha i
  have hda := differentiableAt_deriv_of_contDiffAt_two (a := a) ha
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ ι => a ‖y‖)) x e e = _
  have hnorm_smooth : ContDiffAt ℝ (2 : ℕ)
      (fun y : EuclideanSpace ℝ ι => ‖y‖) x :=
    contDiffAt_norm ℝ hx
  have hradial_smooth : ContDiffAt ℝ (2 : ℕ)
      (fun y : EuclideanSpace ℝ ι => a ‖y‖) x :=
    ha.comp x hnorm_smooth
  have hfd_diff : DifferentiableAt ℝ
      (fderiv ℝ (fun y : EuclideanSpace ℝ ι => a ‖y‖)) x := by
    have hfd_smooth : ContDiffAt ℝ (1 : ℕ)
        (fderiv ℝ (fun y : EuclideanSpace ℝ ι => a ‖y‖)) x :=
      hradial_smooth.fderiv_right (m := 1) (by norm_num)
    exact hfd_smooth.differentiableAt (by norm_num)
  have h_eval :
      fderiv ℝ (fun y : EuclideanSpace ℝ ι =>
          fderiv ℝ (fun z : EuclideanSpace ℝ ι => a ‖z‖) y e) x =
        (ContinuousLinearMap.apply ℝ ℂ e).comp
          (fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ ι => a ‖z‖)) x) := by
    change fderiv ℝ ((ContinuousLinearMap.apply ℝ ℂ e) ∘
        fun y : EuclideanSpace ℝ ι =>
          fderiv ℝ (fun z : EuclideanSpace ℝ ι => a ‖z‖) y) x =
      (ContinuousLinearMap.apply ℝ ℂ e).comp
        (fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ ι => a ‖z‖)) x)
    rw [fderiv_comp (x := x)
      (g := (ContinuousLinearMap.apply ℝ ℂ e))
      (f := fun y : EuclideanSpace ℝ ι =>
        fderiv ℝ (fun z : EuclideanSpace ℝ ι => a ‖z‖) y)]
    · rw [ContinuousLinearMap.fderiv]
    · exact (ContinuousLinearMap.apply ℝ ℂ e).differentiableAt
    · exact hfd_diff
  have hscalar := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hlocal
  calc
    fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ ι => a ‖y‖)) x e e
        = fderiv ℝ (fun y : EuclideanSpace ℝ ι =>
            fderiv ℝ (fun z : EuclideanSpace ℝ ι => a ‖z‖) y e) x e := by
            have happly :=
              congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℂ => L e) h_eval
            simpa using happly.symm
    _ = fderiv ℝ (fun y : EuclideanSpace ℝ ι =>
            deriv a ‖y‖ * (((y i / ‖y‖ : ℝ) : ℂ))) x e := by
            exact congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℂ => L e) hscalar
    _ = deriv (deriv a) ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ)^2) +
        deriv a ‖x‖ *
          (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ)) := by
            simpa [e] using fderiv_radial_chain_product_basisFun hx hda i

/-- Off the origin, the Euclidean Laplacian of a radial profile has the
standard scalar radial form. -/
theorem laplacian_radialProfile_off_origin
    {ι : Type*} [Fintype ι]
    {N : ℕ} (hN : N = Fintype.card ι)
    {a : ℝ → ℂ} {x : EuclideanSpace ℝ ι}
    (hx : x ≠ 0) (ha : ContDiffAt ℝ (2 : ℕ) a ‖x‖) :
    Laplacian.laplacian
        (fun y : EuclideanSpace ℝ ι => a ‖y‖) x =
      radialProfileLaplacian N a ‖x‖ := by
  calc
    Laplacian.laplacian
        (fun y : EuclideanSpace ℝ ι => a ‖y‖) x =
        ∑ i : ι, (iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ ι => a ‖y‖) x)
            ![(EuclideanSpace.basisFun ι ℝ) i,
              (EuclideanSpace.basisFun ι ℝ) i] := by
      exact congrFun
        (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
          (fun y : EuclideanSpace ℝ ι => a ‖y‖)
          (EuclideanSpace.basisFun ι ℝ)) x
    _ = ∑ i : ι,
          (deriv (deriv a) ‖x‖ * (((x i / ‖x‖ : ℝ) : ℂ)^2) +
            deriv a ‖x‖ *
              (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [iteratedFDeriv_radial_comp_basisFun_basisFun hx ha i]
    _ = deriv (deriv a) ‖x‖ *
            (∑ i : ι, (((x i / ‖x‖ : ℝ) : ℂ)^2)) +
          deriv a ‖x‖ *
            (∑ i : ι,
              (((1 / ‖x‖ - (x i)^2 / ‖x‖^3 : ℝ) : ℂ))) := by
          rw [Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = radialProfileLaplacian N a ‖x‖ := by
          rw [sum_complex_coord_sq_div_norm_sq_eq_one hx,
            sum_complex_radial_norm_hessian_coeff hx]
          subst N
          rw [← nat_cast_card_sub_one_of_ne_zero hx]
          simp [radialProfileLaplacian, mul_comm]

/-- The checked quadratic germ removes the apparent singularity of the radial
primitive at the Euclidean origin. -/
theorem contDiffAt_radialPrimitiveProfile_norm_zero
    {ι : Type*} [Fintype ι]
    {N : ℕ} (hNpos : 0 < N) {F : ℝ → ℂ} {R η : ℝ} {c : ℂ}
    (hη : 0 < η) (hηR : η ≤ R)
    (hprim_int_tail :
      IntervalIntegrable (radialPrimitiveDeriv N F) volume η R)
    (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖x‖) 0 := by
  rcases radialPrimitiveProfile_eventually_quadratic_norm_near_zero
      (ι := ι) hNpos hη hηR hprim_int_tail hF_zero with ⟨C, hC⟩
  let K : ℂ := c / (2 * (N : ℂ))
  have hnormsq : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) 0 :=
    contDiffAt_id.norm_sq ℝ
  have hofReal : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ ι => (((‖x‖ ^ 2 : ℝ) : ℂ))) 0 :=
    (Complex.ofRealCLM.contDiff.of_le le_top).contDiffAt.comp 0 hnormsq
  have hquad : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ ι =>
        C + K * (((‖x‖ ^ 2 : ℝ) : ℂ))) 0 := by
    simpa [K] using contDiffAt_const.add (contDiffAt_const.mul hofReal)
  exact hquad.congr_of_eventuallyEq hC

/-- At the origin, the radial primitive has Laplacian equal to the constant
value of the right-hand side near zero. -/
theorem laplacian_radialPrimitiveProfile_norm_zero
    {ι : Type*} [Fintype ι]
    {N : ℕ} (hN : N = Fintype.card ι) (hNpos : 0 < N)
    {F : ℝ → ℂ} {R η : ℝ} {c : ℂ}
    (hη : 0 < η) (hηR : η ≤ R)
    (hprim_int_tail :
      IntervalIntegrable (radialPrimitiveDeriv N F) volume η R)
    (hF_zero : ∀ s ∈ Set.Icc 0 η, F s = c) :
    Laplacian.laplacian
        (fun x : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖x‖)
        0 = c := by
  rcases radialPrimitiveProfile_eventually_quadratic_norm_near_zero
      (ι := ι) hNpos hη hηR hprim_int_tail hF_zero with ⟨C, hC⟩
  let K : ℂ := c / (2 * (N : ℂ))
  let q : EuclideanSpace ℝ ι → ℂ := fun x =>
    C + K * (((‖x‖ ^ 2 : ℝ) : ℂ))
  have hq_lap : Laplacian.laplacian q (0 : EuclideanSpace ℝ ι) =
      K * ((2 * Fintype.card ι : ℝ) : ℂ) := by
    simpa [q, K] using
      laplacian_quadratic_norm_complex (ι := ι) C K (0 : EuclideanSpace ℝ ι)
  have hLap_eventual :
      Laplacian.laplacian
          (fun x : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖x‖) =ᶠ[𝓝 0]
        Laplacian.laplacian q := by
    exact InnerProductSpace.laplacian_congr_nhds hC
  rw [hLap_eventual.eq_of_nhds, hq_lap]
  subst N
  dsimp [K]
  have hcard_ne : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast hNpos.ne'
  field_simp [hcard_ne]
  norm_num
  ring

/-- The radial primitive solves the Euclidean Poisson equation for radial
right-hand sides that are constant near the origin. -/
theorem laplacian_radialPrimitiveProfile
    {ι : Type*} [Fintype ι]
    {N : ℕ} (hN : N = Fintype.card ι) (hNpos : 0 < N)
    {F : ℝ → ℂ} {R η : ℝ} {c : ℂ}
    (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
    (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c) :
    ∀ x : EuclideanSpace ℝ ι,
      Laplacian.laplacian
        (fun y : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖y‖) x =
      F ‖x‖ := by
  intro x
  by_cases hx0 : x = 0
  · subst x
    have hprim_int_tail :
        IntervalIntegrable (radialPrimitiveDeriv N F) volume η R :=
      intervalIntegrable_radialPrimitiveDeriv_of_pos hF_smooth.continuous hη hRpos
    rw [laplacian_radialPrimitiveProfile_norm_zero hN hNpos hη hηR
      hprim_int_tail hF_zero]
    symm
    simpa using hF_zero 0 ⟨le_rfl, hη.le⟩
  · have hx : x ≠ 0 := hx0
    have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have ha : ContDiffAt ℝ (2 : ℕ)
        (fun r : ℝ => radialPrimitiveProfile N F R r) ‖x‖ :=
      (contDiffOn_radialPrimitiveProfile_of_pos (N := N) (R := R)
        hF_smooth hRpos).contDiffAt (Ioi_mem_nhds hrpos)
    calc
      Laplacian.laplacian
          (fun y : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖y‖) x =
          radialProfileLaplacian N
            (fun r : ℝ => radialPrimitiveProfile N F R r) ‖x‖ :=
        laplacian_radialProfile_off_origin hN hx ha
      _ = F ‖x‖ :=
        radialProfileLaplacian_radialPrimitiveProfile_of_pos_of_R_pos
          hNpos hF_smooth.continuous hRpos ‖x‖ hrpos

/-- The radial primitive composed with the Euclidean norm is globally smooth
when the profile is smooth and constant near the origin. -/
theorem contDiff_radialPrimitiveProfile_norm
    {ι : Type*} [Fintype ι]
    {N : ℕ} (hNpos : 0 < N)
    {F : ℝ → ℂ} {R η : ℝ} {c : ℂ}
    (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
    (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx0 : x = 0
  · subst x
    have hprim_int_tail :
        IntervalIntegrable (radialPrimitiveDeriv N F) volume η R :=
      intervalIntegrable_radialPrimitiveDeriv_of_pos hF_smooth.continuous hη hRpos
    exact contDiffAt_radialPrimitiveProfile_norm_zero hNpos hη hηR
      hprim_int_tail hF_zero
  · have hx : x ≠ 0 := hx0
    have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hprofile : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun r : ℝ => radialPrimitiveProfile N F R r) ‖x‖ :=
      (contDiffOn_radialPrimitiveProfile_of_pos_infty (N := N) (R := R)
        hF_smooth hRpos).contDiffAt (Ioi_mem_nhds hrpos)
    have hnorm : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : EuclideanSpace ℝ ι => ‖y‖) x :=
      contDiffAt_norm ℝ hx
    exact hprofile.comp x hnorm

theorem radialMass_eq_radialMass_of_support_ge
    {N : ℕ} {F : ℝ → ℂ} {R r : ℝ}
    (hF_cont : Continuous F)
    (hr : R ≤ r)
    (hF_support : Function.support F ⊆ Set.Icc (-R) R) :
    radialMass N F r = radialMass N F R := by
  let G : ℝ → ℂ := fun s => ((s ^ (N - 1) : ℝ) : ℂ) * F s
  have hG_cont : Continuous G := by
    have hpow : Continuous (fun s : ℝ => ((s ^ (N - 1) : ℝ) : ℂ)) := by
      fun_prop
    exact hpow.mul hF_cont
  have htail_zero : (∫ s in R..r, G s) = 0 := by
    apply intervalIntegral.integral_zero_ae
    exact Eventually.of_forall fun s hs => by
      have hsIoc : s ∈ Set.Ioc R r := by
        simpa [uIoc_of_le hr] using hs
      have hF_zero : F s = 0 := by
        by_contra hne
        have hmem : s ∈ Function.support F := by
          rw [Function.mem_support]
          exact hne
        have hbound := hF_support hmem
        exact (not_le_of_gt hsIoc.1) hbound.2
      simp [G, hF_zero]
  have hsplit :
      (∫ s in (0 : ℝ)..R, G s) + ∫ s in R..r, G s =
        ∫ s in (0 : ℝ)..r, G s := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (hG_cont.intervalIntegrable 0 R)
      (hG_cont.intervalIntegrable R r)
  rw [radialMass, radialMass]
  change (∫ s in (0 : ℝ)..r, G s) = ∫ s in (0 : ℝ)..R, G s
  rw [← hsplit, htail_zero, add_zero]

theorem radialPrimitiveProfile_eq_zero_of_ge
    {N : ℕ} {F : ℝ → ℂ} {R r : ℝ}
    (hF_cont : Continuous F)
    (hR : 0 ≤ R) (hr : R ≤ r)
    (hF_support : Function.support F ⊆ Set.Icc (-R) R)
    (hMass_R : radialMass N F R = 0) :
    radialPrimitiveProfile N F R r = 0 := by
  have hderiv_zero : (∫ t in r..R, radialPrimitiveDeriv N F t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    exact Eventually.of_forall fun t ht => by
      have htIoc : t ∈ Set.Ioc R r := by
        simpa [uIoc_comm, uIoc_of_le hr] using ht
      have ht_pos : 0 < t := lt_of_le_of_lt hR htIoc.1
      rw [radialPrimitiveDeriv_eq_inv_mul ht_pos.ne']
      rw [radialMass_eq_radialMass_of_support_ge hF_cont htIoc.1.le hF_support,
        hMass_R, mul_zero]
  simp [radialPrimitiveProfile, hderiv_zero]

theorem radialPrimitiveProfile_eventually_zero_outside
    {N : ℕ} {F : ℝ → ℂ} {R : ℝ}
    (hF_cont : Continuous F)
    (hR : 0 ≤ R)
    (hF_support : Function.support F ⊆ Set.Icc (-R) R)
    (hMass_R : radialMass N F R = 0) :
    ∀ᶠ r : ℝ in Filter.atTop, radialPrimitiveProfile N F R r = 0 := by
  exact eventually_atTop.2
    ⟨R, fun r hr =>
      radialPrimitiveProfile_eq_zero_of_ge hF_cont hR hr hF_support hMass_R⟩

/-- If the source profile is supported in `[-R, R]` and the radial mass
vanishes at `R`, then the norm-composed radial primitive has topological support
inside the closed ball of radius `R`. -/
theorem tsupport_radialPrimitiveProfile_norm_subset
    {ι : Type*} [Fintype ι]
    {N : ℕ} {F : ℝ → ℂ} {R : ℝ}
    (hF_cont : Continuous F) (hR : 0 ≤ R)
    (hF_support : Function.support F ⊆ Set.Icc (-R) R)
    (hMass_R : radialMass N F R = 0) :
    tsupport
        (fun x : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖x‖) ⊆
      Metric.closedBall 0 R := by
  let E := EuclideanSpace ℝ ι
  have hsupp : Function.support
      (fun x : E => radialPrimitiveProfile N F R ‖x‖) ⊆
      Metric.closedBall 0 R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hnot
    have hR_le : R ≤ ‖x‖ := le_of_lt (not_le.mp hnot)
    exact hx
      (radialPrimitiveProfile_eq_zero_of_ge hF_cont hR hR_le hF_support hMass_R)
  rw [tsupport]
  exact closure_minimal hsupp isClosed_closedBall

/-- If the source profile is supported in `[-R, R]` and the radial mass
vanishes at `R`, then the norm-composed radial primitive is compactly
supported in the closed ball of radius `R`. -/
theorem hasCompactSupport_radialPrimitiveProfile_norm
    {ι : Type*} [Fintype ι]
    {N : ℕ} {F : ℝ → ℂ} {R : ℝ}
    (hF_cont : Continuous F) (hR : 0 ≤ R)
    (hF_support : Function.support F ⊆ Set.Icc (-R) R)
    (hMass_R : radialMass N F R = 0) :
    HasCompactSupport
      (fun x : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖x‖) := by
  let E := EuclideanSpace ℝ ι
  have htsupport : tsupport
      (fun x : E => radialPrimitiveProfile N F R ‖x‖) ⊆
      Metric.closedBall 0 R :=
    tsupport_radialPrimitiveProfile_norm_subset (ι := ι) (N := N)
      hF_cont hR hF_support hMass_R
  exact IsCompact.of_isClosed_subset
    (isCompact_closedBall (0 : E) R)
    (isClosed_tsupport _)
    htsupport

/-- Package the compactly supported smooth norm-composed radial primitive as a
Schwartz function. -/
theorem exists_schwartz_radialPrimitiveProfile_norm
    {ι : Type*} [Fintype ι]
    {N : ℕ} (hNpos : 0 < N)
    {F : ℝ → ℂ} {R η : ℝ} {c : ℂ}
    (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
    (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c)
    (hF_support : Function.support F ⊆ Set.Icc (-R) R)
    (hMass_R : radialMass N F R = 0) :
    ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      HasCompactSupport (A : EuclideanSpace ℝ ι → ℂ) ∧
      ∀ x : EuclideanSpace ℝ ι,
        A x = radialPrimitiveProfile N F R ‖x‖ := by
  let f : EuclideanSpace ℝ ι → ℂ := fun x =>
    radialPrimitiveProfile N F R ‖x‖
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_radialPrimitiveProfile_norm (ι := ι) (N := N) hNpos
      hRpos hη hηR hF_smooth hF_zero
  have hcompact : HasCompactSupport f :=
    hasCompactSupport_radialPrimitiveProfile_norm (ι := ι) (N := N)
      hF_smooth.continuous hRpos.le hF_support hMass_R
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_⟩
  · simpa [HasCompactSupport.toSchwartzMap] using hcompact
  · intro x
    exact HasCompactSupport.toSchwartzMap_toFun hcompact hsmooth x

/-- Package the compactly supported smooth norm-composed radial primitive as a
Schwartz function, retaining its explicit closed-ball support bound. -/
theorem exists_schwartz_radialPrimitiveProfile_norm_with_support
    {ι : Type*} [Fintype ι]
    {N : ℕ} (hNpos : 0 < N)
    {F : ℝ → ℂ} {R η : ℝ} {c : ℂ}
    (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
    (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c)
    (hF_support : Function.support F ⊆ Set.Icc (-R) R)
    (hMass_R : radialMass N F R = 0) :
    ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      HasCompactSupport (A : EuclideanSpace ℝ ι → ℂ) ∧
      tsupport (A : EuclideanSpace ℝ ι → ℂ) ⊆ Metric.closedBall 0 R ∧
      ∀ x : EuclideanSpace ℝ ι,
        A x = radialPrimitiveProfile N F R ‖x‖ := by
  let f : EuclideanSpace ℝ ι → ℂ := fun x =>
    radialPrimitiveProfile N F R ‖x‖
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_radialPrimitiveProfile_norm (ι := ι) (N := N) hNpos
      hRpos hη hηR hF_smooth hF_zero
  have hcompact : HasCompactSupport f :=
    hasCompactSupport_radialPrimitiveProfile_norm (ι := ι) (N := N)
      hF_smooth.continuous hRpos.le hF_support hMass_R
  have htsupport : tsupport f ⊆ Metric.closedBall 0 R :=
    tsupport_radialPrimitiveProfile_norm_subset (ι := ι) (N := N)
      hF_smooth.continuous hRpos.le hF_support hMass_R
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_, ?_⟩
  · simpa [HasCompactSupport.toSchwartzMap] using hcompact
  · simpa [HasCompactSupport.toSchwartzMap] using htsupport
  · intro x
    exact HasCompactSupport.toSchwartzMap_toFun hcompact hsmooth x

/-- A compact radial primitive whose scalar source is represented by a
Schwartz function has that Schwartz function as its Schwartz Laplacian. -/
theorem exists_compact_laplacian_eq_radial_schwartz
    {ι : Type*} [Fintype ι]
    {N : ℕ} (hN : N = Fintype.card ι) (hNpos : 0 < N)
    {F : ℝ → ℂ} {R η : ℝ} {c : ℂ}
    (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
    (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c)
    (hF_support : Function.support F ⊆ Set.Icc (-R) R)
    (hMass_R : radialMass N F R = 0)
    (B : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hB : ∀ x : EuclideanSpace ℝ ι, B x = F ‖x‖) :
    ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      HasCompactSupport (A : EuclideanSpace ℝ ι → ℂ) ∧
      LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
          (SchwartzMap (EuclideanSpace ℝ ι) ℂ) A = B := by
  rcases exists_schwartz_radialPrimitiveProfile_norm (ι := ι) (N := N)
      hNpos hRpos hη hηR hF_smooth hF_zero hF_support hMass_R with
    ⟨A, hAcompact, hAeq⟩
  refine ⟨A, hAcompact, ?_⟩
  ext x
  rw [SchwartzMap.laplacianCLM_eq]
  rw [SchwartzMap.laplacian_apply]
  have hevent : (A : EuclideanSpace ℝ ι → ℂ) =ᶠ[𝓝 x]
      (fun y : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖y‖) :=
    Eventually.of_forall hAeq
  have hLap_eventual :
      Laplacian.laplacian (A : EuclideanSpace ℝ ι → ℂ) =ᶠ[𝓝 x]
        Laplacian.laplacian
          (fun y : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖y‖) :=
    InnerProductSpace.laplacian_congr_nhds hevent
  rw [hLap_eventual.eq_of_nhds]
  rw [laplacian_radialPrimitiveProfile hN hNpos hRpos hη hηR
    hF_smooth hF_zero]
  exact (hB x).symm

/-- A compact radial primitive with an explicit support radius whose scalar
source is represented by a Schwartz function has that Schwartz function as its
Schwartz Laplacian. -/
theorem exists_compact_laplacian_eq_radial_schwartz_with_support
    {ι : Type*} [Fintype ι]
    {N : ℕ} (hN : N = Fintype.card ι) (hNpos : 0 < N)
    {F : ℝ → ℂ} {R η : ℝ} {c : ℂ}
    (hRpos : 0 < R) (hη : 0 < η) (hηR : η ≤ R)
    (hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c)
    (hF_support : Function.support F ⊆ Set.Icc (-R) R)
    (hMass_R : radialMass N F R = 0)
    (B : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hB : ∀ x : EuclideanSpace ℝ ι, B x = F ‖x‖) :
    ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      HasCompactSupport (A : EuclideanSpace ℝ ι → ℂ) ∧
      tsupport (A : EuclideanSpace ℝ ι → ℂ) ⊆ Metric.closedBall 0 R ∧
      LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
          (SchwartzMap (EuclideanSpace ℝ ι) ℂ) A = B := by
  rcases exists_schwartz_radialPrimitiveProfile_norm_with_support (ι := ι) (N := N)
      hNpos hRpos hη hηR hF_smooth hF_zero hF_support hMass_R with
    ⟨A, hAcompact, hAsupp, hAeq⟩
  refine ⟨A, hAcompact, hAsupp, ?_⟩
  ext x
  rw [SchwartzMap.laplacianCLM_eq]
  rw [SchwartzMap.laplacian_apply]
  have hevent : (A : EuclideanSpace ℝ ι → ℂ) =ᶠ[𝓝 x]
      (fun y : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖y‖) :=
    Eventually.of_forall hAeq
  have hLap_eventual :
      Laplacian.laplacian (A : EuclideanSpace ℝ ι → ℂ) =ᶠ[𝓝 x]
        Laplacian.laplacian
          (fun y : EuclideanSpace ℝ ι => radialPrimitiveProfile N F R ‖y‖) :=
    InnerProductSpace.laplacian_congr_nhds hevent
  rw [hLap_eventual.eq_of_nhds]
  rw [laplacian_radialPrimitiveProfile hN hNpos hRpos hη hηR
    hF_smooth hF_zero]
  exact (hB x).symm

/-- The difference of two normalized Euclidean Weyl bumps is the Schwartz
Laplacian of a compactly supported Schwartz function, in positive dimension. -/
theorem exists_compact_laplacian_eq_euclideanWeylBump_sub
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      HasCompactSupport (A : EuclideanSpace ℝ ι → ℂ) ∧
      LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
          (SchwartzMap (EuclideanSpace ℝ ι) ℂ) A =
        euclideanWeylBump ε hε - euclideanWeylBump δ hδ := by
  let N := Fintype.card ι
  let R : ℝ := max ε δ
  let η : ℝ := min ε δ / 2
  let c : ℂ :=
    (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) -
      (((euclideanWeylRawIntegralReal (ι := ι) δ : ℝ) : ℂ)⁻¹)
  let F : ℝ → ℂ := euclideanWeylBumpSubProfile (ι := ι) ε δ
  have hN : N = Fintype.card ι := rfl
  have hNpos : 0 < N := Fintype.card_pos_iff.mpr inferInstance
  have hRpos : 0 < R := lt_of_lt_of_le hε (le_max_left ε δ)
  have hη : 0 < η := by
    unfold η
    positivity
  have hηR : η ≤ R := by
    unfold η R
    have hmin_le_ε : min ε δ ≤ ε := min_le_left ε δ
    have hε_le_max : ε ≤ max ε δ := le_max_left ε δ
    nlinarith
  rcases euclideanWeylBumpSubProfile_spec (ι := ι) hε hδ with
    ⟨hF_smooth, hF_support, _hplateau, hnorm, hweighted_zero⟩
  have hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c := by
    intro r hr
    have hr_abs : |r| ≤ min ε δ / 2 := by
      rw [abs_of_nonneg hr.1]
      simpa [η] using hr.2
    simpa [F, c] using
      euclideanWeylBumpSubProfile_eq_plateau_of_abs_le_half_min
        (ι := ι) hε hδ hr_abs
  have hweight_int : IntegrableOn
      (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ) * F r)
      (Set.Ioi 0) volume := by
    let fε : ℝ → ℂ := fun r =>
      ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylNormalizedProfile (ι := ι) ε r
    let fδ : ℝ → ℂ := fun r =>
      ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylNormalizedProfile (ι := ι) δ r
    have hrew : (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ) * F r) =
        fun r : ℝ => fε r - fδ r := by
      funext r
      simp [F, fε, fδ, euclideanWeylBumpSubProfile]
      ring
    rw [hrew]
    exact ((euclideanWeylWeightedNormalizedProfile_integrable (ι := ι) N hε).sub
      (euclideanWeylWeightedNormalizedProfile_integrable (ι := ι) N hδ)).integrableOn
  have hMass_R : radialMass N F R = 0 := by
    rw [radialMass_eq_weightedMass_of_support hRpos.le hweight_int hF_support]
    exact hweighted_zero
  exact exists_compact_laplacian_eq_radial_schwartz (ι := ι) (N := N)
    hN hNpos hRpos hη hηR hF_smooth hF_zero hF_support hMass_R
    (euclideanWeylBump ε hε - euclideanWeylBump δ hδ)
    (fun x => (hnorm x).symm)

/-- The difference of two normalized Euclidean Weyl bumps is the Schwartz
Laplacian of a compactly supported Schwartz function whose support lies in the
larger bump ball. -/
theorem exists_compact_laplacian_eq_euclideanWeylBump_sub_with_support
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      HasCompactSupport (A : EuclideanSpace ℝ ι → ℂ) ∧
      tsupport (A : EuclideanSpace ℝ ι → ℂ) ⊆ Metric.closedBall 0 (max ε δ) ∧
      LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
          (SchwartzMap (EuclideanSpace ℝ ι) ℂ) A =
        euclideanWeylBump ε hε - euclideanWeylBump δ hδ := by
  let N := Fintype.card ι
  let R : ℝ := max ε δ
  let η : ℝ := min ε δ / 2
  let c : ℂ :=
    (((euclideanWeylRawIntegralReal (ι := ι) ε : ℝ) : ℂ)⁻¹) -
      (((euclideanWeylRawIntegralReal (ι := ι) δ : ℝ) : ℂ)⁻¹)
  let F : ℝ → ℂ := euclideanWeylBumpSubProfile (ι := ι) ε δ
  have hN : N = Fintype.card ι := rfl
  have hNpos : 0 < N := Fintype.card_pos_iff.mpr inferInstance
  have hRpos : 0 < R := lt_of_lt_of_le hε (le_max_left ε δ)
  have hη : 0 < η := by
    unfold η
    positivity
  have hηR : η ≤ R := by
    unfold η R
    have hmin_le_ε : min ε δ ≤ ε := min_le_left ε δ
    have hε_le_max : ε ≤ max ε δ := le_max_left ε δ
    nlinarith
  rcases euclideanWeylBumpSubProfile_spec (ι := ι) hε hδ with
    ⟨hF_smooth, hF_support, _hplateau, hnorm, hweighted_zero⟩
  have hF_zero : ∀ r ∈ Set.Icc 0 η, F r = c := by
    intro r hr
    have hr_abs : |r| ≤ min ε δ / 2 := by
      rw [abs_of_nonneg hr.1]
      simpa [η] using hr.2
    simpa [F, c] using
      euclideanWeylBumpSubProfile_eq_plateau_of_abs_le_half_min
        (ι := ι) hε hδ hr_abs
  have hweight_int : IntegrableOn
      (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ) * F r)
      (Set.Ioi 0) volume := by
    let fε : ℝ → ℂ := fun r =>
      ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylNormalizedProfile (ι := ι) ε r
    let fδ : ℝ → ℂ := fun r =>
      ((r ^ (N - 1) : ℝ) : ℂ) * euclideanWeylNormalizedProfile (ι := ι) δ r
    have hrew : (fun r : ℝ => ((r ^ (N - 1) : ℝ) : ℂ) * F r) =
        fun r : ℝ => fε r - fδ r := by
      funext r
      simp [F, fε, fδ, euclideanWeylBumpSubProfile]
      ring
    rw [hrew]
    exact ((euclideanWeylWeightedNormalizedProfile_integrable (ι := ι) N hε).sub
      (euclideanWeylWeightedNormalizedProfile_integrable (ι := ι) N hδ)).integrableOn
  have hMass_R : radialMass N F R = 0 := by
    rw [radialMass_eq_weightedMass_of_support hRpos.le hweight_int hF_support]
    exact hweighted_zero
  exact exists_compact_laplacian_eq_radial_schwartz_with_support (ι := ι) (N := N)
    hN hNpos hRpos hη hηR hF_smooth hF_zero hF_support hMass_R
    (euclideanWeylBump ε hε - euclideanWeylBump δ hδ)
    (fun x => (hnorm x).symm)

/-- Directional differentiation commutes with Euclidean Schwartz translation. -/
theorem lineDerivOp_euclideanTranslateSchwartzCLM
    {ι : Type*} [Fintype ι]
    (a v : EuclideanSpace ℝ ι)
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    (∂_{v} (euclideanTranslateSchwartzCLM a φ) :
        SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
      euclideanTranslateSchwartzCLM a
        (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) := by
  ext y
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  let τ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun y => y + a
  have hφ : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ ι => φ z) (τ y) :=
    φ.differentiableAt
  have hτ : DifferentiableAt ℝ τ y := by
    unfold τ
    fun_prop
  have hcomp := fderiv_comp (x := y)
    (g := fun z : EuclideanSpace ℝ ι => φ z) (f := τ) hφ hτ
  have hτ_fderiv :
      fderiv ℝ τ y = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι) := by
    unfold τ
    ext w i
    simp
  change (fderiv ℝ ((fun z : EuclideanSpace ℝ ι => φ z) ∘ τ) y) v = _
  rw [hcomp, hτ_fderiv]
  simp [τ]

/-- Directional differentiation commutes with reflected Euclidean translation. -/
theorem lineDerivOp_euclideanReflectedTranslate
    {ι : Type*} [Fintype ι]
    (x v : EuclideanSpace ℝ ι)
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    (∂_{v} (euclideanReflectedTranslate x φ) :
        SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
      euclideanReflectedTranslate x
        (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) := by
  simp [euclideanReflectedTranslate, lineDerivOp_euclideanTranslateSchwartzCLM]

/-- The Euclidean Schwartz Laplacian commutes with reflected translation. -/
theorem laplacianCLM_euclideanReflectedTranslate
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι)
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
        (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
        (euclideanReflectedTranslate x φ) =
      euclideanReflectedTranslate x
        (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
          (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) := by
  calc
    LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
        (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
        (euclideanReflectedTranslate x φ)
        = ∑ i : ι, ∂_{(EuclideanSpace.basisFun ι ℝ) i}
            (∂_{(EuclideanSpace.basisFun ι ℝ) i} (euclideanReflectedTranslate x φ) :
              SchwartzMap (EuclideanSpace ℝ ι) ℂ) :=
          LineDeriv.laplacianCLM_eq_sum (EuclideanSpace.basisFun ι ℝ)
            (euclideanReflectedTranslate x φ)
    _ = euclideanReflectedTranslate x
          (∑ i : ι, ∂_{(EuclideanSpace.basisFun ι ℝ) i}
            (∂_{(EuclideanSpace.basisFun ι ℝ) i} φ :
              SchwartzMap (EuclideanSpace ℝ ι) ℂ)) := by
          simp [euclideanReflectedTranslate, map_sum,
            lineDerivOp_euclideanTranslateSchwartzCLM]
    _ = euclideanReflectedTranslate x
        (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
          (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) := by
          exact congrArg (euclideanReflectedTranslate x)
            (LineDeriv.laplacianCLM_eq_sum (EuclideanSpace.basisFun ι ℝ) φ).symm

/-- A distribution whose Euclidean Laplacian vanishes on tests supported in
`V` gives the same value to all sufficiently local normalized Weyl bumps
centered at the same point, in positive dimension. -/
theorem regularizedDistribution_bump_scale_eq
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    {V : Set (EuclideanSpace ℝ ι)}
    (hΔ :
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        SupportsInOpen (φ : EuclideanSpace ℝ ι → ℂ) V →
          T
            (LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ ι)
              (SchwartzMap (EuclideanSpace ℝ ι) ℂ) φ) = 0)
    {x : EuclideanSpace ℝ ι} {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hxε : Metric.closedBall x ε ⊆ V)
    (hxδ : Metric.closedBall x δ ⊆ V) :
    T (euclideanReflectedTranslate x (euclideanWeylBump ε hε)) =
    T (euclideanReflectedTranslate x (euclideanWeylBump δ hδ)) := by
  rcases exists_compact_laplacian_eq_euclideanWeylBump_sub_with_support
      (ι := ι) hε hδ with
    ⟨A, _hAcompact, hAsupp, hAlap⟩
  have hxR : Metric.closedBall x (max ε δ) ⊆ V := by
    intro y hy
    by_cases hδε : δ ≤ ε
    · apply hxε
      simpa [max_eq_left hδε] using hy
    · have hεδ : ε ≤ δ := le_of_lt (lt_of_not_ge hδε)
      apply hxδ
      simpa [max_eq_right hεδ] using hy
  have hAsuppV :
      SupportsInOpen
        (euclideanReflectedTranslate x A : EuclideanSpace ℝ ι → ℂ) V :=
    supportsInOpen_euclideanReflectedTranslate_of_kernelSupport hxR hAsupp
  have hzero := hΔ (euclideanReflectedTranslate x A) hAsuppV
  rw [laplacianCLM_euclideanReflectedTranslate, hAlap] at hzero
  have htranslate_sub :
      euclideanReflectedTranslate x
          (euclideanWeylBump ε hε - euclideanWeylBump δ hδ) =
        euclideanReflectedTranslate x (euclideanWeylBump ε hε) -
          euclideanReflectedTranslate x (euclideanWeylBump δ hδ) := by
    simp [euclideanReflectedTranslate]
  rw [htranslate_sub] at hzero
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

end SCV
