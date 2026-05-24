/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib

/-!
# OS II Lemma 5.1 Coordinate Estimate

After the directional semigroup continuations are glued by Malgrange-Zerner,
OS II V.1 uses the concrete four-vector basis `(5.11)` and coefficient formula
`(5.12)` to extract a polydisc around the real point.

This file formalizes that quantitative coordinate bridge for the physical four
Euclidean coordinates.  It does not construct the MZ representative; it proves
that once a representative is available on the coefficient sector, the explicit
OS-II coefficient map pulls it back to a holomorphic local polydisc.
-/

noncomputable section

open Complex Topology
open scoped Classical NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace OSReconstruction

/-- The four OS-II basis directions from `(5.11)`, with `T = cot γ`.

The rows are
`(2T, 1, 1, 1)`, `(2T, 1, -1, -1)`,
`(2T, -1, 1, -1)`, `(2T, -1, -1, 1)`. -/
def osiiLemma51E4 (T : ℝ) (μ ν : Fin 4) : ℝ :=
  if ν = 0 then
    2 * T
  else if ν = 1 then
    if μ = 0 ∨ μ = 1 then 1 else -1
  else if ν = 2 then
    if μ = 0 ∨ μ = 2 then 1 else -1
  else
    if μ = 0 ∨ μ = 3 then 1 else -1

/-- The coefficients `w_i^μ` from OS II `(5.12)` for one spacetime difference.

`ξ` is the real base point, `ζ` is the complex perturbation, and `T = cot γ`.
The fixed real vector in the paper is `ξ̂ = (ξ⁰/2, ξ¹, ξ², ξ³)`, so the
constant part of the coefficient is `ξ⁰/(16T)`. -/
def osiiLemma51Coeff4 (T : ℝ) (ξ : Fin 4 → ℝ) (ζ : Fin 4 → ℂ)
    (μ : Fin 4) : ℂ :=
  ((ξ 0 / (16 * T) : ℝ) : ℂ) +
    ζ 0 / ((8 * T : ℝ) : ℂ) +
    (1 / 4 : ℂ) *
      (((osiiLemma51E4 1 μ 1 : ℝ) : ℂ) * ζ 1 +
        ((osiiLemma51E4 1 μ 2 : ℝ) : ℂ) * ζ 2 +
        ((osiiLemma51E4 1 μ 3 : ℝ) : ℂ) * ζ 3)

/-- The coefficient map `ζ ↦ (w^μ)_μ` in OS II `(5.12)`. -/
def osiiLemma51CoeffMap4
    (T : ℝ) (ξ : Fin 4 → ℝ) (ζ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun μ => osiiLemma51Coeff4 T ξ ζ μ

/-- The product of the four right half-planes used for the coefficients. -/
def osiiLemma51RightHalfPlane4 : Set (Fin 4 → ℂ) :=
  {w | ∀ μ : Fin 4, 0 < (w μ).re}

/-- A narrow coefficient sector, expressed without committing to a particular
argument-function normalization.

OS II `(5.8)` uses the stronger condition `Σ |arg w_i^μ| < π/2`, not merely
positive real part.  The ratio condition below is the local quantitative
version used before translating it into the paper's argument-sum bound. -/
def osiiLemma51NarrowSector4 (η : ℝ) : Set (Fin 4 → ℂ) :=
  {w | ∀ μ : Fin 4, 0 < (w μ).re ∧ |(w μ).im| < η * (w μ).re}

/-- The explicit OS-II `(5.8)` coefficient-domain condition for four
directions: the total absolute argument is smaller than `π / 2`. -/
def osiiLemma51ArgSumDomain4 : Set (Fin 4 → ℂ) :=
  {w | ∑ μ : Fin 4, |Complex.arg (w μ)| < Real.pi / 2}

/-- In the right half-plane, a bound on the slope `|Im z| / Re z` bounds the
absolute argument by the corresponding arctangent. -/
theorem osiiLemma51_abs_arg_eq_arctan_abs_im_div_re
    {z : ℂ} (hzre : 0 < z.re) :
    |Complex.arg z| = Real.arctan |z.im / z.re| := by
  have harg_abs_lt : |Complex.arg z| < Real.pi / 2 := by
    exact (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hzre)
  have harg_mem : Complex.arg z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    exact abs_lt.mp harg_abs_lt
  have htan : Real.tan (Complex.arg z) = z.im / z.re := Complex.tan_arg z
  have harg : Real.arctan (z.im / z.re) = Complex.arg z :=
    Real.arctan_eq_of_tan_eq htan harg_mem
  rw [← harg]
  by_cases hq : 0 ≤ z.im / z.re
  · rw [abs_of_nonneg hq, abs_of_nonneg (Real.arctan_nonneg.mpr hq)]
  · have hq_neg : z.im / z.re < 0 := lt_of_not_ge hq
    rw [abs_of_neg hq_neg, abs_of_neg (Real.arctan_lt_zero.mpr hq_neg),
      Real.arctan_neg]

/-- The ratio-sector estimate used in OS II `(5.13)` implies the paper's
argument-sum condition `(5.8)` once the selected ratio aperture has total
arctangent width below `π / 2`. -/
theorem osiiLemma51_narrowSector_subset_argSumDomain4
    {η : ℝ} (hηsum : (4 : ℝ) * Real.arctan η < Real.pi / 2) :
    osiiLemma51NarrowSector4 η ⊆ osiiLemma51ArgSumDomain4 := by
  intro w hw
  have harg_bound :
      ∀ μ : Fin 4, |Complex.arg (w μ)| < Real.arctan η := by
    intro μ
    rcases hw μ with ⟨hre, him⟩
    have hratio : |(w μ).im / (w μ).re| < η := by
      rw [abs_div, abs_of_pos hre]
      exact (div_lt_iff₀ hre).2 him
    rw [osiiLemma51_abs_arg_eq_arctan_abs_im_div_re hre]
    exact Real.arctan_strictMono hratio
  have hsum_lt :
      (∑ μ : Fin 4, |Complex.arg (w μ)|) <
        ∑ μ : Fin 4, Real.arctan η := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun μ _ => harg_bound μ)
  have hconst : (∑ μ : Fin 4, Real.arctan η) = (4 : ℝ) * Real.arctan η := by
    simp
  have hsum_lt_const :
      (∑ μ : Fin 4, |Complex.arg (w μ)|) < (4 : ℝ) * Real.arctan η := by
    simpa [hconst] using hsum_lt
  exact hsum_lt_const.trans hηsum

/-- The fixed real vector `ξ̂ = (ξ⁰/2, ξ¹, ξ², ξ³)` used in OS II `(5.12)`. -/
def osiiLemma51XiHat4 (ξ : Fin 4 → ℝ) (ν : Fin 4) : ℂ :=
  if ν = 0 then ((ξ 0 / 2 : ℝ) : ℂ) else (ξ ν : ℂ)

/-- OS II `(5.11)`--`(5.12)` as an exact coordinate identity.

For each coordinate `ν`,
`ξ̂ν + Σ_μ w^μ e^μ_ν = ξν + ζν`. -/
theorem osiiLemma51_coeff4_linear_identity
    (T : ℝ) (hT : T ≠ 0) (ξ : Fin 4 → ℝ) (ζ : Fin 4 → ℂ) (ν : Fin 4) :
    osiiLemma51XiHat4 ξ ν +
        ∑ μ : Fin 4,
          osiiLemma51Coeff4 T ξ ζ μ *
            ((osiiLemma51E4 T μ ν : ℝ) : ℂ) =
      (ξ ν : ℂ) + ζ ν := by
  have hTc : ((T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT
  fin_cases ν <;>
    simp [osiiLemma51XiHat4, osiiLemma51Coeff4, osiiLemma51E4,
      Fin.sum_univ_succ] <;>
    field_simp [hT, hTc] <;>
    ring

/-- A local small-perturbation estimate for the OS II coefficients `w^μ`.

If the perturbation terms in `(5.12)` are smaller than the positive constant
part `ξ⁰/(16T)`, every coefficient has positive real part. -/
theorem osiiLemma51_coeff4_re_pos_of_small_perturbation
    (T : ℝ) (hT : 0 < T) (ξ : Fin 4 → ℝ) (ζ : Fin 4 → ℂ)
    (hsmall :
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).re| +
          (1 / 4 : ℝ) *
            (|((ζ 1).re)| + |((ζ 2).re)| + |((ζ 3).re)|) <
        ξ 0 / (16 * T))
    (μ : Fin 4) :
    0 < (osiiLemma51Coeff4 T ξ ζ μ).re := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hTc : ((T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hTne
  have hbase_re :
      ((ξ 0 : ℂ) / (16 * (T : ℂ))).re = ξ 0 / (16 * T) := by
    simpa [mul_comm] using (Complex.div_ofReal_re (ξ 0 : ℂ) (16 * T))
  have htime_re :
      (ζ 0 / (8 * (T : ℂ))).re =
        (ζ 0 / ((8 * T : ℝ) : ℂ)).re := by
    simp [mul_comm]
  have hb0 :
      -|(ζ 0 / ((8 * T : ℝ) : ℂ)).re| ≤
        (ζ 0 / ((8 * T : ℝ) : ℂ)).re := neg_abs_le _
  have hbr1 : -|((ζ 1).re)| ≤ (ζ 1).re := neg_abs_le _
  have hbr2 : -|((ζ 2).re)| ≤ (ζ 2).re := neg_abs_le _
  have hbr3 : -|((ζ 3).re)| ≤ (ζ 3).re := neg_abs_le _
  have hbr1_neg : -|((ζ 1).re)| ≤ -(ζ 1).re := by
    exact neg_le_neg (le_abs_self ((ζ 1).re))
  have hbr2_neg : -|((ζ 2).re)| ≤ -(ζ 2).re := by
    exact neg_le_neg (le_abs_self ((ζ 2).re))
  have hbr3_neg : -|((ζ 3).re)| ≤ -(ζ 3).re := by
    exact neg_le_neg (le_abs_self ((ζ 3).re))
  have habs1 : 0 ≤ |((ζ 1).re)| := abs_nonneg _
  have habs2 : 0 ≤ |((ζ 2).re)| := abs_nonneg _
  have habs3 : 0 ≤ |((ζ 3).re)| := abs_nonneg _
  fin_cases μ <;>
    simp [osiiLemma51Coeff4, osiiLemma51E4, hbase_re, htime_re] <;>
    nlinarith

set_option maxHeartbeats 800000 in
/-- A narrow-sector version of the OS II coefficient estimate.

This is the ratio form behind `(5.13)`: if both the real and imaginary
perturbation parts of `(5.12)` are small compared with the positive constant
part, then every coefficient lies in an arbitrarily narrow right sector. -/
theorem osiiLemma51_coeff4_mem_narrowSector_of_small_perturbation
    (T : ℝ) (hT : 0 < T) (ξ : Fin 4 → ℝ) (hξ0 : 0 < ξ 0)
    (ζ : Fin 4 → ℂ) (η : ℝ) (hη : 0 < η)
    (hrealSmall :
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).re| +
          (1 / 4 : ℝ) *
            (|((ζ 1).re)| + |((ζ 2).re)| + |((ζ 3).re)|) <
        (ξ 0 / (16 * T)) / 2)
    (himagSmall :
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).im| +
          (1 / 4 : ℝ) *
            (|((ζ 1).im)| + |((ζ 2).im)| + |((ζ 3).im)|) <
        η * ((ξ 0 / (16 * T)) / 2)) :
    osiiLemma51CoeffMap4 T ξ ζ ∈ osiiLemma51NarrowSector4 η := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hbase : 0 < ξ 0 / (16 * T) := by
    positivity
  have hbase_re :
      ((ξ 0 : ℂ) / (16 * (T : ℂ))).re = ξ 0 / (16 * T) := by
    simpa [mul_comm] using (Complex.div_ofReal_re (ξ 0 : ℂ) (16 * T))
  have hbase_im :
      ((ξ 0 : ℂ) / (16 * (T : ℂ))).im = 0 := by
    simpa [mul_comm] using (Complex.div_ofReal_im (ξ 0 : ℂ) (16 * T))
  have htime_re :
      (ζ 0 / (8 * (T : ℂ))).re =
        (ζ 0 / ((8 * T : ℝ) : ℂ)).re := by
    simp [mul_comm]
  have htime_im :
      (ζ 0 / (8 * (T : ℂ))).im =
        (ζ 0 / ((8 * T : ℝ) : ℂ)).im := by
    simp [mul_comm]
  have hre0_lo :
      -|(ζ 0 / ((8 * T : ℝ) : ℂ)).re| ≤
        (ζ 0 / ((8 * T : ℝ) : ℂ)).re := neg_abs_le _
  have hre1_lo : -|((ζ 1).re)| ≤ (ζ 1).re := neg_abs_le _
  have hre2_lo : -|((ζ 2).re)| ≤ (ζ 2).re := neg_abs_le _
  have hre3_lo : -|((ζ 3).re)| ≤ (ζ 3).re := neg_abs_le _
  have hre1_neg_lo : -|((ζ 1).re)| ≤ -(ζ 1).re :=
    neg_le_neg (le_abs_self ((ζ 1).re))
  have hre2_neg_lo : -|((ζ 2).re)| ≤ -(ζ 2).re :=
    neg_le_neg (le_abs_self ((ζ 2).re))
  have hre3_neg_lo : -|((ζ 3).re)| ≤ -(ζ 3).re :=
    neg_le_neg (le_abs_self ((ζ 3).re))
  have him0_lo :
      -|(ζ 0 / ((8 * T : ℝ) : ℂ)).im| ≤
        (ζ 0 / ((8 * T : ℝ) : ℂ)).im := neg_abs_le _
  have him0_hi :
      (ζ 0 / ((8 * T : ℝ) : ℂ)).im ≤
        |(ζ 0 / ((8 * T : ℝ) : ℂ)).im| := le_abs_self _
  have him1_lo : -|((ζ 1).im)| ≤ (ζ 1).im := neg_abs_le _
  have him2_lo : -|((ζ 2).im)| ≤ (ζ 2).im := neg_abs_le _
  have him3_lo : -|((ζ 3).im)| ≤ (ζ 3).im := neg_abs_le _
  have him1_hi : (ζ 1).im ≤ |((ζ 1).im)| := le_abs_self _
  have him2_hi : (ζ 2).im ≤ |((ζ 2).im)| := le_abs_self _
  have him3_hi : (ζ 3).im ≤ |((ζ 3).im)| := le_abs_self _
  have him1_neg_lo : -|((ζ 1).im)| ≤ -(ζ 1).im :=
    neg_le_neg (le_abs_self ((ζ 1).im))
  have him2_neg_lo : -|((ζ 2).im)| ≤ -(ζ 2).im :=
    neg_le_neg (le_abs_self ((ζ 2).im))
  have him3_neg_lo : -|((ζ 3).im)| ≤ -(ζ 3).im :=
    neg_le_neg (le_abs_self ((ζ 3).im))
  have him1_neg_hi : -(ζ 1).im ≤ |((ζ 1).im)| :=
    by simpa using neg_le_neg (neg_abs_le ((ζ 1).im))
  have him2_neg_hi : -(ζ 2).im ≤ |((ζ 2).im)| :=
    by simpa using neg_le_neg (neg_abs_le ((ζ 2).im))
  have him3_neg_hi : -(ζ 3).im ≤ |((ζ 3).im)| :=
    by simpa using neg_le_neg (neg_abs_le ((ζ 3).im))
  have hrealSmall' :
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).re| +
          (1 / 4 : ℝ) *
            (|((ζ 1).re)| + |((ζ 2).re)| + |((ζ 3).re)|) <
        ξ 0 / (16 * T) := by
    nlinarith
  intro μ
  fin_cases μ
  · simp [osiiLemma51CoeffMap4, osiiLemma51Coeff4, osiiLemma51E4,
      hbase_re, hbase_im, htime_re, htime_im]
    constructor
    · nlinarith [hrealSmall, hre0_lo, hre1_lo, hre2_lo, hre3_lo]
    · rw [abs_lt]
      constructor
      · nlinarith [hrealSmall, hre0_lo, hre1_lo, hre2_lo, hre3_lo,
          himagSmall, him0_lo, him1_lo, him2_lo, him3_lo, hη]
      · nlinarith [hrealSmall, hre0_lo, hre1_lo, hre2_lo, hre3_lo,
          himagSmall, him0_hi, him1_hi, him2_hi, him3_hi, hη]
  · simp [osiiLemma51CoeffMap4, osiiLemma51Coeff4, osiiLemma51E4,
      hbase_re, hbase_im, htime_re, htime_im]
    constructor
    · nlinarith [hrealSmall, hre0_lo, hre1_lo, hre2_neg_lo, hre3_neg_lo]
    · rw [abs_lt]
      constructor
      · nlinarith [hrealSmall, hre0_lo, hre1_lo, hre2_neg_lo, hre3_neg_lo,
          himagSmall, him0_lo, him1_lo, him2_neg_lo, him3_neg_lo, hη]
      · nlinarith [hrealSmall, hre0_lo, hre1_lo, hre2_neg_lo, hre3_neg_lo,
          himagSmall, him0_hi, him1_hi, him2_neg_hi, him3_neg_hi, hη]
  · simp [osiiLemma51CoeffMap4, osiiLemma51Coeff4, osiiLemma51E4,
      hbase_re, hbase_im, htime_re, htime_im]
    constructor
    · nlinarith [hrealSmall, hre0_lo, hre1_neg_lo, hre2_lo, hre3_neg_lo]
    · rw [abs_lt]
      constructor
      · nlinarith [hrealSmall, hre0_lo, hre1_neg_lo, hre2_lo, hre3_neg_lo,
          himagSmall, him0_lo, him1_neg_lo, him2_lo, him3_neg_lo, hη]
      · nlinarith [hrealSmall, hre0_lo, hre1_neg_lo, hre2_lo, hre3_neg_lo,
          himagSmall, him0_hi, him1_neg_hi, him2_hi, him3_neg_hi, hη]
  · simp [osiiLemma51CoeffMap4, osiiLemma51Coeff4, osiiLemma51E4,
      hbase_re, hbase_im, htime_re, htime_im]
    constructor
    · nlinarith [hrealSmall, hre0_lo, hre1_neg_lo, hre2_neg_lo, hre3_lo]
    · rw [abs_lt]
      constructor
      · nlinarith [hrealSmall, hre0_lo, hre1_neg_lo, hre2_neg_lo, hre3_lo,
          himagSmall, him0_lo, him1_neg_lo, him2_neg_lo, him3_lo, hη]
      · nlinarith [hrealSmall, hre0_lo, hre1_neg_lo, hre2_neg_lo, hre3_lo,
          himagSmall, him0_hi, him1_neg_hi, him2_neg_hi, him3_hi, hη]

/-- A genuine local-polydisc version of the coefficient estimate. -/
theorem osiiLemma51_exists_coord_radius_coeff4_rightHalfPlane
    (T : ℝ) (hT : 0 < T) (ξ : Fin 4 → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ζ : Fin 4 → ℂ,
        (∀ ν : Fin 4, ‖ζ ν‖ < ρ) →
          ∀ μ : Fin 4, 0 < (osiiLemma51Coeff4 T ξ ζ μ).re := by
  let base : ℝ := ξ 0 / (16 * T)
  have hbase : 0 < base := by
    dsimp [base]
    positivity
  let ρ : ℝ := min (T * base) (base / 3)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (mul_pos hT hbase) (by positivity)
  refine ⟨ρ, hρpos, ?_⟩
  intro ζ hζ μ
  have h8Tpos : 0 < 8 * T := by positivity
  have hnorm_den : ‖(((8 * T : ℝ) : ℂ))‖ = 8 * T :=
    Complex.norm_of_nonneg (le_of_lt h8Tpos)
  have hρ_le_Tbase : ρ ≤ T * base := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_base_div_three : ρ ≤ base / 3 := by
    dsimp [ρ]
    exact min_le_right _ _
  have htime_lt :
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).re| < base / 8 := by
    calc
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).re|
          ≤ ‖ζ 0 / ((8 * T : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
      _ = ‖ζ 0‖ / (8 * T) := by
          rw [norm_div, hnorm_den]
      _ < ρ / (8 * T) := div_lt_div_of_pos_right (hζ 0) h8Tpos
      _ ≤ (T * base) / (8 * T) :=
          div_le_div_of_nonneg_right hρ_le_Tbase (le_of_lt h8Tpos)
      _ = base / 8 := by
          field_simp [ne_of_gt hT]
  have hζ1 : |((ζ 1).re)| < ρ :=
    lt_of_le_of_lt (Complex.abs_re_le_norm (ζ 1)) (hζ 1)
  have hζ2 : |((ζ 2).re)| < ρ :=
    lt_of_le_of_lt (Complex.abs_re_le_norm (ζ 2)) (hζ 2)
  have hζ3 : |((ζ 3).re)| < ρ :=
    lt_of_le_of_lt (Complex.abs_re_le_norm (ζ 3)) (hζ 3)
  have hspatial_lt :
      (1 / 4 : ℝ) *
          (|((ζ 1).re)| + |((ζ 2).re)| + |((ζ 3).re)|) <
        base / 4 := by
    have hsum_lt :
        |((ζ 1).re)| + |((ζ 2).re)| + |((ζ 3).re)| < 3 * ρ := by
      nlinarith
    nlinarith [hρ_le_base_div_three]
  have hsmall :
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).re| +
          (1 / 4 : ℝ) *
            (|((ζ 1).re)| + |((ζ 2).re)| + |((ζ 3).re)|) <
        ξ 0 / (16 * T) := by
    dsimp [base] at hbase htime_lt hspatial_lt
    nlinarith
  exact osiiLemma51_coeff4_re_pos_of_small_perturbation T hT ξ ζ hsmall μ

/-- Local-polydisc version of the narrow-sector estimate. -/
theorem osiiLemma51_exists_coord_radius_coeff4_narrowSector
    (T : ℝ) (hT : 0 < T) (ξ : Fin 4 → ℝ) (hξ0 : 0 < ξ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ζ : Fin 4 → ℂ,
        (∀ ν : Fin 4, ‖ζ ν‖ < ρ) →
          osiiLemma51CoeffMap4 T ξ ζ ∈ osiiLemma51NarrowSector4 η := by
  let base : ℝ := ξ 0 / (16 * T)
  have hbase : 0 < base := by
    dsimp [base]
    positivity
  let realCap : ℝ := min (T * base) (base / 3)
  let imagCap : ℝ := min (T * η * base) (η * base / 3)
  let ρ : ℝ := min realCap imagCap
  have hρpos : 0 < ρ := by
    dsimp [ρ, realCap, imagCap]
    exact lt_min
      (lt_min (mul_pos hT hbase) (by positivity))
      (lt_min (by positivity) (by positivity))
  refine ⟨ρ, hρpos, ?_⟩
  intro ζ hζ
  have h8Tpos : 0 < 8 * T := by positivity
  have hnorm_den : ‖(((8 * T : ℝ) : ℂ))‖ = 8 * T :=
    Complex.norm_of_nonneg (le_of_lt h8Tpos)
  have hρ_le_Tbase : ρ ≤ T * base := by
    dsimp [ρ, realCap, imagCap]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ_le_base_div_three : ρ ≤ base / 3 := by
    dsimp [ρ, realCap, imagCap]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ_le_Tηbase : ρ ≤ T * η * base := by
    dsimp [ρ, realCap, imagCap]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_le_ηbase_div_three : ρ ≤ η * base / 3 := by
    dsimp [ρ, realCap, imagCap]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have htime_re_lt :
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).re| < base / 8 := by
    calc
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).re|
          ≤ ‖ζ 0 / ((8 * T : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
      _ = ‖ζ 0‖ / (8 * T) := by
          rw [norm_div, hnorm_den]
      _ < ρ / (8 * T) := div_lt_div_of_pos_right (hζ 0) h8Tpos
      _ ≤ (T * base) / (8 * T) :=
          div_le_div_of_nonneg_right hρ_le_Tbase (le_of_lt h8Tpos)
      _ = base / 8 := by
          field_simp [ne_of_gt hT]
  have htime_im_lt :
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).im| < η * base / 8 := by
    calc
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).im|
          ≤ ‖ζ 0 / ((8 * T : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
      _ = ‖ζ 0‖ / (8 * T) := by
          rw [norm_div, hnorm_den]
      _ < ρ / (8 * T) := div_lt_div_of_pos_right (hζ 0) h8Tpos
      _ ≤ (T * η * base) / (8 * T) :=
          div_le_div_of_nonneg_right hρ_le_Tηbase (le_of_lt h8Tpos)
      _ = η * base / 8 := by
          field_simp [ne_of_gt hT]
  have hζ1_re : |((ζ 1).re)| < ρ :=
    lt_of_le_of_lt (Complex.abs_re_le_norm (ζ 1)) (hζ 1)
  have hζ2_re : |((ζ 2).re)| < ρ :=
    lt_of_le_of_lt (Complex.abs_re_le_norm (ζ 2)) (hζ 2)
  have hζ3_re : |((ζ 3).re)| < ρ :=
    lt_of_le_of_lt (Complex.abs_re_le_norm (ζ 3)) (hζ 3)
  have hζ1_im : |((ζ 1).im)| < ρ :=
    lt_of_le_of_lt (Complex.abs_im_le_norm (ζ 1)) (hζ 1)
  have hζ2_im : |((ζ 2).im)| < ρ :=
    lt_of_le_of_lt (Complex.abs_im_le_norm (ζ 2)) (hζ 2)
  have hζ3_im : |((ζ 3).im)| < ρ :=
    lt_of_le_of_lt (Complex.abs_im_le_norm (ζ 3)) (hζ 3)
  have hspatial_re_lt :
      (1 / 4 : ℝ) *
          (|((ζ 1).re)| + |((ζ 2).re)| + |((ζ 3).re)|) <
        base / 4 := by
    have hsum_lt :
        |((ζ 1).re)| + |((ζ 2).re)| + |((ζ 3).re)| < 3 * ρ := by
      nlinarith
    nlinarith [hρ_le_base_div_three]
  have hspatial_im_lt :
      (1 / 4 : ℝ) *
          (|((ζ 1).im)| + |((ζ 2).im)| + |((ζ 3).im)|) <
        η * base / 4 := by
    have hsum_lt :
        |((ζ 1).im)| + |((ζ 2).im)| + |((ζ 3).im)| < 3 * ρ := by
      nlinarith
    nlinarith [hρ_le_ηbase_div_three]
  have hrealSmall :
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).re| +
          (1 / 4 : ℝ) *
            (|((ζ 1).re)| + |((ζ 2).re)| + |((ζ 3).re)|) <
        (ξ 0 / (16 * T)) / 2 := by
    dsimp [base] at htime_re_lt hspatial_re_lt
    nlinarith
  have himagSmall :
      |(ζ 0 / ((8 * T : ℝ) : ℂ)).im| +
          (1 / 4 : ℝ) *
            (|((ζ 1).im)| + |((ζ 2).im)| + |((ζ 3).im)|) <
        η * ((ξ 0 / (16 * T)) / 2) := by
    dsimp [base] at htime_im_lt hspatial_im_lt
    nlinarith
  exact osiiLemma51_coeff4_mem_narrowSector_of_small_perturbation
    T hT ξ hξ0 ζ η hη hrealSmall himagSmall

/-- Pull back a holomorphic MZ right-half-plane representative through the
Lemma 5.1 coefficient map on a sufficiently small coordinate polydisc. -/
theorem osiiLemma51_local_polydisc_extension_differentiableOn
    (T : ℝ) (hT : 0 < T) (ξ : Fin 4 → ℝ) (hξ0 : 0 < ξ 0)
    (F : (Fin 4 → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F osiiLemma51RightHalfPlane4) :
    ∃ ρ : ℝ, 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin 4 → ℂ => F (osiiLemma51CoeffMap4 T ξ ζ))
        {ζ : Fin 4 → ℂ | ∀ ν : Fin 4, ‖ζ ν‖ < ρ} := by
  rcases osiiLemma51_exists_coord_radius_coeff4_rightHalfPlane T hT ξ hξ0 with
    ⟨ρ, hρpos, hρ⟩
  refine ⟨ρ, hρpos, ?_⟩
  let polydisc : Set (Fin 4 → ℂ) := {ζ | ∀ ν : Fin 4, ‖ζ ν‖ < ρ}
  have hcoeff :
      DifferentiableOn ℂ
        (fun ζ : Fin 4 → ℂ => osiiLemma51CoeffMap4 T ξ ζ) polydisc := by
    have hcoeff_global :
        Differentiable ℂ
          (fun ζ : Fin 4 → ℂ => osiiLemma51CoeffMap4 T ξ ζ) := by
      unfold osiiLemma51CoeffMap4 osiiLemma51Coeff4 osiiLemma51E4
      fun_prop
    exact hcoeff_global.differentiableOn
  have hmaps :
      Set.MapsTo (fun ζ : Fin 4 → ℂ => osiiLemma51CoeffMap4 T ξ ζ)
        polydisc osiiLemma51RightHalfPlane4 := by
    intro ζ hζ μ
    exact hρ ζ hζ μ
  simpa [polydisc, Function.comp] using hF.comp hcoeff hmaps

/-- Sector-domain version of the Lemma 5.1 coordinate pullback. -/
theorem osiiLemma51_local_polydisc_sector_extension_differentiableOn
    (T : ℝ) (hT : 0 < T) (ξ : Fin 4 → ℝ) (hξ0 : 0 < ξ 0)
    (η : ℝ) (hη : 0 < η)
    (F : (Fin 4 → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (osiiLemma51NarrowSector4 η)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin 4 → ℂ => F (osiiLemma51CoeffMap4 T ξ ζ))
        {ζ : Fin 4 → ℂ | ∀ ν : Fin 4, ‖ζ ν‖ < ρ} := by
  rcases osiiLemma51_exists_coord_radius_coeff4_narrowSector
      T hT ξ hξ0 η hη with
    ⟨ρ, hρpos, hρ⟩
  refine ⟨ρ, hρpos, ?_⟩
  let polydisc : Set (Fin 4 → ℂ) := {ζ | ∀ ν : Fin 4, ‖ζ ν‖ < ρ}
  have hcoeff :
      DifferentiableOn ℂ
        (fun ζ : Fin 4 → ℂ => osiiLemma51CoeffMap4 T ξ ζ) polydisc := by
    have hcoeff_global :
        Differentiable ℂ
          (fun ζ : Fin 4 → ℂ => osiiLemma51CoeffMap4 T ξ ζ) := by
      unfold osiiLemma51CoeffMap4 osiiLemma51Coeff4 osiiLemma51E4
      fun_prop
    exact hcoeff_global.differentiableOn
  have hmaps :
      Set.MapsTo (fun ζ : Fin 4 → ℂ => osiiLemma51CoeffMap4 T ξ ζ)
        polydisc (osiiLemma51NarrowSector4 η) := by
    intro ζ hζ
    exact hρ ζ hζ
  simpa [polydisc, Function.comp] using hF.comp hcoeff hmaps

end OSReconstruction
