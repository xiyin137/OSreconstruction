import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51CoordinateEstimate

/-!
# OS-II Lemma 5.1, Axis-Pair General-d Geometry

This file records the general-spatial-dimension replacement for the four-vector
coefficient calculation in OS II Lemma 5.1.  The paper's four basis vectors are
replaced by the `2d` axis-pair directions `(T, plus/minus e_j)`.

The constant coefficient parts contribute half of the positive time coordinate
and cancel spatially; the common `ζ^0` part contributes the time perturbation;
the signed half-spatial parts contribute the spatial perturbations.  A small
coordinate polydisc therefore maps into the right half-plane coefficient
domain, so any holomorphic coefficient representative pulls back to a
holomorphic local representative in physical coordinates.
-/

noncomputable section

open Complex Topology
open scoped Classical BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Axis-pair index set for the general-`d` OS-II Lemma 5.1 geometry. -/
abbrev osiiAxisPairIndex (d : ℕ) := Fin d × Bool

/-- Axis-pair directions `(T, plus/minus e_j)` for the general-`d` Lemma 5.1
coordinate calculation. -/
def osiiAxisPairDir (T : ℝ) (a : osiiAxisPairIndex d) :
    Fin (d + 1) → ℝ :=
  Fin.cases T (fun j => if a.1 = j then (if a.2 then 1 else -1) else 0)

/-- The fixed real vector `xi-hat`: half the time coordinate and the original
spatial base point. -/
def osiiAxisPairXiHat (ξ : Fin (d + 1) → ℝ) :
    Fin (d + 1) → ℂ :=
  Fin.cases ((ξ 0 / 2 : ℝ) : ℂ) (fun j => (ξ (Fin.succ j) : ℂ))

/-- Coefficients for the axis-pair directions.

For each spatial axis there are two coefficients.  Their common constant part
contributes `ξ^0 / 2` to the time coordinate after summing all `2d` directions;
their common `ζ^0` part contributes the perturbation in time; and the signed
half-spatial part contributes `ζ^{j+1}`. -/
def osiiAxisPairCoeff
    (T : ℝ) (ξ : Fin (d + 1) → ℝ) (ζ : Fin (d + 1) → ℂ)
    (a : osiiAxisPairIndex d) : ℂ :=
  (ξ 0 : ℂ) / (((4 * (d : ℝ) * T : ℝ) : ℂ)) +
    ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ)) +
      if a.2 then ζ (Fin.succ a.1) / 2 else -ζ (Fin.succ a.1) / 2

/-- The full axis-pair coefficient map. -/
def osiiAxisPairCoeffMap
    (T : ℝ) (ξ : Fin (d + 1) → ℝ) (ζ : Fin (d + 1) → ℂ) :
    osiiAxisPairIndex d → ℂ :=
  fun a => osiiAxisPairCoeff T ξ ζ a

/-- Right half-plane carrier for all axis-pair coefficients. -/
def osiiAxisPairRightHalfPlane : Set (osiiAxisPairIndex d → ℂ) :=
  {w | ∀ a : osiiAxisPairIndex d, 0 < (w a).re}

/-- A narrow sector for all axis-pair coefficients.  This is the general-`d`
ratio form of OS II `(5.13)`. -/
def osiiAxisPairNarrowSector (η : ℝ) :
    Set (osiiAxisPairIndex d → ℂ) :=
  {w | ∀ a : osiiAxisPairIndex d, 0 < (w a).re ∧ |(w a).im| < η * (w a).re}

/-- The argument-sum coefficient domain used in OS II `(5.8)`, now over the
axis-pair index family. -/
def osiiAxisPairArgSumDomain : Set (osiiAxisPairIndex d → ℂ) :=
  {w | ∑ a : osiiAxisPairIndex d, |Complex.arg (w a)| < Real.pi / 2}

/-- The corresponding logarithmic MZ carrier over the axis-pair index family. -/
def osiiAxisPairLogDomain : Set (osiiAxisPairIndex d → ℂ) :=
  {r | ∑ a : osiiAxisPairIndex d, |(r a).im| < Real.pi / 2}

theorem osiiAxisPair_narrowSector_subset_argSumDomain
    {η : ℝ}
    (hηsum :
      (Fintype.card (osiiAxisPairIndex d) : ℝ) * Real.arctan η < Real.pi / 2) :
    osiiAxisPairNarrowSector (d := d) η ⊆
      osiiAxisPairArgSumDomain (d := d) := by
  classical
  intro w hw
  have harg_bound :
      ∀ a : osiiAxisPairIndex d, |Complex.arg (w a)| < Real.arctan η := by
    intro a
    rcases hw a with ⟨hre, him⟩
    have hratio : |(w a).im / (w a).re| < η := by
      rw [abs_div, abs_of_pos hre]
      exact (div_lt_iff₀ hre).2 him
    rw [osiiLemma51_abs_arg_eq_arctan_abs_im_div_re hre]
    exact Real.arctan_strictMono hratio
  have hnonempty : (Finset.univ : Finset (osiiAxisPairIndex d)).Nonempty := by
    refine ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true), Finset.mem_univ _⟩
  have hsum_lt :
      (∑ a : osiiAxisPairIndex d, |Complex.arg (w a)|) <
        ∑ _a : osiiAxisPairIndex d, Real.arctan η := by
    exact Finset.sum_lt_sum_of_nonempty hnonempty
      (fun a _ => harg_bound a)
  have hconst :
      (∑ _a : osiiAxisPairIndex d, Real.arctan η) =
        (Fintype.card (osiiAxisPairIndex d) : ℝ) * Real.arctan η := by
    simp
  have hsum_lt_const :
      (∑ a : osiiAxisPairIndex d, |Complex.arg (w a)|) <
        (Fintype.card (osiiAxisPairIndex d) : ℝ) * Real.arctan η := by
    simpa [hconst] using hsum_lt
  simpa [osiiAxisPairArgSumDomain] using hsum_lt_const.trans hηsum

/-- A concrete narrow-sector aperture whose total argument width is below
`π / 2` for the finite axis-pair family. -/
theorem exists_osiiAxisPair_eta_argSum :
    ∃ η : ℝ, 0 < η ∧
      (Fintype.card (osiiAxisPairIndex d) : ℝ) * Real.arctan η < Real.pi / 2 := by
  classical
  let c : ℝ := Fintype.card (osiiAxisPairIndex d)
  have hcard_pos : 0 < Fintype.card (osiiAxisPairIndex d) :=
    Fintype.card_pos_iff.2 ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true)⟩
  have hc_pos : 0 < c := by
    dsimp [c]
    exact_mod_cast hcard_pos
  let x : ℝ := Real.pi / (4 * c)
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hx_lt : x < Real.pi / 2 := by
    dsimp [x]
    have hcle : (1 : ℝ) ≤ c := by
      dsimp [c]
      exact_mod_cast hcard_pos
    have hden_ge : (4 : ℝ) ≤ 4 * c := by nlinarith
    have hdiv_le : Real.pi / (4 * c) ≤ Real.pi / 4 := by
      exact div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by norm_num) hden_ge
    nlinarith [Real.pi_pos, hdiv_le]
  let η : ℝ := Real.tan x
  have hηpos : 0 < η := by
    dsimp [η]
    exact Real.tan_pos_of_pos_of_lt_pi_div_two hx_pos hx_lt
  refine ⟨η, hηpos, ?_⟩
  have hx_low : -(Real.pi / 2) < x := by nlinarith [Real.pi_pos, hx_pos]
  have harctan : Real.arctan η = x := by
    dsimp [η]
    exact Real.arctan_tan hx_low hx_lt
  rw [harctan]
  dsimp [x, c]
  field_simp [ne_of_gt hc_pos]
  nlinarith [Real.pi_pos]

private theorem osiiAxisPair_bool_sum_signed_half (z : ℂ) :
    (∑ b : Bool, (if b then z / 2 else -z / 2)) = 0 := by
  simp
  ring

private theorem osiiAxisPair_bool_sum_signed_half_mul_sign (z : ℂ) :
    (∑ b : Bool,
      (if b then z / 2 else -z / 2) * (((if b then 1 else -1 : ℝ) : ℂ))) = z := by
  simp
  ring

private theorem osiiAxisPair_bool_sum_const_mul_sign (c : ℂ) :
    (∑ b : Bool, c * (((if b then 1 else -1 : ℝ) : ℂ))) = 0 := by
  simp

private theorem osiiAxisPairCoeff_time_sum
    (T : ℝ) (hT : T ≠ 0)
    (ξ : Fin (d + 1) → ℝ) (ζ : Fin (d + 1) → ℂ) :
    (∑ a : osiiAxisPairIndex d,
        osiiAxisPairCoeff T ξ ζ a * ((T : ℝ) : ℂ)) =
      (ξ 0 / 2 : ℝ) + ζ 0 := by
  classical
  have hd_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  have hden_ne : ((2 * (d : ℝ) * T : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (mul_ne_zero two_ne_zero hd_ne) hT)
  have hden4_ne : ((4 * (d : ℝ) * T : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hd_ne) hT)
  have hdC_ne : (d : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  have hTC_ne : (T : ℂ) ≠ 0 := by
    exact_mod_cast hT
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Fin d,
        ∑ b : Bool,
          osiiAxisPairCoeff T ξ ζ (x, b) * (T : ℂ))
        =
      ∑ _x : Fin d,
        ((2 : ℂ) *
          ((ξ 0 : ℂ) / (((4 * (d : ℝ) * T : ℝ) : ℂ)) * (T : ℂ)) +
            (2 : ℂ) * ((ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))) * (T : ℂ))) := by
        apply Finset.sum_congr rfl
        intro x _
        simp [osiiAxisPairCoeff]
        ring_nf
    _ =
      (d : ℂ) *
        ((2 : ℂ) *
          ((ξ 0 : ℂ) / (((4 * (d : ℝ) * T : ℝ) : ℂ)) * (T : ℂ)) +
            (2 : ℂ) * ((ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))) * (T : ℂ))) := by
        simp
        ring
    _ = (ξ 0 / 2 : ℝ) + ζ 0 := by
        field_simp [hden_ne, hden4_ne, hdC_ne, hTC_ne, hT, hd_ne]
        push_cast
        ring_nf

private theorem osiiAxisPairCoeff_spatial_sum
    (T : ℝ) (ξ : Fin (d + 1) → ℝ) (ζ : Fin (d + 1) → ℂ) (j : Fin d) :
    (∑ a : osiiAxisPairIndex d,
        osiiAxisPairCoeff T ξ ζ a *
          (((osiiAxisPairDir (d := d) T a (Fin.succ j) : ℝ) : ℂ))) =
      ζ (Fin.succ j) := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Fin d,
        ∑ b : Bool,
          osiiAxisPairCoeff T ξ ζ (x, b) *
            (((osiiAxisPairDir (d := d) T (x, b) (Fin.succ j) : ℝ) : ℂ)))
        =
      ∑ x : Fin d,
        if x = j then ζ (Fin.succ j) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = j
        · subst hx
          simp [osiiAxisPairDir, osiiAxisPairCoeff,
            osiiAxisPair_bool_sum_const_mul_sign,
            osiiAxisPair_bool_sum_signed_half_mul_sign]
          ring_nf
        · simp [osiiAxisPairDir, hx]
    _ = ζ (Fin.succ j) := by
        simpa using
          (Finset.sum_ite_eq' (s := (Finset.univ : Finset (Fin d)))
            (a := j) (b := fun _ : Fin d => ζ (Fin.succ j))
            (h := fun _ : Fin d => 0) (Finset.mem_univ j))

/-- Axis-pair analogue of OS II `(5.11)`--`(5.12)` in general spatial
dimension. -/
theorem osiiAxisPairCoeff_linear_identity
    (T : ℝ) (hT : T ≠ 0)
    (ξ : Fin (d + 1) → ℝ) (ζ : Fin (d + 1) → ℂ)
    (ν : Fin (d + 1)) :
    osiiAxisPairXiHat (d := d) ξ ν +
        ∑ a : osiiAxisPairIndex d,
          osiiAxisPairCoeff T ξ ζ a *
            (((osiiAxisPairDir (d := d) T a ν : ℝ) : ℂ)) =
      (ξ ν : ℂ) + ζ ν := by
  refine Fin.cases ?_ ?_ ν
  · simp [osiiAxisPairXiHat, osiiAxisPairDir,
      osiiAxisPairCoeff_time_sum (d := d) T hT ξ ζ]
    ring
  · intro j
    simp [osiiAxisPairXiHat,
      osiiAxisPairCoeff_spatial_sum (d := d) T ξ ζ j]

/-- Public weighted-time coefficient sum from the axis-pair Lemma 5.1
calculation.

The coefficients themselves are attached to directions whose time component is
`T`; therefore the physical positive-time displacement is the `T`-weighted
coefficient sum, not the bare sum of coefficients. -/
theorem osiiAxisPairCoeffMap_weighted_time_sum
    (T : ℝ) (hT : T ≠ 0)
    (ξ : Fin (d + 1) → ℝ) (ζ : Fin (d + 1) → ℂ) :
    (∑ a : osiiAxisPairIndex d,
        osiiAxisPairCoeffMap T ξ ζ a * ((T : ℝ) : ℂ)) =
      (ξ 0 / 2 : ℝ) + ζ 0 := by
  simpa [osiiAxisPairCoeffMap] using
    osiiAxisPairCoeff_time_sum (d := d) T hT ξ ζ

/-- Equivalent left-weighted form of
`osiiAxisPairCoeffMap_weighted_time_sum`. -/
theorem osiiAxisPairCoeffMap_time_mul_sum
    (T : ℝ) (hT : T ≠ 0)
    (ξ : Fin (d + 1) → ℝ) (ζ : Fin (d + 1) → ℂ) :
    ((T : ℂ) * ∑ a : osiiAxisPairIndex d,
        osiiAxisPairCoeffMap T ξ ζ a) =
      (ξ 0 / 2 : ℝ) + ζ 0 := by
  calc
    ((T : ℂ) * ∑ a : osiiAxisPairIndex d,
        osiiAxisPairCoeffMap T ξ ζ a) =
      ∑ a : osiiAxisPairIndex d,
        osiiAxisPairCoeffMap T ξ ζ a * ((T : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = (ξ 0 / 2 : ℝ) + ζ 0 :=
        osiiAxisPairCoeffMap_weighted_time_sum (d := d) T hT ξ ζ

/-- Direct positivity estimate for the general-`d` axis-pair coefficients.

This is the local small-perturbation core of OS-II Lemma 5.1: if the time
coefficient perturbation and the signed spatial half-perturbations are smaller
than one quarter of the positive constant coefficient, every coefficient stays
in the right half-plane. -/
theorem osiiAxisPairCoeff_re_pos_of_small_perturbation
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (ζ : Fin (d + 1) → ℂ)
    (hsmall_time :
      |(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).re| <
        (ξ 0 / (4 * (d : ℝ) * T)) / 4)
    (hsmall_spatial :
      ∀ j : Fin d, |((ζ (Fin.succ j)).re)| / 2 <
        (ξ 0 / (4 * (d : ℝ) * T)) / 4)
    (a : osiiAxisPairIndex d) :
    0 < (osiiAxisPairCoeff T ξ ζ a).re := by
  classical
  let base : ℝ := ξ 0 / (4 * (d : ℝ) * T)
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have hbase : 0 < base := by
    dsimp [base]
    positivity
  have hbase_re :
      (((ξ 0 : ℂ) / (((4 * (d : ℝ) * T : ℝ) : ℂ))).re) = base := by
    dsimp [base]
    simpa using (Complex.div_ofReal_re (ξ 0 : ℂ) (4 * (d : ℝ) * T))
  have hsmall_time' :
      |(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).re| < base / 4 := by
    simpa [base] using hsmall_time
  have hsmall_spatial' :
      ∀ j : Fin d, |((ζ (Fin.succ j)).re)| / 2 < base / 4 := by
    intro j
    simpa [base] using hsmall_spatial j
  rcases a with ⟨j, b⟩
  have htime_lo :
      -|(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).re| ≤
        (ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).re :=
    neg_abs_le _
  have hbase_re' :
      ((ξ 0 : ℂ) / (4 * (d : ℂ) * (T : ℂ))).re = base := by
    simpa using hbase_re
  have htime_lo' :
      -|(ζ 0 / (2 * (d : ℂ) * (T : ℂ))).re| ≤
        (ζ 0 / (2 * (d : ℂ) * (T : ℂ))).re := by
    simpa using htime_lo
  have hsmall_time'' :
      |(ζ 0 / (2 * (d : ℂ) * (T : ℂ))).re| < base / 4 := by
    simpa using hsmall_time'
  have hsp_lo : -|((ζ (Fin.succ j)).re)| / 2 ≤ (ζ (Fin.succ j)).re / 2 := by
    nlinarith [neg_abs_le ((ζ (Fin.succ j)).re)]
  have hsp_neg_lo : -|((ζ (Fin.succ j)).re)| / 2 ≤ -(ζ (Fin.succ j)).re / 2 := by
    nlinarith [neg_le_neg (le_abs_self ((ζ (Fin.succ j)).re))]
  cases b
  · simp [osiiAxisPairCoeff, hbase_re]
    rw [hbase_re']
    nlinarith [hbase, hsmall_time'', hsmall_spatial' j, htime_lo', hsp_neg_lo]
  · simp [osiiAxisPairCoeff, hbase_re]
    rw [hbase_re']
    nlinarith [hbase, hsmall_time'', hsmall_spatial' j, htime_lo', hsp_lo]

/-- Narrow-sector version of the general-`d` axis-pair coefficient estimate.

This is the OS-II `(5.13)` estimate in the axis-pair coordinates: sufficiently
small real and imaginary perturbations keep every coefficient in an arbitrarily
narrow sector inside the right half-plane. -/
theorem osiiAxisPairCoeff_mem_narrowSector_of_small_perturbation
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (ζ : Fin (d + 1) → ℂ)
    (η : ℝ) (hη : 0 < η)
    (hsmall_time_re :
      |(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).re| <
        (ξ 0 / (4 * (d : ℝ) * T)) / 4)
    (hsmall_spatial_re :
      ∀ j : Fin d, |((ζ (Fin.succ j)).re)| / 2 <
        (ξ 0 / (4 * (d : ℝ) * T)) / 4)
    (hsmall_time_im :
      |(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).im| <
        η * (ξ 0 / (4 * (d : ℝ) * T)) / 4)
    (hsmall_spatial_im :
      ∀ j : Fin d, |((ζ (Fin.succ j)).im)| / 2 <
        η * (ξ 0 / (4 * (d : ℝ) * T)) / 4) :
    osiiAxisPairCoeffMap T ξ ζ ∈
      osiiAxisPairNarrowSector (d := d) η := by
  classical
  let base : ℝ := ξ 0 / (4 * (d : ℝ) * T)
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have hbase : 0 < base := by
    dsimp [base]
    positivity
  have hbase_re :
      (((ξ 0 : ℂ) / (((4 * (d : ℝ) * T : ℝ) : ℂ))).re) = base := by
    dsimp [base]
    simpa using (Complex.div_ofReal_re (ξ 0 : ℂ) (4 * (d : ℝ) * T))
  have hbase_im :
      (((ξ 0 : ℂ) / (((4 * (d : ℝ) * T : ℝ) : ℂ))).im) = 0 := by
    simpa using (Complex.div_ofReal_im (ξ 0 : ℂ) (4 * (d : ℝ) * T))
  have hbase_re' :
      ((ξ 0 : ℂ) / (4 * (d : ℂ) * (T : ℂ))).re = base := by
    simpa using hbase_re
  have hbase_im' :
      ((ξ 0 : ℂ) / (4 * (d : ℂ) * (T : ℂ))).im = 0 := by
    simpa using hbase_im
  intro a
  rcases a with ⟨j, b⟩
  let timeC : ℂ := ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))
  let spC : ℂ := ζ (Fin.succ j)
  have htime_re_abs : |timeC.re| < base / 4 := by
    simpa [timeC, base] using hsmall_time_re
  have htime_im_abs : |timeC.im| < η * base / 4 := by
    simpa [timeC, base] using hsmall_time_im
  have hsp_re_abs : |spC.re / 2| < base / 4 := by
    have habs : |spC.re / 2| = |spC.re| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs]
    simpa [spC, base] using hsmall_spatial_re j
  have hsp_im_abs : |spC.im / 2| < η * base / 4 := by
    have habs : |spC.im / 2| = |spC.im| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs]
    simpa [spC, base] using hsmall_spatial_im j
  have hcoeff_re :
      (osiiAxisPairCoeffMap T ξ ζ (j, b)).re =
        base + timeC.re + (if b then spC.re / 2 else -spC.re / 2) := by
    cases b <;>
      simp [osiiAxisPairCoeffMap, osiiAxisPairCoeff, timeC, spC, hbase_re']
  have hcoeff_im :
      (osiiAxisPairCoeffMap T ξ ζ (j, b)).im =
        timeC.im + (if b then spC.im / 2 else -spC.im / 2) := by
    cases b <;>
      simp [osiiAxisPairCoeffMap, osiiAxisPairCoeff, timeC, spC, hbase_im']
  have hsp_re_neg_abs : |-spC.re / 2| < base / 4 := by
    have h : |-(spC.re / 2)| < base / 4 := by
      simpa using hsp_re_abs
    simpa [neg_div] using h
  have hsp_im_neg_abs : |-spC.im / 2| < η * base / 4 := by
    have h : |-(spC.im / 2)| < η * base / 4 := by
      simpa using hsp_im_abs
    simpa [neg_div] using h
  have hsp_re_signed_abs :
      |(if b then spC.re / 2 else -spC.re / 2)| < base / 4 := by
    cases b
    · simpa using hsp_re_neg_abs
    · simpa using hsp_re_abs
  have hsp_im_signed_abs :
      |(if b then spC.im / 2 else -spC.im / 2)| < η * base / 4 := by
    cases b
    · simpa using hsp_im_neg_abs
    · simpa using hsp_im_abs
  have hre_half :
      base / 2 < (osiiAxisPairCoeffMap T ξ ζ (j, b)).re := by
    have htime_lo := (abs_lt.mp htime_re_abs).1
    have hsp_lo := (abs_lt.mp hsp_re_signed_abs).1
    rw [hcoeff_re]
    nlinarith
  have him_abs :
      |(osiiAxisPairCoeffMap T ξ ζ (j, b)).im| < η * base / 2 := by
    rw [hcoeff_im]
    calc
      |timeC.im + (if b then spC.im / 2 else -spC.im / 2)|
          ≤ |timeC.im| + |(if b then spC.im / 2 else -spC.im / 2)| :=
            abs_add_le _ _
      _ < η * base / 4 + η * base / 4 :=
          add_lt_add htime_im_abs hsp_im_signed_abs
      _ = η * base / 2 := by ring
  constructor
  · exact lt_trans (by positivity : (0 : ℝ) < base / 2) hre_half
  · nlinarith [hη, hbase, hre_half, him_abs]

/-- Local-radius right-half-plane form of the general-`d` axis-pair Lemma 5.1
coefficient estimate. -/
theorem osiiAxisPair_exists_coord_radius_coeff_rightHalfPlane
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ζ : Fin (d + 1) → ℂ,
        (∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ) →
          ∀ a : osiiAxisPairIndex d,
            0 < (osiiAxisPairCoeff T ξ ζ a).re := by
  classical
  let base : ℝ := ξ 0 / (4 * (d : ℝ) * T)
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have hbase : 0 < base := by
    dsimp [base]
    positivity
  let ρT : ℝ := (d : ℝ) * T * base / 2
  let ρS : ℝ := base / 2
  let ρ : ℝ := min ρT ρS
  have hρpos : 0 < ρ := by
    dsimp [ρ, ρT, ρS]
    exact lt_min (by positivity) (by positivity)
  refine ⟨ρ, hρpos, ?_⟩
  intro ζ hζ
  have hden_pos : 0 < 2 * (d : ℝ) * T := by positivity
  have hnorm_den : ‖(((2 * (d : ℝ) * T : ℝ) : ℂ))‖ = 2 * (d : ℝ) * T :=
    Complex.norm_of_nonneg (le_of_lt hden_pos)
  have hρ_le_T : ρ ≤ (d : ℝ) * T * base / 2 := by
    dsimp [ρ, ρT]
    exact min_le_left _ _
  have hρ_le_S : ρ ≤ base / 2 := by
    dsimp [ρ, ρS]
    exact min_le_right _ _
  have hsmall_time :
      |(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).re| <
        base / 4 := by
    calc
      |(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).re|
          ≤ ‖ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))‖ :=
            Complex.abs_re_le_norm _
      _ = ‖ζ 0‖ / (2 * (d : ℝ) * T) := by
          rw [norm_div, hnorm_den]
      _ < ρ / (2 * (d : ℝ) * T) :=
          div_lt_div_of_pos_right (hζ 0) hden_pos
      _ ≤ ((d : ℝ) * T * base / 2) / (2 * (d : ℝ) * T) :=
          div_le_div_of_nonneg_right hρ_le_T (le_of_lt hden_pos)
      _ = base / 4 := by
          field_simp [ne_of_gt hT, ne_of_gt hd_pos]
          ring
  have hsmall_spatial :
      ∀ j : Fin d, |((ζ (Fin.succ j)).re)| / 2 < base / 4 := by
    intro j
    calc
      |((ζ (Fin.succ j)).re)| / 2
          ≤ ‖ζ (Fin.succ j)‖ / 2 := by
            exact div_le_div_of_nonneg_right
              (Complex.abs_re_le_norm (ζ (Fin.succ j))) (by norm_num)
      _ < ρ / 2 := div_lt_div_of_pos_right (hζ (Fin.succ j)) (by norm_num)
      _ ≤ (base / 2) / 2 :=
          div_le_div_of_nonneg_right hρ_le_S (by norm_num)
      _ = base / 4 := by ring
  intro a
  exact
    osiiAxisPairCoeff_re_pos_of_small_perturbation
      (d := d) T hT ξ hξ0 ζ
      (by simpa [base] using hsmall_time)
      (by
        intro j
        simpa [base] using hsmall_spatial j)
      a

/-- Local-radius narrow-sector form of the general-`d` axis-pair Lemma 5.1
coefficient estimate. -/
theorem osiiAxisPair_exists_coord_radius_coeff_narrowSector
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ζ : Fin (d + 1) → ℂ,
        (∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ) →
          osiiAxisPairCoeffMap T ξ ζ ∈
            osiiAxisPairNarrowSector (d := d) η := by
  classical
  let base : ℝ := ξ 0 / (4 * (d : ℝ) * T)
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have hbase : 0 < base := by
    dsimp [base]
    positivity
  let ρT : ℝ := (d : ℝ) * T * base / 2
  let ρS : ℝ := base / 2
  let ρTi : ℝ := (d : ℝ) * T * η * base / 2
  let ρSi : ℝ := η * base / 2
  let ρ : ℝ := min (min ρT ρS) (min ρTi ρSi)
  have hρpos : 0 < ρ := by
    dsimp [ρ, ρT, ρS, ρTi, ρSi]
    exact lt_min
      (lt_min (by positivity) (by positivity))
      (lt_min (by positivity) (by positivity))
  refine ⟨ρ, hρpos, ?_⟩
  intro ζ hζ
  have hden_pos : 0 < 2 * (d : ℝ) * T := by positivity
  have hnorm_den : ‖(((2 * (d : ℝ) * T : ℝ) : ℂ))‖ = 2 * (d : ℝ) * T :=
    Complex.norm_of_nonneg (le_of_lt hden_pos)
  have hρ_le_T : ρ ≤ (d : ℝ) * T * base / 2 := by
    dsimp [ρ, ρT, ρS]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ_le_S : ρ ≤ base / 2 := by
    dsimp [ρ, ρT, ρS]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ_le_Tη : ρ ≤ (d : ℝ) * T * η * base / 2 := by
    dsimp [ρ, ρTi, ρSi]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_le_ηS : ρ ≤ η * base / 2 := by
    dsimp [ρ, ρTi, ρSi]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hsmall_time_re :
      |(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).re| <
        base / 4 := by
    calc
      |(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).re|
          ≤ ‖ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))‖ :=
            Complex.abs_re_le_norm _
      _ = ‖ζ 0‖ / (2 * (d : ℝ) * T) := by
          rw [norm_div, hnorm_den]
      _ < ρ / (2 * (d : ℝ) * T) :=
          div_lt_div_of_pos_right (hζ 0) hden_pos
      _ ≤ ((d : ℝ) * T * base / 2) / (2 * (d : ℝ) * T) :=
          div_le_div_of_nonneg_right hρ_le_T (le_of_lt hden_pos)
      _ = base / 4 := by
          field_simp [ne_of_gt hT, ne_of_gt hd_pos]
          ring
  have hsmall_time_im :
      |(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).im| <
        η * base / 4 := by
    calc
      |(ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))).im|
          ≤ ‖ζ 0 / (((2 * (d : ℝ) * T : ℝ) : ℂ))‖ :=
            Complex.abs_im_le_norm _
      _ = ‖ζ 0‖ / (2 * (d : ℝ) * T) := by
          rw [norm_div, hnorm_den]
      _ < ρ / (2 * (d : ℝ) * T) :=
          div_lt_div_of_pos_right (hζ 0) hden_pos
      _ ≤ ((d : ℝ) * T * η * base / 2) / (2 * (d : ℝ) * T) :=
          div_le_div_of_nonneg_right hρ_le_Tη (le_of_lt hden_pos)
      _ = η * base / 4 := by
          field_simp [ne_of_gt hT, ne_of_gt hd_pos]
          ring
  have hsmall_spatial_re :
      ∀ j : Fin d, |((ζ (Fin.succ j)).re)| / 2 < base / 4 := by
    intro j
    calc
      |((ζ (Fin.succ j)).re)| / 2
          ≤ ‖ζ (Fin.succ j)‖ / 2 := by
            exact div_le_div_of_nonneg_right
              (Complex.abs_re_le_norm (ζ (Fin.succ j))) (by norm_num)
      _ < ρ / 2 := div_lt_div_of_pos_right (hζ (Fin.succ j)) (by norm_num)
      _ ≤ (base / 2) / 2 :=
          div_le_div_of_nonneg_right hρ_le_S (by norm_num)
      _ = base / 4 := by ring
  have hsmall_spatial_im :
      ∀ j : Fin d, |((ζ (Fin.succ j)).im)| / 2 < η * base / 4 := by
    intro j
    calc
      |((ζ (Fin.succ j)).im)| / 2
          ≤ ‖ζ (Fin.succ j)‖ / 2 := by
            exact div_le_div_of_nonneg_right
              (Complex.abs_im_le_norm (ζ (Fin.succ j))) (by norm_num)
      _ < ρ / 2 := div_lt_div_of_pos_right (hζ (Fin.succ j)) (by norm_num)
      _ ≤ (η * base / 2) / 2 :=
          div_le_div_of_nonneg_right hρ_le_ηS (by norm_num)
      _ = η * base / 4 := by ring
  exact
    osiiAxisPairCoeff_mem_narrowSector_of_small_perturbation
      (d := d) T hT ξ hξ0 ζ η hη
      (by simpa [base] using hsmall_time_re)
      (by
        intro j
        simpa [base] using hsmall_spatial_re j)
      (by simpa [base] using hsmall_time_im)
      (by
        intro j
        simpa [base] using hsmall_spatial_im j)

/-- Pull back a holomorphic coefficient representative through the general-`d`
axis-pair coefficient map on a sufficiently small coordinate polydisc. -/
theorem osiiAxisPair_local_polydisc_extension_differentiableOn
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (F : (osiiAxisPairIndex d → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (osiiAxisPairRightHalfPlane (d := d))) :
    ∃ ρ : ℝ, 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ =>
          F (osiiAxisPairCoeffMap T ξ ζ))
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} := by
  rcases osiiAxisPair_exists_coord_radius_coeff_rightHalfPlane
      (d := d) T hT ξ hξ0 with
    ⟨ρ, hρpos, hρ⟩
  refine ⟨ρ, hρpos, ?_⟩
  let polydisc : Set (Fin (d + 1) → ℂ) := {ζ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ}
  have hcoeff :
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ => osiiAxisPairCoeffMap T ξ ζ)
        polydisc := by
    have hcoeff_global :
        Differentiable ℂ
          (fun ζ : Fin (d + 1) → ℂ => osiiAxisPairCoeffMap T ξ ζ) := by
      rw [differentiable_pi]
      intro a
      rcases a with ⟨j, b⟩
      cases b <;>
        simp [osiiAxisPairCoeffMap, osiiAxisPairCoeff] <;>
        fun_prop
    exact hcoeff_global.differentiableOn
  have hmaps :
      Set.MapsTo
        (fun ζ : Fin (d + 1) → ℂ => osiiAxisPairCoeffMap T ξ ζ)
        polydisc (osiiAxisPairRightHalfPlane (d := d)) := by
    intro ζ hζ a
    exact hρ ζ hζ a
  simpa [polydisc, Function.comp] using hF.comp hcoeff hmaps

/-- Taking principal logarithms of coefficients in the axis-pair argument-sum
domain lands in the corresponding OS-II log carrier. -/
theorem osiiAxisPair_logCoeffMap_mem_logDomain_of_argSum
    {w : osiiAxisPairIndex d → ℂ}
    (hw : w ∈ osiiAxisPairArgSumDomain (d := d)) :
    (fun a : osiiAxisPairIndex d => Complex.log (w a)) ∈
      osiiAxisPairLogDomain (d := d) := by
  simpa [osiiAxisPairLogDomain, osiiAxisPairArgSumDomain, Complex.log_im] using hw

/-- Log-domain version of the general-`d` axis-pair Lemma 5.1 pullback.

This is the checked bridge from an MZ logarithmic coefficient representative
over the `2d` axis-pair family to a local holomorphic representative in the
physical coordinate perturbation `ζ`. -/
theorem osiiAxisPair_local_polydisc_logDomain_extension_differentiableOn
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (Fintype.card (osiiAxisPairIndex d) : ℝ) * Real.arctan η < Real.pi / 2)
    (Γ : (osiiAxisPairIndex d → ℂ) → ℂ)
    (hΓ : DifferentiableOn ℂ Γ (osiiAxisPairLogDomain (d := d))) :
    ∃ ρ : ℝ, 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ =>
          Γ (fun a : osiiAxisPairIndex d => Complex.log (osiiAxisPairCoeffMap T ξ ζ a)))
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} := by
  classical
  rcases osiiAxisPair_exists_coord_radius_coeff_narrowSector
      (d := d) T hT ξ hξ0 η hη with
    ⟨ρ, hρpos, hρ⟩
  refine ⟨ρ, hρpos, ?_⟩
  let polydisc : Set (Fin (d + 1) → ℂ) := {ζ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ}
  let L : (Fin (d + 1) → ℂ) → osiiAxisPairIndex d → ℂ := fun ζ a =>
    Complex.log (osiiAxisPairCoeffMap T ξ ζ a)
  have hLdiff : DifferentiableOn ℂ L polydisc := by
    rw [differentiableOn_pi]
    intro a ζ hζ
    have hpos : 0 < (osiiAxisPairCoeffMap T ξ ζ a).re :=
      (hρ ζ hζ a).1
    have hslit : osiiAxisPairCoeffMap T ξ ζ a ∈ Complex.slitPlane := by
      simp [Complex.slitPlane]
      left
      exact hpos
    have hcoord_global :
        Differentiable ℂ (fun ζ : Fin (d + 1) → ℂ =>
          osiiAxisPairCoeffMap T ξ ζ a) := by
      rcases a with ⟨j, b⟩
      cases b <;>
        simp [osiiAxisPairCoeffMap, osiiAxisPairCoeff] <;>
        fun_prop
    simpa [L, Function.comp] using
      (Complex.differentiableAt_log hslit).comp_differentiableWithinAt
        ζ (hcoord_global.differentiableAt.differentiableWithinAt)
  have hmaps :
      Set.MapsTo L polydisc (osiiAxisPairLogDomain (d := d)) := by
    intro ζ hζ
    exact osiiAxisPair_logCoeffMap_mem_logDomain_of_argSum
      ((osiiAxisPair_narrowSector_subset_argSumDomain
          (d := d) hηsum) (hρ ζ hζ))
  simpa [polydisc, L, Function.comp] using hΓ.comp hLdiff hmaps

end OSReconstruction
