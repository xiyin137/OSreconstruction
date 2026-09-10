/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51CoordinateEstimate
















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

/-- A narrow sector for all axis-pair coefficients.  This is the general-`d`
ratio form of OS II `(5.13)`. -/
def osiiAxisPairNarrowSector (η : ℝ) :
    Set (osiiAxisPairIndex d → ℂ) :=
  {w | ∀ a : osiiAxisPairIndex d, 0 < (w a).re ∧ |(w a).im| < η * (w a).re}

/-- The corresponding logarithmic MZ carrier over the axis-pair index family. -/
def osiiAxisPairLogDomain : Set (osiiAxisPairIndex d → ℂ) :=
  {r | ∑ a : osiiAxisPairIndex d, |(r a).im| < Real.pi / 2}

/-- Real embedding in the axis-pair logarithmic coordinates. -/
def osiiAxisPairLogRealEmbed
    (x : osiiAxisPairIndex d → ℝ) :
    osiiAxisPairIndex d → ℂ :=
  fun a => (x a : ℂ)

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

/-- The physical displacement represented by a real axis-pair coefficient
chart. Its time component is the positive common displacement, while its
spatial components are the physical perturbation coordinates. -/
def osiiAxisPairPhysicalShift
    (ξ ζ : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases (ξ 0 / 2 + ζ 0) (fun j => ζ (Fin.succ j))

/-- The real axis-pair coefficient chart represents a physical displacement
which is independent of the auxiliary slope. -/
theorem osiiAxisPairCoeffMap_real_sum_smul_dir
    (T : ℝ) (hT : T ≠ 0)
    (ξ ζ : Fin (d + 1) → ℝ) :
    (∑ a : osiiAxisPairIndex d,
        (osiiAxisPairCoeffMap T ξ
          (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re •
            osiiAxisPairDir (d := d) T a) =
      osiiAxisPairPhysicalShift ξ ζ := by
  funext ν
  refine Fin.cases ?_ ?_ ν
  · have hlinear :=
      congrArg Complex.re
        (osiiAxisPairCoeff_linear_identity
          (d := d) T hT ξ
            (fun μ : Fin (d + 1) => (ζ μ : ℂ)) 0)
    simp [osiiAxisPairPhysicalShift, osiiAxisPairXiHat,
      osiiAxisPairCoeffMap, Complex.mul_re] at hlinear ⊢
    linarith
  · intro j
    have hlinear :=
      congrArg Complex.re
        (osiiAxisPairCoeff_linear_identity
          (d := d) T hT ξ
            (fun μ : Fin (d + 1) => (ζ μ : ℂ)) (Fin.succ j))
    simpa [osiiAxisPairPhysicalShift, osiiAxisPairXiHat,
      osiiAxisPairCoeffMap, Complex.mul_re] using hlinear

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

end OSReconstruction
