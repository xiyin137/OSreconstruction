import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Segment

/-!
# BEG Trigonometric Estimates

Small trigonometric lemmas for the Bros-Epstein-Glaser path analysis.

The current use case is the semisimple/rotation case in the `R -> E`
translation-invariance lane, where one needs positivity of a sinusoidal factor
along a canonical path.
-/

open Real Set

noncomputable section

namespace OSReconstruction

/-- Phase decomposition for a positive cosine coefficient. -/
theorem phase_decomp (p q : ℝ) (hq : 0 < q) (θ : ℝ) :
    q * cos θ + p * sin θ =
      Real.sqrt (p ^ 2 + q ^ 2) * cos (θ - arctan (p / q)) := by
  set R := Real.sqrt (p ^ 2 + q ^ 2)
  set ψ := arctan (p / q)
  have hR_pos : 0 < R := sqrt_pos_of_pos (by positivity)
  have hsqrt_rw : Real.sqrt (1 + (p / q) ^ 2) = R / q := by
    have h1 : 1 + (p / q) ^ 2 = (p ^ 2 + q ^ 2) / q ^ 2 := by
      field_simp
      ring
    rw [h1, show (p ^ 2 + q ^ 2) / q ^ 2 = (R / q) ^ 2 from by
      rw [div_pow]
      congr 1
      exact (Real.sq_sqrt (by positivity)).symm]
    exact Real.sqrt_sq (div_nonneg (le_of_lt hR_pos) (le_of_lt hq))
  have hcψ : cos ψ = q / R := by
    rw [cos_arctan, hsqrt_rw]
    field_simp
  have hsψ : sin ψ = p / R := by
    rw [sin_arctan, hsqrt_rw]
    field_simp
  rw [cos_sub, hcψ, hsψ]
  field_simp

/-- The core BEG Case 2 positivity estimate. -/
theorem sinusoidal_pos_of_endpoints_pos
    (p q β : ℝ) (hq : 0 < q) (hend : q * cos β + p * sin β > 0)
    (hβ : |β| ≤ π) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    q * cos (β * t) + p * sin (β * t) > 0 := by
  set R := Real.sqrt (p ^ 2 + q ^ 2)
  set ψ := arctan (p / q)
  have hR_pos : 0 < R := sqrt_pos_of_pos (by positivity)
  rw [phase_decomp p q hq] at hend ⊢
  change 0 < R * cos (β - ψ) at hend
  have hcos_end : 0 < cos (β - ψ) := by
    exact (mul_pos_iff.mp hend).elim (fun h => h.2)
      (fun h => absurd h.1 (not_lt.mpr hR_pos.le))
  have hψ_lo : -(π / 2) < ψ := neg_pi_div_two_lt_arctan _
  have hψ_hi : ψ < π / 2 := arctan_lt_pi_div_two _
  have hβψ_range : β - ψ ∈ Ioo (-(3 * π / 2)) (3 * π / 2) := by
    constructor <;> [nlinarith [abs_le.mp hβ]; nlinarith [abs_le.mp hβ]]
  have hβψ_lo : -(π / 2) < β - ψ := by
    by_contra h
    push_neg at h
    have hle : π / 2 ≤ -(β - ψ) := by linarith
    have hhi : -(β - ψ) ≤ π + π / 2 := by
      have := hβψ_range.1
      linarith
    linarith [cos_nonpos_of_pi_div_two_le_of_le hle hhi, cos_neg (β - ψ)]
  have hβψ_hi : β - ψ < π / 2 := by
    by_contra h
    push_neg at h
    have hhi : β - ψ ≤ π + π / 2 := by
      have := hβψ_range.2
      linarith
    linarith [cos_nonpos_of_pi_div_two_le_of_le h hhi]
  have hleft : -ψ ∈ Ioo (-(π / 2)) (π / 2) := by
    constructor <;> linarith
  have hright : β - ψ ∈ Ioo (-(π / 2)) (π / 2) := ⟨hβψ_lo, hβψ_hi⟩
  have hseg : β * t - ψ ∈ segment ℝ (-ψ) (β - ψ) := by
    rw [segment_eq_image_lineMap]
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    simp [AffineMap.lineMap_apply, sub_eq_add_neg]
    ring
  have hmem : β * t - ψ ∈ Ioo (-(π / 2)) (π / 2) := by
    exact (convex_Ioo (-(π / 2)) (π / 2)).segment_subset hleft hright hseg
  exact mul_pos hR_pos (cos_pos_of_mem_Ioo hmem)

end OSReconstruction
