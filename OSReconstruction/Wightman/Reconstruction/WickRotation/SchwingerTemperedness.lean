/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslation
import OSReconstruction.Wightman.Reconstruction.UniversalProjection
import OSReconstruction.ComplexLieGroups.D1OrbitSet
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.JostWitnessGeneralSigma
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import OSReconstruction.SCV.VladimirovTillmann

/-!
# Schwinger Temperedness and Zero-Diagonal Pairing

This file isolates the E0 / temperedness front of the `R -> E` direction.
It is split out of `SchwingerAxioms.lean` so the remaining honest analytic
gaps around zero-diagonal pairing and continuity do not live in a >3000-line
monolith.

The key sanity-check theorem in this file is
`kernel_mul_zeroDiagonal_integrable_of_ae_infDist_mul_pow_le_polynomial`:
if a Euclidean kernel has only finite-order coincidence singularities and at
most polynomial growth at infinity, then it pairs integrably with every
`ZeroDiagonalSchwartz` test function. This is the abstract reason the corrected
OS-I temperedness surface is `°S` rather than full Schwartz space.
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]
/-- Wick rotation of a single point preserves each component norm:
    `‖wickRotatePoint x i‖ = ‖x i‖` for each i.
    - i = 0: `‖I * ↑(x 0)‖ = |x 0|` since `‖I‖ = 1`
    - i > 0: `‖↑(x i)‖ = |x i|` since `Complex.norm_real` -/
theorem wickRotatePoint_component_norm_eq {d : ℕ}
    (x : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    ‖wickRotatePoint x i‖ = ‖x i‖ := by
  simp only [wickRotatePoint]; split_ifs with h
  · subst h; rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
  · rw [Complex.norm_real]

/-- The norm of a Wick-rotated Euclidean configuration is at most the original norm.

    Since `‖wickRotatePoint(x k) i‖ = ‖x k i‖` componentwise, and the Pi norm
    is the sup over all components, the Wick-rotated norm equals the original.
    We prove ≤ which suffices for the polynomial growth argument. -/
theorem wickRotate_norm_le {d n : ℕ}
    (x : Fin n → Fin (d + 1) → ℝ) :
    ‖fun k => wickRotatePoint (x k)‖ ≤ ‖x‖ := by
  -- Both norms are Pi sup norms. We bound each component.
  -- Step 1: ∀ k i, ‖wickRotatePoint(x k) i‖ ≤ ‖x‖
  have hcomp : ∀ (k : Fin n) (i : Fin (d + 1)),
      ‖wickRotatePoint (x k) i‖ ≤ ‖x‖ := by
    intro k i
    rw [wickRotatePoint_component_norm_eq]
    exact (norm_le_pi_norm (x k) i).trans (norm_le_pi_norm x k)
  -- Step 2: ∀ k, ‖wickRotatePoint(x k)‖ ≤ ‖x‖
  have hk : ∀ k : Fin n, ‖wickRotatePoint (x k)‖ ≤ ‖x‖ := by
    intro k
    -- Component bound → pi norm bound (manual, to avoid norm instance issues)
    simp only [Pi.norm_def, Pi.nnnorm_def]
    rw [NNReal.coe_le_coe]
    apply Finset.sup_le
    intro i _
    have := hcomp k i
    -- ‖wickRotatePoint(x k) i‖ ≤ ‖x‖ is in terms of ℂ norm and ℝ nested pi norm
    -- We need: ‖wickRotatePoint(x k) i‖₊ ≤ sup_j sup_μ ‖x j μ‖₊
    simp only [Pi.norm_def, Pi.nnnorm_def] at this
    exact_mod_cast this
  -- Step 3: ‖fun k => wickRotatePoint(x k)‖ ≤ ‖x‖
  simp only [Pi.norm_def, Pi.nnnorm_def]
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro k _
  have := hk k
  simp only [Pi.norm_def, Pi.nnnorm_def] at this
  exact_mod_cast this

/-- A consecutive difference is controlled by twice the ambient sup norm. -/
private theorem abs_consecutiveDiff_le_two_norm {d n : ℕ}
    (x : NPointDomain d n) (k : Fin n) (μ : Fin (d + 1)) :
    |BHW.consecutiveDiff x k μ| ≤ 2 * ‖x‖ := by
  by_cases hk : (k : ℕ) = 0
  · simp [BHW.consecutiveDiff, hk]
    calc
      |x k μ| = ‖x k μ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖x k‖ := norm_le_pi_norm (x k) μ
      _ ≤ ‖x‖ := norm_le_pi_norm x k
      _ ≤ 2 * ‖x‖ := by nlinarith [norm_nonneg x]
  · let km1 : Fin n := ⟨k.val - 1, by omega⟩
    calc
      |BHW.consecutiveDiff x k μ| = |x k μ - x km1 μ| := by
        simp [BHW.consecutiveDiff, hk, km1]
      _ ≤ |x k μ| + |x km1 μ| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (x k μ) (-x km1 μ)
      _ ≤ ‖x‖ + ‖x‖ := by
        gcongr
        · calc
            |x k μ| = ‖x k μ‖ := by rw [Real.norm_eq_abs]
            _ ≤ ‖x k‖ := norm_le_pi_norm (x k) μ
            _ ≤ ‖x‖ := norm_le_pi_norm x k
        · calc
            |x km1 μ| = ‖x km1 μ‖ := by rw [Real.norm_eq_abs]
            _ ≤ ‖x km1‖ := norm_le_pi_norm (x km1) μ
            _ ≤ ‖x‖ := norm_le_pi_norm x km1
      _ = 2 * ‖x‖ := by ring

/-- A perturbation of a pure time-like vector remains in the open forward cone. -/
private theorem inOpenForwardCone_of_perturbation {d : ℕ} [NeZero d]
    (t : ℝ) (ht : 0 < t) (w : Fin (d + 1) → ℝ)
    (hw : ∀ μ, |w μ - (if μ = 0 then t else 0)| < t / (d + 2 : ℝ)) :
    InOpenForwardCone d w := by
  have hw0 : t * (d + 1 : ℝ) / (d + 2 : ℝ) < w 0 := by
    have h0 := hw 0
    simp at h0
    have h0' := abs_lt.mp h0
    have hdpos : (0 : ℝ) < d + 2 := by positivity
    have h0l : -(t / (d + 2 : ℝ)) < w 0 - t := h0'.1
    have htmp : t - t / (d + 2 : ℝ) < w 0 := by linarith
    have heq : t - t / (d + 2 : ℝ) = t * (d + 1 : ℝ) / (d + 2 : ℝ) := by
      field_simp [hdpos.ne']
      ring
    simpa [heq] using htmp
  have hw0_pos : 0 < w 0 := by
    have : 0 < t * (d + 1 : ℝ) / (d + 2 : ℝ) := by positivity
    linarith
  have hspatial : ∀ i : Fin d, (w i.succ) ^ 2 < (t / (d + 2 : ℝ)) ^ 2 := by
    intro i
    have hi := hw i.succ
    simp only [Fin.succ_ne_zero, if_false, sub_zero] at hi
    have hi' := abs_lt.mp hi
    nlinarith
  have hspatial_sum : MinkowskiSpace.spatialNormSq d w ≤ (d : ℝ) * (t / (d + 2 : ℝ)) ^ 2 := by
    unfold MinkowskiSpace.spatialNormSq
    calc
      ∑ i : Fin d, (w i.succ) ^ 2 ≤ ∑ _i : Fin d, (t / (d + 2 : ℝ)) ^ 2 := by
        exact Finset.sum_le_sum (fun i _ => le_of_lt (hspatial i))
      _ = (d : ℝ) * (t / (d + 2 : ℝ)) ^ 2 := by
        simp [Finset.sum_const]
  refine ⟨hw0_pos, ?_⟩
  rw [MinkowskiSpace.minkowskiNormSq_decomp]
  have hmain : MinkowskiSpace.spatialNormSq d w < (w 0) ^ 2 := by
    calc
      MinkowskiSpace.spatialNormSq d w ≤ (d : ℝ) * (t / (d + 2 : ℝ)) ^ 2 := hspatial_sum
      _ < (t * (d + 1 : ℝ) / (d + 2 : ℝ)) ^ 2 := by
        have hdlt : (d : ℝ) < (d + 1 : ℝ) ^ 2 := by
          nlinarith
        have hsqpos : 0 < (t / (d + 2 : ℝ)) ^ 2 := by positivity
        have heq :
            (t * (d + 1 : ℝ) / (d + 2 : ℝ)) ^ 2 =
              ((d + 1 : ℝ) ^ 2) * (t / (d + 2 : ℝ)) ^ 2 := by
          ring
        rw [heq]
        nlinarith
      _ < (w 0) ^ 2 := by
        have haux : 0 ≤ t * (d + 1 : ℝ) / (d + 2 : ℝ) := by positivity
        nlinarith [hw0, hw0_pos, haux]
  have := hmain
  nlinarith

/-- Pure-time-gap configurations stay a definite distance away from the boundary of
    the absolute forward cone. -/
private theorem infDist_forwardConeAbs_lower_bound {d n : ℕ} [NeZero d] [NeZero n]
    (y : NPointDomain d n) (t_min : ℝ) (ht_pos : 0 < t_min)
    (hy_time : ∀ k : Fin n, t_min ≤ BHW.consecutiveDiff y k 0)
    (hy_space : ∀ k : Fin n, ∀ μ : Fin (d + 1), μ ≠ 0 → BHW.consecutiveDiff y k μ = 0) :
    t_min / (2 * d + 4 : ℝ) ≤ Metric.infDist y (ForwardConeAbs d n)ᶜ := by
  have hcompl_nonempty : (ForwardConeAbs d n)ᶜ.Nonempty := by
    exact ⟨0, fun h => by
      have := h (0 : Fin n)
      simp [InOpenForwardCone] at this⟩
  refine (Metric.le_infDist hcompl_nonempty).2 ?_
  intro u hu
  by_contra hudist
  have hudist' : dist y u < t_min / (2 * d + 4 : ℝ) := by linarith
  have hu_mem : u ∈ ForwardConeAbs d n := by
    intro k
    apply inOpenForwardCone_of_perturbation (t := BHW.consecutiveDiff y k 0)
    · exact lt_of_lt_of_le ht_pos (hy_time k)
    · intro μ
      have hdist_norm : ‖u - y‖ < t_min / (2 * d + 4 : ℝ) := by
        simpa [dist_eq_norm, norm_sub_rev] using hudist'
      have hdiff :
          BHW.consecutiveDiff u k μ - BHW.consecutiveDiff y k μ =
            BHW.consecutiveDiff (u - y) k μ := by
        by_cases hk : (k : ℕ) = 0
        · simp [BHW.consecutiveDiff, hk, Pi.sub_apply]
        · simp [BHW.consecutiveDiff, hk, Pi.sub_apply, sub_eq_add_neg]
          abel
      have hcd :
          |BHW.consecutiveDiff u k μ - BHW.consecutiveDiff y k μ| ≤ 2 * ‖u - y‖ := by
        rw [hdiff]
        exact abs_consecutiveDiff_le_two_norm (u - y) k μ
      have hcd' :
          |BHW.consecutiveDiff u k μ - BHW.consecutiveDiff y k μ| <
            BHW.consecutiveDiff y k 0 / (d + 2 : ℝ) := by
        calc
          |BHW.consecutiveDiff u k μ - BHW.consecutiveDiff y k μ|
            ≤ 2 * ‖u - y‖ := hcd
          _ < 2 * (t_min / (2 * d + 4 : ℝ)) := by
            gcongr
          _ = t_min / (d + 2 : ℝ) := by
            field_simp
            ring
          _ ≤ BHW.consecutiveDiff y k 0 / (d + 2 : ℝ) := by
            have hdpos : (0 : ℝ) < d + 2 := by positivity
            exact (div_le_div_of_nonneg_right (hy_time k) hdpos.le)
      by_cases hμ : μ = 0
      · subst hμ
        by_cases hk : (k : ℕ) = 0
        · simp [BHW.consecutiveDiff, hk] at hcd' ⊢
          exact hcd'
        · simp [BHW.consecutiveDiff, hk] at hcd' ⊢
          exact hcd'
      · have hyμ : BHW.consecutiveDiff y k μ = 0 := hy_space k μ hμ
        by_cases hk : (k : ℕ) = 0
        · have hyμ' : y k μ = 0 := by
            simpa [BHW.consecutiveDiff, hk] using hyμ
          simp [BHW.consecutiveDiff, hk, hμ, hyμ'] at hcd' ⊢
          exact hcd'
        · have hyμ' : y k μ - y ⟨k.val - 1, by omega⟩ μ = 0 := by
            simpa [BHW.consecutiveDiff, hk] using hyμ
          simp [BHW.consecutiveDiff, hk, hμ, hyμ'] at hcd' ⊢
          exact hcd'
  exact hu hu_mem

omit [NeZero d] in
private lemma abs_matrix_le_one {d : ℕ}
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1) (i j : Fin (d + 1)) : |R i j| ≤ 1 := by
  have hRT : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  have hdiag : (R * R.transpose) i i = 1 := by
    rw [hRT]
    simp
  have hrow : (R * R.transpose) i i = ∑ k : Fin (d + 1), R i k ^ 2 := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hs :
      R i j ^ 2 ≤ ∑ k : Fin (d + 1), R i k ^ 2 := by
    exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  rw [← hrow, hdiag] at hs
  have hsq : R i j ^ 2 ≤ 1 := hs
  have hlow : -1 ≤ R i j := by nlinarith [sq_nonneg (R i j), hsq]
  have hhigh : R i j ≤ 1 := by nlinarith [sq_nonneg (R i j), hsq]
  exact abs_le.mpr ⟨hlow, hhigh⟩

omit [NeZero d] in
/-- Orthogonal matrices stretch the Pi sup norm by at most `d + 1`. -/
private theorem norm_mulVec_le_of_orthogonal {d n : ℕ}
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hR : R.transpose * R = 1)
    (x : NPointDomain d n) :
    ‖fun k => R.mulVec (x k)‖ ≤ (d + 1 : ℝ) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  calc
    |(R.mulVec (x k)) i|
      = |∑ j : Fin (d + 1), R i j * x k j| := by simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j : Fin (d + 1), |R i j * x k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin (d + 1), |R i j| * |x k j| := by simp_rw [abs_mul]
    _ ≤ ∑ _j : Fin (d + 1), 1 * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      gcongr
      · exact abs_matrix_le_one R hR i j
      · calc
          |x k j| = ‖x k j‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖x k‖ := norm_le_pi_norm (x k) j
          _ ≤ ‖x‖ := norm_le_pi_norm x k
    _ = (d + 1 : ℝ) * ‖x‖ := by
      simp [Finset.sum_const]

omit [NeZero d] in
private theorem collapse_vt_denominator_algebra
    (C_vt F_norm z_norm x_norm δ Δ c C_z : ℝ) (N_vt q_vt : ℕ)
    (hC_pos : 0 ≤ C_vt) (hc_pos : 0 < c) (hΔ_pos : 0 < Δ) (hδ_pos : 0 < δ)
    (_hCz_pos : 0 ≤ C_z)
    (hF_le : F_norm ≤ C_vt * (1 + z_norm) ^ N_vt * (1 + δ⁻¹) ^ q_vt)
    (hδ_bound : c * Δ ≤ δ)
    (hz_bound : z_norm ≤ C_z * (1 + x_norm))
    (hΔ_le : Δ ≤ 2 * x_norm)
    (hx_nonneg : 0 ≤ x_norm) (hz_nonneg : 0 ≤ z_norm) :
    F_norm * Δ ^ (q_vt + 1) ≤
      (C_vt * (2 * max 1 C_z) ^ N_vt * (max 2 c⁻¹) ^ q_vt * 2 + 1) *
        (1 + x_norm) ^ (N_vt + q_vt + 1) := by
  let K1 : ℝ := max 2 c⁻¹
  have hK1_pos : 0 < K1 := by
    dsimp [K1]
    exact (show (0 : ℝ) < 2 by norm_num).trans_le (le_max_left _ _)
  have hterm : (1 + δ⁻¹) * Δ ≤ K1 * (1 + x_norm) := by
    have hδinv : δ⁻¹ ≤ (c * Δ)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (mul_pos hc_pos hΔ_pos) hδ_bound
    have hmul : (c * Δ)⁻¹ * Δ = c⁻¹ := by
      field_simp [hc_pos.ne', hΔ_pos.ne']
    calc
      (1 + δ⁻¹) * Δ = Δ + δ⁻¹ * Δ := by ring
      _ ≤ Δ + (c * Δ)⁻¹ * Δ := by gcongr
      _ = Δ + c⁻¹ := by rw [hmul]
      _ ≤ 2 * x_norm + c⁻¹ := by gcongr
      _ ≤ K1 * x_norm + K1 * 1 := by
        have h2 : (2 : ℝ) ≤ K1 := le_max_left _ _
        have hcinv : c⁻¹ ≤ K1 := le_max_right _ _
        nlinarith
      _ = K1 * (1 + x_norm) := by ring
  have hz : 1 + z_norm ≤ (2 * max 1 C_z) * (1 + x_norm) := by
    have hmax1 : (1 : ℝ) ≤ max 1 C_z := le_max_left _ _
    have hCz_le : C_z ≤ max 1 C_z := le_max_right _ _
    have hx1_nonneg : 0 ≤ 1 + x_norm := by linarith
    calc
      1 + z_norm ≤ 1 + C_z * (1 + x_norm) := by linarith
      _ ≤ max 1 C_z * (1 + x_norm) + max 1 C_z * (1 + x_norm) := by
        nlinarith
      _ = (2 * max 1 C_z) * (1 + x_norm) := by ring
  let C_base : ℝ := C_vt * (2 * max 1 C_z) ^ N_vt * K1 ^ q_vt * 2
  calc
    F_norm * Δ ^ (q_vt + 1) = F_norm * (Δ ^ q_vt * Δ) := by
      rw [pow_succ']
      ring
    _ ≤ (C_vt * (1 + z_norm) ^ N_vt * (1 + δ⁻¹) ^ q_vt) * (Δ ^ q_vt * Δ) := by
      gcongr
    _ = C_vt * (1 + z_norm) ^ N_vt * (((1 + δ⁻¹) * Δ) ^ q_vt) * Δ := by
      rw [mul_pow]
      ring
    _ ≤ C_vt * (((2 * max 1 C_z) * (1 + x_norm)) ^ N_vt) * ((K1 * (1 + x_norm)) ^ q_vt) *
          (2 * (1 + x_norm)) := by
      have hpow_z :
          (1 + z_norm) ^ N_vt ≤ ((2 * max 1 C_z) * (1 + x_norm)) ^ N_vt := by
        exact pow_le_pow_left₀ (by linarith) hz N_vt
      have hpow_term :
          (((1 + δ⁻¹) * Δ) ^ q_vt) ≤ (K1 * (1 + x_norm)) ^ q_vt := by
        exact pow_le_pow_left₀ (by positivity) hterm q_vt
      have hΔ_one : Δ ≤ 2 * (1 + x_norm) := by
        nlinarith
      gcongr
    _ = C_base * ((1 + x_norm) ^ N_vt * (1 + x_norm) ^ q_vt * (1 + x_norm)) := by
      dsimp [C_base]
      rw [show (((2 * max 1 C_z) * (1 + x_norm)) ^ N_vt) =
          (2 * max 1 C_z) ^ N_vt * (1 + x_norm) ^ N_vt by rw [mul_pow]]
      rw [show ((K1 * (1 + x_norm)) ^ q_vt) =
          K1 ^ q_vt * (1 + x_norm) ^ q_vt by rw [mul_pow]]
      ac_rfl
    _ = C_base * (1 + x_norm) ^ (N_vt + q_vt + 1) := by
      congr 1
      rw [show N_vt + q_vt + 1 = N_vt + (q_vt + 1) by omega, pow_add, pow_succ']
      ac_rfl
    _ ≤ (C_base + 1) * (1 + x_norm) ^ (N_vt + q_vt + 1) := by
      gcongr
      linarith
    _ = (C_vt * (2 * max 1 C_z) ^ N_vt * (max 2 c⁻¹) ^ q_vt * 2 + 1) *
          (1 + x_norm) ^ (N_vt + q_vt + 1) := by
      rfl

/-- Compact-support cancellation theorem for zero-diagonal test functions.

    This isolates the measure-theoretic heart of the corrected OS-I pairing:
    if a kernel `K` has locally bounded product with a sufficiently high power of
    `dist(x, CoincidenceLocus)`, then every compactly supported
    `f ∈ ZeroDiagonalSchwartz` pairs integrably with `K`.

    What remains open for the BHW kernel is therefore not the cancellation step,
    but the analytic theorem asserting such a weighted local bound near the
    Euclidean coincidence strata. -/
theorem kernel_mul_zeroDiagonal_integrable_of_hasCompactSupport_of_infDist_mul_pow_bounded
    {d n : ℕ} [NeZero d] (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (f : ZeroDiagonalSchwartz d n)
    (hcompact : HasCompactSupport ((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (m : ℕ) (hcoin : (CoincidenceLocus d n).Nonempty)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ tsupport (((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ)),
        ‖K x‖ * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) ≤ C) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
      MeasureTheory.volume := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  let S : Set (NPointDomain d n) :=
    tsupport (((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ))
  have hS_compact : IsCompact S := by
    simpa [S] using hcompact.isCompact
  have hS_meas : MeasurableSet S := hS_compact.isClosed.measurableSet
  obtain ⟨Cf, hCf_nonneg, hCf⟩ :=
    VanishesToInfiniteOrderOnCoincidence.norm_le_infDist_CoincidenceLocus_pow_succ_on_isCompact
      (f := f.1) f.2 hS_compact m hcoin
  obtain ⟨CK, hCK_nonneg, hCK⟩ := hbound
  have h_on_S :
      ∀ x ∈ S,
        ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ ≤ CK * Cf := by
    intro x hx
    calc
      ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ =
          ‖K x‖ * ‖(f.1 : NPointDomain d n → ℂ) x‖ := norm_mul _ _
      _ ≤ ‖K x‖ * (Cf * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1)) := by
          gcongr
          exact hCf x hx
      _ = Cf * (‖K x‖ * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1)) := by ring
      _ ≤ Cf * CK := by
          exact mul_le_mul_of_nonneg_left (hCK x hx) hCf_nonneg
      _ = CK * Cf := by ring
  have h_int_on_S :
      MeasureTheory.IntegrableOn
        (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
        S MeasureTheory.volume := by
    refine MeasureTheory.IntegrableOn.of_bound hS_compact.measure_lt_top
      ((hK_meas.mul (f.1.integrable.aestronglyMeasurable)).restrict)
      (CK * Cf) ?_
    exact (MeasureTheory.ae_restrict_iff' hS_meas).2 <| Filter.Eventually.of_forall h_on_S
  have h_zero_off_S :
      Set.EqOn
        (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
        (fun _ : NPointDomain d n => (0 : ℂ))
        Sᶜ := by
    intro x hx
    have hx_support : x ∉ Function.support ((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
      intro hx'
      exact hx (subset_tsupport _ hx')
    have hfx : ((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ) x = 0 := by
      by_contra hne
      exact hx_support (by simp [Function.mem_support, hne])
    simp [hfx]
  have h_int_on_Sc :
      MeasureTheory.IntegrableOn
        (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
        Sᶜ MeasureTheory.volume := by
    exact MeasureTheory.integrableOn_zero.congr_fun h_zero_off_S.symm hS_meas.compl
  have h_int_univ :
      MeasureTheory.IntegrableOn
        (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
        Set.univ MeasureTheory.volume := by
    simpa [S] using h_int_on_S.union h_int_on_Sc
  exact (MeasureTheory.integrableOn_univ.mp h_int_univ)

/-- Global reduction theorem for the corrected E0 lane.

    If a measurable kernel has at most polynomial growth at infinity after being
    weighted by a sufficiently high power of `dist(x, CoincidenceLocus)`, then it
    pairs integrably with every zero-diagonal Schwartz test function. This is the
    exact combination of the two genuine ingredients now available on the test-function
    side:

    1. infinite-order vanishing at the coincidence locus, and
    2. Schwartz decay at spatial infinity.

    This is the abstract sanity check behind the corrected OS-I axiom surface:
    kernels that are analytic away from coincidence points and no worse than
    inverse-power singular along the diagonal still define the honest Euclidean
    pairing on `ZeroDiagonalSchwartz`.

    For the actual BHW kernel, the remaining gap is therefore precisely the analytic
    theorem asserting the displayed weighted polynomial bound. -/
theorem kernel_mul_zeroDiagonal_integrable_of_ae_infDist_mul_pow_le_polynomial
    {d n : ℕ} [NeZero d] (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (f : ZeroDiagonalSchwartz d n)
    (m M : ℕ) (hcoin : (CoincidenceLocus d n).Nonempty)
    (C_bd : ℝ) (hC : 0 ≤ C_bd)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) ≤
        C_bd * (1 + ‖x‖) ^ M) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
      MeasureTheory.volume := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  set D := Module.finrank ℝ (NPointDomain d n)
  have hD_lt : (D : ℝ) < ↑(D + 1) := by
    push_cast
    linarith
  have htail_int :
      MeasureTheory.Integrable
        (fun x : NPointDomain d n => (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)))
        MeasureTheory.volume :=
    integrable_one_add_norm hD_lt
  obtain ⟨Cf, hCf_nonneg, hCf⟩ :=
    VanishesToInfiniteOrderOnCoincidence.one_add_norm_pow_mul_norm_le_infDist_CoincidenceLocus_pow_succ
      (f := f.1) f.2 (M + D + 1) m hcoin
  have hdom_int :
      MeasureTheory.Integrable
        (fun x : NPointDomain d n => C_bd * Cf * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)))
        MeasureTheory.volume :=
    htail_int.const_mul (C_bd * Cf)
  apply hdom_int.mono' (hK_meas.mul f.1.integrable.aestronglyMeasurable)
  filter_upwards [hK_bound] with x hx
  let δ : ℝ := Metric.infDist x (CoincidenceLocus d n)
  have hδ_nonneg : 0 ≤ δ := Metric.infDist_nonneg
  have hf_weighted :
      (1 + ‖x‖) ^ (M + D + 1) * ‖(f.1 : NPointDomain d n → ℂ) x‖ ≤
        Cf * δ ^ (m + 1) := by
    simpa [δ] using hCf x
  by_cases hδ : δ = 0
  · have hprod_nonneg :
        0 ≤ (1 + ‖x‖) ^ (M + D + 1) * ‖(f.1 : NPointDomain d n → ℂ) x‖ := by
      positivity
    have hprod_zero :
        (1 + ‖x‖) ^ (M + D + 1) * ‖(f.1 : NPointDomain d n → ℂ) x‖ = 0 :=
      le_antisymm (by simpa [hδ] using hf_weighted) hprod_nonneg
    have hpow_ne : (1 + ‖x‖) ^ (M + D + 1) ≠ 0 := by positivity
    have hnorm_zero : ‖(f.1 : NPointDomain d n → ℂ) x‖ = 0 := by
      exact (mul_eq_zero.mp hprod_zero).resolve_left hpow_ne
    have hfx : (f.1 : NPointDomain d n → ℂ) x = 0 := norm_eq_zero.mp hnorm_zero
    calc
      ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ = 0 := by simp [hfx]
      _ ≤ C_bd * Cf * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) := by
        have htail_nonneg : 0 ≤ (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) := by
          apply Real.rpow_nonneg
          positivity
        exact mul_nonneg (mul_nonneg hC hCf_nonneg) htail_nonneg
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (Ne.symm hδ)
    have hδpow_pos : 0 < δ ^ (m + 1) := pow_pos hδ_pos _
    have hpow_pos : 0 < (1 + ‖x‖) ^ (M + D + 1) := by positivity
    have hK' :
        ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ M / δ ^ (m + 1) := by
      rw [le_div_iff₀ hδpow_pos]
      simpa [δ, mul_comm, mul_left_comm, mul_assoc] using hx
    have hF' :
        ‖(f.1 : NPointDomain d n → ℂ) x‖ ≤
          Cf * δ ^ (m + 1) / (1 + ‖x‖) ^ (M + D + 1) := by
      rw [le_div_iff₀ hpow_pos]
      simpa [δ, mul_comm, mul_left_comm, mul_assoc] using hf_weighted
    have hpow_split :
        (1 + ‖x‖) ^ (M + D + 1) = (1 + ‖x‖) ^ M * (1 + ‖x‖) ^ (D + 1) := by
      rw [show M + D + 1 = M + (D + 1) by omega, pow_add]
    calc
      ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ =
          ‖K x‖ * ‖(f.1 : NPointDomain d n → ℂ) x‖ := norm_mul _ _
      _ ≤
          (C_bd * (1 + ‖x‖) ^ M / δ ^ (m + 1)) *
            (Cf * δ ^ (m + 1) / (1 + ‖x‖) ^ (M + D + 1)) := by
              gcongr
      _ = C_bd * Cf * ((1 + ‖x‖) ^ (D + 1))⁻¹ := by
          rw [hpow_split]
          have hδpow_ne : δ ^ (m + 1) ≠ 0 := by positivity
          have hpowM_ne : (1 + ‖x‖) ^ M ≠ 0 := by positivity
          have hpowD_ne : (1 + ‖x‖) ^ (D + 1) ≠ 0 := by positivity
          field_simp [hδpow_ne, hpowM_ne, hpowD_ne]
      _ = C_bd * Cf * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) := by
          rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- **The Wick-rotated BHW kernel is a.e. strongly measurable.**

    The function x ↦ F_ext(Wick(x)) is a.e. strongly measurable on NPointDomain.
    This follows from the fact that F_ext is holomorphic (hence continuous) on the
    permuted extended tube, Wick rotation is continuous, and a.e. Euclidean points
    lie in PET (by `ae_euclidean_points_in_permutedTube`). -/
theorem bhw_euclidean_kernel_measurable {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : NPointDomain d n =>
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)))
      MeasureTheory.volume := by
  -- Strategy: F_ext is continuous on PET (holomorphic ⇒ continuous). Wick is continuous.
  -- The composition is ContinuousOn on S = Wick⁻¹(PET), which is open and has full measure.
  -- ContinuousOn.aestronglyMeasurable gives AEStronglyMeasurable on μ.restrict S.
  -- Since μ(Sᶜ) = 0, piecewise with 0 on Sᶜ gives the result.
  set F_ext := (W_analytic_BHW Wfn n).val
  set wick : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ) :=
    fun x k => wickRotatePoint (x k)
  set S := wick ⁻¹' (PermutedExtendedTube d n)
  -- F_ext is continuous on PET
  have hF_cont : ContinuousOn F_ext (PermutedExtendedTube d n) :=
    (W_analytic_BHW Wfn n).property.1.continuousOn
  -- wickRotatePoint is continuous as a function Fin (d+1) → ℝ → Fin (d+1) → ℂ
  have hwickpt_cont : Continuous (wickRotatePoint (d := d)) := by
    apply continuous_pi; intro μ
    simp only [wickRotatePoint]
    split_ifs
    · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
    · exact Complex.continuous_ofReal.comp (continuous_apply μ)
  -- wick : NPointDomain d n → Fin n → Fin (d+1) → ℂ is continuous
  have hwick_cont : Continuous wick := by
    apply continuous_pi; intro k
    exact hwickpt_cont.comp (continuous_apply k)
  -- PET is open, so S is open and measurable
  have hPET_open : IsOpen (PermutedExtendedTube d n) :=
    BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube
  have hS_open : IsOpen S := hPET_open.preimage hwick_cont
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  -- F_ext ∘ wick is ContinuousOn S
  have hcomp_cont : ContinuousOn (fun x => F_ext (wick x)) S :=
    hF_cont.comp hwick_cont.continuousOn (Set.mapsTo_preimage wick _)
  -- Sᶜ has measure zero (ae_euclidean_points_in_permutedTube)
  have hSc_null : MeasureTheory.volume Sᶜ = 0 :=
    MeasureTheory.mem_ae_iff.mp ae_euclidean_points_in_permutedTube
  -- AEStronglyMeasurable on μ.restrict S
  have h_on_S : MeasureTheory.AEStronglyMeasurable
      (fun x => F_ext (wick x)) (MeasureTheory.volume.restrict S) :=
    hcomp_cont.aestronglyMeasurable hS_meas
  -- Since Sᶜ has measure zero, volume.restrict S = volume
  have hrestr : MeasureTheory.volume.restrict S = MeasureTheory.volume :=
    MeasureTheory.Measure.restrict_eq_self_of_ae_mem
      (MeasureTheory.mem_ae_iff.mpr hSc_null)
  change MeasureTheory.AEStronglyMeasurable (fun x => F_ext (wick x))
    MeasureTheory.volume
  rw [← hrestr]
  exact h_on_S

private theorem measure_timeEq_zero {d n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    MeasureTheory.volume {x : NPointDomain d n | x i 0 = x j 0} = 0 := by
  let L : NPointDomain d n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x i 0 - x j 0
      map_add' := by
        intro x y
        simp
        ring
      map_smul' := by
        intro a x
        simp
        ring }
  have hset :
      {x : NPointDomain d n | x i 0 = x j 0} = (LinearMap.ker L : Set (NPointDomain d n)) := by
    ext x
    simp [L, LinearMap.mem_ker, sub_eq_zero]
  have hker_ne_top : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hzero : L = 0 := LinearMap.ker_eq_top.mp htop
    have hval : L (fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0) = 0 := by
      simpa using congrArg
        (fun f => f (fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0)) hzero
    have hji : j ≠ i := by
      intro h
      exact hij h.symm
    have : (1 : ℝ) = 0 := by
      simp [L, hji] at hval
    norm_num at this
  rw [hset]
  exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume (LinearMap.ker L) hker_ne_top

private theorem ae_pairwise_distinct_timeCoords {d n : ℕ} :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0 := by
  have hall : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ∀ p : {p : Fin n × Fin n // p.1 ≠ p.2}, x p.1.1 0 ≠ x p.1.2 0 := by
    simpa using
      ((Set.toFinite (Set.univ : Set {p : Fin n × Fin n // p.1 ≠ p.2})).eventually_all
        (l := MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)))
        (p := fun p => fun x : NPointDomain d n => x p.1.1 0 ≠ x p.1.2 0)).2
        (fun p _ => by
          let s : Set (NPointDomain d n) := {x | x p.1.1 0 = x p.1.2 0}
          have hs0 : MeasureTheory.volume s = 0 := by
            simpa [s] using measure_timeEq_zero (d := d) p.1.1 p.1.2 p.2
          have hsae :
              sᶜ ∈ MeasureTheory.ae
                (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
            MeasureTheory.compl_mem_ae_iff.mpr hs0
          simpa [s, Set.compl_setOf] using hsae)
  filter_upwards [hall] with x hx i j hij
  exact hx ⟨⟨i, j⟩, hij⟩

theorem schwartz_polynomial_kernel_integrable {d n : ℕ} [NeZero d]
    (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : C_bd > 0)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    ∀ f : SchwartzNPoint d n,
      MeasureTheory.Integrable (fun x => K x * f x) MeasureTheory.volume := by
  -- This is the `hKf_int` argument from `schwartz_polynomial_kernel_continuous`.
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have h_binom_ineq : ∀ (t : ℝ), 0 ≤ t → (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
    intro t ht
    have h2t : 1 + t ≤ 2 * max 1 t :=
      calc 1 + t ≤ max 1 t + max 1 t := add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = 2 * max 1 t := by ring
    calc (1 + t) ^ N
        ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by positivity) h2t N
      _ = 2 ^ N * (max 1 t) ^ N := by rw [mul_pow]
      _ ≤ 2 ^ N * (1 + t ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total t 1 with h | h
          · rw [max_eq_left h]; simp [one_pow]; linarith [pow_nonneg ht N]
          · rw [max_eq_right h]; linarith [show (1 : ℝ) ^ N = 1 from one_pow N]
  intro f
  have hf_int := f.integrable (μ := MeasureTheory.volume)
  have hf_pow_int := f.integrable_pow_mul MeasureTheory.volume N
  have hg_int : MeasureTheory.Integrable
      (fun x => C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
        ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖)) MeasureTheory.volume :=
    (hf_int.norm.add hf_pow_int).const_mul (C_bd * 2 ^ N)
  apply hg_int.mono' (hK_meas.mul f.integrable.aestronglyMeasurable)
  filter_upwards [hK_bound] with x hx
  simp only [Pi.mul_apply, norm_mul]
  calc ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖
      ≤ C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ :=
        mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ ≤ C_bd * (2 ^ N * (1 + ‖x‖ ^ N)) * ‖(f : NPointDomain d n → ℂ) x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (h_binom_ineq ‖x‖ (norm_nonneg _)) (le_of_lt hC)
    _ = C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
          ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖) := by ring

/-! ### Helpers for the VT-to-ForwardTubeGrowth bridge -/

/-- **Universal Projection Lemma (Ruelle's Lemma)**

    For any n points in ℝ^{d+1} (d ≥ 1), there exists a universal constant c > 0
    and a proper rotation R ∈ SO(d+1) such that the time-axis projections of ALL
    pairwise differences are bounded below by c times their full Euclidean distance:

      |⟨R(x_i - x_j), e₀⟩| ≥ c · ‖x_i - x_j‖  for all i ≠ j

    This guarantees we can simultaneously rotate all points so that no time gap
    is much smaller than the corresponding Euclidean distance.

    The proof uses a measure argument on S^d: for each pair, the "bad" directions
    where the time projection is small form a band of measure O(ε) on the sphere.
    Since there are finitely many pairs (≤ n²), choosing ε < vol(S^d)/(n² · band_width)
    ensures the union of bad bands doesn't cover S^d. The maximum over the compact
    configuration space gives a universal constant.

    Ref: Ruelle, "Statistical Mechanics", §3; Glimm-Jaffe, Ch. 6 -/
private theorem exists_universal_time_projection (d n : ℕ) [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : NPointDomain d n),
      ∃ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
        R.transpose * R = 1 ∧ R.det = 1 ∧
        ∀ i j : Fin n, i ≠ j →
          c * ‖x i - x j‖ ≤ |(R.mulVec (x i - x j)) 0| := by
  simpa using exists_universal_time_projection' d n

/-- The Vladimirov-Tillmann theorem + BHW Euclidean rotation invariance implies
    `HasForwardTubeGrowth` for any `WightmanFunctions`.

    The proof:
    1. Apply the Universal Projection Lemma to get R ∈ SO(d+1) with all time
       projections ≥ c · ‖x_i - x_j‖
    2. Rotate x by R, sort by new time coordinates, translate to positive times
    3. The rotated-sorted-translated configuration y has wick(y) ∈ ForwardTube
       with δ_min ≥ c · infDist(x, CoincidenceLocus)
    4. Apply VT to get ‖W(wick(y))‖ ≤ C·(1+‖y‖)^N · (1+δ⁻¹)^q
    5. By BHW rotation + permutation + translation invariance:
       F_ext(wick(x)) = F_ext(wick(y)) = W_analytic(wick(y))
    6. Since δ_min ≥ c·infDist, the (1+δ⁻¹)^q factor is bounded by
       (1 + (c·infDist)⁻¹)^q, and clearing the denominator:
       ‖W‖ · infDist^{q+1} ≤ C' · (1+‖x‖)^{N'} -/
theorem hasForwardTubeGrowth_of_wightman {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) : HasForwardTubeGrowth Wfn := by
  intro n
  -- For n ≤ 1, CoincidenceLocus is empty so infDist = 0, LHS = ‖W‖·0 = 0 ≤ anything
  by_cases hn : n ≤ 1
  · refine ⟨1, 0, 0, one_pos, fun x _ => ?_⟩
    have hset_empty :
        { y : Fin n → Fin (d + 1) → ℝ | ∃ i j : Fin n, i ≠ j ∧ y i = y j } = ∅ := by
      interval_cases n
      · ext y; simp
      · exact coincidenceLocus_one_eq_empty (d := d)
    simp [hset_empty]
  push_neg at hn
  haveI : NeZero n := ⟨by omega⟩
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, hn⟩ : Fin n) := by
    rw [Fin.ne_iff_vne]
    norm_num
  -- Step 1: Get W_analytic and VT bound (reusing the VT application from above)
  let W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ := (Wfn.spectrum_condition n).choose
  have hW_holo : DifferentiableOn ℂ W_analytic (ForwardTube d n) :=
    (Wfn.spectrum_condition n).choose_spec.1
  have hW_bv := (Wfn.spectrum_condition n).choose_spec.2
  have hFT_eq : ForwardTube d n = TubeDomainSetPi (ForwardConeAbs d n) := by
    ext z; exact (forwardTube_eq_imPreimage d n ▸ Iff.rfl)
  have hC_open := forwardConeAbs_isOpen d n
  have hC_conv := forwardConeAbs_convex d n
  have hC_cone : IsCone (ForwardConeAbs d n) := fun y hy t ht => by
    show t • y ∈ ForwardConeAbs d n; exact forwardConeAbs_smul d n t ht y hy
  have hC_salient : IsSalientCone (ForwardConeAbs d n) :=
    forwardConeAbs_salient d n
  have hW_clm : ∃ (Wcl : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ),
      ∀ f, Wcl f = Wfn.W n f :=
    ⟨{ toLinearMap := ⟨⟨Wfn.W n, (Wfn.linear n).map_add⟩, (Wfn.linear n).map_smul⟩,
       cont := Wfn.tempered n }, fun _ => rfl⟩
  obtain ⟨Wcl, hWcl⟩ := hW_clm
  have hW_holo' : DifferentiableOn ℂ W_analytic (TubeDomainSetPi (ForwardConeAbs d n)) :=
    hFT_eq ▸ hW_holo
  have hW_bv' : ∀ (η : NPointDomain d n), η ∈ ForwardConeAbs d n →
      ∀ (φ : SchwartzMap (NPointDomain d n) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (Wcl φ)) := by
    intro η hη φ; rw [hWcl]
    exact hW_bv φ η ((inForwardCone_iff_mem_forwardConeAbs η).mpr hη)
  obtain ⟨_, ⟨C_vt, N_vt, q_vt, hC_vt_pos, hVT_bound⟩⟩ :=
    vladimirov_tillmann (ForwardConeAbs d n) hC_open hC_conv hC_cone hC_salient
      W_analytic hW_holo' Wcl hW_bv'
  -- Step 2: Get the universal projection constant
  obtain ⟨c_proj, hc_pos, hproj⟩ := exists_universal_time_projection d n
  let c_geom : ℝ := c_proj / (2 * d + 4 : ℝ)
  let C_z : ℝ := c_proj + (((n + 1) * (d + 1) : ℕ) : ℝ) + 1
  -- Step 3: Produce constants and prove the bound for each x with wick(x) ∈ ForwardTube.
  -- The algebra: ‖W‖ · Δ^{q+1} ≤ C·(1+‖y‖)^N · (cΔ+1)^q · Δ / c^q
  --   ≤ C·(C'(1+‖x‖))^N · (2c‖x‖+1)^q · 2‖x‖ / c^q ≤ C'' · (1+‖x‖)^{N+q+1}
  -- where Δ = infDist(x, Coinc), y = translate(sort(rotate(x))), ‖y‖ ≤ C'(1+‖x‖).
  -- We use q = q_vt and N = N_vt + q_vt + 1.
  refine ⟨?C_out, N_vt + q_vt + 1, q_vt, ?hC_out, fun x hx_ft => ?_⟩
  · exact C_vt * (2 * max 1 C_z) ^ N_vt * (max 2 c_geom⁻¹) ^ q_vt * 2 + 1
  · positivity
  -- For this x with wick(x) ∈ ForwardTube:
  -- (a) Get rotation R from Universal Projection
  obtain ⟨R, hR_orth, hR_det, hR_proj⟩ := hproj x
  let x' : NPointDomain d n := fun k => R.mulVec (x k)
  -- (b) x' has distinct times (from projection + x not in CoincidenceLocus)
  -- Since wick(x) ∈ ForwardTube, x has strictly increasing times, hence x ∉ Coinc.
  -- After rotation, |t'_i - t'_j| ≥ c·‖x_i - x_j‖ > 0 for i ≠ j.
  have hx'_distinct : ∀ i j : Fin n, i ≠ j → x' i 0 ≠ x' j 0 := by
    -- From projection lemma: |t'_i - t'_j| ≥ c·‖x_i - x_j‖ > 0 for i ≠ j
    -- (x has distinct points since wick(x) ∈ ForwardTube implies sorted positive times)
    intro i j hij hEq
    have htime_strict : StrictMono (fun k : Fin n => x k 0) := by
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
      rw [Fin.strictMono_iff_lt_succ]
      intro k
      have hk := (hx_ft k.succ).1
      simpa [wickRotatePoint, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Fin.succ_ne_zero, zero_mul, one_mul, zero_add]
        using hk
    have hx_ne : x i ≠ x j := by
      intro hEqx
      apply hij
      exact htime_strict.injective (by simpa using congrArg (fun y : SpacetimeDim d => y 0) hEqx)
    have hnorm_pos : 0 < ‖x i - x j‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hx_ne)
    have hproj_ij := hR_proj i j hij
    have habs_zero : |(R.mulVec (x i - x j)) 0| = 0 := by
      rw [show (R.mulVec (x i - x j)) 0 = x' i 0 - x' j 0 by
        simp [x', Matrix.mulVec_sub]]
      simp [hEq]
    have : c_proj * ‖x i - x j‖ ≤ 0 := by simpa [habs_zero] using hproj_ij
    have hprod_pos : 0 < c_proj * ‖x i - x j‖ := mul_pos hc_pos hnorm_pos
    linarith
  -- (c) Shift to positive times
  let Δ : ℝ := Metric.infDist x (CoincidenceLocus d n)
  let A' : ℝ := 1 + c_proj * Δ + ∑ i : Fin n, |x' i 0|
  let a' : SpacetimeDim d := fun μ => if μ = 0 then A' else 0
  let xs' : NPointDomain d n := fun k μ => x' k μ + a' μ
  have hΔ_nonneg : 0 ≤ Δ := by
    dsimp [Δ]
    exact Metric.infDist_nonneg
  have hpos' : ∀ i : Fin n, xs' i 0 > 0 := by
    intro i
    have hi_le : |x' i 0| ≤ ∑ j : Fin n, |x' j 0| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (x' j 0)) (Finset.mem_univ i)
    have hcore : 0 ≤ x' i 0 + ∑ j : Fin n, |x' j 0| := by
      linarith [neg_abs_le (x' i 0), hi_le]
    have hshift : 0 < 1 + c_proj * Δ := by
      nlinarith [hΔ_nonneg, le_of_lt hc_pos]
    have : 0 < x' i 0 + A' := by
      dsimp [A']
      linarith
    simpa [xs', a'] using this
  have hdistinct_xs' : ∀ i j : Fin n, i ≠ j → xs' i 0 ≠ xs' j 0 := by
    intro i j hij; simpa [xs', a'] using hx'_distinct i j hij
  -- (d) Sort by time
  let π' := Tuple.sort (fun k => xs' k 0)
  have hmono' := Tuple.monotone_sort (fun k => xs' k 0)
  have hinj' : Function.Injective (fun k => xs' k 0) := by
    intro i j h; by_contra hij; exact hdistinct_xs' i j hij h
  have hstrict' : StrictMono ((fun k => xs' k 0) ∘ π') :=
    hmono'.strictMono_of_injective (hinj'.comp π'.injective)
  have hord' : ∀ k j : Fin n, k < j → xs' (π' k) 0 < xs' (π' j) 0 :=
    fun k j hkj => hstrict' hkj
  have hfwd' : (fun k => wickRotatePoint (xs' (π' k))) ∈ ForwardTube d n :=
    euclidean_ordered_in_forwardTube (fun k => xs' (π' k)) hord'
      (fun k => hpos' (π' k))
  -- (e) BHW chain: W_analytic(wick(x)) = W_analytic(wick(y)) where y = xs' ∘ π'
  -- First: wick(x) ∈ ForwardTube ⊆ PET
  have hx_pet : (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n := by
    have hFT_BHW : (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx_ft
    have hPET_BHW : (fun k => wickRotatePoint (x k)) ∈ BHW.PermutedExtendedTube d n :=
      BHW.forwardTube_subset_permutedExtendedTube hFT_BHW
    simpa [BHW_permutedExtendedTube_eq (d := d) (n := n)] using hPET_BHW
  -- W_analytic(wick(x)) = F_ext(wick(x))
  have hagree_x : (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (x k)) =
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) := by
    exact ((W_analytic_BHW Wfn n).property.2.1 _ hx_ft).symm
  -- F_ext(wick(x)) = F_ext(wick(x')) by rotation invariance
  -- (same as F_ext_rotation_invariant, proved later in this file at line ~1538,
  -- via schwinger_euclidean_invariant from AnalyticContinuation.lean)
  have hrot : (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x' k)) := by
    have := schwinger_euclidean_invariant
      (fun n => (W_analytic_BHW Wfn n).val)
      (fun n Λ z hz => (W_analytic_BHW Wfn n).property.2.2.1 Λ z hz)
      n R hR_det hR_orth x hx_pet
    simpa [SchwingerFromWightman] using this.symm
  -- F_ext(wick(x')) = F_ext(wick(xs')) by translation invariance
  have hxs'_pet : (fun k => wickRotatePoint (xs' k)) ∈ PermutedExtendedTube d n :=
    euclidean_distinct_in_permutedTube xs' hdistinct_xs' hpos'
  have hwick_add' : (fun k => wickRotatePoint (xs' k)) =
      (fun k μ => wickRotatePoint (x' k) μ + wickRotatePoint a' μ) := by
    ext k μ; simp only [wickRotatePoint, xs', a']; split_ifs <;> push_cast <;> ring
  have hx'_pet : (fun k => wickRotatePoint (x' k)) ∈ PermutedExtendedTube d n := by
    have hR_detT : R.transpose.det = 1 := by simpa [Matrix.det_transpose] using hR_det
    have hR_orthT : R * R.transpose = 1 := by simpa using mul_eq_one_comm.mp hR_orth
    have hpre :
        (fun k => wickRotatePoint (R.transpose.mulVec (x' k))) ∈ PermutedExtendedTube d n := by
      simpa [x', Matrix.mulVec_mulVec, hR_orth, Matrix.one_mulVec] using hx_pet
    exact PermutedExtendedTube_euclidean_preimage (d := d) R.transpose hR_detT hR_orthT x' hpre
  have htransl' : (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x' k)) =
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs' k)) := by
    rw [hwick_add']
    exact (bhw_translation_invariant Wfn (wickRotatePoint a')
      (fun k => wickRotatePoint (x' k)) hx'_pet
      (by simpa [hwick_add'] using hxs'_pet)).symm
  -- F_ext(wick(xs')) = F_ext(wick(xs' ∘ π')) by permutation invariance
  have hperm' : (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs' k)) =
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs' (π' k))) :=
    ((W_analytic_BHW Wfn n).property.2.2.2 π'
      (fun k => wickRotatePoint (xs' k)) hxs'_pet).symm
  -- F_ext(wick(xs' ∘ π')) = W_analytic(wick(xs' ∘ π')) by BHW agreement on ForwardTube
  have hagree_y : (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs' (π' k))) =
      (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (xs' (π' k))) :=
    (W_analytic_BHW Wfn n).property.2.1 _ hfwd'
  -- Full chain: W_analytic(wick(x)) = W_analytic(wick(xs' ∘ π'))
  have hnorm_chain :
      ‖(Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (x k))‖ =
      ‖(Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (xs' (π' k)))‖ := by
    rw [hagree_x, hrot, htransl', hperm', hagree_y]
  -- (f) Apply VT at the rotated-sorted-translated point
  have hVT_at_y := hVT_bound (fun k => wickRotatePoint (xs' (π' k))) (hFT_eq ▸ hfwd')
  rw [hnorm_chain]
  have htime_strict : StrictMono (fun k : Fin n => x k 0) := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    have hk := (hx_ft k.succ).1
    simpa [wickRotatePoint, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Fin.succ_ne_zero, zero_mul, one_mul, zero_add]
      using hk
  have hcoin_nonempty : (CoincidenceLocus d n).Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨(⟨0, by omega⟩ : Fin n), (⟨1, hn⟩ : Fin n), h01, rfl⟩
  have hx_not_mem : x ∉ CoincidenceLocus d n := by
    intro hxCoin
    rcases hxCoin with ⟨i, j, hij, hEq⟩
    exact hij (htime_strict.injective (by simpa using congrArg (fun y : SpacetimeDim d => y 0) hEq))
  have hΔ_pos : 0 < Δ := by
    have hclosed : IsClosed (CoincidenceLocus d n) := isClosed_CoincidenceLocus (d := d) (n := n)
    simpa [Δ] using (hclosed.notMem_iff_infDist_pos hcoin_nonempty).1 hx_not_mem
  have hΔ_le_norm : Δ ≤ ‖x‖ := by
    have hzero_mem : (0 : NPointDomain d n) ∈ CoincidenceLocus d n := by
      exact ⟨(⟨0, by omega⟩ : Fin n), (⟨1, hn⟩ : Fin n), h01, rfl⟩
    have h := Metric.infDist_le_dist_of_mem hzero_mem (x := x)
    simpa [Δ, dist_eq_norm] using h
  have hΔ_le_two_norm : Δ ≤ 2 * ‖x‖ := by nlinarith [hΔ_le_norm, norm_nonneg x]
  have hx'_norm : ‖x'‖ ≤ (d + 1 : ℝ) * ‖x‖ := by
    simpa [x'] using norm_mulVec_le_of_orthogonal R hR_orth x
  let y : NPointDomain d n := fun k => xs' (π' k)
  let η : NPointDomain d n := fun k μ => (wickRotatePoint (y k) μ).im
  have hη_space : ∀ k : Fin n, ∀ μ : Fin (d + 1), μ ≠ 0 → BHW.consecutiveDiff η k μ = 0 := by
    intro k μ hμ
    by_cases hk : (k : ℕ) = 0
    · simp [η, y, BHW.consecutiveDiff, hk, wickRotatePoint, hμ]
    · simp [η, y, BHW.consecutiveDiff, hk, wickRotatePoint, hμ]
  have hη_time : ∀ k : Fin n, c_proj * Δ ≤ BHW.consecutiveDiff η k 0 := by
    intro k
    by_cases hk : (k : ℕ) = 0
    · have hi_le : |x' (π' k) 0| ≤ ∑ j : Fin n, |x' j 0| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (x' j 0)) (Finset.mem_univ (π' k))
      have h0 : c_proj * Δ ≤ x' (π' k) 0 + A' := by
        dsimp [A']
        linarith [neg_abs_le (x' (π' k) 0), hi_le]
      simpa [η, y, xs', a', BHW.consecutiveDiff, hk, wickRotatePoint] using h0
    · let km1 : Fin n := ⟨k.val - 1, by omega⟩
      have hkm1_lt : km1 < k := by
        exact Fin.lt_def.mpr (by
          dsimp [km1]
          omega)
      have hπ_ne : π' k ≠ π' km1 := by
        intro hEq
        have : k = km1 := π'.injective hEq
        omega
      have hΔ_pair : Δ ≤ ‖x (π' k) - x (π' km1)‖ :=
        infDist_CoincidenceLocus_le_pairDifference (d := d) (n := n) x (π' k) (π' km1) hπ_ne
      have hproj_pair : c_proj * Δ ≤ |(R.mulVec (x (π' k) - x (π' km1))) 0| := by
        calc
          c_proj * Δ ≤ c_proj * ‖x (π' k) - x (π' km1)‖ := by
            gcongr
          _ ≤ |(R.mulVec (x (π' k) - x (π' km1))) 0| := hR_proj (π' k) (π' km1) hπ_ne
      have hgap_eq :
          (R.mulVec (x (π' k) - x (π' km1))) 0 = y k 0 - y km1 0 := by
        simp [y, xs', a', x', Matrix.mulVec_sub]
      have hgap_nonneg : 0 ≤ (R.mulVec (x (π' k) - x (π' km1))) 0 := by
        have hordered : y km1 0 < y k 0 := hord' km1 k hkm1_lt
        linarith [hgap_eq, hordered]
      have hgap_bound : c_proj * Δ ≤ y k 0 - y km1 0 := by
        have hproj_pair' : c_proj * Δ ≤ |y k 0 - y km1 0| := by
          simpa [hgap_eq] using hproj_pair
        have habs_eq : |y k 0 - y km1 0| = y k 0 - y km1 0 := by
          apply abs_of_nonneg
          have hordered : y km1 0 < y k 0 := hord' km1 k hkm1_lt
          linarith
        rw [habs_eq] at hproj_pair'
        exact hproj_pair'
      simpa [η, y, BHW.consecutiveDiff, hk, wickRotatePoint, km1] using hgap_bound
  have hδ_bound :
      c_geom * Δ ≤ Metric.infDist η (ForwardConeAbs d n)ᶜ := by
    have h := infDist_forwardConeAbs_lower_bound (d := d) (n := n) η (c_proj * Δ)
      (mul_pos hc_pos hΔ_pos) hη_time hη_space
    dsimp [c_geom]
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hδ_pos : 0 < Metric.infDist η (ForwardConeAbs d n)ᶜ := by
    have hc_geom_pos : 0 < c_geom := by
      dsimp [c_geom]
      positivity
    exact lt_of_lt_of_le (mul_pos hc_geom_pos hΔ_pos) hδ_bound
  have hsum_x' : ∑ i : Fin n, |x' i 0| ≤ (n : ℝ) * ‖x'‖ := by
    calc
      ∑ i : Fin n, |x' i 0| ≤ ∑ _i : Fin n, ‖x'‖ := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          |x' i 0| = ‖x' i 0‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖x' i‖ := norm_le_pi_norm (x' i) 0
          _ ≤ ‖x'‖ := norm_le_pi_norm x' i
      _ = (n : ℝ) * ‖x'‖ := by
        simp [Finset.sum_const]
  have hy_norm : ‖y‖ ≤ ‖x'‖ + A' := by
    have hA_nonneg : 0 ≤ A' := by
      dsimp [A']
      positivity
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro μ
    rw [Real.norm_eq_abs]
    dsimp [y, xs', a']
    split_ifs with hμ
    · calc
        |x' (π' k) μ + A'| ≤ |x' (π' k) μ| + |A'| := abs_add_le _ _
        _ ≤ ‖x'‖ + A' := by
          gcongr
          · calc
              |x' (π' k) μ| = ‖x' (π' k) μ‖ := by rw [Real.norm_eq_abs]
              _ ≤ ‖x' (π' k)‖ := norm_le_pi_norm (x' (π' k)) μ
              _ ≤ ‖x'‖ := norm_le_pi_norm x' (π' k)
          · exact le_of_eq (abs_of_nonneg hA_nonneg)
    · calc
        |x' (π' k) μ + 0| = |x' (π' k) μ| := by rw [add_zero]
        _ = ‖x' (π' k) μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖x' (π' k)‖ := norm_le_pi_norm (x' (π' k)) μ
        _ ≤ ‖x'‖ := norm_le_pi_norm x' (π' k)
        _ ≤ ‖x'‖ + A' := by linarith
  have hz_bound :
      ‖fun k => wickRotatePoint (xs' (π' k))‖ ≤ C_z * (1 + ‖x‖) := by
    have hA'_le : A' ≤ 1 + c_proj * ‖x‖ + (n : ℝ) * ‖x'‖ := by
      dsimp [A']
      gcongr
    calc
      ‖fun k => wickRotatePoint (xs' (π' k))‖ ≤ ‖y‖ := by
        simpa [y] using wickRotate_norm_le (d := d) (n := n) y
      _ ≤ ‖x'‖ + A' := hy_norm
      _ ≤ ‖x'‖ + (1 + c_proj * ‖x‖ + (n : ℝ) * ‖x'‖) := by
        linarith [hA'_le]
      _ ≤ (d + 1 : ℝ) * ‖x‖ + (1 + c_proj * ‖x‖ + (n : ℝ) * ((d + 1 : ℝ) * ‖x‖)) := by
        gcongr
      _ = 1 + (c_proj + (((n + 1) * (d + 1) : ℕ) : ℝ)) * ‖x‖ := by
        push_cast
        ring
      _ ≤ C_z * (1 + ‖x‖) := by
        dsimp [C_z]
        nlinarith [norm_nonneg x, le_of_lt hc_pos]
  have hz_nonneg : 0 ≤ ‖fun k => wickRotatePoint (xs' (π' k))‖ := norm_nonneg _
  have hcollapse := collapse_vt_denominator_algebra
      C_vt
      ‖W_analytic (fun k => wickRotatePoint (xs' (π' k)))‖
      ‖fun k => wickRotatePoint (xs' (π' k))‖
      ‖x‖
      (Metric.infDist η (ForwardConeAbs d n)ᶜ)
      Δ
      c_geom
      C_z
      N_vt q_vt
      (le_of_lt hC_vt_pos)
      (by
        dsimp [c_geom]
        positivity)
      hΔ_pos
      hδ_pos
      (by
        dsimp [C_z]
        positivity)
      hVT_at_y
      hδ_bound
      hz_bound
      hΔ_le_two_norm
      (norm_nonneg x)
      hz_nonneg
  simpa [W_analytic, Δ, c_geom, C_z, CoincidenceLocus, η] using hcollapse

/-- **Integrability of the Wick-rotated BHW kernel on the zero-diagonal test space.**

    Uses explicit forward-tube growth input together with the global reduction
    theorem. -/
theorem wick_rotated_kernel_mul_zeroDiagonal_integrable {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ f : ZeroDiagonalSchwartz d n,
      MeasureTheory.Integrable
        (fun x : NPointDomain d n =>
          (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * f.1 x)
        MeasureTheory.volume := by
  have hgrowthW := hasForwardTubeGrowth_of_wightman Wfn
  intro f
  obtain ⟨C_bd, N, q, hC_pos, hgrowth⟩ := hgrowthW n
  by_cases hcoin : (CoincidenceLocus d n).Nonempty
  · -- Main case: n ≥ 2 (CoincidenceLocus nonempty)
    have hcoinc_eq : { y : NPointDomain d n | ∃ i j : Fin n, i ≠ j ∧ y i = y j } =
        CoincidenceLocus d n := rfl
    set nR : ℝ := ((n + 2 : ℕ) : ℝ) with hnR_def
    apply kernel_mul_zeroDiagonal_integrable_of_ae_infDist_mul_pow_le_polynomial
      (hK_meas := bhw_euclidean_kernel_measurable Wfn)
      (m := q) (M := N) (hcoin := hcoin)
      (C_bd := C_bd * nR ^ N) (hC := by positivity)
    -- Prove the a.e. weighted bound on the BHW kernel
    filter_upwards [ae_euclidean_points_in_permutedTube (d := d) (n := n),
      ae_pairwise_distinct_timeCoords (d := d) (n := n)] with x hx_pet hx_distinct
    -- Step 1: Shift to positive times
    let A : ℝ := 1 + ∑ i : Fin n, |x i 0|
    let a : SpacetimeDim d := fun μ => if μ = 0 then A else 0
    let xs : NPointDomain d n := fun k μ => x k μ + a μ
    -- xs has positive times
    have hpos : ∀ i : Fin n, xs i 0 > 0 := by
      intro i
      have hi_le : |x i 0| ≤ ∑ j : Fin n, |x j 0| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (x j 0)) (Finset.mem_univ i)
      have : 0 < x i 0 + A := by dsimp [A]; linarith [neg_abs_le (x i 0)]
      simpa [xs, a] using this
    -- xs has distinct times
    have hdistinct_xs : ∀ i j : Fin n, i ≠ j → xs i 0 ≠ xs j 0 := by
      intro i j hij; simpa [xs, a] using hx_distinct i j hij
    -- Step 2: Sort xs by time and get ForwardTube membership
    let π := Tuple.sort (fun k => xs k 0)
    have hmono := Tuple.monotone_sort (fun k => xs k 0)
    have hinj : Function.Injective (fun k => xs k 0) := by
      intro i j h; by_contra hij; exact hdistinct_xs i j hij h
    have hstrict : StrictMono ((fun k => xs k 0) ∘ π) :=
      hmono.strictMono_of_injective (hinj.comp π.injective)
    have hord : ∀ k j : Fin n, k < j → xs (π k) 0 < xs (π j) 0 :=
      fun k j hkj => hstrict hkj
    have hpos' : ∀ k : Fin n, xs (π k) 0 > 0 := fun k => hpos (π k)
    have hfwd : (fun k => wickRotatePoint (xs (π k))) ∈ ForwardTube d n :=
      euclidean_ordered_in_forwardTube (fun k => xs (π k)) hord hpos'
    have hxs_pet : (fun k => wickRotatePoint (xs k)) ∈ PermutedExtendedTube d n :=
      euclidean_distinct_in_permutedTube xs hdistinct_xs hpos
    -- Step 3: Translation invariance — F_ext(wick(x)) = F_ext(wick(xs))
    have hwick_add : (fun k => wickRotatePoint (xs k)) =
        (fun k μ => wickRotatePoint (x k) μ + wickRotatePoint a μ) := by
      ext k μ; simp only [wickRotatePoint, xs, a]; split_ifs <;> push_cast <;> ring
    have htransl : (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) =
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs k)) := by
      rw [hwick_add]
      exact (bhw_translation_invariant Wfn (wickRotatePoint a)
        (fun k => wickRotatePoint (x k)) hx_pet
        (by simpa [hwick_add] using hxs_pet)).symm
    -- Step 4: Permutation invariance — F_ext(wick(xs)) = F_ext(wick(xs ∘ π))
    have hperm : (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs k)) =
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs (π k))) :=
      ((W_analytic_BHW Wfn n).property.2.2.2 π
        (fun k => wickRotatePoint (xs k)) hxs_pet).symm
    -- Step 5: BHW agreement on ForwardTube — F_ext = W_analytic
    have hagree : (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs (π k))) =
        (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (xs (π k))) :=
      (W_analytic_BHW Wfn n).property.2.1 _ hfwd
    -- Step 6: Apply forward_tube_growth to the sorted shifted configuration
    have hbound := hgrowth (fun k => xs (π k)) hfwd
    rw [hcoinc_eq] at hbound
    -- Step 7: Norm chain — ‖K(x)‖ = ‖W_analytic(wick(xs ∘ π))‖
    have hnorm_eq : ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ =
        ‖(Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (xs (π k)))‖ := by
      rw [htransl, hperm, hagree]
    -- Step 8: infDist preservation — shift and permutation preserve pairwise distances
    have hinfDist_eq : Metric.infDist (fun k => xs (π k)) (CoincidenceLocus d n) =
        Metric.infDist x (CoincidenceLocus d n) := by
      -- Step 8a: constant shift y ↦ c + y preserves infDist
      let c : NPointDomain d n := fun _ => a
      have hxs_eq : xs = c + x := by ext k μ; simp [xs, c, add_comm]
      have hΦ_isom : Isometry ((c + ·) : NPointDomain d n → NPointDomain d n) :=
        Isometry.of_dist_eq fun y z => dist_vadd_cancel_left c y z
      have hΦ_coinc : (c + ·) '' CoincidenceLocus d n = CoincidenceLocus d n := by
        ext y; simp only [Set.mem_image, CoincidenceLocus, Set.mem_setOf_eq]; constructor
        · rintro ⟨z, ⟨i, j, hij, hzij⟩, rfl⟩
          exact ⟨i, j, hij, show c i + z i = c j + z j by rw [show c i = c j from rfl, hzij]⟩
        · rintro ⟨i, j, hij, hyij⟩
          refine ⟨-c + y, ⟨i, j, hij, show (-c + y) i = (-c + y) j from ?_⟩, by simp⟩
          ext μ; simp only [Pi.add_apply, Pi.neg_apply]
          have := congr_fun hyij μ; linarith
      have h_shift : Metric.infDist xs (CoincidenceLocus d n) =
          Metric.infDist x (CoincidenceLocus d n) := by
        have h := Metric.infDist_image hΦ_isom (x := x) (t := CoincidenceLocus d n)
        rw [hΦ_coinc] at h; rw [hxs_eq]; exact h
      -- Step 8b: permutation y ↦ y ∘ π preserves infDist
      let Ψ : NPointDomain d n → NPointDomain d n := fun y k => y (π k)
      have hΨ_isom : Isometry Ψ := fun y z => by
        show edist (Ψ y) (Ψ z) = edist y z
        change edist (fun k => y (π k)) (fun k => z (π k)) = edist y z
        rw [edist_pi_def, edist_pi_def]
        simp only [Finset.sup_univ_eq_iSup]
        exact Equiv.iSup_comp (g := fun k => edist (y k) (z k)) π
      have hΨ_coinc : Ψ '' CoincidenceLocus d n = CoincidenceLocus d n := by
        ext y; simp only [Set.mem_image, CoincidenceLocus, Set.mem_setOf_eq, Ψ]; constructor
        · rintro ⟨z, ⟨i, j, hij, hzij⟩, rfl⟩
          exact ⟨π.symm i, π.symm j, fun h => hij (π.symm.injective h), by simp [hzij]⟩
        · rintro ⟨i, j, hij, hyij⟩
          exact ⟨fun k => y (π.symm k),
            ⟨π i, π j, fun h => hij (π.injective h), by simp [hyij]⟩, by ext k; simp⟩
      have h_perm : Metric.infDist (Ψ xs) (CoincidenceLocus d n) =
          Metric.infDist xs (CoincidenceLocus d n) := by
        have h := Metric.infDist_image hΨ_isom (x := xs) (t := CoincidenceLocus d n)
        rw [hΨ_coinc] at h; exact h
      exact h_perm.trans h_shift
    -- Step 9: Norm bound — (1 + ‖xs ∘ π‖)^N ≤ (nR * (1 + ‖x‖))^N
    have hnorm_bound : (1 + ‖fun k => xs (π k)‖) ^ N ≤ (nR * (1 + ‖x‖)) ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      -- A is nonneg
      have hA_nonneg : (0 : ℝ) ≤ A := by dsimp [A]; positivity
      -- Each component of xs(π k) is bounded by ‖x‖ + A
      have hcomp_bound : ∀ (k : Fin n) (μ : Fin (d + 1)),
          |xs (π k) μ| ≤ ‖x‖ + A := by
        intro k μ
        simp only [xs, a]
        split_ifs with h
        · calc |x (π k) μ + A|
              ≤ |x (π k) μ| + |A| := abs_add_le _ _
            _ ≤ ‖x‖ + A := by
              gcongr
              · exact (norm_le_pi_norm (x (π k)) μ).trans (norm_le_pi_norm x (π k))
              · exact le_of_eq (abs_of_nonneg hA_nonneg)
        · calc |x (π k) μ + 0| = |x (π k) μ| := by rw [add_zero]
            _ ≤ ‖x‖ := (norm_le_pi_norm (x (π k)) μ).trans (norm_le_pi_norm x (π k))
            _ ≤ ‖x‖ + A := le_add_of_nonneg_right hA_nonneg
      -- Hence ‖xs ∘ π‖ ≤ ‖x‖ + A via pi_norm_le_iff
      have hpi_bound : ‖fun k => xs (π k)‖ ≤ ‖x‖ + A := by
        apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro k
        apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro μ
        rw [Real.norm_eq_abs]; exact hcomp_bound k μ
      -- A ≤ 1 + n * ‖x‖
      have hA_le : A ≤ 1 + n * ‖x‖ := by
        dsimp [A]; gcongr
        calc ∑ i : Fin n, |x i 0|
            ≤ ∑ _ : Fin n, ‖x‖ := by
              gcongr with i
              exact (Real.norm_eq_abs (x i 0) ▸ norm_le_pi_norm (x i) 0).trans
                (norm_le_pi_norm x i)
          _ = n * ‖x‖ := by simp [Finset.sum_const, smul_eq_mul]
      -- Combine: 1 + ‖xs ∘ π‖ ≤ 1 + ‖x‖ + A ≤ (n+2)(1+‖x‖) = nR * (1+‖x‖)
      calc 1 + ‖fun k => xs (π k)‖
          ≤ 1 + (‖x‖ + A) := by linarith [hpi_bound]
        _ ≤ 1 + (‖x‖ + (1 + n * ‖x‖)) := by linarith [hA_le]
        _ = 2 + (↑n + 1) * ‖x‖ := by push_cast; ring
        _ ≤ (↑n + 2) * (1 + ‖x‖) := by nlinarith [norm_nonneg x]
        _ = nR * (1 + ‖x‖) := by dsimp [nR]; push_cast; ring
    -- Step 10: Assemble the final bound
    calc ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ *
          Metric.infDist x (CoincidenceLocus d n) ^ (q + 1)
        = ‖(Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (xs (π k)))‖ *
            Metric.infDist (fun k => xs (π k)) (CoincidenceLocus d n) ^ (q + 1) := by
          rw [hnorm_eq, hinfDist_eq]
      _ ≤ C_bd * (1 + ‖fun k => xs (π k)‖) ^ N := hbound
      _ ≤ C_bd * (nR * (1 + ‖x‖)) ^ N := by gcongr
      _ = C_bd * nR ^ N * (1 + ‖x‖) ^ N := by rw [mul_pow]; ring
  · -- Degenerate case: n ≤ 1 (CoincidenceLocus empty)
    -- Derive n ≤ 1 from emptiness of CoincidenceLocus
    have hn_le : n ≤ 1 := by
      by_contra h
      push_neg at h
      apply hcoin
      haveI : NeZero n := ⟨by omega⟩
      refine ⟨fun _ => 0, 0, ⟨1, by omega⟩, ?_, rfl⟩
      simp [Fin.ext_iff]
    interval_cases n
    · -- n = 0: NPointDomain d 0 is Unique (empty product); volume is dirac
      haveI : Unique (NPointDomain d 0) := inferInstance
      haveI : MeasureTheory.IsFiniteMeasure
          (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d 0)) := by
        have : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d 0)) =
          MeasureTheory.Measure.pi (fun _ : Fin 0 => MeasureTheory.volume) := rfl
        rw [this, MeasureTheory.Measure.pi_of_empty]
        exact MeasureTheory.Measure.dirac.instIsFiniteMeasure
      exact MeasureTheory.Integrable.of_subsingleton
    · -- n = 1: For n=1, W_analytic is translation-invariant on the forward tube
      -- (by W_analytic_translation_on_forwardTube). Since any two points in the
      -- n=1 forward tube differ by a translation staying in the tube, W_analytic
      -- is constant. So F_ext ∘ wick is a.e. constant, and constant × Schwartz
      -- is integrable.
      -- Reference point: e₀ = (1, 0, ..., 0) has wick(e₀) ∈ ForwardTube d 1
      let x₀ : NPointDomain d 1 := fun _ => Pi.single (0 : Fin (d + 1)) 1
      let v₀ : ℂ := (W_analytic_BHW Wfn 1).val (fun k => wickRotatePoint (x₀ k))
      -- The kernel equals v₀ a.e. (via translation to positive time + constancy)
      have hkernel_ae : ∀ᵐ (x : NPointDomain d 1) ∂MeasureTheory.volume,
          (W_analytic_BHW Wfn 1).val (fun k => wickRotatePoint (x k)) = v₀ := by
        filter_upwards [ae_euclidean_points_in_permutedTube (d := d) (n := 1)] with x hx_pet
        -- Shift x to positive time
        let A₁ : ℝ := 1 + |x 0 0|
        let a₁ : SpacetimeDim d := fun μ => if μ = 0 then A₁ else 0
        let xs₁ : NPointDomain d 1 := fun k μ => x k μ + a₁ μ
        have hpos₁ : xs₁ 0 0 > 0 := by
          simp [xs₁, a₁, A₁]; linarith [neg_abs_le (x 0 0)]
        have hfwd₁ : (fun k => wickRotatePoint (xs₁ k)) ∈ ForwardTube d 1 :=
          euclidean_ordered_in_forwardTube (fun k => xs₁ k)
            (fun k j hkj => by fin_cases k <;> fin_cases j <;> simp_all [Fin.lt_iff_val_lt_val])
            (fun k => by fin_cases k; exact hpos₁)
        have hxs₁_pet : (fun k => wickRotatePoint (xs₁ k)) ∈ PermutedExtendedTube d 1 :=
          euclidean_distinct_in_permutedTube xs₁
            (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all)
            (fun i => by fin_cases i; exact hpos₁)
        -- F_ext(wick(x)) = F_ext(wick(xs₁))
        have hwick_add₁ : (fun k => wickRotatePoint (xs₁ k)) =
            (fun k μ => wickRotatePoint (x k) μ + wickRotatePoint a₁ μ) := by
          ext k μ; simp only [wickRotatePoint, xs₁, a₁]; split_ifs <;> push_cast <;> ring
        have htransl₁ : (W_analytic_BHW Wfn 1).val (fun k => wickRotatePoint (x k)) =
            (W_analytic_BHW Wfn 1).val (fun k => wickRotatePoint (xs₁ k)) := by
          rw [hwick_add₁]
          exact (bhw_translation_invariant Wfn (wickRotatePoint a₁)
            (fun k => wickRotatePoint (x k)) hx_pet
            (by simpa [hwick_add₁] using hxs₁_pet)).symm
        -- F_ext(wick(xs₁)) = W_analytic(wick(xs₁)) on ForwardTube
        have hagree₁ := (W_analytic_BHW Wfn 1).property.2.1 _ hfwd₁
        -- W_analytic(wick(xs₁)) = W_analytic(wick(x₀)) by translation invariance
        -- The reference point x₀ also has wick(x₀) ∈ ForwardTube d 1
        have hfwd₀ : (fun k => wickRotatePoint (x₀ k)) ∈ ForwardTube d 1 :=
          euclidean_ordered_in_forwardTube (fun k => x₀ k)
            (fun k j hkj => by fin_cases k <;> fin_cases j <;> simp_all [Fin.lt_iff_val_lt_val])
            (fun k => by fin_cases k; simp [x₀, Pi.single_apply])
        -- W_analytic(wick(xs₁)) = W_analytic(wick(x₀)) by translation invariance
        have htransl_const :
            (Wfn.spectrum_condition 1).choose (fun k => wickRotatePoint (xs₁ k)) =
            (Wfn.spectrum_condition 1).choose (fun k => wickRotatePoint (x₀ k)) := by
          let c₁ : Fin (d + 1) → ℂ := fun μ =>
            wickRotatePoint (xs₁ 0) μ - wickRotatePoint (x₀ 0) μ
          have hzc_eq : (fun k μ => wickRotatePoint (x₀ k) μ + c₁ μ) =
              (fun k => wickRotatePoint (xs₁ k)) := by
            ext k μ; fin_cases k; simp [c₁]
          have hzc_ft : (fun k μ => wickRotatePoint (x₀ k) μ + c₁ μ) ∈ ForwardTube d 1 :=
            hzc_eq ▸ hfwd₁
          have h := W_analytic_translation_on_forwardTube Wfn c₁
            (fun k => wickRotatePoint (x₀ k)) hfwd₀ hzc_ft
          -- h : W_analytic(x₀ + c₁) = W_analytic(x₀)
          -- hzc_eq : (x₀ + c₁) = xs₁ (as Wick-rotated functions)
          rw [hzc_eq] at h; exact h
        -- Chain: F_ext(wick(x)) = ... = v₀
        have hagree₀ := (W_analytic_BHW Wfn 1).property.2.1 _ hfwd₀
        rw [htransl₁, hagree₁, htransl_const, ← hagree₀]
      -- Constant × Schwartz is integrable
      haveI : MeasureTheory.Measure.IsAddHaarMeasure
          (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d 1)) :=
        MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
      have hf_int : MeasureTheory.Integrable
          (fun x => (f.1 : NPointDomain d 1 → ℂ) x) MeasureTheory.volume :=
        f.1.integrable (μ := MeasureTheory.volume)
      exact (hf_int.const_mul v₀).congr
        (hkernel_ae.mono fun x hx => by simp [mul_comm, hx])

/-- Helper: the integral of a polynomial-growth kernel against a Schwartz function defines
    a continuous linear functional on Schwartz space.

    The mathematical content is standard (Reed-Simon I, Theorem V.10):
    |∫ K(x)f(x)dx| ≤ C_bd · I_dim · 2^(N+dim+1) · seminorm_{N+dim+1,0}(f)
    where I_dim = ∫ (1+|x|)^{-(dim+1)} dx is finite (dim = n*(d+1)).

    The proof requires:
    - `SchwartzMap.one_add_le_sup_seminorm_apply` for decay of Schwartz functions
    - `integrable_one_add_norm` for integrability of (1+|x|)^{-r} when r > dim
    - `SchwartzMap.mkCLMtoNormedSpace` to assemble the CLM from the seminorm bound
    - `HasTemperateGrowth` instance for `volume` on `NPointDomain d n`

    Currently blocked by: `IsAddHaarMeasure` for `volume` on `Fin n → Fin (d+1) → ℝ`
    (nested Pi type). Mathlib provides the instance for single-level Pi types
    (`Fin n → ℝ`) but not for nested Pi types. The mathematical content is
    unambiguous — this is a standard functional analysis result. -/
theorem schwartz_polynomial_kernel_continuous {d n : ℕ} [NeZero d]
    (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : C_bd > 0)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    Continuous (fun f : SchwartzNPoint d n => ∫ x, K x * f x) := by
  -- Provide the IsAddHaarMeasure instance for the nested pi type (not found by inferInstance)
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  -- Strategy: construct a CLM via mkCLMtoNormedSpace and extract continuity
  suffices h : ∃ (A : SchwartzNPoint d n →L[ℂ] ℂ), ∀ f, A f = ∫ x, K x * f x by
    obtain ⟨A, hA⟩ := h; simp_rw [← hA]; exact A.continuous
  -- Key: (1+t)^N ≤ 2^N * (1 + t^N) for t ≥ 0
  have h_binom_ineq : ∀ (t : ℝ), 0 ≤ t → (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
    intro t ht
    have h2t : 1 + t ≤ 2 * max 1 t :=
      calc 1 + t ≤ max 1 t + max 1 t := add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = 2 * max 1 t := by ring
    calc (1 + t) ^ N
        ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by positivity) h2t N
      _ = 2 ^ N * (max 1 t) ^ N := by rw [mul_pow]
      _ ≤ 2 ^ N * (1 + t ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total t 1 with h | h
          · rw [max_eq_left h]; simp [one_pow]; linarith [pow_nonneg ht N]
          · rw [max_eq_right h]; linarith [show (1 : ℝ) ^ N = 1 from one_pow N]
  -- Helper: K*f is integrable for any Schwartz f
  have hKf_int : ∀ f : SchwartzNPoint d n,
      MeasureTheory.Integrable (fun x => K x * f x) MeasureTheory.volume := by
    intro f
    have hf_int := f.integrable (μ := MeasureTheory.volume)
    have hf_pow_int := f.integrable_pow_mul MeasureTheory.volume N
    -- Majorant: g(x) = C_bd * 2^N * (‖f(x)‖ + ‖x‖^N * ‖f(x)‖) is integrable
    have hg_int : MeasureTheory.Integrable
        (fun x => C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
          ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖)) MeasureTheory.volume :=
      (hf_int.norm.add hf_pow_int).const_mul (C_bd * 2 ^ N)
    apply hg_int.mono' (hK_meas.mul f.integrable.aestronglyMeasurable)
    filter_upwards [hK_bound] with x hx
    simp only [Pi.mul_apply, norm_mul]
    calc ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖
        ≤ C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ :=
          mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ ≤ C_bd * (2 ^ N * (1 + ‖x‖ ^ N)) * ‖(f : NPointDomain d n → ℂ) x‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (h_binom_ineq ‖x‖ (norm_nonneg _)) (le_of_lt hC)
      _ = C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
            ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖) := by ring
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (fun f => ∫ x, K x * f x) ?_ ?_ ?_,
    fun f => rfl⟩
  · -- Additivity: ∫ K*(f+g) = ∫ K*f + ∫ K*g
    intro f g; simp only [SchwartzMap.add_apply, mul_add]
    exact MeasureTheory.integral_add (hKf_int f) (hKf_int g)
  · -- Scalar: ∫ K*(a•f) = a • ∫ K*f
    intro a f; simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ x : NPointDomain d n, K x * (a * f x) = a * (K x * f x) from
      fun x => by ring]
    exact MeasureTheory.integral_const_mul a _
  · -- Seminorm bound: ∃ s C, 0 ≤ C ∧ ∀ f, ‖∫ K*f‖ ≤ C * (s.sup seminormFamily) f
    -- Let D = finrank, M = N + D + 1
    set D := Module.finrank ℝ (NPointDomain d n)
    set M := N + D + 1
    -- I_D = ∫ (1+‖x‖)^(-(D+1)) < ∞
    have hD_lt : (D : ℝ) < ↑(D + 1) := by push_cast; linarith
    have hI_int : MeasureTheory.Integrable
        (fun x : NPointDomain d n => (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)))
        MeasureTheory.volume :=
      integrable_one_add_norm hD_lt
    set I_D := ∫ x : NPointDomain d n, (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ))
    -- The constant
    set C_sem := C_bd * 2 ^ M * I_D
    refine ⟨Finset.Iic (M, 0), C_sem, ?_, ?_⟩
    · -- 0 ≤ C_sem
      apply mul_nonneg (mul_nonneg (le_of_lt hC) (by positivity))
      apply MeasureTheory.integral_nonneg
      intro x; apply Real.rpow_nonneg; linarith [norm_nonneg x]
    · -- The bound: ‖∫ K*f‖ ≤ C_sem * (s.sup seminormFamily) f
      intro f
      -- Abbreviate the seminorm
      set sem := (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)
      -- From one_add_le_sup_seminorm_apply: (1+‖x‖)^M * ‖f(x)‖ ≤ 2^M * sem(f)
      have hsem_bound : ∀ x : NPointDomain d n,
          (1 + ‖x‖) ^ M * ‖(f : NPointDomain d n → ℂ) x‖ ≤ 2 ^ M * sem f := by
        intro x
        have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, 0))
          (le_refl M) (le_refl 0) f x
        rwa [norm_iteratedFDeriv_zero] at h
      -- Pointwise bound: ‖K x * f x‖ ≤ C_bd * 2^M * sem(f) * (1+‖x‖)^(-(D+1))
      have hpointwise : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
          ‖K x * (f : NPointDomain d n → ℂ) x‖ ≤
            C_bd * 2 ^ M * sem f * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) := by
        filter_upwards [hK_bound] with x hx
        have h1x_pos : (0 : ℝ) < 1 + ‖x‖ := by linarith [norm_nonneg x]
        have h1xD1_pos : (0 : ℝ) < (1 + ‖x‖) ^ (D + 1) := pow_pos h1x_pos _
        -- Rewrite rpow as inverse of natural power
        rw [Real.rpow_neg (le_of_lt h1x_pos), Real.rpow_natCast]
        rw [norm_mul]
        -- ‖K x‖ * ‖f x‖ ≤ C_bd * (1+‖x‖)^N * ‖f x‖
        have step1 : ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖ ≤
            C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ :=
          mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        -- (1+‖x‖)^N * ‖f x‖ ≤ 2^M * sem(f) / (1+‖x‖)^(D+1)
        -- From: (1+‖x‖)^M * ‖f x‖ ≤ 2^M * sem(f) and M = N + D + 1
        have step2 : (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ ≤
            2 ^ M * sem f * ((1 + ‖x‖) ^ (D + 1))⁻¹ := by
          rw [le_mul_inv_iff₀ h1xD1_pos]
          calc (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ * (1 + ‖x‖) ^ (D + 1)
              = (1 + ‖x‖) ^ (N + (D + 1)) * ‖(f : NPointDomain d n → ℂ) x‖ := by
                rw [pow_add]; ring
            _ = (1 + ‖x‖) ^ M * ‖(f : NPointDomain d n → ℂ) x‖ := by
                congr 1
            _ ≤ 2 ^ M * sem f := hsem_bound x
        calc ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖
            ≤ C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ := step1
          _ = C_bd * ((1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖) := by ring
          _ ≤ C_bd * (2 ^ M * sem f * ((1 + ‖x‖) ^ (D + 1))⁻¹) :=
              mul_le_mul_of_nonneg_left step2 (le_of_lt hC)
          _ = C_bd * 2 ^ M * sem f * ((1 + ‖x‖) ^ (D + 1))⁻¹ := by ring
      -- Integrate the pointwise bound
      calc ‖(fun f => ∫ x, K x * f x) f‖
          = ‖∫ x, K x * (f : NPointDomain d n → ℂ) x‖ := by rfl
        _ ≤ ∫ x, ‖K x * (f : NPointDomain d n → ℂ) x‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ x, C_bd * 2 ^ M * sem f * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) :=
            MeasureTheory.integral_mono_ae (hKf_int f).norm
              (hI_int.const_mul (C_bd * 2 ^ M * sem f)) hpointwise
        _ = C_bd * 2 ^ M * sem f * I_D := by
            rw [MeasureTheory.integral_const_mul]
        _ = C_bd * 2 ^ M * I_D * sem f := by ring
        _ = C_sem * sem f := by rfl

/-- **Continuity of Schwartz integration against a polynomially bounded kernel.**

    If K : D → ℂ is measurable and satisfies the a.e. polynomial bound
    ‖K(x)‖ ≤ C · (1 + ‖x‖)^N, then the linear functional f ↦ ∫ K(x)·f(x) dx
    is continuous on Schwartz space.

    Ref: Reed-Simon I, Theorem V.10; Hormander, Theorem 7.1.18 -/
theorem schwartz_continuous_of_polynomial_bound {d n : ℕ} [NeZero d]
    (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : C_bd > 0)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    Continuous (fun f : SchwartzNPoint d n => ∫ x, K x * f x) :=
  schwartz_polynomial_kernel_continuous K hK_meas C_bd N hC hK_bound

/-- On compact Euclidean regions whose Wick images stay inside PET,
    the BHW Euclidean kernel is uniformly bounded.

    This is the genuine local regularity statement available from the current
    analytic continuation infrastructure: away from the PET boundary, the kernel
    is just the restriction of a holomorphic function and therefore locally
    bounded. The remaining E0 difficulty is to control what happens near the
    Euclidean singular locus where the Wick image approaches the PET boundary,
    together with the behavior at spatial infinity. -/
private theorem bhw_euclidean_kernel_bounded_on_compact_in_permutedExtendedTube
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (hPET : ∀ x ∈ K, (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
    ∃ C : ℝ, ∀ x ∈ K,
      ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ ≤ C := by
  set F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ := (W_analytic_BHW Wfn n).val
  set wick : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ) :=
    fun x k => wickRotatePoint (x k)
  have hF_cont : ContinuousOn F_ext (PermutedExtendedTube d n) :=
    (W_analytic_BHW Wfn n).property.1.continuousOn
  have hwickpt_cont : Continuous (wickRotatePoint (d := d)) := by
    apply continuous_pi
    intro μ
    simp only [wickRotatePoint]
    split_ifs
    · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
    · exact Complex.continuous_ofReal.comp (continuous_apply μ)
  have hwick_cont : Continuous wick := by
    apply continuous_pi
    intro k
    exact hwickpt_cont.comp (continuous_apply k)
  have hkernel_cont : ContinuousOn (fun x : NPointDomain d n => ‖F_ext (wick x)‖) K := by
    refine (hF_cont.comp hwick_cont.continuousOn ?_).norm
    intro x hx
    simpa [wick] using hPET x hx
  obtain ⟨C, hC⟩ :=
    hK.exists_bound_of_continuousOn (f := fun x : NPointDomain d n => ‖F_ext (wick x)‖)
      hkernel_cont
  refine ⟨C, ?_⟩
  intro x hx
  simpa [F_ext, wick] using hC x hx

/-- Corollary of local PET boundedness on compact Euclidean regions with strictly
    increasing positive time coordinates. -/
private theorem bhw_euclidean_kernel_bounded_on_compact_positiveOrdered
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (hord : ∀ x ∈ K, ∀ k j : Fin n, k < j → x k 0 < x j 0)
    (hpos : ∀ x ∈ K, ∀ k : Fin n, 0 < x k 0) :
    ∃ C : ℝ, ∀ x ∈ K,
      ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ ≤ C := by
  refine bhw_euclidean_kernel_bounded_on_compact_in_permutedExtendedTube
    (Wfn := Wfn) hK ?_
  intro x hx
  have hFT : (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n :=
      euclidean_ordered_in_forwardTube x (hord x hx) (hpos x hx)
  have hFT_BHW : (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hFT
  have hPET_BHW : (fun k => wickRotatePoint (x k)) ∈ BHW.PermutedExtendedTube d n :=
    BHW.forwardTube_subset_permutedExtendedTube hFT_BHW
  simpa [BHW_permutedExtendedTube_eq (d := d) (n := n)] using hPET_BHW

/-- On compact Euclidean regions whose points stay pairwise distinct and lie in a
    common open half-space, the BHW Euclidean kernel is uniformly bounded.

    This packages the pointwise geometry now available in
    `euclidean_commonHalfSpace_in_permutedTube`: after a suitable Euclidean
    rotation, such configurations have distinct positive times, hence lie in PET. -/
private theorem bhw_euclidean_kernel_bounded_on_compact_commonHalfSpace
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (hOmega : ∀ x ∈ K, x ∈ OmegaRegion d n)
    (hhs : ∃ v : Fin (d + 1) → ℝ, ∀ x ∈ K, ∀ i : Fin n, ∑ μ, v μ * x i μ > 0) :
    ∃ C : ℝ, ∀ x ∈ K,
      ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ ≤ C := by
  rcases hhs with ⟨v, hv⟩
  refine bhw_euclidean_kernel_bounded_on_compact_in_permutedExtendedTube
    (Wfn := Wfn) hK ?_
  intro x hx
  exact euclidean_commonHalfSpace_in_permutedTube (d := d) x (hOmega x hx) ⟨v, hv x hx⟩

/-- The Wick-rotated BHW kernel is integrable against any compactly supported
    Schwartz function whose topological support stays inside PET.

    This isolates the genuinely easy half of the Euclidean pairing problem:
    away from the PET boundary/diagonal singular strata, the kernel is continuous
    and therefore bounded on the compact support. The unresolved part of
    `wick_rotated_kernel_mul_zeroDiagonal_integrable` is exactly what happens
    when the support approaches the coincidence strata. -/
theorem wick_rotated_kernel_mul_schwartz_integrable_of_hasCompactSupport_of_tsupport_in_permutedTube
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d) (f : SchwartzNPoint d n)
    (hcompact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hPET : ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * f x)
      MeasureTheory.volume := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  let K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))
  have hK_meas :
      MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume :=
    bhw_euclidean_kernel_measurable (Wfn := Wfn)
  obtain ⟨C, hC⟩ :=
    bhw_euclidean_kernel_bounded_on_compact_in_permutedExtendedTube
      (Wfn := Wfn) hcompact.isCompact hPET
  let C' : ℝ := max C 0
  have hf_int : MeasureTheory.Integrable (fun x : NPointDomain d n => f x) MeasureTheory.volume :=
    f.integrable (μ := MeasureTheory.volume)
  have hdom_int : MeasureTheory.Integrable (fun x : NPointDomain d n => C' * ‖f x‖)
      MeasureTheory.volume :=
    hf_int.norm.const_mul C'
  apply hdom_int.mono' (hK_meas.mul hf_int.aestronglyMeasurable)
  filter_upwards with x
  by_cases hx : x ∈ tsupport (f : NPointDomain d n → ℂ)
  · have hKx : ‖K x‖ ≤ C' := (hC x hx).trans (le_max_left _ _)
    calc
      ‖K x * f x‖ = ‖K x‖ * ‖f x‖ := norm_mul _ _
      _ ≤ C' * ‖f x‖ := mul_le_mul_of_nonneg_right hKx (norm_nonneg _)
  · have hx_support : x ∉ Function.support (f : NPointDomain d n → ℂ) := by
      intro hx'
      exact hx (subset_tsupport _ hx')
    have hfx : f x = 0 := by
      by_contra hne
      exact hx_support (by simpa [Function.mem_support, hne])
    calc
      ‖K x * f x‖ = 0 := by simp [hfx]
      _ ≤ C' * ‖f x‖ := by
        exact mul_nonneg (le_max_right _ _) (norm_nonneg _)

/-- The Wick-rotated BHW kernel is integrable against compactly supported
    Schwartz functions supported on configurations that stay pairwise distinct
    inside a common open half-space.

    This is the intrinsic Euclidean version of the previous PET-support lemma:
    the support hypothesis is stated on real configurations rather than directly
    on their Wick images. The common-half-space geometry is exactly what lets the
    Wick-rotated support sit inside PET pointwise. -/
theorem wick_rotated_kernel_mul_schwartz_integrable_of_hasCompactSupport_of_tsupport_in_commonHalfSpace
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d) (f : SchwartzNPoint d n)
    (hcompact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hOmega : tsupport (f : NPointDomain d n → ℂ) ⊆ OmegaRegion d n)
    (hhs : ∃ v : Fin (d + 1) → ℝ,
      ∀ x ∈ tsupport (f : NPointDomain d n → ℂ), ∀ i : Fin n, ∑ μ, v μ * x i μ > 0) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * f x)
      MeasureTheory.volume := by
  let K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))
  have hK_meas :
      MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume :=
    bhw_euclidean_kernel_measurable (Wfn := Wfn)
  obtain ⟨C, hC⟩ :=
    bhw_euclidean_kernel_bounded_on_compact_commonHalfSpace
      (Wfn := Wfn) hcompact.isCompact
      (fun x hx => hOmega hx)
      hhs
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  let C' : ℝ := max C 0
  have hf_int : MeasureTheory.Integrable (fun x : NPointDomain d n => f x) MeasureTheory.volume :=
    f.integrable (μ := MeasureTheory.volume)
  have hdom_int : MeasureTheory.Integrable (fun x : NPointDomain d n => C' * ‖f x‖)
      MeasureTheory.volume :=
    hf_int.norm.const_mul C'
  apply hdom_int.mono' (hK_meas.mul hf_int.aestronglyMeasurable)
  filter_upwards with x
  by_cases hx : x ∈ tsupport (f : NPointDomain d n → ℂ)
  · have hKx : ‖K x‖ ≤ C' := (hC x hx).trans (le_max_left _ _)
    calc
      ‖K x * f x‖ = ‖K x‖ * ‖f x‖ := norm_mul _ _
      _ ≤ C' * ‖f x‖ := mul_le_mul_of_nonneg_right hKx (norm_nonneg _)
  · have hx_support : x ∉ Function.support (f : NPointDomain d n → ℂ) := by
      intro hx'
      exact hx (subset_tsupport _ hx')
    have hfx : f x = 0 := by
      by_contra hne
      exact hx_support (by simpa [Function.mem_support, hne])
    calc
      ‖K x * f x‖ = 0 := by simp [hfx]
      _ ≤ C' * ‖f x‖ := by
        exact mul_nonneg (le_max_right _ _) (norm_nonneg _)

omit [NeZero d] in
private def translateNPointDomain (a : SpacetimeDim d) {n : ℕ} :
    NPointDomain d n → NPointDomain d n :=
  fun x i => x i - a

omit [NeZero d] in
private theorem translateNPointDomain_antilipschitz (a : SpacetimeDim d) {n : ℕ} :
    AntilipschitzWith 1 (translateNPointDomain (d := d) (n := n) a) := by
  refine AntilipschitzWith.of_le_mul_dist ?_
  intro x y
  have hsub :
      x - y = translateNPointDomain (d := d) (n := n) a x -
        translateNPointDomain (d := d) (n := n) a y := by
    ext i μ
    simp [translateNPointDomain, sub_eq_add_neg]
  simpa [one_mul, dist_eq_norm] using le_of_eq (congrArg norm hsub)

omit [NeZero d] in
private theorem translateNPointDomain_hasTemperateGrowth (a : SpacetimeDim d) {n : ℕ} :
    Function.HasTemperateGrowth (translateNPointDomain (d := d) (n := n) a) := by
  let c : NPointDomain d n := fun _ => -a
  have hconst : Function.HasTemperateGrowth (fun _ : NPointDomain d n => c) :=
    Function.HasTemperateGrowth.const c
  have hid : Function.HasTemperateGrowth (fun x : NPointDomain d n => x) := by
    simpa using (ContinuousLinearMap.id ℝ (NPointDomain d n)).hasTemperateGrowth
  simpa [translateNPointDomain, c, sub_eq_add_neg, Pi.add_apply] using hid.add hconst

/-- Compactly supported coincidence-free Schwartz functions pair integrably with
    the Wick-rotated BHW kernel.

    This removes the remaining *local* singularity issue on compact sets away from
    the coincidence locus. The proof shifts the compact support far enough in
    Euclidean time so that every translated configuration lies in a common open
    half-space, applies the previous common-half-space integrability theorem
    there, and transports integrability back using measure-preserving translation
    plus the a.e. Euclidean translation invariance of the BHW kernel. -/
theorem wick_rotated_kernel_mul_schwartz_integrable_of_hasCompactSupport_of_tsupport_in_OmegaRegion
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d) (f : SchwartzNPoint d n)
    (hcompact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hOmega : tsupport (f : NPointDomain d n → ℂ) ⊆ OmegaRegion d n) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * f x)
      MeasureTheory.volume := by
  let K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))
  have hK_meas :
      MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume :=
    bhw_euclidean_kernel_measurable (Wfn := Wfn)
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  obtain ⟨C, hC⟩ :=
    hcompact.isCompact.exists_bound_of_continuousOn
      (f := fun x : NPointDomain d n => ‖x‖) continuous_norm.continuousOn
  let T : ℝ := max C 0 + 1
  let a : SpacetimeDim d := fun μ => if μ = 0 then T else 0
  let aN : NPointDomain d n := fun _ => a
  let τ : NPointDomain d n → NPointDomain d n := translateNPointDomain (d := d) (n := n) a
  let g : SchwartzNPoint d n :=
    SchwartzMap.compCLMOfAntilipschitz ℂ
      (translateNPointDomain_hasTemperateGrowth (d := d) (n := n) a)
      (translateNPointDomain_antilipschitz (d := d) (n := n) a) f
  have hg_apply : ∀ x : NPointDomain d n, g x = f (τ x) := by
    intro x
    simp [g, τ]
  have hg_compact : HasCompactSupport (g : NPointDomain d n → ℂ) := by
    simpa [g, τ, translateNPointDomain, sub_eq_add_neg]
      using hcompact.comp_homeomorph (Homeomorph.addRight (-aN))
  have hτ_tsupport :
      tsupport (g : NPointDomain d n → ℂ) =
        (Homeomorph.addRight (-aN)) ⁻¹' tsupport (f : NPointDomain d n → ℂ) := by
    simpa [g, τ, translateNPointDomain, aN, sub_eq_add_neg] using
      (tsupport_comp_eq_preimage (g := (f : NPointDomain d n → ℂ))
        (Homeomorph.addRight (-aN)))
  have hτ_mem : ∀ x ∈ tsupport (g : NPointDomain d n → ℂ),
      τ x ∈ tsupport (f : NPointDomain d n → ℂ) := by
    intro x hx
    simpa [hτ_tsupport, τ, translateNPointDomain, aN, sub_eq_add_neg] using hx
  have hg_Omega : tsupport (g : NPointDomain d n → ℂ) ⊆ OmegaRegion d n := by
    intro x hx i j hij
    have hx' := hτ_mem x hx
    have hdist := hOmega hx' i j hij
    intro hEq
    apply hdist
    simpa [τ, translateNPointDomain, hEq]
  have hT_pos : 0 < T := by
    have : 0 ≤ max C 0 := le_max_right _ _
    linarith
  have hg_hs :
      ∃ v : Fin (d + 1) → ℝ,
        ∀ x ∈ tsupport (g : NPointDomain d n → ℂ), ∀ i : Fin n, ∑ μ, v μ * x i μ > 0 := by
    refine ⟨fun μ => if μ = 0 then (1 : ℝ) else 0, ?_⟩
    intro x hx i
    have hx' := hτ_mem x hx
    have hτ_norm : ‖τ x‖ ≤ C := by
      simpa using hC (τ x) hx'
    have hcoord_norm : ‖(τ x i) 0‖ ≤ ‖τ x‖ := by
      exact (norm_le_pi_norm (τ x i) 0).trans (norm_le_pi_norm (τ x) i)
    have hcoord_lower : -‖τ x‖ ≤ (τ x i) 0 := by
      calc
        -‖τ x‖ ≤ -‖(τ x i) 0‖ := by linarith
        _ ≤ (τ x i) 0 := by
          simpa [Real.norm_eq_abs] using neg_abs_le ((τ x i) 0)
    have htime : 0 < x i 0 := by
      have hx_eq : x i 0 = (τ x i) 0 + T := by
        simp [τ, translateNPointDomain, a, T]
      rw [hx_eq]
      have hmax : C ≤ max C 0 := le_max_left _ _
      linarith
    simpa using htime
  have hg_int :=
    wick_rotated_kernel_mul_schwartz_integrable_of_hasCompactSupport_of_tsupport_in_commonHalfSpace
      (Wfn := Wfn) g hg_compact hg_Omega hg_hs
  have hg_add : ∀ x : NPointDomain d n, g (x + aN) = f x := by
    intro x
    rw [hg_apply]
    congr 1
    ext i μ
    simp [τ, translateNPointDomain, aN, sub_eq_add_neg]
  have hg_shift_int :
      MeasureTheory.Integrable
        (fun x : NPointDomain d n => K (x + aN) * f x) MeasureTheory.volume := by
    have hEq :
        (fun x : NPointDomain d n => K (x + aN) * f x) =
          (fun x : NPointDomain d n => (K x * g x)) ∘ fun x => x + aN := by
      funext x
      simp [hg_add]
    rw [hEq]
    exact hg_int.comp_add_right aN
  have hf_int : MeasureTheory.Integrable (fun x : NPointDomain d n => f x) MeasureTheory.volume :=
    f.integrable (μ := MeasureTheory.volume)
  let P : NPointDomain d n → Prop :=
    fun x => (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n
  have hP_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume, P x :=
    ae_euclidean_points_in_permutedTube
  have hP_shift_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume, P (x + aN) := by
    exact (MeasureTheory.eventually_add_right_iff
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)))
      (t := aN) (p := P)).2 hP_ae
  have hK_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume, K x = K (x + aN) := by
    filter_upwards [hP_ae, hP_shift_ae] with x hx hx_shift
    have hx' : (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n := by
      simpa [P] using hx
    have hx_shift0 : (fun k => wickRotatePoint (x k + a)) ∈ PermutedExtendedTube d n := by
      simpa [P, aN] using hx_shift
    have hwick_add :
        (fun k => wickRotatePoint (x k + a)) =
          (fun k μ => wickRotatePoint (x k) μ + wickRotatePoint a μ) := by
      ext k μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [wickRotatePoint, mul_add]
      · simp [wickRotatePoint, hμ]
    have hx_shift' :
        (fun k μ => wickRotatePoint (x k) μ + wickRotatePoint a μ) ∈
          PermutedExtendedTube d n := by
      simpa [hwick_add] using hx_shift0
    simpa [K, aN, hwick_add] using
      (bhw_translation_invariant Wfn (wickRotatePoint a)
        (fun k => wickRotatePoint (x k)) hx' hx_shift').symm
  exact hg_shift_int.congr <| hK_ae.mono fun x hx => by
    simpa [K] using congrArg (fun z : ℂ => z * f x) hx.symm

set_option maxHeartbeats 400000 in
/-- The constructed Schwinger functional is continuous on the OS-I
    zero-diagonal test space.

    This is the honest E0 surface currently needed in `OsterwalderSchraderAxioms`.
    Unlike the deleted full-Schwartz theorem fronts, this matches the corrected
    OS-I axiom surface after the zero-diagonal repair. -/
theorem constructedSchwinger_tempered_zeroDiagonal (Wfn : WightmanFunctions d) (n : ℕ) :
    Continuous (constructSchwingerFunctions Wfn n) := by
  -- K : NPointDomain d n → ℂ is the Wick-rotated BHW kernel
  set K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) with hK_def
  -- Unfold the definition: constructSchwingerFunctions Wfn n f = ∫ K * f.1
  show Continuous (fun f : ZeroDiagonalSchwartz d n =>
    ∫ x : NPointDomain d n, K x * (f.1 : NPointDomain d n → ℂ) x)
  -- IsAddHaarMeasure instance for NPointDomain (needed throughout)
  haveI hHaar : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  -- K is a.e. strongly measurable
  have hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume :=
    bhw_euclidean_kernel_measurable Wfn
  by_cases hcoin : (CoincidenceLocus d n).Nonempty
  · -- n ≥ 2: use WithSeminorms on ZeroDiagonalSchwartz + Seminorm.cont_withSeminorms_normedSpace
    -- Step 1: Get growth bound from WightmanFunctions
    obtain ⟨C_bd, N, q, hC_pos, hgrowth⟩ := (hasForwardTubeGrowth_of_wightman Wfn) n
    -- Step 2: WithSeminorms on ZeroDiagonalSchwartz d n (via induced topology)
    have hWS : WithSeminorms
        ((schwartzSeminormFamily ℂ (NPointDomain d n) ℂ).comp
          (zeroDiagonalSubmodule d n).subtype) :=
      Topology.IsInducing.withSeminorms
        (schwartz_withSeminorms (𝕜 := ℂ) (E := NPointDomain d n) (F := ℂ))
        Topology.IsInducing.subtypeVal
    -- Step 3: Build the linear map T f = ∫ K * f.1
    have hlin : IsLinearMap ℂ
        (fun f : ZeroDiagonalSchwartz d n =>
          ∫ x : NPointDomain d n, K x * (f.1 : NPointDomain d n → ℂ) x) := by
      constructor
      · intro f g
        have hf_int := wick_rotated_kernel_mul_zeroDiagonal_integrable (Wfn := Wfn) f
        have hg_int := wick_rotated_kernel_mul_zeroDiagonal_integrable (Wfn := Wfn) g
        have heq : (fun x : NPointDomain d n =>
              K x * ((f + g).1 : NPointDomain d n → ℂ) x) =
            fun x => K x * (f.1 : NPointDomain d n → ℂ) x +
              K x * (g.1 : NPointDomain d n → ℂ) x := by
          ext x
          have : ((f + g).1 : NPointDomain d n → ℂ) x = f.1 x + g.1 x := by
            change (f.1 + g.1) x = _; rfl
          rw [this]; ring
        simp_rw [heq]
        exact MeasureTheory.integral_add hf_int hg_int
      · intro c f
        have heq : (fun x : NPointDomain d n =>
              K x * ((c • f).1 : NPointDomain d n → ℂ) x) =
            fun x => c • (K x * (f.1 : NPointDomain d n → ℂ) x) := by
          ext x
          have : ((c • f).1 : NPointDomain d n → ℂ) x = c * f.1 x := by
            change (c • f.1) x = _; simp [smul_eq_mul]
          rw [this, smul_eq_mul]; ring
        simp_rw [heq]
        exact MeasureTheory.integral_smul c _
    let T : ZeroDiagonalSchwartz d n →ₗ[ℂ] ℂ := hlin.mk'
    -- Step 4: Prove T is continuous via seminorm bound
    change Continuous T
    -- deg_D = finrank ℝ (NPointDomain d n), deg_M = N + deg_D + q + 2
    -- Note: deg_M is chosen so that deg_M = N + (deg_D + q + 2), ensuring cancellation
    let deg_D : ℕ := Module.finrank ℝ (NPointDomain d n)
    let deg_M : ℕ := N + deg_D + q + 2
    let nR : ℝ := ((n + 2 : ℕ) : ℝ)
    -- Integral of the tail: I_tail = ∫ (1+|x|)^{-(deg_D+1)}
    have hD_lt : (deg_D : ℝ) < ↑(deg_D + 1) := by push_cast; linarith
    have hI_int : MeasureTheory.Integrable
        (fun x : NPointDomain d n => (1 + ‖x‖) ^ (-(↑(deg_D + 1) : ℝ)))
        MeasureTheory.volume :=
      integrable_one_add_norm hD_lt
    let I_tail : ℝ := ∫ x : NPointDomain d n, (1 + ‖x‖) ^ (-(↑(deg_D + 1) : ℝ))
    have hI_tail_nonneg : 0 ≤ I_tail :=
      MeasureTheory.integral_nonneg fun x => Real.rpow_nonneg (by linarith [norm_nonneg x]) _
    -- C_sem_val = C_bd * nR^N * (2^(deg_M+q+1) / q!) * I_tail
    -- (Note: uses Finset.Iic (deg_M, q+1) seminorm since the vanishing bound uses (deg_M, q+1))
    let C_sem_val : ℝ := C_bd * nR ^ N * (2 ^ (deg_M + q + 1) / (Nat.factorial q : ℝ)) * I_tail
    have hC_sem_nonneg : 0 ≤ C_sem_val := by positivity
    let C_sem : NNReal := ⟨C_sem_val, hC_sem_nonneg⟩
    apply Seminorm.cont_withSeminorms_normedSpace ℂ hWS T
    -- Use Finset.Iic (deg_M, q+1) since C_vanish uses (deg_M, q+1) seminorm
    refine ⟨Finset.Iic (deg_M, q + 1), C_sem, ?_⟩
    -- Prove: (normSeminorm ℂ ℂ).comp T ≤ C_sem • (Finset.Iic (deg_M, q+1)).sup
    --   ((schwartzSeminormFamily ℂ .. ℂ).comp (zeroDiagonalSubmodule d n).subtype)
    -- i.e. ∀ f, ‖T f‖ ≤ C_sem_val * sem_f where sem_f = (Finset.Iic (deg_M,q+1)).sup sem f.1
    rw [Seminorm.le_def]
    intro f
    -- The Schwartz seminorm using (deg_M, q+1)
    let sem_f := ((Finset.Iic (deg_M, q + 1)).sup
      (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)) f.1
    -- Step 4a: A.e. kernel weighted bound
    have hK_ae_bound :
        ∀ᵐ x : NPointDomain d n ∂MeasureTheory.volume,
          ‖K x‖ * Metric.infDist x (CoincidenceLocus d n) ^ (q + 1) ≤
            C_bd * nR ^ N * (1 + ‖x‖) ^ N := by
      filter_upwards [ae_euclidean_points_in_permutedTube (d := d) (n := n),
        ae_pairwise_distinct_timeCoords (d := d) (n := n)] with x hx_pet hx_distinct
      let A : ℝ := 1 + ∑ i : Fin n, |x i 0|
      let a : SpacetimeDim d := fun μ => if μ = 0 then A else 0
      let xs : NPointDomain d n := fun k μ => x k μ + a μ
      have hpos : ∀ i : Fin n, xs i 0 > 0 := fun i => by
        have hi_le : |x i 0| ≤ ∑ j : Fin n, |x j 0| :=
          Finset.single_le_sum (fun j _ => abs_nonneg (x j 0)) (Finset.mem_univ i)
        simp [xs, a, A]; linarith [neg_abs_le (x i 0)]
      have hdistinct_xs : ∀ i j : Fin n, i ≠ j → xs i 0 ≠ xs j 0 :=
        fun i j hij => by simpa [xs, a] using hx_distinct i j hij
      let π := Tuple.sort (fun k => xs k 0)
      have hmono := Tuple.monotone_sort (fun k => xs k 0)
      have hinj : Function.Injective (fun k => xs k 0) :=
        fun i j h => by by_contra hij; exact hdistinct_xs i j hij h
      have hstrict : StrictMono ((fun k => xs k 0) ∘ π) :=
        hmono.strictMono_of_injective (hinj.comp π.injective)
      have hord : ∀ k j : Fin n, k < j → xs (π k) 0 < xs (π j) 0 :=
        fun k j hkj => hstrict hkj
      have hpos' : ∀ k : Fin n, xs (π k) 0 > 0 := fun k => hpos (π k)
      have hfwd : (fun k => wickRotatePoint (xs (π k))) ∈ ForwardTube d n :=
        euclidean_ordered_in_forwardTube (fun k => xs (π k)) hord hpos'
      have hxs_pet : (fun k => wickRotatePoint (xs k)) ∈ PermutedExtendedTube d n :=
        euclidean_distinct_in_permutedTube xs hdistinct_xs hpos
      have hwick_add : (fun k => wickRotatePoint (xs k)) =
          (fun k μ => wickRotatePoint (x k) μ + wickRotatePoint a μ) := by
        ext k μ; simp only [wickRotatePoint, xs, a]; split_ifs <;> push_cast <;> ring
      have htransl : K x = (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs k)) := by
        simp only [K, hK_def]; rw [hwick_add]
        exact (bhw_translation_invariant Wfn (wickRotatePoint a)
          (fun k => wickRotatePoint (x k)) hx_pet
          (by simpa [hwick_add] using hxs_pet)).symm
      have hperm : (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs k)) =
          (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs (π k))) :=
        ((W_analytic_BHW Wfn n).property.2.2.2 π
          (fun k => wickRotatePoint (xs k)) hxs_pet).symm
      have hagree : (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (xs (π k))) =
          (Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (xs (π k))) :=
        (W_analytic_BHW Wfn n).property.2.1 _ hfwd
      have hbound := hgrowth (fun k => xs (π k)) hfwd
      have hinfDist_eq : Metric.infDist (fun k => xs (π k)) (CoincidenceLocus d n) =
          Metric.infDist x (CoincidenceLocus d n) := by
        let c : NPointDomain d n := fun _ => a
        have hxs_eq : xs = c + x := by ext k μ; simp [xs, c, add_comm]
        have hΦ_isom : Isometry ((c + ·) : NPointDomain d n → NPointDomain d n) :=
          Isometry.of_dist_eq fun y z => dist_vadd_cancel_left c y z
        have hΦ_coinc : (c + ·) '' CoincidenceLocus d n = CoincidenceLocus d n := by
          ext y; simp only [Set.mem_image, CoincidenceLocus, Set.mem_setOf_eq]; constructor
          · rintro ⟨z, ⟨i, j, hij, hzij⟩, rfl⟩
            exact ⟨i, j, hij, show c i + z i = c j + z j by rw [show c i = c j from rfl, hzij]⟩
          · rintro ⟨i, j, hij, hyij⟩
            refine ⟨-c + y, ⟨i, j, hij, show (-c + y) i = (-c + y) j from ?_⟩, by simp⟩
            ext μ; simp only [Pi.add_apply, Pi.neg_apply]; have := congr_fun hyij μ; linarith
        have h_shift : Metric.infDist xs (CoincidenceLocus d n) =
            Metric.infDist x (CoincidenceLocus d n) := by
          have h := Metric.infDist_image hΦ_isom (x := x) (t := CoincidenceLocus d n)
          rw [hΦ_coinc] at h; rw [hxs_eq]; exact h
        let Ψ : NPointDomain d n → NPointDomain d n := fun y k => y (π k)
        have hΨ_isom : Isometry Ψ := fun y z => by
          show edist (Ψ y) (Ψ z) = edist y z
          rw [edist_pi_def, edist_pi_def]; simp only [Finset.sup_univ_eq_iSup]
          exact Equiv.iSup_comp (g := fun k => edist (y k) (z k)) π
        have hΨ_coinc : Ψ '' CoincidenceLocus d n = CoincidenceLocus d n := by
          ext y; simp only [Set.mem_image, CoincidenceLocus, Set.mem_setOf_eq, Ψ]; constructor
          · rintro ⟨z, ⟨i, j, hij, hzij⟩, rfl⟩
            exact ⟨π.symm i, π.symm j, fun h => hij (π.symm.injective h), by simp [hzij]⟩
          · rintro ⟨i, j, hij, hyij⟩
            exact ⟨fun k => y (π.symm k),
              ⟨π i, π j, fun h => hij (π.injective h), by simp [hyij]⟩, by ext k; simp⟩
        have h_perm : Metric.infDist (Ψ xs) (CoincidenceLocus d n) =
            Metric.infDist xs (CoincidenceLocus d n) := by
          have h := Metric.infDist_image hΨ_isom (x := xs) (t := CoincidenceLocus d n)
          rw [hΨ_coinc] at h; exact h
        exact h_perm.trans h_shift
      have hnorm_bound : (1 + ‖fun k => xs (π k)‖) ^ N ≤ (nR * (1 + ‖x‖)) ^ N := by
        apply pow_le_pow_left₀ (by positivity)
        have hA_nonneg : (0 : ℝ) ≤ A := by dsimp [A]; positivity
        have hcomp_bound : ∀ (k : Fin n) (μ : Fin (d + 1)), |xs (π k) μ| ≤ ‖x‖ + A := by
          intro k μ; simp only [xs, a]; split_ifs with h
          · calc |x (π k) μ + A|
                ≤ |x (π k) μ| + |A| := abs_add_le _ _
              _ ≤ ‖x‖ + A := by
                gcongr
                · exact (norm_le_pi_norm (x (π k)) μ).trans (norm_le_pi_norm x (π k))
                · exact le_of_eq (abs_of_nonneg hA_nonneg)
          · calc |x (π k) μ + 0| = |x (π k) μ| := by rw [add_zero]
              _ ≤ ‖x‖ := (norm_le_pi_norm (x (π k)) μ).trans (norm_le_pi_norm x (π k))
              _ ≤ ‖x‖ + A := le_add_of_nonneg_right hA_nonneg
        have hpi_bound : ‖fun k => xs (π k)‖ ≤ ‖x‖ + A := by
          apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro k
          apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro μ
          rw [Real.norm_eq_abs]; exact hcomp_bound k μ
        have hA_le : A ≤ 1 + n * ‖x‖ := by
          dsimp [A]; gcongr
          calc ∑ i : Fin n, |x i 0|
              ≤ ∑ _ : Fin n, ‖x‖ := by
                gcongr with i
                exact (Real.norm_eq_abs (x i 0) ▸ norm_le_pi_norm (x i) 0).trans (norm_le_pi_norm x i)
            _ = n * ‖x‖ := by simp [Finset.sum_const]
        calc 1 + ‖fun k => xs (π k)‖
            ≤ 1 + (‖x‖ + A) := by linarith [hpi_bound]
          _ ≤ 1 + (‖x‖ + (1 + n * ‖x‖)) := by linarith [hA_le]
          _ = 2 + (↑n + 1) * ‖x‖ := by push_cast; ring
          _ ≤ (↑n + 2) * (1 + ‖x‖) := by nlinarith [norm_nonneg x]
          _ = nR * (1 + ‖x‖) := by dsimp [nR]; push_cast; ring
      calc ‖K x‖ * Metric.infDist x (CoincidenceLocus d n) ^ (q + 1)
          = ‖(Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (xs (π k)))‖ *
              Metric.infDist (fun k => xs (π k)) (CoincidenceLocus d n) ^ (q + 1) := by
            rw [htransl, hperm, hagree, hinfDist_eq]
        _ ≤ C_bd * (1 + ‖fun k => xs (π k)‖) ^ N := hbound
        _ ≤ C_bd * (nR * (1 + ‖x‖)) ^ N := by gcongr
        _ = C_bd * nR ^ N * (1 + ‖x‖) ^ N := by rw [mul_pow]; ring
    -- Step 4b: Vanishing bound using explicit constant (no opaque existential)
    -- From weighted_infDist_bound_explicit with N=deg_M, m=q:
    -- (1+‖x‖)^deg_M * ‖f x‖ ≤ (2^(deg_M+q+1)/q!) * sem_f * δ^(q+1)
    let C_vanish_factor : ℝ := 2 ^ (deg_M + q + 1) / (Nat.factorial q : ℝ)
    have hvanish : ∀ x : NPointDomain d n,
        (1 + ‖x‖) ^ deg_M * ‖(f.1 : NPointDomain d n → ℂ) x‖ ≤
          C_vanish_factor * sem_f * Metric.infDist x (CoincidenceLocus d n) ^ (q + 1) :=
      VanishesToInfiniteOrderOnCoincidence.weighted_infDist_bound_explicit
        (f := f.1) f.2 deg_M q hcoin
    -- Step 4c: Pointwise product bound
    -- Note: the bound will have C_bd * nR^N * C_vanish_factor * sem_f / (1+‖x‖)^(deg_D+1)
    -- = (C_sem_val / I_tail) * sem_f / (1+‖x‖)^(deg_D+1)
    -- After integration this gives (C_sem_val / I_tail) * sem_f * I_tail = C_sem_val * sem_f.
    -- We set C_ptwise = C_bd * nR^N * C_vanish_factor for the pointwise constant.
    let C_ptwise : ℝ := C_bd * nR ^ N * C_vanish_factor
    have hC_ptwise_nonneg : 0 ≤ C_ptwise := by positivity
    have hC_ptwise_itail : C_ptwise * I_tail = C_sem_val := by
      simp only [C_ptwise, C_vanish_factor, C_sem_val]
    have hpointwise : ∀ᵐ x : NPointDomain d n ∂MeasureTheory.volume,
        ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ ≤
          C_ptwise * sem_f * (1 + ‖x‖) ^ (-(↑(deg_D + 1) : ℝ)) := by
      filter_upwards [hK_ae_bound] with x hx
      let δ : ℝ := Metric.infDist x (CoincidenceLocus d n)
      have hδ_nonneg : 0 ≤ δ := Metric.infDist_nonneg
      have hf_weighted : (1 + ‖x‖) ^ deg_M * ‖(f.1 : NPointDomain d n → ℂ) x‖ ≤
          C_vanish_factor * sem_f * δ ^ (q + 1) := hvanish x
      have h1x_pos : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
      rw [Real.rpow_neg (le_of_lt h1x_pos), Real.rpow_natCast, norm_mul]
      by_cases hδ : δ = 0
      · -- δ = 0 means x ∈ CoincidenceLocus, so f.1(x) = 0
        have hfx : ‖(f.1 : NPointDomain d n → ℂ) x‖ = 0 := by
          have hpow_pos : 0 < (1 + ‖x‖) ^ deg_M := pow_pos h1x_pos _
          have : (1 + ‖x‖) ^ deg_M * ‖(f.1 : NPointDomain d n → ℂ) x‖ = 0 := by
            have := hf_weighted; simp [hδ] at this
            exact le_antisymm this (mul_nonneg hpow_pos.le (norm_nonneg _))
          exact (mul_eq_zero.mp this).resolve_left (by positivity)
        simp [hfx]; positivity
      · -- δ > 0: combine bounds
        have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (Ne.symm hδ)
        have hδpow_pos : 0 < δ ^ (q + 1) := pow_pos hδ_pos _
        have hpow_pos : 0 < (1 + ‖x‖) ^ deg_M := pow_pos h1x_pos _
        have hK_div : ‖K x‖ ≤ C_bd * nR ^ N * (1 + ‖x‖) ^ N / δ ^ (q + 1) := by
          rw [le_div_iff₀ hδpow_pos]; nlinarith [hx, mul_nonneg (norm_nonneg (K x)) hδpow_pos.le]
        have hf_div : ‖(f.1 : NPointDomain d n → ℂ) x‖ ≤
            C_vanish_factor * sem_f * δ ^ (q + 1) / (1 + ‖x‖) ^ deg_M := by
          rw [le_div_iff₀ hpow_pos]
          nlinarith [hf_weighted, mul_nonneg hpow_pos.le
            (norm_nonneg ((f.1 : NPointDomain d n → ℂ) x))]
        have hpow_split : deg_M = N + (deg_D + q + 2) := by omega
        have hpow_D1_le : (1 + ‖x‖) ^ (deg_D + q + 2) ≥ (1 + ‖x‖) ^ (deg_D + 1) :=
          pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
        calc ‖K x‖ * ‖(f.1 : NPointDomain d n → ℂ) x‖
            ≤ (C_bd * nR ^ N * (1 + ‖x‖) ^ N / δ ^ (q + 1)) *
              (C_vanish_factor * sem_f * δ ^ (q + 1) / (1 + ‖x‖) ^ deg_M) := by gcongr
          _ = C_bd * nR ^ N * C_vanish_factor * sem_f / (1 + ‖x‖) ^ (deg_D + q + 2) := by
              rw [show deg_M = N + (deg_D + q + 2) from hpow_split, pow_add]
              field_simp [pow_pos h1x_pos, hδpow_pos.ne']; ring
          _ ≤ C_bd * nR ^ N * C_vanish_factor * sem_f / (1 + ‖x‖) ^ (deg_D + 1) := by
              exact div_le_div_of_nonneg_left (by positivity) (pow_pos h1x_pos _) hpow_D1_le
          _ = C_ptwise * sem_f * ((1 + ‖x‖) ^ (deg_D + 1))⁻¹ := by
              simp only [C_ptwise]; field_simp
    -- Step 4d: Integrate the bound
    have hdom_int : MeasureTheory.Integrable
        (fun x : NPointDomain d n =>
          C_ptwise * sem_f * (1 + ‖x‖) ^ (-(↑(deg_D + 1) : ℝ)))
        MeasureTheory.volume :=
      hI_int.const_mul (C_ptwise * sem_f)
    -- The integral of the pointwise bound is C_ptwise * sem_f * I_tail = C_sem_val * sem_f
    have hint_bound : ‖∫ x : NPointDomain d n, K x * (f.1 : NPointDomain d n → ℂ) x‖ ≤
        C_sem_val * sem_f := by
      calc ‖∫ x : NPointDomain d n, K x * (f.1 : NPointDomain d n → ℂ) x‖
          ≤ ∫ x : NPointDomain d n, ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ x : NPointDomain d n,
              C_ptwise * sem_f * (1 + ‖x‖) ^ (-(↑(deg_D + 1) : ℝ)) :=
            MeasureTheory.integral_mono_ae
              (wick_rotated_kernel_mul_zeroDiagonal_integrable (Wfn := Wfn) f).norm
              hdom_int hpointwise
        _ = C_ptwise * sem_f * I_tail := by rw [MeasureTheory.integral_const_mul]
        _ = C_sem_val * sem_f := by simp only [C_ptwise, C_sem_val]; ring
    -- Step 4e: Match the goal from Seminorm.cont_withSeminorms_normedSpace
    -- Goal: ((normSeminorm ℂ ℂ).comp T) f ≤
    --   (↑C_sem • (Finset.Iic ...).sup ((schwartzSeminormFamily ..).comp subtype)) f
    -- LHS = ‖T f‖, RHS = C_sem_val * ((s.sup (sem.comp subtype)) f)
    -- We show (s.sup (sem.comp subtype)) f = (s.sup sem) f.val = sem_f
    have hsem_comp : ((Finset.Iic (deg_M, q + 1)).sup
        ((schwartzSeminormFamily ℂ (NPointDomain d n) ℂ).comp
          (zeroDiagonalSubmodule d n).subtype)) f = sem_f := by
      simp only [sem_f]
      rw [Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
      congr 1
    simp only [Seminorm.coe_comp, Function.comp_apply, normSeminorm, Seminorm.smul_apply,
      NNReal.smul_def, NNReal.coe_mk, IsLinearMap.mk'_apply]
    rw [hsem_comp]
    exact hint_bound
  · -- n ≤ 1: K is a.e. polynomially bounded → use schwartz_polynomial_kernel_continuous
    -- Derive n ≤ 1 from emptiness of CoincidenceLocus
    have hn_le : n ≤ 1 := by
      by_contra h
      push_neg at h
      apply hcoin
      haveI : NeZero n := ⟨by omega⟩
      refine ⟨fun _ => 0, 0, ⟨1, by omega⟩, ?_, rfl⟩
      simp [Fin.ext_iff]
    -- Show K is a.e. polynomially bounded
    have hK_poly : ∃ (C_bd : ℝ) (N : ℕ), 0 < C_bd ∧
        ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
          ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N := by
      interval_cases n
      · -- n = 0: NPointDomain d 0 is Unique; K is just a constant
        refine ⟨‖K default‖ + 1, 0, by linarith [norm_nonneg (K default)],
          Filter.Eventually.of_forall fun x => ?_⟩
        have hx : x = default := Subsingleton.elim x default
        subst hx
        simp only [pow_zero, mul_one]
        linarith [norm_nonneg (K default)]
      · -- n = 1: K is a.e. equal to v₀ (translation invariance of W_analytic)
        let x₀ : NPointDomain d 1 := fun _ => Pi.single (0 : Fin (d + 1)) 1
        let v₀ : ℂ := K x₀
        have hfwd₀ : (fun k => wickRotatePoint (x₀ k)) ∈ ForwardTube d 1 :=
          euclidean_ordered_in_forwardTube (fun k => x₀ k)
            (fun k j hkj => by fin_cases k <;> fin_cases j <;> simp_all [Fin.lt_iff_val_lt_val])
            (fun k => by fin_cases k; simp [x₀, Pi.single_apply])
        have hkernel_ae : ∀ᵐ (x : NPointDomain d 1) ∂MeasureTheory.volume, K x = v₀ := by
          filter_upwards [ae_euclidean_points_in_permutedTube (d := d) (n := 1)] with x hx_pet
          simp only [K, v₀, hK_def]
          let A₁ : ℝ := 1 + |x 0 0|
          let a₁ : SpacetimeDim d := fun μ => if μ = 0 then A₁ else 0
          let xs₁ : NPointDomain d 1 := fun k μ => x k μ + a₁ μ
          have hpos₁ : xs₁ 0 0 > 0 := by
            simp [xs₁, a₁, A₁]; linarith [neg_abs_le (x 0 0)]
          have hfwd₁ : (fun k => wickRotatePoint (xs₁ k)) ∈ ForwardTube d 1 :=
            euclidean_ordered_in_forwardTube (fun k => xs₁ k)
              (fun k j hkj => by fin_cases k <;> fin_cases j <;> simp_all [Fin.lt_iff_val_lt_val])
              (fun k => by fin_cases k; exact hpos₁)
          have hxs₁_pet : (fun k => wickRotatePoint (xs₁ k)) ∈ PermutedExtendedTube d 1 :=
            euclidean_distinct_in_permutedTube xs₁
              (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all)
              (fun i => by fin_cases i; exact hpos₁)
          have hwick_add₁ : (fun k => wickRotatePoint (xs₁ k)) =
              (fun k μ => wickRotatePoint (x k) μ + wickRotatePoint a₁ μ) := by
            ext k μ; simp only [wickRotatePoint, xs₁, a₁]; split_ifs <;> push_cast <;> ring
          have htransl₁ :
              (W_analytic_BHW Wfn 1).val (fun k => wickRotatePoint (x k)) =
              (W_analytic_BHW Wfn 1).val (fun k => wickRotatePoint (xs₁ k)) := by
            rw [hwick_add₁]
            exact (bhw_translation_invariant Wfn (wickRotatePoint a₁)
              (fun k => wickRotatePoint (x k)) hx_pet
              (by simpa [hwick_add₁] using hxs₁_pet)).symm
          have hagree₁ := (W_analytic_BHW Wfn 1).property.2.1 _ hfwd₁
          have hagree₀ := (W_analytic_BHW Wfn 1).property.2.1 _ hfwd₀
          have htransl_const :
              (Wfn.spectrum_condition 1).choose (fun k => wickRotatePoint (xs₁ k)) =
              (Wfn.spectrum_condition 1).choose (fun k => wickRotatePoint (x₀ k)) := by
            let c₁ : Fin (d + 1) → ℂ := fun μ =>
              wickRotatePoint (xs₁ 0) μ - wickRotatePoint (x₀ 0) μ
            have hzc_eq : (fun k μ => wickRotatePoint (x₀ k) μ + c₁ μ) =
                (fun k => wickRotatePoint (xs₁ k)) := by
              ext k μ; fin_cases k; simp [c₁]
            have hzc_ft : (fun k μ => wickRotatePoint (x₀ k) μ + c₁ μ) ∈ ForwardTube d 1 :=
              hzc_eq ▸ hfwd₁
            have h := W_analytic_translation_on_forwardTube Wfn c₁
              (fun k => wickRotatePoint (x₀ k)) hfwd₀ hzc_ft
            rw [hzc_eq] at h; exact h
          rw [htransl₁, hagree₁, htransl_const, ← hagree₀]
        refine ⟨‖v₀‖ + 1, 0, by linarith [norm_nonneg v₀],
          hkernel_ae.mono fun x hx => ?_⟩
        simp only [pow_zero, mul_one]
        rw [hx]
        linarith [norm_nonneg v₀]
    obtain ⟨C_bd, N, hC_pos, hK_ae⟩ := hK_poly
    -- Continuity on ZeroDiagonalSchwartz = composition of full-Schwartz continuity with val
    have hcont_full : Continuous
        (fun f : SchwartzNPoint d n => ∫ x, K x * f x) :=
      schwartz_polynomial_kernel_continuous K hK_meas C_bd N hC_pos hK_ae
    have : (fun f : ZeroDiagonalSchwartz d n =>
          ∫ x : NPointDomain d n, K x * (f.1 : NPointDomain d n → ℂ) x) =
        (fun f : SchwartzNPoint d n => ∫ x, K x * f x) ∘ Subtype.val := by
      funext f; simp
    rw [this]
    exact hcont_full.comp continuous_subtype_val
