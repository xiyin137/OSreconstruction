import OSReconstruction.Wightman.Reconstruction.UniversalProjection
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Proper Rotations with Time and Spatial Separation

Add the zero vector, the spatial separation vector, and the unit time vector
to the existing universal projection problem. The last vector keeps the time
axis component bounded below; orthogonality then controls the surviving
spatial separation. Orienting the first row preserves all internal gap bounds.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace OSReconstruction
variable {d : ℕ} [NeZero d]
set_option maxHeartbeats 800000

omit [NeZero d] in
private theorem orthogonal_row_sq
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hR : R.transpose * R = 1) :
    ∑ j, (R 0 j)^2 = 1 := by
  have hRR : R * R.transpose = 1 := mul_eq_one_comm.mp hR
  have h := congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => M 0 0) hRR
  simpa [Matrix.mul_apply, pow_two] using h

omit [NeZero d] in
private theorem orthogonal_sum_sq
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hR : R.transpose * R = 1)
    (a : Fin (d + 1) → ℝ) :
    ∑ j, (R.mulVec a j)^2 = ∑ j, (a j)^2 := by
  have h : a ⬝ᵥ (R.transpose *ᵥ (R *ᵥ a)) = a ⬝ᵥ a := by
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at h
  simpa [dotProduct, pow_two] using h

omit [NeZero d] in
private theorem pi_norm_sq_le_sum_sq (a : Fin (d + 1) → ℝ) :
    ‖a‖^2 ≤ ∑ j, (a j)^2 := by
  have hS : 0 ≤ ∑ j, (a j)^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hcoord (j : Fin (d + 1)) : |a j| ≤ Real.sqrt (∑ k, (a k)^2) := by
    apply (Real.le_sqrt (abs_nonneg _) hS).2
    simpa only [sq_abs] using
      (Finset.single_le_sum (fun k _ => sq_nonneg (a k)) (Finset.mem_univ j))
  have hn : ‖a‖ ≤ Real.sqrt (∑ j, (a j)^2) :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
      (fun j => by simpa only [Real.norm_eq_abs] using hcoord j)
  nlinarith [Real.sq_sqrt hS, norm_nonneg a]

omit [NeZero d] in
private theorem orthogonal_spatial_sq_lower
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hR : R.transpose * R = 1)
    (a : Fin (d + 1) → ℝ) (ha : a 0 = 0) :
    (R 0 0)^2 * (∑ j, (a j)^2) ≤ ∑ j : Fin d, (R.mulVec a j.succ)^2 := by
  have hrow := orthogonal_row_sq R hR
  rw [Fin.sum_univ_succ] at hrow
  have htotal := orthogonal_sum_sq R hR a
  rw [Fin.sum_univ_succ] at htotal
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin d => R 0 j.succ) (fun j : Fin d => a j.succ)
  have ht : R.mulVec a 0 = ∑ j : Fin d, R 0 j.succ * a j.succ := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, ha]
  have hsum : (∑ j : Fin d, (a j.succ)^2) = ∑ j, (a j)^2 := by
    simp [Fin.sum_univ_succ, ha]
  rw [hsum, ← ht] at hcs
  have hrowA := congrArg (fun x : ℝ => x * (∑ j, (a j)^2)) hrow
  nlinarith [hrowA]

private theorem orient_projection
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hR : R.transpose * R = 1)
    (hdet : R.det = 1) (a : Fin (d + 1) → ℝ) :
    ∃ S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      S.transpose * S = 1 ∧ S.det = 1 ∧
      S.mulVec a 0 = |R.mulVec a 0| ∧ |S 0 0| = |R 0 0| ∧
      ∀ b, |S.mulVec b 0| = |R.mulVec b 0| := by
  by_cases hpos : 0 ≤ R.mulVec a 0
  · exact ⟨R, hR, hdet, (abs_of_nonneg hpos).symm, rfl, fun _ => rfl⟩
  · have hv : ∑ j, (-R 0 j)^2 = 1 := by
      simpa only [neg_sq] using orthogonal_row_sq R hR
    obtain ⟨S, hS, hSdet, hrow⟩ :=
      exists_orthogonal_matrix_with_first_row (fun j => -R 0 j) hv
    have ht (b : Fin (d + 1) → ℝ) : S.mulVec b 0 = -R.mulVec b 0 := by
      simp only [Matrix.mulVec, dotProduct, hrow, neg_mul, Finset.sum_neg_distrib]
    refine ⟨S, hS, hSdet, ?_, ?_, fun b => ?_⟩
    · rw [ht, abs_of_neg (lt_of_not_ge hpos)]
    · rw [hrow, abs_neg]
    · rw [ht, abs_neg]

/-- One dimension/arity constant controls internal gaps and both separation components. -/
theorem rToE_exists_proper_rotation_separating_time_and_space (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : Fin n → Fin (d + 1) → ℝ)
      (a : Fin (d + 1) → ℝ), a 0 = 0 →
      ∃ R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
        R.transpose * R = 1 ∧ R.det = 1 ∧
        c * ‖a‖ ≤ R.mulVec a 0 ∧
        (c * ‖a‖)^2 ≤ ∑ j : Fin d, (R.mulVec a j.succ)^2 ∧
        ∀ i j : Fin n, i ≠ j →
          c * ‖x i - x j‖ ≤ |R.mulVec (x i - x j) 0| := by
  classical
  obtain ⟨c, hc, hproj⟩ := exists_universal_time_projection' d (n + 3)
  refine ⟨c, hc, fun x a ha => ?_⟩
  let e : Fin (d + 1) → ℝ := Pi.single 0 1
  let z : Fin (n + 3) → Fin (d + 1) → ℝ := Fin.append x ![0, a, e]
  obtain ⟨Q, hQ, hQdet, hQproj⟩ := hproj z
  have htime : c * ‖a‖ ≤ |Q.mulVec a 0| := by
    simpa [z] using hQproj (Fin.natAdd n (1 : Fin 3)) (Fin.natAdd n (0 : Fin 3))
      (by simp)
  have haxis : c ≤ |Q 0 0| := by
    simpa [z, e, Pi.norm_single, Matrix.mulVec_single_one] using
      hQproj (Fin.natAdd n (2 : Fin 3)) (Fin.natAdd n (0 : Fin 3)) (by simp)
  have hinternal (i j : Fin n) (hij : i ≠ j) :
      c * ‖x i - x j‖ ≤ |Q.mulVec (x i - x j) 0| := by
    simpa [z] using hQproj (Fin.castAdd 3 i) (Fin.castAdd 3 j) (by simpa using hij)
  obtain ⟨R, hR, hRdet, hRa, hRaxis, hRproj⟩ := orient_projection Q hQ hQdet a
  refine ⟨R, hR, hRdet, ?_, ?_, fun i j hij => ?_⟩
  · rw [hRa]
    exact htime
  · have haxis' : c ≤ |R 0 0| := by rwa [hRaxis]
    have hcsq : c^2 ≤ (R 0 0)^2 := by
      nlinarith [sq_abs (R 0 0), abs_nonneg (R 0 0)]
    calc
      (c * ‖a‖)^2 = c^2 * ‖a‖^2 := mul_pow _ _ _
      _ ≤ c^2 * (∑ j, (a j)^2) :=
        mul_le_mul_of_nonneg_left (pi_norm_sq_le_sum_sq a) (sq_nonneg _)
      _ ≤ (R 0 0)^2 * (∑ j, (a j)^2) :=
        mul_le_mul_of_nonneg_right hcsq (Finset.sum_nonneg fun j _ => sq_nonneg _)
      _ ≤ _ := orthogonal_spatial_sq_lower R hR a ha
  · rw [hRproj]
    exact hinternal i j hij

end OSReconstruction
