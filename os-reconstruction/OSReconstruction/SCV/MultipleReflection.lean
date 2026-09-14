import Mathlib

open Real Filter
open scoped Topology

noncomputable section

namespace SCV
namespace MultipleReflection

/-- The key doubling inequality behind the multiple-reflection contraction
argument. -/
structure HasDoublingBound (N : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 < t → 0 ≤ N t
  nonneg_zero : 0 ≤ N 0
  doubling : ∀ t, 0 < t → N t ^ 2 ≤ N 0 * N (2 * t)

theorem contraction_of_zero_base (N : ℝ → ℝ) (hD : HasDoublingBound N)
    (t : ℝ) (ht : 0 < t) (hN0 : N 0 = 0) :
    N t ≤ N 0 := by
  have h := hD.doubling t ht
  rw [hN0, zero_mul] at h
  have := hD.nonneg t ht
  nlinarith [sq_nonneg (N t)]

/-- Log form of the doubling inequality. -/
theorem log_doubling (N : ℝ → ℝ) (hD : HasDoublingBound N)
    (t : ℝ) (ht : 0 < t)
    (hNt : 0 < N t) (hN0 : 0 < N 0) (hN2t : 0 < N (2 * t)) :
    2 * Real.log (N t) ≤ Real.log (N 0) + Real.log (N (2 * t)) := by
  have hdb := hD.doubling t ht
  have h1 : Real.log (N t ^ 2) ≤ Real.log (N 0 * N (2 * t)) :=
    Real.log_le_log (by positivity) hdb
  rw [Real.log_pow, Real.log_mul (ne_of_gt hN0) (ne_of_gt hN2t)] at h1
  exact_mod_cast h1

/-- Iterated log bound from repeated doubling. -/
theorem iterated_log_doubling (N : ℝ → ℝ) (hD : HasDoublingBound N)
    (t : ℝ) (ht : 0 < t)
    (hNpos_dyadic : ∀ k : ℕ, 0 < N (2 ^ k * t)) (hN0 : 0 < N 0)
    (n : ℕ) :
    Real.log (N t) ≤
      (1 - (1 / 2 : ℝ) ^ n) * Real.log (N 0) +
      (1 / 2 : ℝ) ^ n * Real.log (N (2 ^ n * t)) := by
  induction n with
  | zero =>
      simp [pow_zero, one_mul]
  | succ n ih =>
      have h2nt_pos : 0 < 2 ^ n * t := by positivity
      have hN2nt_pos := hNpos_dyadic n
      have hN2n1t_pos := hNpos_dyadic (n + 1)
      have hlog := log_doubling N hD (2 ^ n * t) h2nt_pos hN2nt_pos hN0 (by
        rw [show 2 * (2 ^ n * t) = 2 ^ (n + 1) * t by ring]
        exact hN2n1t_pos)
      rw [show 2 * (2 ^ n * t) = 2 ^ (n + 1) * t by ring] at hlog
      have hlog' : Real.log (N (2 ^ n * t)) ≤
          (1 / 2 : ℝ) * Real.log (N 0) +
          (1 / 2 : ℝ) * Real.log (N (2 ^ (n + 1) * t)) := by
        linarith
      calc
        Real.log (N t)
          ≤ (1 - (1 / 2 : ℝ) ^ n) * Real.log (N 0) +
              (1 / 2 : ℝ) ^ n * Real.log (N (2 ^ n * t)) := ih
        _ ≤ (1 - (1 / 2 : ℝ) ^ n) * Real.log (N 0) +
              (1 / 2 : ℝ) ^ n *
                ((1 / 2 : ℝ) * Real.log (N 0) +
                  (1 / 2 : ℝ) * Real.log (N (2 ^ (n + 1) * t))) := by
              have h12n : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
              linarith [mul_le_mul_of_nonneg_left hlog' h12n]
        _ = (1 - (1 / 2 : ℝ) ^ (n + 1)) * Real.log (N 0) +
              (1 / 2 : ℝ) ^ (n + 1) * Real.log (N (2 ^ (n + 1) * t)) := by
              ring

/-- Remainder form of the iterated log bound. -/
theorem iterated_log_remainder (N : ℝ → ℝ) (hD : HasDoublingBound N)
    (t : ℝ) (ht : 0 < t)
    (hNpos_dyadic : ∀ k : ℕ, 0 < N (2 ^ k * t)) (hN0 : 0 < N 0)
    (n : ℕ) :
    Real.log (N t) ≤
      Real.log (N 0) + (1 / 2 : ℝ) ^ n * (Real.log (N (2 ^ n * t)) - Real.log (N 0)) := by
  have := iterated_log_doubling N hD t ht hNpos_dyadic hN0 n
  linarith

/-- Abstract multiple-reflection contraction theorem. -/
theorem contraction_of_doubling_and_growth (N : ℝ → ℝ)
    (hD : HasDoublingBound N)
    (C α : ℝ) (hC : 0 < C) (hα : 0 ≤ α)
    (hbound : ∀ T, 1 ≤ T → N T ≤ C * T ^ α)
    (t : ℝ) (ht : 0 < t) :
    N t ≤ N 0 := by
  rcases eq_or_lt_of_le hD.nonneg_zero with hN0_eq | hN0_pos
  · exact contraction_of_zero_base N hD t ht hN0_eq.symm
  rcases eq_or_lt_of_le (hD.nonneg t ht) with hNt_eq | hNt_pos
  · linarith
  have hNpos_dyadic : ∀ n : ℕ, 0 < N (2 ^ n * t) := by
    intro n
    induction n with
    | zero =>
        simpa [pow_zero, one_mul] using hNt_pos
    | succ n ih =>
        have h2nt_pos : 0 < 2 ^ n * t := by positivity
        have hdb := hD.doubling (2 ^ n * t) h2nt_pos
        rw [show 2 * (2 ^ n * t) = 2 ^ (n + 1) * t by ring] at hdb
        have hsq : 0 < N (2 ^ n * t) ^ 2 := by positivity
        by_contra h
        push_neg at h
        have hnn := hD.nonneg (2 ^ (n + 1) * t) (by positivity)
        have hzero : N (2 ^ (n + 1) * t) = 0 := le_antisymm h hnn
        rw [hzero, mul_zero] at hdb
        linarith
  rw [← Real.log_le_log_iff hNt_pos hN0_pos]
  apply le_of_forall_pos_lt_add
  intro ε hε
  set K := |Real.log C| + α * |Real.log t| + |Real.log (N 0)| + 1
  have h_nr :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have h_r :
      Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have h_combined :
      Filter.Tendsto
        (fun n : ℕ => K * (1 / 2 : ℝ) ^ n + α * Real.log 2 * ((n : ℝ) * (1 / 2 : ℝ) ^ n))
        Filter.atTop (nhds 0) := by
    have := (h_r.const_mul K).add (h_nr.const_mul (α * Real.log 2))
    simp only [mul_zero, zero_add] at this
    exact this.congr (fun n => by ring)
  rw [Metric.tendsto_atTop] at h_combined
  obtain ⟨n₀, hn₀⟩ := h_combined ε hε
  obtain ⟨n₁, hn₁'⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (1 : ℝ) / 2 < 1)
  have hn₁_bound : 1 ≤ 2 ^ n₁ * t := by
    have h2pos : (0 : ℝ) < 2 ^ n₁ := by positivity
    have h12 : (1 / 2 : ℝ) ^ n₁ * 2 ^ n₁ = 1 := by
      rw [one_div, inv_pow, inv_mul_cancel₀ (ne_of_gt h2pos)]
    nlinarith
  set n := max n₀ n₁
  have hn_ge : n₀ ≤ n := le_max_left _ _
  specialize hn₀ n hn_ge
  rw [Real.dist_eq, sub_zero] at hn₀
  have hiter := iterated_log_remainder N hD t ht hNpos_dyadic hN0_pos n
  have h2nt_ge_1 : 1 ≤ 2 ^ n * t := by
    calc
      (1 : ℝ) ≤ 2 ^ n₁ * t := hn₁_bound
      _ ≤ 2 ^ n * t := by
          apply mul_le_mul_of_nonneg_right _ ht.le
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_max_right _ _)
  have hN2nt_pos := hNpos_dyadic n
  have hN2nt_bound := hbound (2 ^ n * t) h2nt_ge_1
  have hlog_N : Real.log (N (2 ^ n * t)) ≤ Real.log C + α * Real.log (2 ^ n * t) := by
    have h1 : Real.log (N (2 ^ n * t)) ≤ Real.log (C * (2 ^ n * t) ^ α) :=
      Real.log_le_log hN2nt_pos hN2nt_bound
    rw [Real.log_mul (ne_of_gt hC) (by positivity), Real.log_rpow (by positivity)] at h1
    exact h1
  have hlog_2nt : Real.log (2 ^ n * t) = (n : ℝ) * Real.log 2 + Real.log t := by
    rw [Real.log_mul (by positivity) (ne_of_gt ht), Real.log_pow]
  have hrem : Real.log (N (2 ^ n * t)) - Real.log (N 0) ≤ K + α * Real.log 2 * n := by
    have := hlog_N
    rw [hlog_2nt] at this
    have h1 : Real.log C ≤ |Real.log C| := le_abs_self _
    have h2 : α * Real.log t ≤ α * |Real.log t| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self _) hα
    have h3 : -Real.log (N 0) ≤ |Real.log (N 0)| := neg_le_abs _
    nlinarith
  have h12n : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  calc
    Real.log (N t)
      ≤ Real.log (N 0) +
          (1 / 2 : ℝ) ^ n * (Real.log (N (2 ^ n * t)) - Real.log (N 0)) := hiter
    _ ≤ Real.log (N 0) + (1 / 2 : ℝ) ^ n * (K + α * Real.log 2 * n) := by
        linarith [mul_le_mul_of_nonneg_left hrem h12n]
    _ < Real.log (N 0) + ε := by
        have hsmall :
            (1 / 2 : ℝ) ^ n * (K + α * Real.log 2 * n) < ε := by
          have habs :
              K * (1 / 2 : ℝ) ^ n + α * Real.log 2 * (n : ℝ) * (1 / 2 : ℝ) ^ n < ε :=
            lt_of_le_of_lt (le_abs_self _) (by simpa [mul_assoc] using hn₀)
          linarith
        linarith

end MultipleReflection
end SCV
