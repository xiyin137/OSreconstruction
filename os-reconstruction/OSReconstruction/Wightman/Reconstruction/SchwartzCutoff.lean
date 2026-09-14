/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.MetricSpace.Basic







noncomputable section

open SchwartzMap

namespace OSReconstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

/-- If a sequence of Schwartz functions vanishes on the growing ball
`‖x‖ ≤ n + 1` at derivative order `l`, and their `(k + 2, l)` seminorms are
uniformly bounded, then the `(k,l)` seminorms tend to `0`. -/
theorem schwartz_seminorm_tendsto_zero_of_vanish_on_ball_uniform
    (h : ℕ → SchwartzMap E ℂ) (k l : ℕ)
    (hvanish : ∀ (n : ℕ) (x : E), ‖x‖ ≤ (n : ℝ) + 1 →
      iteratedFDeriv ℝ l (⇑(h n)) x = 0)
    (M : ℝ) (hM_pos : 0 ≤ M) (hM : ∀ n, (SchwartzMap.seminorm ℝ (k + 2) l) (h n) ≤ M) :
    Filter.Tendsto (fun n => (SchwartzMap.seminorm ℝ k l) (h n))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨Nat.ceil (Real.sqrt (M / ε)) + 1, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  apply lt_of_le_of_lt
  · apply SchwartzMap.seminorm_le_bound ℝ k l (h n) (M := M / ((n : ℝ) + 1) ^ 2)
    · exact div_nonneg hM_pos (sq_nonneg _)
    · intro x
      by_cases hx : ‖x‖ ≤ (n : ℝ) + 1
      · simp [hvanish n x hx]
        exact div_nonneg hM_pos (sq_nonneg _)
      · push_neg at hx
        have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hx_pos : 0 < ‖x‖ := lt_trans hn1_pos hx
        calc
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(h n)) x‖
              = (‖x‖ ^ (k + 2) * ‖iteratedFDeriv ℝ l (⇑(h n)) x‖) / ‖x‖ ^ 2 := by
                  field_simp [ne_of_gt (pow_pos hx_pos 2)]
                  ring
          _ ≤ (SchwartzMap.seminorm ℝ (k + 2) l) (h n) / ‖x‖ ^ 2 := by
                apply div_le_div_of_nonneg_right _ (sq_nonneg _)
                exact SchwartzMap.le_seminorm ℝ (k + 2) l (h n) x
          _ ≤ M / ‖x‖ ^ 2 := by
                apply div_le_div_of_nonneg_right (hM n) (sq_nonneg _)
          _ ≤ M / ((n : ℝ) + 1) ^ 2 := by
                apply div_le_div_of_nonneg_left hM_pos (pow_pos hn1_pos 2)
                exact sq_le_sq' (by linarith) hx.le
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)]
    have hn1 : (n : ℝ) + 1 ≥ Real.sqrt (M / ε) + 1 := by
      have h1 : (⌈Real.sqrt (M / ε)⌉₊ : ℝ) ≥ Real.sqrt (M / ε) :=
        Nat.le_ceil (Real.sqrt (M / ε))
      have h2 : (n : ℝ) ≥ (⌈Real.sqrt (M / ε)⌉₊ : ℝ) + 1 := by
        exact_mod_cast hn
      linarith
    have hsq : M / ε < ((n : ℝ) + 1) ^ 2 := by
      calc
        M / ε ≤ (Real.sqrt (M / ε)) ^ 2 :=
          le_of_eq (Real.sq_sqrt (div_nonneg hM_pos hε.le)).symm
        _ < ((n : ℝ) + 1) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (M / ε)]
    linarith [div_lt_iff₀ hε |>.mp hsq]

end OSReconstruction
