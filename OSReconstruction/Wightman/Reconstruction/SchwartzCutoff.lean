import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz Tail Decay

Small Schwartz-space estimates used in cutoff and density arguments.
-/

noncomputable section

open SchwartzMap

namespace OSReconstruction

variable {n : ℕ}

/-- For a Schwartz function `f`, the weighted derivative norm
`‖x‖^k * ‖D^p f(x)‖` is uniformly small outside a large ball. -/
theorem schwartz_tail_decay (f : SchwartzMap (Fin n → ℝ) ℂ) (k p : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ (x : Fin n → ℝ), R₀ < ‖x‖ →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (⇑f) x‖ < ε := by
  obtain ⟨C, hC⟩ := f.decay' (k + 2) p
  refine ⟨max 1 (Real.sqrt (|C| / ε) + 1), by positivity, fun x hR₀ => ?_⟩
  have hx2_pos : 0 < ‖x‖ ^ 2 := by
    have hx_pos : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) (le_of_lt hR₀)
    positivity
  have key : ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (⇑f) x‖ ≤ |C| / ‖x‖ ^ 2 := by
    have hbound := hC x
    have hpow : ‖x‖ ^ (k + 2) = ‖x‖ ^ k * ‖x‖ ^ 2 := by ring
    rw [hpow] at hbound
    rw [le_div_iff₀ hx2_pos]
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (⇑f) x‖ * ‖x‖ ^ 2
          = ‖x‖ ^ k * ‖x‖ ^ 2 * ‖iteratedFDeriv ℝ p (⇑f) x‖ := by ring
      _ ≤ C := hbound
      _ ≤ |C| := le_abs_self C
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (⇑f) x‖ ≤ |C| / ‖x‖ ^ 2 := key
    _ < ε := by
      rw [div_lt_iff₀ hx2_pos]
      have hR_bound : Real.sqrt (|C| / ε) + 1 < ‖x‖ :=
        lt_of_le_of_lt (le_max_right _ _) hR₀
      have hsqrt_lt : Real.sqrt (|C| / ε) < ‖x‖ := by
        linarith
      have hCε : |C| / ε < ‖x‖ ^ 2 := by
        have h1 :=
          Real.sq_sqrt (show 0 ≤ |C| / ε from div_nonneg (abs_nonneg _) (le_of_lt hε))
        have hsqrt_nonneg : 0 ≤ Real.sqrt (|C| / ε) := Real.sqrt_nonneg _
        have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
        have hsq : (Real.sqrt (|C| / ε)) ^ 2 < ‖x‖ ^ 2 := by
          nlinarith
        calc
          |C| / ε = (Real.sqrt (|C| / ε)) ^ 2 := h1.symm
          _ < ‖x‖ ^ 2 := hsq
      have := (div_lt_iff₀ hε).mp hCε
      linarith

end OSReconstruction
