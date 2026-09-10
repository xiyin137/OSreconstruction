import OSReconstruction.Mathlib429Compat
import OSReconstruction.Wightman.Reconstruction.SchwartzCutoff
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz

/-!
# Schwartz Density

Compact-support approximation in Schwartz space via radial bump truncations.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open SchwartzMap

namespace OSReconstruction

set_option maxHeartbeats 4000000

def bumpTruncationRadiusValue (n : ℕ) : ℝ := ((n : ℝ) + 1) + 1

theorem bumpTruncationRadiusValue_pos (n : ℕ) : 0 < bumpTruncationRadiusValue n := by
  simpa [bumpTruncationRadiusValue] using (show (0 : ℝ) < ((n : ℝ) + 1) + 1 by positivity)

/-- The radius-`n + 2` bump truncation of a Schwartz function. -/
noncomputable def bumpTruncationRadius {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) (n : ℕ) : SchwartzMap (Fin m → ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (unitBallBumpSchwartzPiRadius m (bumpTruncationRadiusValue n)
      (bumpTruncationRadiusValue_pos n)) f

/-- The bump truncation `χ_n · f` converges to `f` in every Schwartz seminorm. -/
theorem _root_.SchwartzMap.tendsto_bump_truncation {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) (k l : ℕ) :
    Filter.Tendsto
      (fun n : ℕ =>
        (SchwartzMap.seminorm ℝ k l) (f - bumpTruncationRadius f n))
      Filter.atTop (nhds 0) := by
  let u : ℕ → SchwartzMap (Fin m → ℝ) ℂ := fun n =>
    f - SchwartzMap.smulLeftCLM ℂ
      (unitBallBumpSchwartzPiRadius m (((n : ℝ) + 1) + 1) (by positivity)) f
  have hvanish : ∀ (n : ℕ) (x : Fin m → ℝ), ‖x‖ ≤ (n : ℝ) + 1 →
      iteratedFDeriv ℝ l (⇑(u n)) x = 0 := by
    intro n x hx
    exact iteratedFDeriv_cutoff_compl_radius_add_one_eq_zero_on_closedBall
      ((n : ℝ) + 1) (by positivity) f
      (by simpa [u, Metric.mem_closedBall] using hx)
  obtain ⟨M, hM_nonneg, hM_bound⟩ :=
    smulLeftCLM_cutoff_compl_uniform_seminorm_bound f (k + 2) l
  have hM : ∀ n, (SchwartzMap.seminorm ℝ (k + 2) l) (u n) ≤ M := by
    intro n
    exact hM_bound ((n : ℝ) + 1) (by positivity)
  have ht :=
    schwartz_seminorm_tendsto_zero_of_vanish_on_ball_uniform u k l hvanish M hM_nonneg hM
  simpa [u, bumpTruncationRadius, bumpTruncationRadiusValue, add_assoc] using ht

theorem _root_.SchwartzMap.tendsto_bump_truncation_nhds {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    Filter.Tendsto (fun n : ℕ => bumpTruncationRadius f n) Filter.atTop (nhds f) := by
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds_atTop _ _]
  intro p ε hε
  obtain ⟨n₀, hn₀⟩ :=
    Metric.tendsto_atTop.mp (SchwartzMap.tendsto_bump_truncation f p.1 p.2) ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  have h := hn₀ n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
  have hneg :
      schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ p
          (bumpTruncationRadius f n - f) =
        (SchwartzMap.seminorm ℝ p.1 p.2) (f - bumpTruncationRadius f n) := by
    rw [schwartzSeminormFamily_apply]
    rw [show bumpTruncationRadius f n - f = -(f - bumpTruncationRadius f n) by
      ext x
      abel_nf]
    exact map_neg_eq_map _ _
  rw [hneg]
  exact h

/-- Compactly supported Schwartz functions are dense in Schwartz space. -/
theorem _root_.SchwartzMap.dense_hasCompactSupport {m : ℕ} :
    Dense {f : SchwartzMap (Fin m → ℝ) ℂ | HasCompactSupport (f : (Fin m → ℝ) → ℂ)} := by
  intro f
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n => bumpTruncationRadius f n, ?_, SchwartzMap.tendsto_bump_truncation_nhds f⟩
  intro n
  exact hasCompactSupport_cutoff_mul_radius (bumpTruncationRadiusValue n)
    (bumpTruncationRadiusValue_pos n) f

end OSReconstruction
