/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialStageCoherence
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSimultaneousStageLevel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedBridgeBlocks













noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

/-- At every positive reduced arity there is a narrow-sector aperture small
enough for the finite axis-pair product chart. -/
theorem exists_initialStage_aperture (k : ℕ) :
    ∃ η : ℝ, 0 < η ∧
      ((k + 1 : ℕ) : ℝ) *
          (Fintype.card (osiiAxisPairIndex d) : ℝ) *
            Real.arctan η <
        Real.pi / 2 := by
  classical
  let c : ℝ :=
    ((k + 1 : ℕ) : ℝ) *
      (Fintype.card (osiiAxisPairIndex d) : ℝ)
  have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    positivity
  have hcard_pos : 0 < Fintype.card (osiiAxisPairIndex d) :=
    Fintype.card_pos_iff.2
      ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true)⟩
  have hcard_pos_real :
      (0 : ℝ) < (Fintype.card (osiiAxisPairIndex d) : ℝ) := by
    exact_mod_cast hcard_pos
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  let x : ℝ := Real.pi / (4 * c)
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hc_one : (1 : ℝ) ≤ c := by
    dsimp [c]
    have hk_one : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hcard_one :
        (1 : ℝ) ≤ (Fintype.card (osiiAxisPairIndex d) : ℝ) := by
      exact_mod_cast hcard_pos
    nlinarith
  have hx_lt : x < Real.pi / 2 := by
    dsimp [x]
    have hden_ge : (4 : ℝ) ≤ 4 * c := by nlinarith
    have hdiv_le : Real.pi / (4 * c) ≤ Real.pi / 4 := by
      exact div_le_div_of_nonneg_left
        (le_of_lt Real.pi_pos) (by norm_num) hden_ge
    nlinarith [Real.pi_pos, hdiv_le]
  let η : ℝ := Real.tan x
  have hη_pos : 0 < η := by
    dsimp [η]
    exact Real.tan_pos_of_pos_of_lt_pi_div_two hx_pos hx_lt
  refine ⟨η, hη_pos, ?_⟩
  have hx_low : -(Real.pi / 2) < x := by
    nlinarith [Real.pi_pos, hx_pos]
  have harctan : Real.arctan η = x := by
    dsimp [η]
    exact Real.arctan_tan hx_low hx_lt
  rw [harctan]
  change c * x < Real.pi / 2
  dsimp [x]
  field_simp [ne_of_gt hc_pos]
  nlinarith [Real.pi_pos]

end OSIIChapterV
end OSReconstruction
