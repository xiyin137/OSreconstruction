import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.RegularizationIterated
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

noncomputable section

open MeasureTheory
open scoped LineDeriv

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The reflected positive-time convolution sequence has a uniform Schwartz
seminorm bound in every derivative order. This packages the iterated
directional-derivative estimate into the actual `(N,j)` seminorm needed by the
OS linear-growth condition. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_seminorm_uniform_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (N j : ℕ)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      SchwartzMap.seminorm ℝ N j
        (((positiveTimeCompactSupportConvolution
            (⟨reflectedSchwartzSpacetime (φ_seq n),
              ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                  (hφ_compact n)⟩⟩)
            h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)) ≤ C := by
  rcases
      positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_iteratedLineDeriv_seminorm_zero_uniform_local
        (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_ball N j h with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro n
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  let convn : SchwartzSpacetime d :=
    (((positiveTimeCompactSupportConvolution ψn h : positiveTimeCompactSupportSubmodule d) :
      SchwartzSpacetime d))
  refine SchwartzMap.seminorm_le_bound ℝ N j convn hC_nonneg ?_
  intro x
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin j => SpacetimeDim d) ℂ :=
    iteratedFDeriv ℝ j (convn : SpacetimeDim d → ℂ) x
  have hpoint :
      ∀ u : Fin j → SpacetimeDim d,
        ‖((‖x‖ ^ N : ℝ) • L) u‖ ≤ C * ∏ i, ‖u i‖ := by
    intro u
    calc
      ‖((‖x‖ ^ N : ℝ) • L) u‖ = ‖x‖ ^ N * ‖L u‖ := by
            simp [L]
      _ = ‖x‖ ^ N * ‖(LineDeriv.iteratedLineDerivOp u convn : SchwartzSpacetime d) x‖ := by
            simp [L, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
      _ ≤ SchwartzMap.seminorm ℝ N 0 (LineDeriv.iteratedLineDerivOp u convn : SchwartzSpacetime d) := by
            simpa [norm_iteratedFDeriv_zero] using
              (SchwartzMap.le_seminorm ℝ N 0
                (LineDeriv.iteratedLineDerivOp u convn : SchwartzSpacetime d) x)
      _ ≤ C * ∏ i, ‖u i‖ := hC u n
  have hL :
      ‖((‖x‖ ^ N : ℝ) • L)‖ ≤ C := by
    exact (ContinuousMultilinearMap.opNorm_le_iff hC_nonneg).2 hpoint
  simpa [L, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hL

end OSReconstruction
