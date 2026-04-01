/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Smooth Cutoff Functions via Convolution Mollifier

For any closed set S in ℝ^m, there exists a smooth function χ : ℝ^m → [0,1]
that equals 1 on a neighborhood of S and vanishes at distance > 1 from S,
with all derivatives globally bounded.

## Construction

1. Let `A = {ξ : dist(ξ, S) ≤ 1/2}` (the 1/2-neighborhood of S)
2. Let `φ ∈ C_c^∞(B_{1/2}(0))` be a smooth bump with `∫ φ = 1` and `0 ≤ φ`
3. Define `χ = 1_A * φ` (convolution)

Then:
- χ is smooth (convolution of L^∞ with C_c^∞)
- χ = 1 on S (and on the ε-neighborhood for some ε > 0)
- χ = 0 outside the 1-neighborhood of S
- 0 ≤ χ ≤ 1 (positive bump convolved with indicator)
- All derivatives bounded (derivatives of φ are bounded, convolution preserves bounds)

## Main result

`exists_smooth_cutoff_of_closed`: For any closed set S, there exists
a smooth cutoff with the above properties.

## Applications

- `fixedConeCutoff_exists` in DualCone.lean
- General smooth partition of unity arguments

## References

- Hörmander, "The Analysis of Linear PDOs I", §1.4
- Mathlib: `ContDiffBumpFunction`, `MeasureTheory.convolution`
-/

open scoped Classical ComplexConjugate BigOperators
open MeasureTheory Metric
noncomputable section

variable {m : ℕ}

/-- **Existence of smooth cutoff adapted to a closed set.**

    For any closed set S ⊆ ℝ^m, there exists `χ : ℝ^m → ℝ` with:
    1. `ContDiff ℝ ⊤ χ` (C^∞ smooth)
    2. `χ = 1` on an ε-neighborhood of S
    3. `χ = 0` outside the 1-neighborhood of S
    4. All iterated derivatives globally bounded
    5. `0 ≤ χ ≤ 1`

    **Proof**: Construct via convolution `χ = 1_{S+B_{1/2}} * φ` where
    `φ ∈ C_c^∞(B_{1/2}(0))` is a smooth bump with `∫ φ = 1`.

    Mathlib ingredients:
    - `ContDiffBumpFunction` or `Real.smoothTransition` for the bump φ
    - `MeasureTheory.convolution` for the convolution product
    - `HasCompactSupport.contDiff_convolution_left` for smoothness
    - `MeasureTheory.integral_nonneg` + `integral_le_one` for [0,1] bounds -/
axiom exists_smooth_cutoff_of_closed
    (S : Set (Fin m → ℝ)) (hS : IsClosed S) :
    ∃ (χ : (Fin m → ℝ) → ℝ),
      ContDiff ℝ ⊤ χ ∧
      (∃ ε > 0, ∀ ξ, infDist ξ S < ε → χ ξ = 1) ∧
      (∀ ξ, infDist ξ S > 1 → χ ξ = 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ C) ∧
      (∀ ξ, 0 ≤ χ ξ) ∧
      (∀ ξ, χ ξ ≤ 1)

end
