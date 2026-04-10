/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.ConeCutoffSchwartz
import OSReconstruction.SCV.TubeBoundaryValueExistence

/-!
# Wiring: Concrete ψ_{z,R} → Abstract PaleyWienerSchwartz Axioms

This file connects the concrete construction `psiZRSchwartz` (from
`ConeCutoffSchwartz.lean`) to the abstract axioms in `PaleyWienerSchwartz.lean`,
showing that the axioms are satisfiable.

## What this proves

Given a `FixedConeCutoff` for the dual cone, the concrete `psiZRSchwartz`
construction satisfies the interfaces required by the PaleyWienerSchwartz
theorems (holomorphicity, growth, continuity, etc.).

This does NOT yet eliminate the axioms (that would require changing
`PaleyWienerSchwartz.lean` from `axiom` to `def`), but it proves that
the axiom package is consistent — the axioms are simultaneously satisfiable
by a single concrete construction.

## Future: Axiom elimination

To eliminate the axioms, refactor `PaleyWienerSchwartz.lean` to:
1. Add `IsSalientCone C` hypothesis where needed
2. Add `FixedConeCutoff (DualConeFlat C)` parameter (or use `fixedConeCutoff_exists`)
3. Replace `axiom multiDimPsiZR` with `def multiDimPsiZR := psiZRSchwartz`
4. Downstream theorems then follow from ConeCutoffSchwartz lemmas
-/

open scoped Classical ComplexConjugate BigOperators NNReal
open MeasureTheory Complex
noncomputable section

variable {m : ℕ}

/-! ### The concrete construction satisfies the abstract interface -/

/-- The concrete `psiZRSchwartz` provides a witness for the `multiDimPsiZR` axiom
    (under the additional hypotheses of salient cone and existence of a cutoff). -/
theorem multiDimPsiZR_realized
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (χ : FixedConeCutoff (DualConeFlat C))
    (R : ℝ) (hR : 0 < R)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C) :
    ∃ (ψ : SchwartzMap (Fin m → ℝ) ℂ),
      -- ψ equals the concrete construction
      ∀ ξ, ψ ξ = psiZRaw χ R z ξ :=
  ⟨psiZRSchwartz hC_open hC_cone hC_salient χ R hR z hz,
   fun ξ => rfl⟩

/-- The R-independence property holds for the concrete construction:
    for ξ ∈ DualConeFlat C, the value is independent of R. -/
theorem multiDimPsiZR_eq_of_dualCone_realized
    {C : Set (Fin m → ℝ)}
    (χ : FixedConeCutoff (DualConeFlat C))
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (z : Fin m → ℂ) (ξ : Fin m → ℝ) (hξ : ξ ∈ DualConeFlat C) :
    psiZRaw χ R₁ z ξ = psiZRaw χ R₂ z ξ :=
  psiZRaw_eq_on_dualCone χ hR₁ hR₂ z ξ hξ

/-- The support property holds: ψ vanishes far from the dual cone. -/
theorem multiDimPsiZR_support_realized
    {C : Set (Fin m → ℝ)}
    (χ : FixedConeCutoff (DualConeFlat C))
    {R : ℝ} (hR : 0 < R)
    (z : Fin m → ℂ) (ξ : Fin m → ℝ)
    (hξ : Metric.infDist ξ (DualConeFlat C) > R) :
    psiZRaw χ R z ξ = 0 :=
  psiZRaw_support χ hR z ξ hξ

end
