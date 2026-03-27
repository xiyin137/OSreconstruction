/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

# Adapter: HilleYosida → OSreconstruction

Replaces both BCR 4.1.13 axioms with proofs from the HilleYosida project.

## Prerequisites

Add to `lakefile.toml`:
```toml
[[require]]
name = "HilleYosida"
git = "https://github.com/mrdouglasny/hille-yosida.git"
```

Both projects must be on the same Mathlib version.

## Axioms eliminated

- `semigroupGroup_bochner` — existence (BCR 4.1.13)
- `laplaceFourier_measure_unique` — uniqueness (BCR 4.1.13)
-/

import HilleYosida.SemigroupGroupExtension
import HilleYosida.BCR_General

open MeasureTheory Complex Set Filter Finset BigOperators
open scoped Topology

noncomputable section

namespace SCV

/-- The `IsSemigroupGroupPD` definitions are definitionally equal:
`starRingEnd ℂ` and `star` coincide on `ℂ`. -/
theorem isSemigroupGroupPD_iff (d : ℕ) (F : ℝ → (Fin d → ℝ) → ℂ) :
    IsSemigroupGroupPD d F ↔ _root_.IsSemigroupGroupPD d F :=
  Iff.rfl

/-- **Semigroup-group Bochner theorem** (BCR Theorem 4.1.13, existence).

Eliminates the `semigroupGroup_bochner` axiom by applying the fully proved
`semigroupGroupBochner` theorem from the HilleYosida project.

Hypothesis adaptation:
- `Continuous` → `ContinuousOn` on `[0,∞) × ℝ^d` (via `.continuousOn`)
- Global bound → half-space bound (drop unused `0 ≤ t`)
- `starRingEnd ℂ` vs `star` — definitionally equal on `ℂ` -/
theorem semigroupGroup_bochner' (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : Continuous (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2))
    (hbdd : ∃ C : ℝ, ∀ t a, ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        F t a = ∫ p : ℝ × (Fin d → ℝ),
          Complex.exp (-(↑(t * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ :=
  semigroupGroupBochner d F
    hcont.continuousOn
    (hbdd.imp fun C hC t a _ => hC t a)
    hpd

/-- **Laplace-Fourier uniqueness** (BCR Theorem 4.1.13, uniqueness).

Eliminates the `laplaceFourier_measure_unique` axiom by applying
`laplaceFourier_unique` from the HilleYosida project.

Hypothesis adaptation:
- `0 < t` → `0 < t` (identical) -/
theorem laplaceFourier_measure_unique' {d : ℕ}
    (μ₁ μ₂ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h₁ : μ₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (h₂ : μ₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (heq : ∀ (t : ℝ), 0 < t → ∀ (a : Fin d → ℝ),
      ∫ p : ℝ × (Fin d → ℝ),
        Complex.exp (-(↑(t * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ₁ =
      ∫ p : ℝ × (Fin d → ℝ),
        Complex.exp (-(↑(t * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ₂) :
    μ₁ = μ₂ :=
  laplaceFourier_unique μ₁ μ₂ h₁ h₂ heq

end SCV
