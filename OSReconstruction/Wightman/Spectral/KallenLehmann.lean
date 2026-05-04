/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import OSReconstruction.Wightman.SchwartzTensorProduct
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.GeneralResults.SNAGTheorem
import Bochner.Main

/-!
# Källén-Lehmann spectral representation

The Källén-Lehmann (KL) spectral representation expresses the Wightman 2-point
function as a Fourier transform of a positive measure on momentum space:
$$W_2(x - y) = \int_{\mathbb{R}^{d+1}} e^{-i\, p \cdot (x - y)}\, d\rho(p).$$

**Strategy.**
1. For each test function `f : SchwartzNPoint d 1`, define the
   *spectral function* `φ_f : SpacetimeDim d → ℂ` by
   `φ_f(a) := W_2(f̄ ⊗ T_a f)` where `T_a` is spacetime translation by `a`.
2. Show `φ_f` is continuous (from temperedness `Wfn.tempered`).
3. Show `φ_f` is positive-definite (from R2 `Wfn.positive_definite`).
4. Apply `bochner_theorem` (BochnerMinlos repo, finite-dim Bochner) to obtain
   a unique probability measure (after normalization by `φ_f(0)`) whose
   characteristic function equals `φ_f`.

**Application to cluster decomposition.** For test functions `f, g` with
`∫ f = ∫ g = 0` (orthogonal to the constants), the spectral measure is
supported away from `p = 0`, and Riemann-Lebesgue gives
`W_2(f ⊗ T_a g) → 0` as `‖a‖ → ∞`. This is the cluster property at the
2-point level. The truncated decomposition `W_n^T` extends this to
arbitrary `n`.

**Status.** This file currently scaffolds the spectral function and states
the goal theorem. Discharging the proof is scheduled as follow-up work
(~1 week per `MEMORY.md` calibration; reuses `bochner_theorem` from the
`BochnerMinlos` package).

## References

* Källén, *Helv. Phys. Acta* 25 (1952), 417–434.
* Lehmann, *Nuovo Cimento* 11 (1954), 342–357.
* Streater, Wightman, *PCT, Spin and Statistics, and All That*, §3.4.
* Glimm, Jaffe, *Quantum Physics*, Chapter 6.
* Reed, Simon, *Methods of Modern Mathematical Physics, Vol. II*, §IX.8.
-/

namespace OSReconstruction
namespace KallenLehmann

variable {d : ℕ} [NeZero d]

open MeasureTheory

/-- Spacetime translation of a `SchwartzSpacetime` test function.

`spacetimeTranslate a f x = f (x - a)`. This is the standard QFT
translation operator: `T_a f` is `f` shifted so its support moves by `a`.

Implemented via `SCV.translateSchwartz (-a) f`, which Mathlib-side gives
`f (x + (-a)) = f (x - a)`. -/
noncomputable def spacetimeTranslate (a : SpacetimeDim d)
    (f : SchwartzSpacetime d) : SchwartzSpacetime d :=
  SCV.translateSchwartz (-a) f

@[simp] theorem spacetimeTranslate_apply (a : SpacetimeDim d)
    (f : SchwartzSpacetime d) (x : SpacetimeDim d) :
    spacetimeTranslate a f x = f (x - a) := by
  simp [spacetimeTranslate, SCV.translateSchwartz_apply, sub_eq_add_neg]

/-- The spectral function of a Wightman 2-point function against a
spacetime test function `f`.

`φ_f(a) := W_2(f̄ ⊗ T_a f)` where:
* `f̄ ⊗ g` = `(SchwartzMap.conjTensorProduct f g)` builds a 2-point
  Schwartz function on `Fin 2 → SpacetimeDim d` evaluating to
  `conj(f(splitFirst _)) * g(splitLast _)`. With both blocks of arity 1,
  the `Fin.rev` in `conjTensorProduct` is trivial, so this simplifies to
  `(x_0, x_1) ↦ conj(f(x_0)) * g(x_1)`.
* `T_a f` is `spacetimeTranslate a f` (i.e., `f(x - a)`).
* The 1-point factors are bridged to `SchwartzMap (Fin 1 → ·) ℂ` via
  `onePointToFin1CLM` from `SchwingerOS.lean`.

By temperedness of `W_2` (continuity of `Wfn.W 2` as a CLM on Schwartz
2-point functions), `φ_f` is continuous in `a`. By Wightman positivity
(R2 = `Wfn.positive_definite`) applied to length-1 Borchers sequences
of translates of `f`, `φ_f` is positive-definite as a function on
`(SpacetimeDim d, +)`. Applying `bochner_theorem` (after normalization
by `φ_f(0)`) extracts a finite positive Borel measure on momentum
space — the *vacuum spectral measure of `f`*. -/
noncomputable def spectralFunction (Wfn : WightmanFunctions d)
    (f : SchwartzSpacetime d) : SpacetimeDim d → ℂ :=
  fun a =>
    Wfn.W 2 ((onePointToFin1CLM d f).conjTensorProduct
              (onePointToFin1CLM d (spacetimeTranslate a f)))

/-- **Vacuum spectral measure of the Wightman 2-point function.**

For each `f : SchwartzNPoint d 1`, there exists a finite positive Borel
measure `μ` on `SpacetimeDim d` (= `Fin (d+1) → ℝ`, i.e. momentum space)
such that the Wightman 2-point matrix element against `f̄ ⊗ T_a f` is the
Fourier transform of `μ`:
  `W_2(f̄ ⊗ T_a f) = ∫ exp(-i a·p) dμ(p)` for all `a : SpacetimeDim d`.

The measure has total mass `μ(univ) = W_2(f̄ ⊗ f)` (the value at `a = 0`),
which is real and ≥ 0 by `Wfn.positive_definite`.

**Proof strategy** (deferred):
1. Show `a ↦ W_2(f̄ ⊗ T_a f)` is continuous (from `Wfn.tempered` plus
   continuity of `translateSchwartz` on `SchwartzMap`).
2. Show it is positive-definite as a function `SpacetimeDim d → ℂ`
   (from `Wfn.positive_definite`: positivity of the Wightman inner
   product on Borchers sequences applied to the sequence
   `[Borchers ↦ T_{a_i} f]_i` gives the matrix
   `[W_2(T_{a_i}f̄ ⊗ T_{a_j}f)]_{ij} ≥ 0`, equivalent to
   positive-definiteness of `φ_f` via translation invariance R1).
3. Normalize by `W_2(f̄ ⊗ f)` to get `φ_f(0) = 1`, apply
   `bochner_theorem` from the `BochnerMinlos` package, and de-normalize.

**Reference:** Streater-Wightman §3.4; Glimm-Jaffe §6.2. -/
theorem vacuum_spectral_measure_W2 (Wfn : WightmanFunctions d)
    (f : SchwartzSpacetime d) :
    ∃ μ : Measure (SpacetimeDim d),
      IsFiniteMeasure μ ∧
      ∀ a : SpacetimeDim d,
        spectralFunction Wfn f a =
          ∫ p : SpacetimeDim d, Complex.exp (-Complex.I * (∑ i, (a i : ℂ) * (p i : ℂ))) ∂μ := by
  -- Substantive proof deferred. Plan:
  -- 1. Prove `Continuous (spectralFunction Wfn f)`:
  --    composition of `Wfn.tempered 2` (CLM continuity) with continuity of
  --    `a ↦ (onePointToFin1CLM d f).conjTensorProduct
  --             (onePointToFin1CLM d (spacetimeTranslate a f))`
  --    in the Schwartz topology — uses
  --    `SchwartzMap.conjTensorProduct_continuous_right` (already proved)
  --    plus continuity of `SCV.translateSchwartzCLM` in its parameter.
  -- 2. Prove `IsPositiveDefinite (spectralFunction Wfn f)` on
  --    `(SpacetimeDim d, +)`: for any finite (a_k, c_k),
  --    ∑_{i,j} c_i conj(c_j) φ_f(a_i - a_j) =
  --      Wfn.W 2 (F̄ ⊗ F) where F = ∑_k c_k T_{a_k} f.
  --    Then apply Wfn.positive_definite to the length-1 Borchers
  --    sequence `[F]`. Re-arrangement requires
  --    Wfn.translation_invariant for the difference shift.
  -- 3. Set φ̃(a) := φ_f(a) / φ_f(0) (assuming φ_f(0) ≠ 0; the f = 0
  --    case gives μ = 0 trivially). φ̃ is continuous PD with φ̃(0) = 1.
  --    Apply `bochner_theorem` to get a unique probability measure ν.
  --    Take μ := φ_f(0).re • ν (positive scalar; nonneg from R2).
  -- 4. Verify the Fourier inversion: charFun ν (a) = φ̃(a) is the
  --    Bochner conclusion. Multiply through by φ_f(0).
  sorry

end KallenLehmann
end OSReconstruction
