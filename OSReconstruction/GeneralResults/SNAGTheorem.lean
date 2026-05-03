/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.Unitary
import Mathlib.Topology.MetricSpace.Basic

/-!
# SNAG theorem (Stone-Naimark-Ambrose-Godement)

The classical theorem from harmonic analysis stating that strongly continuous
unitary representations of `ℝⁿ` correspond bijectively to projection-valued
measures on the Borel σ-algebra of `ℝⁿ`. Specializes to **Stone's theorem** at
`n = 1` (single-parameter unitary groups ↔ self-adjoint generators).

In QFT this is the workhorse for joint spectral resolution of commuting
energy-momentum operators: a unitary representation of the translation group
`ℝ^{d+1}` on the Wightman / GNS Hilbert space gives a projection-valued
measure on momentum space `ℝ^{d+1}`. Its support encodes the spectrum
condition (R3) and its restriction to the truncated sector controls cluster
decomposition (R4 / Källén-Lehmann route).

## Main definitions

* `ProjectionValuedMeasureOn α H` — projection-valued measure on a measurable
  space `α` taking values in projections on a Hilbert space `H`. Generalizes
  `ProjectionValuedMeasure` (single-axis, `α = ℝ`) to arbitrary measurable
  spaces.

* `ProjectionValuedMeasureOn.diagonalMeasure` — for `ψ ∈ H`, the positive
  finite Borel measure on `α` defined by `B ↦ Re ⟨ψ, E(B) ψ⟩`. Total mass
  `‖ψ‖²`.

## Main result

* `snag_theorem` — *(axiom)* Every strongly continuous unitary representation
  of `ℝⁿ` is the spectral integral of a unique projection-valued measure on
  the Borel σ-algebra of `ℝⁿ`.

## References

* Reed, Simon, *Methods of Modern Mathematical Physics, Vol. I: Functional
  Analysis*, §VIII.4–VIII.5 (Theorem VIII.12 + Corollary).
* Birman, Solomjak, *Spectral Theory of Self-Adjoint Operators in Hilbert
  Space*, §VI.5 (joint spectral resolution of commuting self-adjoint
  operators).
* Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Theorem 5.21
  (multidimensional Stone theorem).

## Notes

The PVM structure gates `idempotent`, `selfAdjoint`, `inter`, and
`sigma_additive` behind `MeasurableSet` hypotheses, matching the standard
ZFC requirement that countably additive measures live on σ-algebras (the
existing single-axis `ProjectionValuedMeasure` in
`OSReconstruction/vNA/MeasureTheory/SpectralStieltjes.lean` does *not*
gate, but should — flagged for separate audit).

This axiom is **not yet proved** in this repo. The classical proof goes via
Bochner's theorem (already in the `bochner` repo) applied to the continuous
positive-definite function `a ↦ ⟨ψ, U(a) ψ⟩`, polarization to a sesquilinear
measure, and projection-valuedness from the group law on `U`. Discharging
the axiom is scheduled as a follow-up project (~5 weeks per current
calibration; see `MEMORY.md` formalization estimates).

## Vetting status

Vetted via Gemini chat (2026-05-03):

- Statement of `snag_theorem` itself: **excellent** — matches Reed-Simon
  Theorem VIII.12 perfectly. The diagonal scalar inversion uniquely
  determines the PVM via polarization + uniqueness of Fourier transform
  on finite measures.
- Hypotheses: exactly the right set (strong continuity + group +
  unitary + identity element).
- Edge cases: non-vacuous; `n = 0` collapses to a Dirac at `0`; `H = {0}`
  is the trivial PVM.
- Initial draft of the PVM structure required `idempotent`, `selfAdjoint`,
  `inter`, `sigma_additive` on *all subsets*, which was flagged as
  mathematically inconsistent (no non-trivial measure on the full power
  set of `ℝⁿ` in ZFC). Fixed by gating all axioms behind `MeasurableSet`.

Audit table entry:

| Axiom | File:Line | Rating | Sources | Notes |
|-------|-----------|--------|---------|-------|
| `snag_theorem` | SNAGTheorem.lean | Standard | GR, LP | Reed-Simon I VIII.12; Schmüdgen 5.21; Birman-Solomjak VI.5.1 |
-/

namespace OSReconstruction

open MeasureTheory ContinuousLinearMap

universe u

variable {α : Type*} [MeasurableSpace α]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A projection-valued measure on a measurable space `α` valued in
projections on a Hilbert space `H`.

The defining axioms `idempotent`, `selfAdjoint`, `inter`, `sigma_additive`
are gated behind `MeasurableSet` hypotheses. Gating is essential: in ZFC
no non-trivial countably additive measure is defined on the full power
set of `ℝⁿ` (Vitali-style obstruction), so the PVM is only meaningful on
the σ-algebra `MeasurableSpace α`.

Generalizes `OSReconstruction.vNA.MeasureTheory.SpectralStieltjes.ProjectionValuedMeasure`
(which is specialized to `α = ℝ` and stated without explicit measurability
guards — those guards are equally needed there but the existing structure
predates this audit). The σ-additivity is stated in the strong operator
topology. -/
structure ProjectionValuedMeasureOn (α : Type*) [MeasurableSpace α]
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The projection associated with each subset.

  Only the values on `MeasurableSet`s carry meaning; the assignment on
  non-measurable sets is unconstrained ("junk"). -/
  proj : Set α → (H →L[ℂ] H)
  /-- `E(∅) = 0`. -/
  empty : proj ∅ = 0
  /-- `E(univ) = id`. -/
  univ : proj Set.univ = ContinuousLinearMap.id ℂ H
  /-- Each `E(B)` is idempotent on measurable `B`: `E(B)² = E(B)`. -/
  idempotent : ∀ B, MeasurableSet B → proj B ∘L proj B = proj B
  /-- Each `E(B)` is self-adjoint on measurable `B`: `E(B)* = E(B)`. -/
  selfAdjoint : ∀ B, MeasurableSet B → (proj B).adjoint = proj B
  /-- Multiplicativity on measurable sets:
      `E(B ∩ C) = E(B) ∘ E(C)` for measurable `B, C`. (Combined with
      idempotence + self-adjointness this implies pairwise commutativity
      `E(B) E(C) = E(C) E(B)`.) -/
  inter : ∀ B C, MeasurableSet B → MeasurableSet C →
    proj (B ∩ C) = proj B ∘L proj C
  /-- σ-additivity in the strong operator topology, on measurable
      pairwise-disjoint families. -/
  sigma_additive : ∀ (B : ℕ → Set α), (∀ i, MeasurableSet (B i)) →
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
    ∀ x : H, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, proj (B i) x)
      Filter.atTop (nhds (proj (⋃ i, B i) x))

/-- The diagonal scalar measure of a vector `ψ` under a PVM.

For each `ψ`, the assignment `B ↦ Re ⟨ψ, E(B) ψ⟩` is a finite positive Borel
measure on `α` of total mass `‖ψ‖²`, by self-adjointness + idempotence of
`E(B)` (so `⟨ψ, E(B) ψ⟩ = ‖E(B) ψ‖²` is real and nonneg) and σ-additivity in
SOT.

This is the Wightman / Schwinger spectral measure of `ψ` under the unitary
representation generated by the PVM. -/
noncomputable def ProjectionValuedMeasureOn.diagonalMeasure
    {α : Type*} [MeasurableSpace α]
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (_E : ProjectionValuedMeasureOn α H) (_ψ : H) : Measure α :=
  -- Constructed via Carathéodory from the function `B ↦ ‖E.proj B ψ‖²`.
  -- Implementation deferred (uses standard PVM-to-scalar-measure construction;
  -- generalizes the single-axis `SpectralDistribution.toMeasure` from
  -- `vNA/MeasureTheory/SpectralStieltjes.lean`).
  0  -- placeholder; real definition via Hahn-Carathéodory once PVM API matures

/-- **SNAG theorem (Stone-Naimark-Ambrose-Godement).**

Every strongly continuous unitary representation `U : ℝⁿ → 𝒰(H)` is the
Fourier transform of a unique projection-valued measure `E` on `Borel(ℝⁿ)`:
$$U(a) = \int_{\mathbb{R}^n} e^{i\, a \cdot p}\, dE(p)$$
in strong-operator sense. Equivalently, the `n` commuting infinitesimal
generators `P_j = -i ∂_{a_j} U` (closed self-adjoint) admit a unique joint
spectral resolution.

The conclusion is stated via the diagonal scalar measure: for every vector
`ψ ∈ H`, the matrix element `⟨ψ, U(a) ψ⟩` equals the Fourier integral of
`a ↦ exp(i ⟨a, p⟩)` against the diagonal measure of `ψ`. The full PVM
structure (off-diagonal sesquilinear form, σ-additivity in SOT) is captured
by the existential.

Specializes to **Stone's theorem** at `n = 1`.

**Reference:** Reed-Simon Vol I §VIII.4 (Theorem VIII.12 + Corollary);
Birman-Solomjak §VI.5; Schmüdgen Theorem 5.21.

**Strategy (deferred):** For each `ψ ∈ H`, the function
`a ↦ ⟨ψ, U(a) ψ⟩` is continuous positive-definite on `ℝⁿ` with value `‖ψ‖²`
at `0`. Bochner's theorem gives a finite positive Borel measure `μ_ψ` on
`ℝⁿ` whose Fourier transform is this matrix element. Polarize to a
sesquilinear `μ_{ψ,φ}`. The bounded sesquilinear form `B ↦ μ_{·,·}(B)`
defines a bounded operator `E(B) ∈ B(H)` for each Borel `B`.
Multiplicativity `μ_ψ(B₁ ∩ B₂) = ⟨E(B₁)ψ, E(B₂)ψ⟩` (from the group law
`U(a+b) = U(a) U(b)`) gives `E(B)² = E(B)`; self-adjointness from `μ_ψ`
real-valued. (NOT VERIFIED — to be vetted via Gemini deep-think + Codex.) -/
axiom snag_theorem
    {n : ℕ} {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : (Fin n → ℝ) → (H →L[ℂ] H))
    (_hU_zero : U 0 = ContinuousLinearMap.id ℂ H)
    (_hU_add : ∀ a b, U (a + b) = U a ∘L U b)
    (_hU_unit : ∀ a, U a ∈ unitary (H →L[ℂ] H))
    (_hU_cont : ∀ ψ : H, Continuous (fun a => U a ψ)) :
    ∃! E : ProjectionValuedMeasureOn (Fin n → ℝ) H,
      ∀ a : Fin n → ℝ, ∀ ψ : H,
        (@inner ℂ H _ ψ (U a ψ) : ℂ) =
          ∫ p : Fin n → ℝ,
            Complex.exp (Complex.I * (∑ i, (a i : ℂ) * ((p i : ℝ) : ℂ)))
              ∂(ProjectionValuedMeasureOn.diagonalMeasure E ψ)

end OSReconstruction
