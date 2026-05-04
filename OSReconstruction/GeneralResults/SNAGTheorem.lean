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
  space `α` taking values in projections on a Hilbert space `H`. The
  underlying assignment `proj` is indexed by *measurable sets only*
  (`proj : ∀ B : Set α, MeasurableSet B → (H →L[ℂ] H)`), eliminating any
  "junk" on non-measurable sets so that uniqueness in the SNAG conclusion
  is genuine.

## Main result

* `snag_theorem` — *(axiom)* Every strongly continuous unitary representation
  of `ℝⁿ` is the spectral integral of a unique projection-valued measure on
  the Borel σ-algebra of `ℝⁿ`. The conclusion existentially binds the
  diagonal spectral measure of each vector `ψ`, characterizing it on
  measurable sets via `‖E(B) ψ‖²` and stating the Fourier inversion against
  it.

## References

* Reed, Simon, *Methods of Modern Mathematical Physics, Vol. I: Functional
  Analysis*, §VIII.4–VIII.5 (Theorem VIII.12 + Corollary).
* Birman, Solomjak, *Spectral Theory of Self-Adjoint Operators in Hilbert
  Space*, §VI.5 (joint spectral resolution of commuting self-adjoint
  operators).
* Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Theorem 5.21
  (multidimensional Stone theorem).

## Notes

This axiom is **not yet proved** in this repo. The classical proof goes via
Bochner's theorem (already in the `bochner` repo, `Bochner/Main.lean:1190`,
proved) applied to the continuous positive-definite function
`a ↦ ⟨ψ, U(a) ψ⟩`, polarization to a sesquilinear measure, and
projection-valuedness from the group law on `U`. Discharging the axiom is
scheduled as a follow-up project (~5 weeks per current calibration).

## Vetting status

Vetted via Gemini chat (2026-05-03) and Codex review:

- Statement of `snag_theorem` itself: matches Reed-Simon Theorem VIII.12.
  Hypothesis set (strong continuity + group + unitary + identity) is
  exactly the textbook set. Diagonal scalar inversion uniquely determines
  the PVM via polarization + Fourier uniqueness on finite measures.
- Initial draft of the PVM structure required PVM axioms on *all*
  `Set α`; flagged by Gemini as ZFC-inconsistent (no non-trivial
  countably additive measure on the full power set of `ℝⁿ`). Fixed
  initially by gating axioms behind `MeasurableSet`, then strengthened
  per Codex review by indexing `proj` itself on measurable sets so the
  uniqueness claim is over genuine measurable-set-indexed data only.
- Initial draft also defined `diagonalMeasure := 0` as a placeholder,
  which (together with the axiom statement quantifying the Fourier
  formula against that placeholder) was inconsistent — it forced
  `⟨ψ, ψ⟩ = 0` for the identity representation on `ℂ`. Fixed by
  removing the def and existentially binding the measure inside the
  axiom statement, with an explicit characterization on measurable sets
  via `‖E(B) ψ‖²`.

Audit table entry:

| Axiom | File:Line | Rating | Sources | Notes |
|-------|-----------|--------|---------|-------|
| `snag_theorem` | SNAGTheorem.lean | Standard | GR, PR, LP | Reed-Simon I VIII.12; Schmüdgen 5.21; Birman-Solomjak VI.5.1 |
-/

namespace OSReconstruction

open MeasureTheory ContinuousLinearMap

universe u

variable {α : Type*} [MeasurableSpace α]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A projection-valued measure on a measurable space `α` valued in
projections on a Hilbert space `H`.

The underlying assignment `proj` takes a *pair* of a set and a proof that
it is measurable. This eliminates "junk" data on non-measurable subsets:
the spectral measures of interest here (Borel / continuous, e.g. Lebesgue
on `ℝⁿ` regularized by an `L¹` density) cannot be extended to the full
power set under ZFC, so the PVM is meaningful only on the σ-algebra
`MeasurableSpace α`. Indexing `proj` directly on measurable sets is what
allows uniqueness in the SNAG theorem to be a genuine extensional
statement (without the gate, two PVMs agreeing on every measurable set
but differing on Vitali-type subsets would be distinct Lean structures).

Generalizes `OSReconstruction.vNA.MeasureTheory.SpectralStieltjes.ProjectionValuedMeasure`
(specialized to `α = ℝ` and indexed on `Set ℝ` directly — that older
structure should be retrofitted with the same gating in a separate audit).
The σ-additivity is in the strong operator topology. -/
structure ProjectionValuedMeasureOn (α : Type*) [MeasurableSpace α]
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The projection associated with each *measurable* subset. -/
  proj : ∀ B : Set α, MeasurableSet B → (H →L[ℂ] H)
  /-- `E(∅) = 0`. -/
  empty : proj ∅ MeasurableSet.empty = 0
  /-- `E(univ) = id`. -/
  univ : proj Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℂ H
  /-- Each `E(B)` is idempotent. -/
  idempotent : ∀ B (hB : MeasurableSet B),
    proj B hB ∘L proj B hB = proj B hB
  /-- Each `E(B)` is self-adjoint. -/
  selfAdjoint : ∀ B (hB : MeasurableSet B),
    (proj B hB).adjoint = proj B hB
  /-- Multiplicativity: `E(B ∩ C) = E(B) ∘ E(C)`. (Combined with idempotence
      and self-adjointness this implies pairwise commutativity
      `E(B) E(C) = E(C) E(B)`.) -/
  inter : ∀ B C (hB : MeasurableSet B) (hC : MeasurableSet C),
    proj (B ∩ C) (hB.inter hC) = proj B hB ∘L proj C hC
  /-- σ-additivity in the strong operator topology, on measurable
      pairwise-disjoint families. -/
  sigma_additive : ∀ (B : ℕ → Set α) (hB : ∀ i, MeasurableSet (B i)),
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
    ∀ x : H, Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n, proj (B i) (hB i) x)
      Filter.atTop (nhds (proj (⋃ i, B i) (MeasurableSet.iUnion hB) x))

/-- **SNAG theorem (Stone-Naimark-Ambrose-Godement).**

Every strongly continuous unitary representation `U : ℝⁿ → 𝒰(H)` is the
Fourier transform of a unique projection-valued measure `E` on `Borel(ℝⁿ)`.
For each vector `ψ ∈ H` there is an associated finite positive Borel
measure (the *diagonal spectral measure of `ψ`*) characterized by
`μ_ψ(B) = ‖E(B) ψ‖²` on measurable `B`, and the matrix element
`⟨ψ, U(a) ψ⟩` is its Fourier transform.

The full PVM structure (off-diagonal sesquilinear form, σ-additivity in
SOT) is implied by the diagonal data via polarization and the uniqueness
of Fourier transforms on finite measures.

Specializes to **Stone's theorem** at `n = 1`.

**Reference:** Reed-Simon Vol I §VIII.4 (Theorem VIII.12 + Corollary);
Birman-Solomjak §VI.5; Schmüdgen Theorem 5.21.

**Strategy (deferred):** For each `ψ ∈ H`, the function
`a ↦ ⟨ψ, U(a) ψ⟩` is continuous positive-definite on `ℝⁿ` with value
`‖ψ‖²` at `0`. Bochner's theorem (proved in the `bochner` repo at
`Bochner/Main.lean:1190`) gives a finite positive Borel measure `μ_ψ` on
`ℝⁿ` whose Fourier transform is this matrix element. Polarize to a
sesquilinear `μ_{ψ,φ}`. The bounded sesquilinear form `B ↦ μ_{·,·}(B)`
defines a bounded operator `E(B) ∈ B(H)` for each Borel `B`.
Multiplicativity from the group law `U(a+b) = U(a) U(b)` gives
`E(B)² = E(B)`; self-adjointness from `μ_ψ` real-valued. -/
axiom snag_theorem
    {n : ℕ} {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : (Fin n → ℝ) → (H →L[ℂ] H))
    (_hU_zero : U 0 = ContinuousLinearMap.id ℂ H)
    (_hU_add : ∀ a b, U (a + b) = U a ∘L U b)
    (_hU_unit : ∀ a, U a ∈ unitary (H →L[ℂ] H))
    (_hU_cont : ∀ ψ : H, Continuous (fun a => U a ψ)) :
    ∃! E : ProjectionValuedMeasureOn (Fin n → ℝ) H,
      ∀ ψ : H, ∃ μ : Measure (Fin n → ℝ),
        IsFiniteMeasure μ ∧
        (∀ B (hB : MeasurableSet B),
          μ B = ENNReal.ofReal (‖E.proj B hB ψ‖^2)) ∧
        ∀ a : Fin n → ℝ,
          (@inner ℂ H _ ψ (U a ψ) : ℂ) =
            ∫ p : Fin n → ℝ,
              Complex.exp (Complex.I *
                (∑ i, (a i : ℂ) * ((p i : ℝ) : ℂ))) ∂μ

end OSReconstruction
