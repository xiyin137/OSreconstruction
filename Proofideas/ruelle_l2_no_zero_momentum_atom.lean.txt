/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors

PARKED 2026-05-07 (was `OSReconstruction/Wightman/Spectral/Ruelle/L2_NoZeroMomentumAtom.lean`).
Per PR #82 review (xiyin137): the L2 target is QFT-specific and
load-bearing (full spatial-cobounded decay of GNS matrix coefficients
on the vacuum complement). Before this can be a production frontier
lemma, the proof needs a precision pass: split into smaller named
lemmas making explicit which step uses `gns_cluster_completion`
(existing), which uses SNAG, which uses no-atom-at-zero, and where AC
of the spatial marginal is assumed/proved/avoided.

Moved here for the precision pass. The current file has the target
statement and proof outline but is not yet ready as accepted
proof debt.
-/
import OSReconstruction.Wightman.Reconstruction.GNSHilbertSpace
import OSReconstruction.GeneralResults.SNAGTheorem

/-!
# L2: No zero-momentum atom on the vacuum complement

For a `WightmanFunctions` family `Wfn` satisfying R4 (`Wfn.cluster`),
the joint spectral measure of the spatial translation generators on
the orthogonal complement of the vacuum has **no atom at zero spatial
momentum**.

This is the spectral-gap content of R4 at the GNS Hilbert-space level,
and the load-bearing input to L6 / L7 in the Ruelle proof chain (see
`Blueprint.lean`).

## Existing infrastructure

* `gnsQFT Wfn : WightmanQFT d` (`GNSHilbertSpace.lean:2125`) — full
  GNS construction from `WightmanFunctions`.
* `gns_vacuum_unique_of_poincare_invariant`
  (`GNSHilbertSpace.lean:2073`) — vacuum is the unique
  Poincaré-invariant vector, *proved* from R4.
* `gns_cluster_completion` (`GNSHilbertSpace.lean:1917`) — *proved*:
  for `Φ : PreHilbert Wfn`, `ψ : GNSHilbert Wfn`, and any nonzero
  spatial direction `a`,
  `⟨Φ, U(r·a) ψ⟩ → ⟨Φ, Ω⟩ ⟨Ω, ψ⟩` as `r → ∞`.
* `snag_theorem` axiom in `GeneralResults/SNAGTheorem.lean` — joint
  spectral resolution of a strongly-continuous unitary representation
  of a finite-dim abelian group.

## Gap to close in this file

`gns_cluster_completion` gives **ray-style decay**: along a single
direction `a`, scaling `r·a` makes matrix elements approach the
disconnected piece. L2 needs **directional uniformity**: full decay
under the spatial-cobounded filter (where `a → ∞` in any direction).

The bridge:
1. Translate `gns_cluster_completion` into a statement about the
   spectral measure `μ_{Φ,ψ}` produced by SNAG: ray-decay along all
   spatial directions implies the spatial Fourier transform of
   `μ_{Φ,ψ}` has no constant component (hence no atom at zero spatial
   momentum on the vacuum complement).
2. State the no-zero-atom result on the vacuum complement directly.

## File status

This file currently contains the target statement as a sorry-stub
plus the proof outline. Lemma signatures are written so the proof can
be filled incrementally.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Reconstruction MeasureTheory Filter Bornology PreHilbertSpace

variable {d : ℕ} [NeZero d]

/-! ### Target statement: spatial-cobounded matrix-element decay on Ω⊥ -/

/-- **L2 target**

For any pair of states orthogonal to the vacuum in the GNS Hilbert
space, the matrix element `⟨Φ, U(a) ψ⟩` decays to `0` as the spatial
part of `a` goes to infinity (along the cobounded filter on
`SpacetimeDim d`, restricted to `a 0 = 0`).

This is the GNS Hilbert-space form of "no zero-momentum atom on the
vacuum complement". Equivalent (via SNAG) to: the joint spectral
measure of the spatial translation generators restricted to `Ω⊥` has
no atom at the origin in spatial momentum space.

The statement needs no SCV or BHW infrastructure — only the GNS
construction + R4. It's a pure FA / Hilbert-space consequence of
R4-cluster + spectral-theorem-via-SNAG.

Proof outline (deferred):

1. Apply `snag_theorem` to the spatial translation subgroup of
   `gnsPoincareRep Wfn`. Produces a joint projection-valued spectral
   measure on the spatial momentum space `Fin d → ℝ`.
2. The matrix element `⟨Φ, U(a) ψ⟩` for `a 0 = 0` equals the spatial
   Fourier transform of the SNAG spectral measure on the pair `(Φ, ψ)`.
3. By orthogonality (`Φ, ψ ⊥ Ω`) and `gns_cluster_completion` along
   every spatial ray, the spectral measure has no atom at `p⃗ = 0`
   (every spatial Fourier ray decays to 0).
4. By Riemann-Lebesgue (L5) applied to the AC marginal of the spectral
   measure (the marginal is AC by spectrum-condition input), the
   spatial Fourier transform tends to 0 along the cobounded filter.

L2 ↔ L5 dependency: step 4 uses Riemann-Lebesgue, which is L5.
The current file leaves L2 as a sorry-stub; once L5 is proved, this
file's proof becomes mechanical assembly. -/
theorem gns_orthogonal_spatial_cobounded_decay
    (Wfn : WightmanFunctions d)
    (Φ ψ : GNSHilbertSpace Wfn)
    (_hΦ : @inner ℂ _ _ (gnsVacuum Wfn) Φ = 0)
    (_hψ : @inner ℂ _ _ (gnsVacuum Wfn) ψ = 0) :
    Tendsto
      (fun a : SpacetimeDim d =>
        @inner ℂ _ _ Φ
          (poincareActGNS Wfn (PoincareGroup.translation' a) ψ))
      (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
        Bornology.cobounded (SpacetimeDim d))
      (nhds (0 : ℂ)) := by
  sorry

/-! ### Spectral-measure form (used by downstream L6 / L7)

The "no atom at zero spatial momentum" form requires committing to the
SNAG output's type (joint PVM on momentum space). Stub deferred until
the SNAG application is concretely written; see proof outline above.
-/
end
