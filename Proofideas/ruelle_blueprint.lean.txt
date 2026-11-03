/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors

PARKED 2026-05-07 (was `OSReconstruction/Wightman/Spectral/Ruelle/Blueprint.lean`).
Per PR #82 review (xiyin137): the top-level `ruelleHypotheses_of_wightman`
sorry stub at the bottom of this file would re-introduce the QFT Ruelle
theorem in disguise as a production theorem-hole. Moved here to keep
production clean while preserving the L1–L7 proof roadmap as
architectural reference.
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.RuelleClusterBound

/-!
# Ruelle 1962 analytic cluster theorem — proof blueprint

This module assembles a proof of `RuelleAnalyticClusterHypotheses Wfn n m`
from R4 (`Wfn.cluster`) + spectrum condition. The end product is the
discharge function

```
ruelleHypotheses_of_wightman (Wfn : WightmanFunctions d) (n m : ℕ) :
    RuelleAnalyticClusterHypotheses Wfn n m
```

which makes the conditional cluster theorem in `RuelleClusterBound.lean`
*unconditional* on Wightman input.

## Textbook chain

Following Streater-Wightman §3.5, Jost VI.1, Araki-Hepp-Ruelle 1962:

```
R4 distributional cluster (Wfn.cluster)
    +
spectrum condition (analytic continuation on ForwardTube)
    │
    ▼ [L1] Truncated decomposition (combinatorial)
W_n = Σ_π ∏_{B ∈ π} W^T_{|B|}
    │
    ▼ [L2] Truncated spectral support (R4 + spectrum cond → no zero atom)
W^T_k Fourier transform supported on V̄+, no atom at zero momentum
    │
    ▼ [L3] Laplace transform representation (Bochner / SCV)
W^T_analytic_k(z) = ∫ exp(i p·z) dν^T_k(p), spectral measure ν^T_k
    │                                     │
    ▼ [L4]                                ▼ [L5+L6]
Uniform-in-a polynomial bound        Pointwise spatial decay of W^T
on (W_analytic_BHW Wfn (n+m))        as |a⃗| → ∞
    │                                     │
    └──────────────┬──────────────────────┘
                   ▼ [L7] Partition recombination
RuelleAnalyticClusterHypotheses.bound  (uniform-in-a polynomial bound)
RuelleAnalyticClusterHypotheses.pointwise  (pointwise factorization)
```

## Module organization

Each L_k is intended to land in a dedicated file within
`OSReconstruction/Wightman/Spectral/Ruelle/`:

* `TruncatedDecomposition.lean` — L1 (combinatorial partition formula).
* `TruncatedSpectralSupport.lean` — L2 (R4 → no zero-momentum atom).
* `LaplaceRepresentation.lean` — L3 (spectral measure ↔ analytic continuation).
* `UniformPolynomialBound.lean` — L4 (a-uniform bound from spectral support).
* `SpectralRiemannLebesgue.lean` — L5 (RL for tempered measures with no atom).
* `TruncatedSpatialCluster.lean` — L6 (pointwise truncated cluster, L2 + L5).
* `PartitionRecombination.lean` — L7 (assembly via L1 + L4 + L6).
* `Discharge.lean` — top-level `ruelleHypotheses_of_wightman`.

For now this single file holds the top-level discharge function as a
sorry-stub and the lemma roster as comments; pieces migrate to dedicated
files as they're proved.

## Existing infrastructure

* `BochnerMinlos` package: Bochner theorem, Fourier transforms of measures.
* `gaussian-field`: SchwartzSpace nuclearity, Fréchet Bochner integration.
* `OSReconstruction.SCV.*`: tube-domain analytic continuation, BV machinery.
* `OSReconstruction.GeneralResults.SNAGTheorem`: SNAG theorem (existing axiom).
* Project-side `Wfn.cluster`, `Wfn.spectrum_condition`, `W_analytic_BHW`.

## Existing parked work

`Proofideas/cluster_from_kallen_lehmann.lean` contains drafts for L2/L3/L5/L6/L7
with 9 sorrys and 4 open vetting issues. Use as architectural reference,
not direct import — the parked file has the existential-bundling antipattern
(KL vetting Issue 1) that the new build should avoid.

## Open questions / subprojects

* **L2 risk**: deriving "truncated correlations have no zero-momentum atom"
  requires GNS vacuum uniqueness + a spectral-measure analysis. The
  existential-bundling refactor (KL Issue 1) is a prerequisite.
* **AC marginal** (KL Issue 4): the truncated state-specific spectral
  measure should have AC spatial marginal. May need a separate axiom
  with literature citation, or a textbook-level proof through mass-hyperboloid
  analysis. Decision point during L2.
-/

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-! ## Top-level discharge (target)

The goal of this module: produce a `RuelleAnalyticClusterHypotheses Wfn n m`
value from a `WightmanFunctions d`.

Currently a sorry-stub; the proof is the L1–L7 chain assembled in
`PartitionRecombination.lean`.

Once proved, callers in `RuelleClusterBound.lean` can drop the
`(hRuelle : RuelleAnalyticClusterHypotheses Wfn n m)` parameter and
recover unconditional theorems. -/

/-- **Ruelle 1962 / Araki-Hepp-Ruelle 1962, formal discharge** —
the analytic cluster hypotheses for a Wightman family follow from R4 +
spectrum condition + standard FA infrastructure. Proof via L1–L7 chain
described in this module's docstring. -/
theorem ruelleHypotheses_of_wightman (Wfn : WightmanFunctions d) (n m : ℕ) :
    RuelleAnalyticClusterHypotheses Wfn n m := by
  sorry

/-! ## Lemma roster (signatures + plans, awaiting proof)

The detailed Lean signatures live in dedicated files; outlined here for
review.

### L1: Truncated decomposition
**File**: `TruncatedDecomposition.lean`.

Define the truncated (connected) Wightman functions `W^T_n` from `W_n`
via the Möbius/cumulant formula:
```
W^T_n(f) := Σ_π (-1)^(|π|-1) (|π|-1)! ∏_{B ∈ π} W_{|B|}(f|_B)
```
over set partitions π of {1, ..., n}.

Statement:
```
W_n = Σ_π ∏_{B ∈ π} W^T_{|B|}
```
on factorizable test functions `f = ⊗ g_i` (and extends to general
Schwartz by continuity / density).

**Effort**: 3–5 active days. Pure combinatorics; pieces in BochnerMinlos.

### L2: Truncated spectral support — no zero atom
**File**: `TruncatedSpectralSupport.lean`.

For each k ≥ 2, the Fourier transform of `W^T_k` (in the relative
coordinates) is a tempered distribution supported on the (k-1)-fold
product of V̄+, with **no atom at any zero-momentum coordinate**.

This is the key spectral-gap content of R4: the cluster property
implies the truncated correlations have no zero-mode contribution.

**Existing infrastructure (discovered 2026-05-07)**:

The project already provides much of this at the GNS level:
* `gnsQFT Wfn : WightmanQFT d` (`GNSHilbertSpace.lean:2125`) — full
  GNS construction.
* `gns_vacuum_unique_of_poincare_invariant`
  (`GNSHilbertSpace.lean:2073`) — *PROVED*: vacuum is the unique
  Poincaré-invariant vector. Reduces from R4 cluster.
* `gns_cluster_completion` (`GNSHilbertSpace.lean:1917`) — *PROVED*:
  for `Φ : PreHilbert Wfn`, `ψ : GNSHilbert Wfn`, and any nonzero
  spatial direction `a`,
  `⟨Φ, U(r·a) ψ⟩ → ⟨Φ, Ω⟩ ⟨Ω, ψ⟩` as `r → ∞`.

**Gap to close**: `gns_cluster_completion` gives **ray decay** along a
single spatial direction. L2 needs **full spatial-cobounded decay**
(uniform in direction at infinity). The lift uses:
* SNAG (`snag_theorem` axiom in `GeneralResults/SNAGTheorem.lean`) →
  joint spectral measure of the translation group.
* Decay along all spatial rays + spectral measure structure → no atom
  at zero spatial momentum on the vacuum complement.
* Then the cobounded-Tendsto form follows from L5 (Riemann-Lebesgue)
  applied to the no-atom-at-zero spectral measure.

**Revised effort**: 3–7 active days (was 8–15). KL Issue 1
(existential bundling) is partially solved by the existing `gnsQFT`
construction; we use that directly rather than redefining a class.
KL Issues 2–3 (OS time reflection, vacuum expectation bridge) still
matter for L7 recombination but not for L2 itself.

### L3: Laplace transform representation
**File**: `LaplaceRepresentation.lean`.

For `z` in the (k-fold relative) forward tube:
```
W^T_analytic_k(z) = ∫ exp(i p · z) dν^T_k(p)
```
where `ν^T_k` is the spectral measure from L2.

Proof sketch: spectrum condition + Bochner's theorem applied per
spectral fibre, then assemble via SNAG / gaussian-field FA tools.

**Effort**: 3–6 active days.

### L4: Uniform-in-a polynomial bound
**File**: `UniformPolynomialBound.lean`.

Apply L3 to bound `(W_analytic_BHW Wfn (n+m)).val (joint config with
shift a)`:
```
‖∫ exp(i p · joint(z₁, z₂ + a)) dν^T_(n+m)(p)‖ ≤ C(1 + ‖z₁‖ + ‖z₂‖)^N
```
The `a`-independence comes from `exp(i p · (z₂ + a)) = exp(i p · z₂)
exp(i p · a)` and `|exp(i p · a)| ≤ 1` (modulus only depends on imaginary
part of `p · a`, which is 0 for real spatial `a`).

**Effort**: 3–7 active days. Standard Laplace bound; may need Mathlib FA
additions for vector-valued tempered measures.

### L5: Spectral Riemann-Lebesgue
**File**: `SpectralRiemannLebesgue.lean`.

For a tempered measure `ν` on V̄+ with no atom at zero momentum, the
spatial Fourier transform tends to 0 at infinity:
```
Tendsto (a ↦ ∫ exp(i p·a) dν(p))_{spatial cobounded} (𝓝 0)
```
provided ν has AC spatial marginal.

Proof: decompose ν = ν_AC + ν_SC + ν_atomic; AC case from Mathlib's
RL lemma; SC from Wiener; atomic forced by no-zero-atom hypothesis to
have no atoms with spatial part 0.

Status: was axiomatized in the parked `spectral_analysis.lean`
(50-line discharge plan in docstring). Discharge here.

**Effort**: 1–3 active days. Pure measure theory.

### L6: Pointwise truncated spatial cluster
**File**: `TruncatedSpatialCluster.lean`.

Combines L2 (no zero atom) + L5 (RL) to give:
```
Tendsto (a ↦ W^T_k(stuff with spatial shift a))_{spatial cobounded} (𝓝 0)
```
for k ≥ 2.

**Effort**: 2–4 active days. Mostly assembly.

### L7: Partition recombination
**File**: `PartitionRecombination.lean`.

Combine L1 (partition formula) with L4 (uniform bound) and L6 (truncated
spatial decay). For the (n+m)-point function on the joint Wick-rotated
config:
```
W_{n+m}(joint with shift a) = Σ_π ∏ W^T_{|B|}(blocks)
                            = Σ_(non-crossing π) ∏ W^T(...) + Σ_(crossing π) → 0 by L6
                            = W_n(z₁) · W_m(z₂)
```

This produces both fields of `RuelleAnalyticClusterHypotheses`.

**Effort**: 3–5 active days.

## Estimated total

Active-days: 28–55. Per recalibrated CLAUDE.md ranges (active ≈ 30–50%
of elapsed): **5–14 weeks elapsed**, with L2 the dominant risk.

If L2 stalls, fall back to:
* Path B (split-region DC, ~3–6 weeks) — shipped as a separate PR.
* Path C (hypothesis refactor, current PR's state) — already shipped.

-/

end OSReconstruction
