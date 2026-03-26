# SCV TODO: OS-Critical Analytic Continuation Chain

Last updated: 2026-03-25

This TODO tracks the remaining `SCV` blockers on the OS reconstruction path.

Count convention in this file: direct tactic holes only,
`rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction/SCV --glob '*.lean'`.

## Live Sorry Census

| Scope | Direct `sorry` lines |
|---|---:|
| `OSReconstruction/SCV` | 2 |

Breakdown:
- `SCV/BochnerTubeTheorem.lean`: 2
- All other SCV files: 0

## Axiom Census

| File | Axioms | Names |
|------|--------|-------|
| `SCV/SemigroupGroupBochner.lean` | 2 | `semigroupGroup_bochner`, `laplaceFourier_measure_unique` |
| `SCV/VladimirovTillmann.lean` | 2 | `vladimirov_tillmann`, `distributional_cluster_lifts_to_tube` |
| **Total** | **4** | |

### Axiom Details

**`semigroupGroup_bochner`** (BCR Theorem 4.1.13): Bounded continuous positive-definite
functions on [0,∞) × ℝᵈ are Fourier-Laplace transforms of finite positive measures.
Used by `OSToWightmanSemigroup.lean` in the E→R semigroup direction.

**`laplaceFourier_measure_unique`**: Finite positive measures supported on nonneg energy
are determined by their joint Laplace-Fourier transform on t > 0. Uniqueness clause
backing the semigroup-group Bochner theorem.

**`vladimirov_tillmann`**: Boundary-value theorem for holomorphic functions on tube domains
with polynomial growth. Gives Vladimirov bound with inverse-boundary-distance factor.
Used by `OSToWightmanBoundaryValues.lean`.

**`distributional_cluster_lifts_to_tube`**: Cluster property from distributional boundary
values lifts to pointwise factorization in the tube interior. Used for the cluster
decomposition axiom transfer.

## Usage in the Main Proof Chain

The SCV module provides analytic continuation infrastructure consumed by:
1. **Edge-of-the-wedge theorem** (`TubeDomainExtension.lean`) — proved, axiom-free,
   used by BHW permutation extension chain
2. **Bochner tube theorem** (`BochnerTubeTheorem.lean`) — 2 sorries, used for
   tube-domain holomorphic extension
3. **Paley-Wiener** (`PaleyWiener.lean`) — sorry-free, one-step Fourier support
4. **Distributional uniqueness** (`DistributionalUniqueness.lean`) — sorry-free,
   boundary-value uniqueness for BHW chain
5. **Schwartz completeness** (`SchwartzComplete.lean`) — sorry-free, Banach-Steinhaus
6. **Semigroup-Bochner axioms** (`SemigroupGroupBochner.lean`) — 2 axioms,
   used by E→R contraction semigroup
7. **Vladimirov-Tillmann axioms** (`VladimirovTillmann.lean`) — 2 axioms,
   used by boundary-value transfer theorems

## File Status

### Sorry-Free Files

| File | Status | Notes |
|------|--------|-------|
| `Analyticity.lean` | Complete | |
| `DistributionalUniqueness.lean` | Complete | Boundary-value uniqueness |
| `EdgeOfWedge.lean` | Complete | |
| `EOWMultiDim.lean` | Complete | |
| `FourierLaplaceCore.lean` | Complete | |
| `IdentityTheorem.lean` | Complete | |
| `IteratedCauchyIntegral.lean` | Complete | |
| `LaplaceHolomorphic.lean` | Complete | |
| `LaplaceSchwartz.lean` | Complete | Weak/regular split |
| `LocalBoundaryRecovery.lean` | Complete | |
| `MoebiusMap.lean` | Complete | |
| `MultipleReflection.lean` | Complete | |
| `Osgood.lean` | Complete | |
| `PaleyWiener.lean` | Complete | |
| `Polydisc.lean` | Complete | |
| `SchwartzComplete.lean` | Complete | CompleteSpace, BarrelledSpace, Banach-Steinhaus |
| `SemigroupBochner.lean` | Complete | |
| `SeparatelyAnalytic.lean` | Complete | |
| `TotallyRealIdentity.lean` | Complete | |
| `TubeDomainExtension.lean` | Complete | Edge-of-the-wedge theorem |
| `TubeDistributions.lean` | Complete | |

### Files with Sorries

| File | Sorrys | Names |
|------|--------|-------|
| `BochnerTubeTheorem.lean` | 2 | `bochner_local_extension`, `bochner_tube_extension` |

### Files with Axioms (no sorries)

| File | Axioms | Names |
|------|--------|-------|
| `SemigroupGroupBochner.lean` | 2 | `semigroupGroup_bochner`, `laplaceFourier_measure_unique` |
| `VladimirovTillmann.lean` | 2 | `vladimirov_tillmann`, `distributional_cluster_lifts_to_tube` |

## Load-Bearing Items

### `SCV/BochnerTubeTheorem.lean` (2 sorries)

Remaining blockers:
- `bochner_local_extension`
- `bochner_tube_extension`

The old generic gluing theorem was too strong and has been removed.
Current work should build on the compatible-family gluing theorem instead.

### `SCV/LaplaceSchwartz.lean` (0 sorries)

The weak/regular split is now honest:
- `HasFourierLaplaceRepr`
- `HasFourierLaplaceReprRegular`
No fake upgrade theorem from weak BV data remains.

### `SCV/TubeDistributions.lean` (0 sorries)

Only the rigorous regular variants remain. The unused weak placeholder fronts
were removed instead of being carried as public `sorry`s.

### `SCV/PaleyWiener.lean` (0 sorries)

`paley_wiener_half_line` and the slice-wise `paley_wiener_one_step` are proved.
No fake multidimensional Fourier-support notion remains in the public API.

## Distributional EOW — COMPLETE (2026-03-10)

**All distributional EOW infrastructure is proved with 0 sorrys.**

Full chain:
1. `SCV/SchwartzComplete.lean` (0 sorrys): `CompleteSpace`, `BarrelledSpace`, Banach-Steinhaus chain
2. `SCV/DistributionalUniqueness.lean` (0 sorrys):
   - `exists_integral_clm_of_continuous` — truncation → CLM via Banach-Steinhaus
   - `distributional_uniqueness_tube_of_zero_bv` — tube uniqueness from distributional BV = 0
   - `eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` — pointwise extraction
3. `Wightman/Reconstruction/ForwardTubeDistributions.lean` (0 sorrys):
   - `distributional_uniqueness_forwardTube` — PROVED (flattening + tube uniqueness)
4. `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean` (0 sorrys):
   - Distributional pairing → pointwise on real open → connected-overlap propagation
5. `Wightman/Reconstruction/WickRotation/BHWExtension.lean`:
   - `W_analytic_swap_boundary_pairing_eq` — PROVED via distributional chain
   - `analytic_extended_local_commutativity` — PROVED (extendF-level pointwise swap)
   - `analytic_boundary_local_commutativity_of_boundary_continuous` — PROVED
6. `PermutationFlow.lean` fully rewired to distributional hypotheses (0 sorrys)

## Execution Order

1. Use the explicit regular package directly in downstream flattened-tube transport.
2. Return to the real missing theorem: construct `HasFourierLaplaceReprRegular`
   from actual Fourier-Laplace input with the right dual-cone support.
3. Return to `BochnerTubeTheorem.lean`.

## Stable Completed Core

- `Polydisc.lean`
- `IteratedCauchyIntegral.lean`
- `Osgood.lean`
- `Analyticity.lean`
- `TubeDomainExtension.lean`
- `IdentityTheorem.lean`
- `FourierLaplaceCore.lean`
- `PaleyWiener.lean`
- `DistributionalUniqueness.lean`
- `SchwartzComplete.lean`

`edge_of_the_wedge_theorem` is proved and axiom-free.
