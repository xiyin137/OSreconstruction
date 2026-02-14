# Wightman QFT Module — TODO

## TOP PRIORITY: OS Reconstruction Theorems

**Key insight**: Nuclear spaces / Minlos are NOT needed for the OS reconstruction theorems.
The reconstruction takes Schwinger functions as given input — nuclear spaces are about
*constructing* those Schwinger functions (upstream), not about reconstructing Wightman QFT.

Fermion theories on the lattice and Yang-Mills at nonzero theta angle do NOT admit
Borel measures in field space, but they are reflection positive and expected to be
Wightman QFTs — OS reconstruction is strictly more general than the NuclearSpaces/Minlos path.

### Critical Path for OS Reconstruction

1. ~~**Schwartz tensor product sorrys**~~ ✅ DONE (SchwartzTensorProduct.lean is sorry-free)
2. ~~**Field operator well-definedness**~~ ✅ DONE (adjoint relation → preserves null → well-defined)
3. ~~**GNS construction**~~ ✅ DONE (GNSConstruction.lean is sorry-free)
4. ~~**Jost lemma**~~ ✅ DONE (AnalyticContinuation.lean:545-640, fully proven)
5. ~~**1D edge-of-the-wedge**~~ ✅ DONE (EdgeOfWedge.lean, Morera + Cauchy-Goursat)
6. ~~**Euclidean point geometry**~~ ✅ DONE (euclidean_ordered_in_forwardTube, euclidean_distinct_in_permutedTube)
7. ~~**R→E top-level wiring**~~ ✅ DONE (wightman_to_os_full proven)
8. **edge_of_the_wedge** (multi-D, Bogoliubov's theorem) ← NEXT
9. **bargmann_hall_wightman** (BHW, depends on 8)
10. **constructedSchwinger_* theorems** (E0,E1,E2,E4 independent; E3 depends on 9)
11. **E→R analytic continuation chain** (OS II §IV-V, independent of 8-10)
12. **constructWightmanFunctions** (7 fields, depend on 9 + 11)
13. **Main reconstruction theorems** (Reconstruction.lean, wiring)

### What Does NOT Block Reconstruction

- Nuclear operator properties (NuclearOperator.lean)
- Nuclear space closure properties (NuclearSpace.lean)
- Schwartz nuclearity (SchwartzNuclear.lean)
- Bochner-Minlos theorems (BochnerMinlos.lean)
- Free field measure (EuclideanMeasure.lean)

These are needed for *constructive QFT* (building concrete examples of Schwinger functions)
but not for the OS reconstruction theorems themselves.

## Sorry Census (25 on critical path)

### SeparatelyAnalytic.lean — 2 sorrys (complex analysis infrastructure)

| # | Line | Theorem | Description | Blocked by |
|---|------|---------|-------------|------------|
| 0a | 72 | `differentiableOn_cauchyIntegral_param` | Cauchy integral with holomorphic parameter | — |
| 0b1 | 95 | `continuousAt_deriv_of_continuousOn` | z-derivative continuous in x (Cauchy integral) | — |

**Note**: `osgood_lemma_prod` is PROVEN using #0b1 and ~~#0b2~~ (2026-02-13).
`osgood_lemma` (Fin m → ℂ version) is PROVEN by induction using `osgood_lemma_prod`.
`holomorphic_extension_across_real` and `tube_domain_gluing` are PROVEN using `osgood_lemma`.
`uniform_bound_near_point` ✅ PROVEN (2026-02-14) — compactness + finite subcover.
`taylor_remainder_bound` ✅ PROVEN (2026-02-14) — combines helpers, no own sorry.
`taylor_remainder_single` ✅ PROVEN (2026-02-14) — all 6 decomposed helpers sorry-free.

### AnalyticContinuation.lean — 2 sorrys

| # | Line | Theorem | Description | Blocked by |
|---|------|---------|-------------|------------|
| 1 | 479 | `edge_of_the_wedge` | Multi-D edge-of-wedge (Bogoliubov) | #0b (Osgood) |
| 2 | 530 | `bargmann_hall_wightman` | BHW: extend to permuted extended tube | #1 |

### WickRotation.lean — 17 sorrys

**R→E direction (constructedSchwinger_*):**

| # | Line | Theorem | Description | Blocked by |
|---|------|---------|-------------|------------|
| 3 | 112 | `constructedSchwinger_tempered` | E0: temperedness | — |
| 4 | 126 | `constructedSchwinger_euclidean_covariant` | E1: Euclidean covariance | — |
| 5 | 142 | `constructedSchwinger_reflection_positive` | E2: reflection positivity | — |
| 6 | 155 | `constructedSchwinger_symmetric` | E3: permutation symmetry | #2 (BHW) |
| 7 | 171 | `constructedSchwinger_cluster` | E4: cluster property | — |

**E→R analytic continuation chain:**

| # | Line | Theorem | Description | Blocked by |
|---|------|---------|-------------|------------|
| 8 | 249 | `inductive_analytic_continuation` | OS II Thm 4.1: C_k^(r) → C_k^(r+1) | — |
| 9 | 262 | `full_analytic_continuation` | Iterate to reach forward tube | #8 |
| 10 | 287 | `boundary_values_tempered` | E0' ⟹ tempered boundary values | #9 |

**constructWightmanFunctions fields:**

| # | Line | Field | Description | Blocked by |
|---|------|-------|-------------|------------|
| 11 | 301 | `normalized` | W₀ from S₀ = 1 | #10 |
| 12 | 305 | `translation_invariant` | From E1 | #10 |
| 13 | 310 | `lorentz_covariant` | From E1 via BHW | #2, #10 |
| 14 | 318 | `spectrum_condition` | Distributional boundary limit | #10 |
| 15 | 321 | `locally_commutative` | From E3 + edge-of-wedge | #1, #10 |
| 16 | 324 | `positive_definite` | From E2 | #10 |
| 17 | 327 | `hermitian` | Reality of Schwinger functions | #10 |

**E→R bridge:**

| # | Line | Theorem | Description | Blocked by |
|---|------|---------|-------------|------------|
| 18 | 415 | `os_to_wightman_full` | Wire IsWickRotationPair | #11-17 |

### Reconstruction.lean — 4 sorrys

| # | Line | Theorem | Description | Blocked by |
|---|------|---------|-------------|------------|
| 19 | 1043 | `wightman_reconstruction` | GNS → WightmanQFT | GNS infra (done) |
| 20 | 1058 | `wightman_uniqueness` | Uniqueness up to unitary equivalence | #19 |
| 21 | 1239 | `wightman_to_os` | Wire to wightman_to_os_full | wightman_to_os_full (done) |
| 22 | 1269 | `os_to_wightman` | Wire to os_to_wightman_full | #18 |

### GNSConstruction.lean — 0 sorrys ✅

(Previously listed as having sorrys — verified sorry-free on 2026-02-13)

## Dependency Graph

```
SeparatelyAnalytic.lean (3 sorrys — leaf nodes, no dependencies)
│
│  continuousAt_deriv_of_continuousOn ──┐
│  taylor_remainder_bound ──────────────┼──▶ osgood_lemma_prod (PROVEN)
│  differentiableOn_cauchyIntegral_param│        │
│                                               │
│                                               ▼
│                              osgood_lemma (PROVEN, by induction)
│                                               │
├───────────────────────────────────────────────┘
│
▼
AnalyticContinuation.lean (2 sorrys)
│
│  edge_of_the_wedge ◀── osgood_lemma (for multi-D gluing)
│        │
│        ▼
│  bargmann_hall_wightman ◀── edge_of_the_wedge + jost_lemma (PROVEN)
│        │
├────────┤
│        │
▼        ▼
WickRotation.lean (17 sorrys)
│
│  ┌─── R→E DIRECTION (5 sorrys) ────────────────────────────────┐
│  │                                                               │
│  │  constructedSchwinger_tempered (E0)         ← independent     │
│  │  constructedSchwinger_euclidean_covariant (E1) ← independent  │
│  │  constructedSchwinger_reflection_positive (E2) ← independent  │
│  │  constructedSchwinger_symmetric (E3)  ◀── bargmann_hall_wightman
│  │  constructedSchwinger_cluster (E4)          ← independent     │
│  │         │                                                     │
│  │         ▼                                                     │
│  │  wightman_to_os_full (PROVEN, wires E0-E4)                   │
│  └───────────────────────────────────────────────────────────────┘
│
│  ┌─── E→R DIRECTION (12 sorrys) ───────────────────────────────┐
│  │                                                               │
│  │  inductive_analytic_continuation ◀── E0' (linear growth)     │
│  │         │                                                     │
│  │         ▼                                                     │
│  │  full_analytic_continuation ◀── iterate inductive step        │
│  │         │                                                     │
│  │         ▼                                                     │
│  │  boundary_values_tempered ◀── E0' controls distribution order │
│  │         │                                                     │
│  │         ▼                                                     │
│  │  constructWightmanFunctions (7 field sorrys):                 │
│  │    .normalized           ← boundary_values_tempered           │
│  │    .translation_invariant ← E1                                │
│  │    .lorentz_covariant    ← E1 + bargmann_hall_wightman        │
│  │    .spectrum_condition   ← full_analytic_continuation         │
│  │    .locally_commutative  ← E3 + edge_of_the_wedge            │
│  │    .positive_definite    ← E2                                 │
│  │    .hermitian            ← reality + analytic continuation    │
│  │         │                                                     │
│  │         ▼                                                     │
│  │  os_to_wightman_full (wires everything)                      │
│  └───────────────────────────────────────────────────────────────┘
│
▼
Reconstruction.lean (4 sorrys — wiring layer)
│
│  wightman_reconstruction  ◀── GNSConstruction (PROVEN infrastructure)
│  wightman_uniqueness      ◀── standard GNS uniqueness argument
│  wightman_to_os           ◀── wightman_to_os_full (PROVEN)
│  os_to_wightman           ◀── os_to_wightman_full
```

## Dependency Tiers (leaves first)

### Tier 0: Leaf sorrys (no sorry dependencies, can be attacked now)

| # | File | Line | Theorem | Proof strategy |
|---|------|------|---------|----------------|
| 0a | SeparatelyAnalytic | 72 | `differentiableOn_cauchyIntegral_param` | Cauchy integral formula for parametric holomorphicity |
| 0b1 | SeparatelyAnalytic | 95 | `continuousAt_deriv_of_continuousOn` | Cauchy integral + continuous_of_dominated |
| 0b2 | SeparatelyAnalytic | 117 | `taylor_remainder_bound` | Power series + Cauchy estimates + geometric series |
| 3 | WickRotation | 112 | `constructedSchwinger_tempered` (E0) | R0 + Schwartz integrability |
| 4 | WickRotation | 126 | `constructedSchwinger_euclidean_covariant` (E1) | Change of variables + translation invariance |
| 5 | WickRotation | 142 | `constructedSchwinger_reflection_positive` (E2) | Borchers involution + R2 |
| 7 | WickRotation | 171 | `constructedSchwinger_cluster` (E4) | R4 via analytic continuation |
| 8 | WickRotation | 249 | `inductive_analytic_continuation` | OS II Thm 4.1: Laplace transform + E0' |
| 19 | Reconstruction | 1043 | `wightman_reconstruction` | Wire GNS (all infrastructure proven) |
| 20 | Reconstruction | 1058 | `wightman_uniqueness` | Standard GNS uniqueness |

### Tier 1: Depend on Tier 0

| # | Theorem | Depends on |
|---|---------|------------|
| 1 | `edge_of_the_wedge` | #0a–0b2 (via osgood_lemma) |
| 9 | `full_analytic_continuation` | #8 (iterate) |
| 21 | `wightman_to_os` | Wire to wightman_to_os_full (proven), needs #3–7 |

### Tier 2: Depend on Tier 1

| # | Theorem | Depends on |
|---|---------|------------|
| 2 | `bargmann_hall_wightman` | #1 (edge_of_the_wedge) |
| 10 | `boundary_values_tempered` | #9 (full_analytic_continuation) + E0' |
| 6 | `constructedSchwinger_symmetric` (E3) | #2 (BHW) |

### Tier 3: Depend on Tier 2

| # | Theorem | Depends on |
|---|---------|------------|
| 11–17 | `constructWightmanFunctions` fields | #10, and some need #1 or #2 |

### Tier 4: Final wiring

| # | Theorem | Depends on |
|---|---------|------------|
| 18 | `os_to_wightman_full` | #11–17 |
| 22 | `os_to_wightman` | #18 |

### Two Critical Bottlenecks

1. **`edge_of_the_wedge` (#1)** — blocks BHW, which blocks E3 (R→E) and
   local commutativity + Lorentz covariance (E→R). Deepest mathematical blocker.
2. **`boundary_values_tempered` (#10)** — blocks all 7 constructWightmanFunctions
   fields. Depends on the analytic continuation chain + E0'.

## Parallel Work Streams (for collaboration)

These groups are **independent** and can be worked on simultaneously:

- **Group A** (complex analysis): SeparatelyAnalytic #0a–0b2 → edge_of_the_wedge → BHW
- **Group B** (analytic continuation): inductive_analytic_continuation → full → boundary_values_tempered
- **Group C** (R→E properties): E0, E1, E2, E4 (mutually independent, no sorry dependencies)
- **Group D** (GNS wiring): wightman_reconstruction + wightman_uniqueness

Groups A and B converge at Tier 3 (constructWightmanFunctions fields need both BHW and boundary values).

## Execution Plan

### Phase 0: Osgood's Lemma Helpers (unblocks Phase 1) ← CURRENT
- ~~**osgood_lemma_prod**~~: ✅ PROVEN (2026-02-13) via direct Fréchet derivative construction
  - Decomposes remainder into Taylor (T₁) + derivative variation (T₂) + Fréchet (T₃)
  - Uses `hasFDerivAt_iff_isLittleO_nhds_zero`, `ContinuousLinearMap.coprod`
  - Depends on two sorry'd helper lemmas:
- **continuousAt_deriv_of_continuousOn** (#0b1): z-derivative varies continuously in x ← NEXT
  - Proof idea: Cauchy integral formula gives `deriv_z f(z₀,x) = (2πi)⁻¹ ∮ f(ζ,x)/(ζ-z₀)² dζ`
  - Integrand is continuous in x (from joint continuity), uniformly bounded on circle
  - Apply `continuous_of_dominated` to get continuity of the integral in x
- ~~**taylor_remainder_single** (#0b2)~~: ✅ PROVEN (2026-02-14) — all helpers sorry-free
  - `uniform_bound_near_point` ✅ PROVEN: compact slice + finite subcover
  - `taylor_remainder_bound` ✅ PROVEN: combines helpers
  - `taylor_remainder_single` ✅ PROVEN: delegates to decomposed helpers
  - `cauchyPowerSeries_one_eq_deriv_mul` ✅ PROVEN: `p 1 (h) = deriv g z₀ * h`
  - `tsum_geometric_tail_le` ✅ PROVEN: `Σ M·r^(n+2) ≤ 2M·r²`
  - `cauchyPowerSeries_coeff_bound` ✅ PROVEN: Cauchy estimates via integral bound
  - `taylor_remainder_eq_tsum` ✅ PROVEN: `hasSum_nat_add_iff'` decomposition
  - `taylor_tail_summable` ✅ PROVEN: tail of convergent power series
  - `taylor_tail_norm_le` ✅ PROVEN: `norm_tsum_le_tsum_norm` + geometric bound
  - Note: `tsum_le_tsum` now uses SummationFilter; resolved via `Summable.tsum_le_tsum`
- **differentiableOn_cauchyIntegral_param** (#0a): May follow from osgood_lemma_prod or prove independently

### Phase 1: Deep Complex Analysis (unblocks both R→E and E→R)
- **edge_of_the_wedge** (#1): Multi-D version via induction on dimension using 1D base case
  - 1D proven in `Helpers/EdgeOfWedge.lean` using Morera's theorem
  - Multi-D: fix (m-1) variables, apply 1D, then glue via Osgood lemma
  - Key Mathlib: `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`
- **bargmann_hall_wightman** (#2): Extend F from forward tube to permuted extended tube
  - Step 1: Real Lorentz invariance → complex Lorentz invariance (identity theorem)
  - Step 2: At Jost points, use local commutativity for adjacent transposition agreement
  - Step 3: Edge-of-wedge glues adjacent permuted tubes
  - Step 4: Iterate over transpositions to cover all permutations

### Phase 2: R→E constructedSchwinger theorems (#3-7)
- `constructedSchwinger_euclidean_covariant` (#4): Change of variables + translation invariance
- `constructedSchwinger_tempered` (#3): Polynomial growth of W_analytic × Schwartz decay
- `constructedSchwinger_reflection_positive` (#5): Borchers involution + Wightman positivity
- `constructedSchwinger_symmetric` (#6): BHW permutation symmetry (needs #2)
- `constructedSchwinger_cluster` (#7): Propagate Wightman cluster through Wick rotation

### Phase 3: E→R Analytic Continuation Chain (#8-10)
- `inductive_analytic_continuation` (#8): OS II Thm 4.1, Laplace transform + E0' + Hartogs
- `full_analytic_continuation` (#9): Iterate #8 for r = 0,...,d
- `boundary_values_tempered` (#10): E0' growth estimates preserved

### Phase 4: constructWightmanFunctions (#11-17)
- Derive each Wightman axiom from the corresponding OS axiom via analytic continuation
- Depends on Phase 3 completion

### Phase 5: Wiring and Main Theorems (#18-22)
- `os_to_wightman_full` (#18): Wire constructWightmanFunctions into IsWickRotationPair
- `wightman_reconstruction` (#19): GNS → WightmanQFT (uses proven GNS infrastructure)
- `wightman_uniqueness` (#20): Standard GNS uniqueness argument
- `wightman_to_os` (#21): Wire to wightman_to_os_full (already proven)
- `os_to_wightman` (#22): Wire to os_to_wightman_full

## Status Overview

| File | Sorrys | Status |
|------|--------|--------|
| Basic.lean | 0 | ✅ Complete |
| Groups/Lorentz.lean | 0 | ✅ Complete |
| Groups/Poincare.lean | 0 | ✅ Complete |
| Spacetime/Metric.lean | 0 | ✅ Complete |
| Spacetime/MinkowskiGeometry.lean | 0 | ✅ Complete |
| SchwartzTensorProduct.lean | 0 | ✅ Complete |
| WightmanAxioms.lean | 2 | Not blocking reconstruction |
| OperatorDistribution.lean | 1 | Not blocking reconstruction |
| Reconstruction/GNSConstruction.lean | 0 | ✅ Complete |
| Reconstruction/Helpers/EdgeOfWedge.lean | 0 | ✅ Complete (1D edge-of-wedge) |
| **Reconstruction/Helpers/SeparatelyAnalytic.lean** | **2** | Cauchy param + deriv continuity |
| **Reconstruction/AnalyticContinuation.lean** | **2** | edge_of_wedge + BHW |
| **Reconstruction/WickRotation.lean** | **17** | OS↔Wightman bridge |
| **Reconstruction.lean** | **4** | Core theorems + wiring |
| NuclearSpaces/NuclearOperator.lean | 0 | ✅ Complete (deferred, not blocking) |
| NuclearSpaces/NuclearSpace.lean | 2 | Deferred |
| NuclearSpaces/BochnerMinlos.lean | 3 | Deferred |
| NuclearSpaces/SchwartzNuclear.lean | 4 | Deferred |
| NuclearSpaces/EuclideanMeasure.lean | 1 | Deferred |
| **Critical path total** | **25** | |

## Proven Infrastructure (sorry-free)

### GNSConstruction.lean
- `WightmanInnerProduct_hermitian` — ⟨F,G⟩ = conj(⟨G,F⟩)
- `null_inner_product_zero` — ⟨X,X⟩.re=0 → ⟨X,Y⟩=0
- `PreHilbertSpace.innerProduct` — Well-defined on quotient
- `fieldOperator` — φ(f) descends to quotient (full chain: adjoint → preserves null → well-defined)
- `gns_reproduces_wightman` — ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = Wₙ(f₁⊗···⊗fₙ)
- `translation_preserves_inner` — WIP(F', G') = WIP(F, G)

### AnalyticContinuation.lean
- `ComplexLorentzGroup.ofReal`, `ComplexLorentzGroup.ofEuclidean` — embeddings
- `ForwardTube_subset_ComplexExtended`, `ComplexExtended_subset_Permuted`
- `euclidean_ordered_in_forwardTube` — ordered Euclidean points ∈ T_n
- `euclidean_distinct_in_permutedTube` — distinct Euclidean ∈ T''_n
- `jost_lemma` — Jost points have spacelike differences
- `schwinger_euclidean_invariant`, `schwinger_permutation_symmetric`
- `schwingerFromWightman_analytic`, `differentiable_complexWickRotate`

### EdgeOfWedge.lean
- `edge_of_the_wedge_1d` — 1D edge-of-wedge via Morera's theorem
- `identity_theorem_connected` — analytic identity theorem
- `holomorphic_translation_invariant`

### WickRotation.lean
- `wightman_to_os_full` — R→E top-level wiring (proven)

## Architecture

```
Layer 0 (DONE): Metric, Lorentz, Poincare, Basic, MinkowskiGeometry — 0 sorrys
    ↓
OperatorDistribution.lean ──> WightmanAxioms.lean
    ↓                              ↓
    └──────────> Reconstruction.lean ←── SchwartzTensorProduct.lean
                     ↓
              Reconstruction/AnalyticContinuation.lean  (tube domains, BHW)
              Reconstruction/GNSConstruction.lean       (✅ sorry-free)
              Reconstruction/WickRotation.lean          (OS↔Wightman bridge)
              Reconstruction/Helpers/EdgeOfWedge.lean   (✅ sorry-free, 1D)
```

Nuclear spaces / Minlos are a SEPARATE development line for constructive QFT.

## Key Mathematical References

- **OS I**: "Reconstruction theorem I.pdf" — Theorem R→E (§5), Theorem E→R (§4)
  - Note: Lemma 8.8 has a gap (fixed in OS II)
- **OS II**: "reconstruction theorem II.pdf" — Linear growth E0' (§IV.1),
  analytic continuation (§V), temperedness estimates (§VI)
- **Streater-Wightman**: "PCT, Spin and Statistics, and All That" — Chapter 3
- **Glimm-Jaffe**: "Quantum Physics" — Chapter 19 (reconstruction)
