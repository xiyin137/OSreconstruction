# Sorry Analysis: OS Reconstruction Bridge Theorems

> Status note (2026-02-27): This analysis is stale and kept for history.
> Canonical current plan and counts: `docs/development_plan_systematic.md`.

*Updated 2026-02-20. Covers WickRotation.lean (18 sorrys), Reconstruction.lean (4 sorrys), and axioms.*

## Current Status

### Fully proved (sorry-free)
- `SCV/Analyticity.lean` — multi-variable power series from Cauchy integrals
- `SCV/TubeDomainExtension.lean` — edge-of-the-wedge theorem
- `SCV/MoebiusMap.lean` — Möbius maps
- `SCV/EOWMultiDim.lean` — multi-dim EOW helpers
- `SCV/IteratedCauchyIntegral.lean` — Cauchy integral on polydiscs
- `SCV/IdentityTheorem.lean` — identity theorem for SCV (proved via `differentiableOn_analyticAt`)
- `Reconstruction/AnalyticContinuation.lean` — BHW bridge, Euclidean invariance proofs
- `Reconstruction/Helpers/SeparatelyAnalytic.lean` — Osgood lemma chain
- `Reconstruction/Helpers/EdgeOfWedge.lean` — 1D edge-of-the-wedge

### Axioms (taken on faith)

#### In AnalyticContinuation.lean
| Axiom | Line | Notes |
|-------|------|-------|
| `bargmann_hall_wightman` | ~788 | Requires connectedness of SO⁺(1,d;ℂ) and identity theorem on complex manifolds |
| ~~`edge_of_the_wedge`~~ | ~730 | **NOW PROVED**: replaced axiom with theorem using `edge_of_the_wedge_theorem` from SCV/TubeDomainExtension.lean |

#### In SCV/TubeDistributions.lean (NEW)
| Axiom | Notes |
|-------|-------|
| `continuous_boundary_tube` | Vladimirov §26.2: holomorphic on tube domain with distributional BVs → continuous at real boundary |
| `distributional_uniqueness_tube` | Vladimirov §26.3: same distributional BVs → equal on tube |
| `polynomial_growth_tube` | S-W Thm 2-6: tempered distributional BVs → polynomial growth |

#### In WickRotation.lean (NEW — forward-tube specializations)
| Axiom | Notes |
|-------|-------|
| `continuous_boundary_forwardTube` | Specialization of `continuous_boundary_tube` to `ForwardTube d n` |
| `distributional_uniqueness_forwardTube` | Specialization of `distributional_uniqueness_tube` to `ForwardTube d n` |

### Recently closed sorrys
- `IdentityTheorem.lean`: `analyticOnNhd_of_finiteDimensional` — proved using `SCV.differentiableOn_analyticAt`
- `WickRotation.lean`: `W_analytic_continuous_boundary` — proved using `continuous_boundary_forwardTube` axiom

---

## R→E Direction (Wightman → Schwinger): 9 sorrys

### Group A: BHW Hypotheses (2 sorrys remaining, 1 closed)

#### A1. `W_analytic_lorentz_on_tube` (line ~152) — SORRY

**Goal**: `W_analytic(Λz) = W_analytic(z)` for restricted Lorentz Λ and z ∈ ForwardTube.

**Proof sketch**: Both `z ↦ W_analytic(z)` and `z ↦ W_analytic(Λz)` are holomorphic on ForwardTube with the same distributional boundary values (by `Wfn.lorentz_covariant`). Apply `distributional_uniqueness_forwardTube`.

**Remaining work**: Need to show (1) `z → W_analytic(Λz)` is holomorphic on ForwardTube (restricted Lorentz preserves ForwardTube), and (2) distributional BVs agree (from `Wfn.lorentz_covariant` + change of variables). Both are formalizable but require ~30 lines of boilerplate each.

#### A2. `W_analytic_continuous_boundary` — PROVED ✓

Proved using `continuous_boundary_forwardTube` axiom with `Wfn.W n` as the boundary distribution.

#### A3. `W_analytic_local_commutativity` (line ~183) — SORRY

**Goal**: At real spacelike-separated points, swapping consecutive arguments doesn't change W_analytic.

**Proof sketch**: By A2, W_analytic extends continuously to boundary. The boundary value agrees with W_n (from `spectrum_condition`). By `Wfn.locally_commutative`, W_n(swap) = W_n at spacelike points. Hence W_analytic(swap(x)) = W_analytic(x).

**Remaining work**: Connecting distributional BVs to pointwise continuous extension values. Needs ~20 lines.

### Group B: F_ext Pointwise Invariance (3 sorrys)

#### B1. `F_ext_translation_invariant` (line ~273)
#### B2. `F_ext_rotation_invariant` (line ~315)
#### B3. `F_ext_permutation_invariant` (line ~423)

All three follow the same pattern: use proved results from AnalyticContinuation.lean (`schwinger_euclidean_invariant`, `schwinger_permutation_symmetric`) at distinct-positive-time Euclidean points, extend to all points by density + analyticity.

**Blocker**: A density/full-measure lemma showing distinct-time configurations are generic in NPointDomain.

### Group C: OS Axiom Verification (4 sorrys)

#### C1. `constructedSchwinger_tempered` — E0 (line ~253)
Needs polynomial growth bounds. Enabler: `polynomial_growth_tube` / `polynomial_growth_forwardTube`.

#### C2. `constructedSchwinger_reflection_positive` — E2 (line ~409)
Deep calculation connecting OS inner product to Wightman positivity (R2).

#### C3. `W_analytic_cluster_integral` — E4 support (line ~491)
Cluster decomposition + dominated convergence.

#### C4. Boundary values in `wightman_to_os_full` (line ~755)
Sign convention issue. See `docs/sign_convention_analysis.md`.

---

## E→R Direction (Schwinger → Wightman): 9 sorrys

### Group D: Inductive Analytic Continuation (3 sorrys)
- D1. `inductive_analytic_continuation` (line ~601) — OS II Theorem 4.1
- D2. `full_analytic_continuation` (line ~611) — d+1 steps of D1
- D3. `boundary_values_tempered` (line ~664) — growth estimates from E0'

### Group E: Wightman Axiom Verification (6 sorrys)
| Field | Proof from | Difficulty |
|-------|-----------|------------|
| `normalized` | S_0 = 1 → W_0 = evaluation | Easy (once D2 done) |
| `translation_invariant` | E1 restricted to translations | Medium |
| `lorentz_covariant` | E1 via BHW | Hard |
| `locally_commutative` | E3 + edge-of-the-wedge | Hard |
| `positive_definite` | E2 (reflection positivity) | Hard |
| `hermitian` | Reality of Schwinger functions | Medium |
| `os_to_wightman_full` | Wire everything | Depends on D+E |

---

## Dependency Graph

```
continuous_boundary_forwardTube (axiom)
    │
    ├── A2 (continuous boundary) ← PROVED ✓
    ├── A3 (local commutativity) ← via A2 + locally_commutative (~20 LOC)
    └── A1 (Lorentz on tube) ← via distributional_uniqueness_forwardTube (~60 LOC)

distributional_uniqueness_forwardTube (axiom)
    │
    └── A1 (Lorentz on tube) ← + holomorphy of W_analytic ∘ Λ + BV agreement

polynomial_growth_tube (axiom)
    │
    └── C1 (E0 temperedness) ← growth bounds + Schwartz decay

Sign fix (x - iεη → x + iεη)
    │
    └── C4 (boundary values in wightman_to_os_full)

Still blocked (deeper arguments needed):
    B1-B3 (F_ext invariance) ← density/full-measure lemma
    C2 (E2 reflection positivity) ← Wightman positivity calculation
    C3 (E4 cluster) ← cluster decomposition + dominated convergence
    D1-D3 (E→R inductive continuation) ← OS II Laplace transform theory
    E1-E6 (Wightman axiom verification) ← depends on D1-D3
```

## Summary

| Category | Total Sorrys | Closed | Remaining |
|----------|-------------|--------|-----------|
| BHW hypotheses (A1-A3) | 3 | 1 (A2) | 2 |
| F_ext invariance (B1-B3) | 3 | 0 | 3 |
| OS axiom verification (C1-C4) | 4 | 0 | 4 |
| E→R continuation (D1-D3) | 3 | 0 | 3 |
| Wightman axioms (E1-E6) | 6 | 0 | 6 |
| `os_to_wightman_full` | 1 | 0 | 1 |
| **Total WickRotation** | **20** | **2** | **18** |
| **Reconstruction.lean** | **4** | **0** | **4** |

With the 5 new axioms (3 general tube domain + 2 forward tube) and continuous boundary proved, the path forward is:
- A1, A3: ~80 lines of proof connecting axioms to Wightman axiom hypotheses
- B1-B3: need density/full-measure lemma (~50 lines)
- C1: need polynomial growth bounds wired through (~30 lines)
- C4: sign convention fix (~5 line change, but affects all downstream)
- C2, C3, D1-D3, E1-E6: deeper mathematical arguments needed
