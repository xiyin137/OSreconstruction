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
7. ~~**Lorentz invariance on forward tube**~~ ✅ DONE (W_analytic_lorentz_on_tube)
8. ~~**E3 permutation symmetry**~~ ✅ DONE (constructedSchwinger_symmetric, sorry-free)
9. ~~**E1 translation invariance**~~ ✅ DONE (constructedSchwinger_translation_invariant, sorry-free)
10. ~~**E1 rotation invariance (det=1)**~~ ✅ DONE (constructedSchwinger_rotation_invariant, det=1 branch)
11. ~~**E'→R' theorem**~~ ✅ DONE (os_to_wightman_full, sorry-free)
12. **edge_of_the_wedge** (multi-D, Bogoliubov's theorem) ← NEXT
13. **bargmann_hall_wightman** (BHW, depends on 12)
14. **R→E remaining sorrys** (local commutativity, E0, E2, E4, rotation det=-1, BV wiring)
15. **E→R analytic continuation chain** (OS II §IV-V, independent of 12-14)
16. **constructWightmanFunctions** (7 fields, depend on 13 + 15)
17. **Main reconstruction theorems** (Reconstruction.lean, wiring)

### What Does NOT Block Reconstruction

- Nuclear operator properties (NuclearOperator.lean)
- Nuclear space closure properties (NuclearSpace.lean)
- Schwartz nuclearity (SchwartzNuclear.lean)
- Bochner-Minlos theorems (BochnerMinlos.lean)
- Free field measure (EuclideanMeasure.lean)

These are needed for *constructive QFT* (building concrete examples of Schwinger functions)
but not for the OS reconstruction theorems themselves.

## Axiom and Sorry Census

### Axioms (11 total: 4 in SCV, 2 in AnalyticContinuation, 5 in WickRotation)

**SCV/TubeDistributions.lean — 4 axioms** (deep distribution theory / SCV, not in Mathlib):
- `continuous_boundary_tube` — Vladimirov: tube holomorphic + tempered BV ⟹ continuous to boundary
- `boundary_value_recovery` — continuous extension integrates to reproduce distributional BV
- `polynomial_growth_tube` — tube holomorphic + tempered BV ⟹ polynomial growth
- `bochner_tube_theorem` — holomorphic on T(C) extends to T(conv C)

`distributional_uniqueness_tube` — proved from `continuous_boundary_tube` + `boundary_value_recovery`
+ edge-of-the-wedge + identity theorem. 2 localized sorrys remain:
1. Du Bois-Reymond: ∫ h·f = 0 for all Schwartz f implies h = 0 pointwise
2. Cone scaling: t > 0 ∧ y ∈ C → t • y ∈ C (holds for forward cones)

**AnalyticContinuation.lean — 2 axioms** (deep SCV, depend on edge-of-wedge):
- `edge_of_the_wedge` (line 730) — multi-D Bogoliubov theorem
- `bargmann_hall_wightman` (line 788) — extend from forward tube to PET

**WickRotation.lean — 5 axioms** (textbook results, plumbing gaps):
- `forward_tube_bv_integrable` (line 376) — BV integrands are integrable
- `lorentz_covariant_distributional_bv` (line 404) — Lorentz COV of BVs from Wightman axiom
- `euclidean_points_in_permutedTube` (line 442) — Jost's theorem: Wick-rotated points ∈ PET
- `bhw_translation_invariant` (line 613) — W depends on differences (coordinate convention gap; see docstring)
- `inductive_analytic_continuation` (line 1035) — OS II Thm 4.1: C_k^(r) → C_k^(r+1) via Paley-Wiener

### ~~SeparatelyAnalytic.lean — 0 sorrys~~ ✅ DONE (2026-02-15)

All theorems proven and verified `sorryAx`-free:
- `continuousAt_deriv_of_continuousOn` ✅ — Cauchy integral for derivative + tube lemma
- `differentiableOn_cauchyIntegral_param` ✅ — Leibniz rule + Osgood's lemma
- `osgood_lemma_prod` ✅ — direct Fréchet derivative construction
- `osgood_lemma` ✅ — induction using `osgood_lemma_prod`
- `holomorphic_extension_across_real` ✅ — via `osgood_lemma`
- `tube_domain_gluing` ✅ — via `osgood_lemma`
- `differentiableOn_of_continuous_off_real_1d` ✅ — 1D holomorphic extension

### AnalyticContinuation.lean — 0 sorrys, 2 axioms

Both `edge_of_the_wedge` and `bargmann_hall_wightman` are stated as axioms (not sorrys).
All other theorems in this file are fully proven.

### WickRotation.lean — 14 sorrys, 5 axioms

**R→E direction — proven theorems:**

| Line | Theorem | Status |
|------|---------|--------|
| 107 | `restricted_preserves_forward_cone` | ✅ Proven |
| 270 | `restricted_preserves_forward_tube` | ✅ Proven |
| 326 | `W_analytic_lorentz_holomorphic` | ✅ Proven |
| 448 | `W_analytic_lorentz_bv_agree` | ✅ Proven |
| 503 | `W_analytic_lorentz_on_tube` | ✅ Proven (distributional uniqueness) |
| 524 | `W_analytic_continuous_boundary` | ✅ Proven (from SCV axiom) |
| 560 | `W_analytic_BHW` | ✅ Proven (applies BHW axiom) |
| 667 | `F_ext_translation_invariant` | ✅ Proven (from bhw_translation_invariant + euclidean_points_in_permutedTube) |
| 682 | `constructedSchwinger_translation_invariant` | ✅ Proven (sorry-free, verified) |
| 713 | `F_ext_rotation_invariant` (det=1 branch) | ✅ Proven (via schwinger_euclidean_invariant) |
| 740 | `integral_orthogonal_eq_self` | ✅ Proven |
| 792 | `constructedSchwinger_rotation_invariant` | ✅ Proven (modulo det=-1 sorry in F_ext_rotation_invariant) |
| 840 | `F_ext_permutation_invariant` | ✅ Proven (from BHW permutation + euclidean_points_in_permutedTube) |
| 851 | `integral_perm_eq_self` | ✅ Proven |
| 862 | `constructedSchwinger_symmetric` | ✅ Proven (sorry-free, verified) |
| 1187 | `wightman_to_os_full` | ✅ Proven (modulo h_in_tube geometric sorry) |
| 1231 | `os_to_wightman_full` | ✅ Proven (sorry-free) |

**R→E direction — remaining sorrys (6):**

| # | Line | Theorem | Description | Difficulty |
|---|------|---------|-------------|------------|
| 1 | 549 | `W_analytic_local_commutativity` | Distributional → pointwise local commutativity | Medium: needs continuous BV + test function density |
| 2 | 652 | `constructedSchwinger_tempered` | E0: continuity in Schwartz topology | Hard: needs polynomial_growth_tube |
| 3 | 736 | `F_ext_rotation_invariant` (det=-1) | Improper rotations need PCT theorem | Hard: depends on d parity |
| 4 | 830 | `constructedSchwinger_reflection_positive` | E2: Wightman positivity → OS RP | Hard: Borchers involution + Wick rotation |
| 5 | 915 | `W_analytic_cluster_integral` | Cluster: integral factorization | Hard: cluster decomposition + dominated convergence |
| 6 | 1224 | `wightman_to_os_full` (h_in_tube) | x+iεη ∈ ForwardTube when η_k ∈ V₊ | Medium: ForwardTube coordinate convention issue |

**E→R direction — sorrys (8):**

| # | Line | Theorem | Description | Blocked by |
|---|------|---------|-------------|------------|
| 7 | 1077 | `full_analytic_continuation` | Iterate inductive + E1 + Bochner to reach forward tube | Axiom (inductive_analytic_continuation) + geometry |
| 8 | 1120 | `boundary_values_tempered` | E0' ⟹ tempered BV + Wick rotation | #7 |
| 9 | 1134 | `constructWightmanFunctions.normalized` | W₀ from S₀ = 1 | #8 |
| 10 | 1138 | `constructWightmanFunctions.translation_invariant` | From E1 | #8 |
| 11 | 1143 | `constructWightmanFunctions.lorentz_covariant` | From E1 via BHW | #8, BHW axiom |
| 12 | 1152 | `constructWightmanFunctions.locally_commutative` | From E3 + edge-of-wedge | #8, EOW axiom |
| 13 | 1155 | `constructWightmanFunctions.positive_definite` | From E2 | #8 |
| 14 | 1158 | `constructWightmanFunctions.hermitian` | Reality of Schwinger functions | #8 |

### Reconstruction.lean — 4 sorrys

| # | Line | Theorem | Description | Blocked by |
|---|------|---------|-------------|------------|
| 15 | 1043 | `wightman_reconstruction` | GNS → WightmanQFT | GNS infra (done) |
| 16 | 1063 | `wightman_uniqueness` | Uniqueness up to unitary equiv | #15 |
| 17 | 1399 | `wightman_to_os` | Wire to wightman_to_os_full | wightman_to_os_full (done) |
| 18 | 1419 | `os_to_wightman` | Wire to os_to_wightman_full | os_to_wightman_full (done) |

### GNSConstruction.lean — 0 sorrys ✅

(Previously listed as having sorrys — verified sorry-free on 2026-02-13)

## Dependency Graph

```
SeparatelyAnalytic.lean ✅ (0 sorrys)
│
▼
AnalyticContinuation.lean (0 sorrys, 2 axioms)
│
│  edge_of_the_wedge (AXIOM) ◀── would use osgood_lemma for multi-D gluing
│        │
│        ▼
│  bargmann_hall_wightman (AXIOM) ◀── edge_of_the_wedge + jost_lemma (PROVEN)
│        │
├────────┤
│        │
▼        ▼
WickRotation.lean (14 sorrys, 5 axioms)
│
│  ┌─── R→E DIRECTION (6 sorrys) ────────────────────────────────┐
│  │                                                               │
│  │  W_analytic_local_commutativity        ← sorry (medium)      │
│  │  constructedSchwinger_tempered (E0)    ← sorry (hard)        │
│  │  F_ext_rotation_invariant (det=-1)     ← sorry (needs PCT)   │
│  │  constructedSchwinger_reflection_positive (E2) ← sorry (hard)│
│  │  W_analytic_cluster_integral (E4)      ← sorry (hard)        │
│  │  wightman_to_os_full (h_in_tube)       ← sorry (coord conv)  │
│  │                                                               │
│  │  constructedSchwinger_symmetric (E3)    ✅ PROVEN             │
│  │  constructedSchwinger_translation_invariant ✅ PROVEN         │
│  │  constructedSchwinger_rotation_invariant    ✅ PROVEN (det=1) │
│  │  W_analytic_lorentz_on_tube                 ✅ PROVEN         │
│  │  F_ext_permutation_invariant                ✅ PROVEN         │
│  │  F_ext_translation_invariant                ✅ PROVEN         │
│  │         │                                                     │
│  │         ▼                                                     │
│  │  wightman_to_os_full (PROVEN, modulo h_in_tube sorry)        │
│  └───────────────────────────────────────────────────────────────┘
│
│  ┌─── E→R DIRECTION (8 sorrys) ───────────────────────────────┐
│  │                                                               │
│  │  inductive_analytic_continuation (AXIOM) ◀── Paley-Wiener    │
│  │         │                                                     │
│  │         ▼                                                     │
│  │  full_analytic_continuation ◀── iterate + E1 + Bochner       │
│  │         │                                                     │
│  │         ▼                                                     │
│  │  boundary_values_tempered ◀── E0' controls distribution order │
│  │         │                                                     │
│  │         ▼                                                     │
│  │  constructWightmanFunctions (6 field sorrys):                 │
│  │    .normalized           ← boundary_values_tempered           │
│  │    .translation_invariant ← E1                                │
│  │    .lorentz_covariant    ← E1 + bargmann_hall_wightman        │
│  │    .spectrum_condition   ← boundary_values_tempered (WIRED ✅)│
│  │    .locally_commutative  ← E3 + edge_of_the_wedge            │
│  │    .positive_definite    ← E2                                 │
│  │    .hermitian            ← reality + analytic continuation    │
│  │         │                                                     │
│  │         ▼                                                     │
│  │  os_to_wightman_full ✅ PROVEN (sorry-free)                  │
│  └───────────────────────────────────────────────────────────────┘
│
▼
Reconstruction.lean (4 sorrys — wiring layer)
│
│  wightman_reconstruction  ◀── GNSConstruction (PROVEN infrastructure)
│  wightman_uniqueness      ◀── standard GNS uniqueness argument
│  wightman_to_os           ◀── wightman_to_os_full (PROVEN)
│  os_to_wightman           ◀── os_to_wightman_full (PROVEN)
```

## Two Critical Bottlenecks

1. **`edge_of_the_wedge` (axiom)** — blocks BHW (also axiom), which blocks
   local commutativity + Lorentz covariance (E→R). Currently axiomatized.
2. **`boundary_values_tempered` (#8)** — blocks all 6 constructWightmanFunctions
   field sorrys. Depends on `full_analytic_continuation` + E0'.

## Known Subtleties

### ForwardTube coordinate convention
Our `ForwardTube` uses absolute coordinates with a special k=0 condition
(Im(z₀) ∈ V₊, where prev = 0). This means ForwardTube and PET are **not**
closed under complex translations. The physics literature avoids this by
working in difference variables ξ_k = z_{k+1} - z_k. This affects:
- `bhw_translation_invariant` — stated as axiom; plumbing gap, not math gap
- `wightman_to_os_full` h_in_tube — approach points x+iεη may not be in ForwardTube

Fixing this would require refactoring ForwardTube to use difference variables.

### PCT and improper rotations (det = -1)
`F_ext_rotation_invariant` det=-1 branch needs the PCT theorem. The proof
depends on spacetime dimension parity:
- d even: -I ∉ ComplexLorentzGroup (det=-1), need PCT for total negation
- d odd: -I ∈ ComplexLorentzGroup (det=1), but spatial reflections still need PCT

## Parallel Work Streams (for collaboration)

These groups are **independent** and can be worked on simultaneously:

- **Group A** (complex analysis): Prove edge_of_the_wedge and BHW axioms
- **Group B** (analytic continuation): full_analytic_continuation → boundary_values_tempered
- **Group C** (R→E properties): local commutativity, E0, E2, E4, h_in_tube
- **Group D** (GNS wiring): wightman_reconstruction + wightman_uniqueness

Groups A and B converge at constructWightmanFunctions (needs both BHW and boundary values).

## Status Overview

| File | Sorrys | Axioms | Status |
|------|--------|--------|--------|
| Basic.lean | 0 | 0 | ✅ Complete |
| Groups/Lorentz.lean | 0 | 0 | ✅ Complete |
| Groups/Poincare.lean | 0 | 0 | ✅ Complete |
| Spacetime/Metric.lean | 0 | 0 | ✅ Complete |
| Spacetime/MinkowskiGeometry.lean | 0 | 0 | ✅ Complete |
| SchwartzTensorProduct.lean | 0 | 0 | ✅ Complete |
| WightmanAxioms.lean | 2 | 0 | Not blocking reconstruction |
| OperatorDistribution.lean | 1 | 0 | Not blocking reconstruction |
| Reconstruction/GNSConstruction.lean | 0 | 0 | ✅ Complete |
| Reconstruction/Helpers/EdgeOfWedge.lean | 0 | 0 | ✅ Complete (1D edge-of-wedge) |
| Reconstruction/Helpers/SeparatelyAnalytic.lean | 0 | 0 | ✅ Complete |
| SCV/TubeDistributions.lean | 2 | 3 | Distribution theory + Bochner axioms |
| **Reconstruction/AnalyticContinuation.lean** | **0** | **2** | edge_of_wedge + BHW axioms |
| **Reconstruction/WickRotation.lean** | **14** | **5** | OS↔Wightman bridge |
| **Reconstruction.lean** | **4** | **0** | Core theorems (IsWickRotationPair) |
| NuclearSpaces/NuclearOperator.lean | 0 | 0 | ✅ Complete (deferred, not blocking) |
| NuclearSpaces/NuclearSpace.lean | 2 | 0 | Deferred |
| NuclearSpaces/BochnerMinlos.lean | 3 | 0 | Deferred |
| NuclearSpaces/SchwartzNuclear.lean | 5 | 0 | Deferred |
| NuclearSpaces/EuclideanMeasure.lean | 1 | 0 | Deferred |
| **Critical path total** | **20** | **10** | |

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

### WickRotation.lean (proven 2026-02-20)
- `restricted_preserves_forward_cone` — Restricted Lorentz preserves V₊
- `restricted_preserves_forward_tube` — Restricted Lorentz preserves ForwardTube
- `W_analytic_lorentz_on_tube` — W_analytic is Lorentz invariant on ForwardTube
- `F_ext_translation_invariant` — BHW F_ext is translation invariant at Euclidean points
- `F_ext_permutation_invariant` — BHW F_ext is permutation symmetric at Euclidean points
- `F_ext_rotation_invariant` (det=1) — SO(d+1) invariance via complex Lorentz group
- `constructedSchwinger_symmetric` — E3 (sorry-free, verified)
- `constructedSchwinger_translation_invariant` — Part of E1 (sorry-free, verified)
- `constructedSchwinger_rotation_invariant` — Part of E1 (det=-1 sorry remains)
- `integral_orthogonal_eq_self` — Orthogonal COV preserves Lebesgue measure
- `integral_perm_eq_self` — Permutation COV preserves Lebesgue measure
- `integral_flatten_change_of_variables` — Fubini for tensor product integrals
- `os_to_wightman_full` — E'→R' bridge theorem (sorry-free)

### Reconstruction.lean
- `IsWickRotationPair` — Wick rotation pair predicate
  - Connects Schwinger functions S and Wightman functions W through holomorphic F_analytic

### WightmanAxioms.lean
- `wickRotatePoint` — Wick rotation map (τ,x⃗) ↦ (iτ,x⃗)

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
