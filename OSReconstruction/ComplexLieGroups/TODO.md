# ComplexLieGroups Module TODO

## Sorry Status

### MatrixLieGroup.lean — 0 sorrys ✓
GL(n;ℂ) and SL(n;ℂ) path-connectedness fully proved.

### SOConnected.lean — 0 sorrys ✓
SO(n;ℂ) path-connectedness fully proved via:
- Exponential map infrastructure (skew-symmetric → orthogonal)
- Givens rotation algebra (P, Q projection matrices)
- Complex rotation elements with `c² + s² = 1`
- Column reduction by induction on n (Givens rotations zero out column entries)
- Block decomposition: first column = e₀ implies block-diagonal form

### Complexification.lean — 0 sorrys ✓
Complex Lorentz group SO⁺(1,d;ℂ) fully defined and path-connected:
- `ComplexLorentzGroup` structure with complex Minkowski metric preservation
- Group/topology instances
- Lie algebra exponential infrastructure
- Wick rotation homeomorphism: `toSOComplex` / `fromSOComplex`
- `isPathConnected` proved by transferring from `SOComplex.isPathConnected`

### LorentzLieGroup.lean — 0 sorrys ✓
`RestrictedLorentzGroup.isPathConnected` fully proved via `joined_one`.

### JostPoints.lean — 4 sorrys
| # | Line | Name | Status |
|---|------|------|--------|
| 1 | 913 | `spatial_rotation_e12_plane` | **sorry** — spatial rotation construction |
| 2 | 929 | `swap_jost_set_exists` | **sorry** — swap-compatible Jost configs exist |
| 3 | 1106 | `isConnected_extendedTube` | **sorry** — extended tube connected |
| 4 | 1117 | `tube_domain_intersection_connected` | **sorry** — ET ∩ σ·ET connected |

**PROVED:**
- `forwardJostSet_subset_extendedTube` (Jost's lemma) ✅ — Wick rotation maps ForwardJostSet into ExtendedTube
- `extendF_holomorphicOn` ✅ — extendF is holomorphic on ExtendedTube
- `extendF_eq_boundary_value` ✅ — extendF agrees with F on real Jost configurations
- `identity_theorem_totally_real` ✅ — identity theorem for totally real submanifolds
- `forwardJostSet_subset_jostSet` ✅ — ForwardJostSet ⊂ JostSet
- `jostSet_nonempty`, `forwardJostSet_nonempty`, `forwardJostSet_isOpen` ✅

### Connectedness.lean — 6 sorrys (down from 7, false lemma deleted)
| # | Line | Name | Status |
|---|------|------|--------|
| 1 | 1257 | `orbitSet_isPreconnected` | **sorry** — O_w connected (fiber/quotient or polar decomp) |
| 2 | 1763 | `eow_adj_swap_extension` | **sorry** — EOW flattening for adjacent swap |
| 3 | 1833 | `T_inter_U_grp_isOpen` | **sorry** — T∩U_grp open on extension domain |
| 4 | 1854 | `U_grp_isPreconnected` | **sorry** — U_grp preconnected on extension domain |
| 5 | 2165 | `iterated_eow_permutation_extension` | **sorry** — EOW iteration for general σ |
| 6 | 2423 | `adjacent_sectors_overlap` | **sorry** — Jost point overlap between sectors |

NOTE: The false lemma `open_locally_path_connected_subset_preconnected` was DELETED
(GitHub issue #30). The counterexample is G = ℝ, S = (-2,-1) ∪ (-½,½) ∪ (1,2).
Also U = {Λ | ∃ w ∈ FT, Λ·w ∈ FT} ≠ G (counterexample: Λ = -I maps V⁺ to V⁻).
See `test/proofideas_orbit_preconnected.lean` for correct proof strategies.

**PROVED (previously sorry):**
- `fullExtendF_well_defined` — reduced to `F_permutation_invariance`
- BHW Property 1 (holomorphicity) — inverse chart argument with EventuallyEq
- BHW Property 2 (F_ext = F on FT) — well-definedness + identity preimage
- BHW Property 3 (Lorentz invariance) — Lorentz group composition
- BHW Property 4 (permutation symmetry) — permutation composition + well-definedness
- **BHW Property 5 (uniqueness)** — identity theorem for product types + PET connected

Note: `nonemptyDomain_isPreconnected` is PROVED from `orbitSet_isPreconnected`
using `isPreconnected_sUnion`. `complex_lorentz_invariance` is proved modulo
`orbitSet_isPreconnected`.

New infrastructure (2026-02-22):
- `SCV.flattenCLE` — CLE from `Fin n → Fin m → ℂ` to `Fin (n*m) → ℂ`
- `analyticAt_of_differentiableOn_product` — Hartogs analyticity for product types
- `identity_theorem_product` — identity theorem for product types
- `complexLorentzAction_isOpenMap` — Lorentz action is open map
- `isOpen_permutedForwardTube` — PFT(π) is open
- `isOpen_permutedExtendedTube` — PET is open

Previously proved infrastructure:
- ForwardTube, complexLorentzAction, PermutedExtendedTube definitions
- `near_identity_invariance` — F(Λ·z₀) = F(z₀) for Λ near 1 in SO⁺(1,d;ℂ)
- `uniform_near_identity_invariance` — uniform version over a nhd of z₀
- `eq_zero_on_convex_of_eventuallyEq_zero` — identity theorem on open convex domains
- `complex_lorentz_invariance` — PROVED modulo `orbitSet_isPreconnected`
- `fullExtendF_well_defined` — PROVED from `F_permutation_invariance`
- `fullExtendF` definition + ALL BHW properties PROVED
- `extendF`, `extendF_eq_on_forwardTube`, `extendF_preimage_eq`, etc.
- BHW theorem statement with all hypotheses

**Total: 10 sorrys across 2 files** (JostPoints: 4, Connectedness: 6)

---

## Remaining Sorrys — Analysis

### `orbitSet_isPreconnected` (geometric)

**Goal:** O_w = {Λ ∈ G : Λ·w ∈ FT} is preconnected for each w ∈ FT.

**Why needed:** `nonemptyDomain_isPreconnected` reduces to this via
`isPreconnected_sUnion`, and `complex_lorentz_invariance` needs it.

**Why `domain_nonempty` (∀ Λ, D_Λ ≠ ∅) is FALSE:** boost(iπ) gives Λ with D_Λ = ∅.

**Approaches:** See Proofideas/complex_lorentz_invariance.lean for detailed analysis.

### `F_permutation_invariance` (edge-of-the-wedge — CORE BHW content)

**Goal:** For w ∈ FT, τ ∈ S_n, Γ ∈ SO⁺(1,d;ℂ) with Γ·(τ·w) ∈ FT:
  F(Γ·(τ·w)) = F(w).

**Analysis:**
- For τ = id: this is `complex_lorentz_invariance` (proved modulo orbitSet sorry).
- For τ ≠ id: uses local commutativity (hF_local) at Jost points + edge-of-the-wedge.
- FT and τ·FT have opposite imaginary parts for permuted differences,
  so FT ∩ τ·FT = ∅ for τ ≠ id. But their closures share Jost points
  (real configs with spacelike separations).
- Edge-of-the-wedge (SCV.edge_of_the_wedge_theorem) glues F on FT with
  F∘σ on σ·FT into a holomorphic function on FT ∪ σ·FT ∪ (Jost neighborhood).
- Iterate over adjacent transpositions for general τ.

### PET preconnected (edge-of-the-wedge)

**Goal:** `IsPreconnected (PermutedExtendedTube d n)`

**Why needed:** BHW uniqueness uses the identity theorem, which requires PET connected.

**Dependencies:** Same as `F_permutation_invariance` — edge-of-the-wedge is what
connects different permutation sectors of PET. Once F_permutation_invariance is
proved, the same analytic continuation argument shows PET is connected.

---

## Dependency Graph

```
MatrixLieGroup.lean ✓ ──────────────────────────────────────────┐
                                                                 │
SOConnected.lean ✓ ──────────────────────────────────┐           │
   SO(n;ℂ) path-connected                           │           │
                                                     ▼           │
LorentzLieGroup.lean ✓                       Complexification.lean ✓
   RestrictedLorentzGroup ✓                  ComplexLorentzGroup
   isPathConnected ✓                         isPathConnected ✓
            │                                        │
            │                                        │
            ▼                                        ▼
          JostPoints.lean (4 sorrys)
            forwardJostSet_subset_extendedTube ✓ (Jost's lemma)
            spatial_rotation_e12_plane [sorry]
            swap_jost_set_exists [sorry]
            isConnected_extendedTube [sorry]
            tube_domain_intersection_connected [sorry]
                     │
                     ▼
          Connectedness.lean (6 sorrys)
            orbitSet_isPreconnected [geometric — needs Lie group fiber theory]
            eow_adj_swap_extension [EOW flattening]
            T_inter_U_grp_isOpen [orbit connectivity on extension domain]
            U_grp_isPreconnected [orbit connectivity on extension domain]
            iterated_eow_permutation_extension [EOW iteration]
            adjacent_sectors_overlap [Jost points]
                     │
                     ▼
          SCV/IdentityTheorem.lean ✓
            flattenCLE, analyticAt_of_differentiableOn_product
            identity_theorem_product
                     │
                     ▼
          (bridges to Wightman/AnalyticContinuation.lean)
```

## Execution Order

1. **Connectedness.lean** — prove `orbitSet_isPreconnected` (geometric analysis)
2. **Connectedness.lean** — prove `F_permutation_invariance` (edge-of-the-wedge)
3. **Connectedness.lean** — prove PET preconnected (follows from 2)
4. Build: `lake build OSReconstruction.ComplexLieGroups`
5. **LorentzLieGroup.lean** — prove `isPathConnected` (Phase 3, when convenient)
