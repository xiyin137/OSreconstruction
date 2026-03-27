# ComplexLieGroups Module TODO

Last updated: 2026-03-25

Plan sync:
- Source recommendations: `claude_to_codex.md`
- Canonical execution plan: `docs/development_plan_systematic.md`
- Canonical BHW status: `docs/BHW_STATUS.md`
- Local permutation blocker status:
  `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/BLOCKER_STATUS.md`

## Sorry Status — 2 sorries across 1 file

| File | Sorrys | Names |
|------|--------|-------|
| `Connectedness/BHWPermutation/PermutationFlowBlocker.lean` | 2 | `blocker_isConnected_permSeedSet_nontrivial`, `blocker_iterated_eow_hExtPerm_d1_nontrivial` |
| **All other files** | **0** | |
| **Total** | **2** | |

### Sorry-Free Files (all 0 sorrys)

- `MatrixLieGroup.lean` — GL(n;ℂ) and SL(n;ℂ) path-connectedness
- `SOConnected.lean` — SO(n;ℂ) path-connectedness (exponential map + Givens rotations)
- `Complexification.lean` — ComplexLorentzGroup SO⁺(1,d;ℂ) path-connected
- `LorentzLieGroup.lean` — RestrictedLorentzGroup path-connected
- `JostPoints.lean` — Jost's lemma, extendF holomorphicity, boundary values
- `GeodesicConvexity.lean` — forward-cone / real-Lorentz infrastructure
- `DifferenceCoordinates.lean` — product cone infrastructure for EOW
- `DifferenceCoordinatesReduced.lean` — reduced difference coordinates
- `DifferenceCoordinatesSCV.lean` — flattened-coordinate EOW instantiation
- `D1OrbitSet.lean` — d=1 orbit-set rapidity decomposition
- `BHWCore.lean` — core BHW infrastructure
- `AdjacentOverlapWitness.lean` — explicit overlap witness for d ≥ 2
- `Connectedness/Action.lean`
- `Connectedness/ComplexInvarianceCore.lean`
- `Connectedness/ComplexInvariance/Core.lean`
- `Connectedness/ComplexInvariance/Extend.lean`
- `Connectedness/ComplexInvariance/OrbitSetN1Geometry.lean`
- `Connectedness/ComplexInvariance/OrbitSetN1Preconnected.lean`
- `Connectedness/ComplexInvariance/QuadricConeImPos.lean`
- `Connectedness/ComplexInvariance/StabilizerI0.lean`
- `Connectedness/DimensionZero.lean`
- `Connectedness/ForwardTubeDomain.lean`
- `Connectedness/OrbitSetBasic.lean`
- `Connectedness/OrbitSetQuotient.lean`
- `Connectedness/Permutation.lean`
- `Connectedness/PermutedTube.lean`
- `Connectedness/PermutedTubeConnected.lean`
- `Connectedness/ReducedPermutedTube.lean`
- `Connectedness/Topology.lean`
- `Connectedness/BHWPermutation/Adjacency.lean`
- `Connectedness/BHWPermutation/AdjacencyDistributional.lean`
- `Connectedness/BHWPermutation/IndexSetD1.lean`
- `Connectedness/BHWPermutation/JostWitnessGeneralSigma.lean`
- `Connectedness/BHWPermutation/PermutationFlow.lean`
- `Connectedness/BHWPermutation/SeedSlices.lean`

## Remaining Sorries — Analysis

### `blocker_isConnected_permSeedSet_nontrivial` (PermutationFlowBlocker.lean:55)

**Goal:** For nontrivial σ with n ≥ 2, the permutation seed set
`permSeedSet n σ = {Λ ∈ CLG : Λ·w ∈ FT ∩ σFT for some w}` is connected.

**Numerical status:** Supported in all 80 trials (d=1, n=2). Earlier mixed results
were a sampling artifact (missing valid boost range).

### `blocker_iterated_eow_hExtPerm_d1_nontrivial` (PermutationFlowBlocker.lean:91)

**Goal:** For d=1, if F satisfies BHW hypotheses and z, σ·z ∈ ExtendedTube,
then extendF F (σ·z) = extendF F z.

**Numerical status:** No numerical falsifier detected. Relative antisymmetry defect
< 10⁻¹² on sampled domain.

**Note:** `PermutationFlow.lean` is now fully sorry-free. The sorry that was previously
at `iterated_eow_permutation_extension` has been resolved. The two remaining sorries
are isolated in `PermutationFlowBlocker.lean` as deferred geometric obligations.

## Fully Proved Infrastructure

### MatrixLieGroup.lean — 0 sorrys
GL(n;ℂ) and SL(n;ℂ) path-connectedness fully proved.

### SOConnected.lean — 0 sorrys
SO(n;ℂ) path-connectedness fully proved via:
- Exponential map infrastructure (skew-symmetric → orthogonal)
- Givens rotation algebra (P, Q projection matrices)
- Complex rotation elements with `c² + s² = 1`
- Column reduction by induction on n (Givens rotations zero out column entries)
- Block decomposition: first column = e₀ implies block-diagonal form

### Complexification.lean — 0 sorrys
Complex Lorentz group SO⁺(1,d;ℂ) fully defined and path-connected:
- `ComplexLorentzGroup` structure with complex Minkowski metric preservation
- Group/topology instances
- Lie algebra exponential infrastructure
- Wick rotation homeomorphism: `toSOComplex` / `fromSOComplex`
- `isPathConnected` proved by transferring from `SOComplex.isPathConnected`

### LorentzLieGroup.lean — 0 sorrys
`RestrictedLorentzGroup.isPathConnected` fully proved via `joined_one`.

### JostPoints.lean — 0 sorrys
- `forwardJostSet_subset_extendedTube` (Jost's lemma)
- `extendF_holomorphicOn` — extendF is holomorphic on ExtendedTube
- `extendF_eq_boundary_value` — extendF agrees with F on real Jost configurations
- `identity_theorem_totally_real` — identity theorem for totally real submanifolds

### GeodesicConvexity.lean — 0 sorrys
Forward-cone/real-Lorentz infrastructure. Previous placeholder theorems
(`cartan_exp_embedding`, `polar_decomposition`) were removed from the active
dependency chain.

### Connectedness/* — 0 sorrys (except PermutationFlowBlocker)

**PermutationFlow.lean — 0 sorrys** (previously had 1 sorry at `iterated_eow_permutation_extension`)
Now fully rewired to distributional hypotheses.

**AdjacencyDistributional.lean — 0 sorrys**
- `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`
- `extendF_adjSwap_eq_on_realOpen_of_distributional_local_commutativity`
- `extendF_adjSwap_eq_of_connected_overlap_of_distributional_local_commutativity`

**JostWitnessGeneralSigma.lean — 0 sorrys**
General-σ Jost witness infrastructure for d ≥ 2.

### BHW Properties — ALL PROVED
- BHW Property 1 (holomorphicity) — inverse chart argument with EventuallyEq
- BHW Property 2 (F_ext = F on FT) — well-definedness + identity preimage
- BHW Property 3 (Lorentz invariance) — Lorentz group composition
- BHW Property 4 (permutation symmetry) — permutation composition + well-definedness
- BHW Property 5 (uniqueness) — identity theorem for product types + PET connected

## Dependency Graph

```
MatrixLieGroup.lean ✅ ──────────────────────────────────────────┐
                                                                 │
SOConnected.lean ✅ ──────────────────────────────────┐           │
   SO(n;ℂ) path-connected                           │           │
                                                     ▼           │
LorentzLieGroup.lean ✅                       Complexification.lean ✅
   RestrictedLorentzGroup ✅                  ComplexLorentzGroup
   isPathConnected ✅                         isPathConnected ✅
            │                                        │
            │                                        │
            ▼                                        ▼
          JostPoints.lean ✅
            forwardJostSet_subset_extendedTube ✅
            extendF_holomorphicOn ✅
            extendF_eq_boundary_value ✅
                     │
                     ▼
          GeodesicConvexity.lean ✅
            forward-cone / real-Lorentz infrastructure
                     │
                     ▼
          Connectedness/* ✅ (except PermutationFlowBlocker: 2 sorrys)
            PermutationFlow.lean ✅
            AdjacencyDistributional.lean ✅
                     │
                     ▼
          SCV/IdentityTheorem.lean ✅
            flattenCLE, analyticAt_of_differentiableOn_product
            identity_theorem_product
                     │
                     ▼
          (bridges to Wightman/AnalyticContinuation.lean)
```

## Remaining Infrastructure

### `orbitSet_isPreconnected` (geometric)

**Goal:** O_w = {Λ ∈ G : Λ·w ∈ FT} is preconnected for each w ∈ FT.

**Why needed:** `nonemptyDomain_isPreconnected` reduces to this via
`isPreconnected_sUnion`, and `complex_lorentz_invariance` needs it.

**Status:**
- Resolved for `d = 0` (trivial group case) and `d = 1` (via `D1OrbitSet.lean`)
- Remaining open branch: `d ≥ 2` on the one-point orbit theorem (`n = 1`)
- Reduced to: preconnectedness of quadric-cone slices
  `hquad_nonreal : ∀ c ≠ 0, c.im ≠ 0 → IsPreconnected (quadricConeSet_wScalarE0 c)`

**Approaches:** See `Proofideas/complex_lorentz_invariance.lean` for detailed analysis.

### `iterated_eow_permutation_extension` — RESOLVED

The sorry that was previously at `PermutationFlow.lean` has been fully resolved.
The remaining obligations are isolated in `PermutationFlowBlocker.lean`:
1. `blocker_isConnected_permSeedSet_nontrivial` — seed-set connectivity
2. `blocker_iterated_eow_hExtPerm_d1_nontrivial` — d=1 overlap invariance

Both are numerically supported with no falsifiers detected.

## Difficulty Assessment and Formalization Effort

| Sorry | Difficulty | Est. effort | Used by |
|-------|-----------|-------------|---------|
| `blocker_isConnected_permSeedSet_nontrivial` | Hard | 3-5 months | Both d ≥ 2 and d = 1 branches |
| `blocker_iterated_eow_hExtPerm_d1_nontrivial` | Medium-Hard | 2-4 months | d = 1 branch only |

### `blocker_isConnected_permSeedSet_nontrivial` — Hard

This is a purely geometric/topological statement — no analytic data involved. But the geometry
is intricate:
- The extended tube ET is the union of complex Lorentz orbits of the forward tube
- The intersection `permSeedSet = ET ∩ σ⁻¹-PermutedForwardTube` is a semi-algebraic subset
  of high-dimensional complex space
- Connectedness requires showing path-connectedness through this intersection

Proof approach would involve:
1. Showing the extended tube is path-connected (known: complex Lorentz group is connected)
2. Showing the intersection with the permuted forward tube is "thick enough" to remain connected
   — requires understanding the geometry of Lorentz orbits and how permutations interact with
   the cone structure
3. The numerical validation supports the assertion for d=1, n=2 but the general case needs a
   geometric argument

This is the **higher-priority** blocker since it is shared by both the d ≥ 2 and d = 1 branches.

### `blocker_iterated_eow_hExtPerm_d1_nontrivial` — Medium-Hard

This is specifically the d = 1 case of permutation invariance of the BHW extension. For d ≥ 2
this is handled by the Jost-point argument (real spacelike points in ET where local commutativity
applies directly). For d = 1 the Jost-point approach breaks down because:
- In 1+1 dimensions, the spatial part is 1-dimensional, so spacelike separation is weaker
- The complex Lorentz group SO⁺(1,1;ℂ) ≅ ℂ* is abelian, changing the orbit geometry
- The proof likely needs a direct analytic continuation argument specific to the d = 1 rapidity
  parametrization

### Comparison with Other Modules

These are qualitatively different from the SCV axioms — they are geometric/combinatorial arguments
about complex Lorentz orbits and tube domains, not deep functional analysis theorems. They do not
require new Mathlib infrastructure; the challenge is purely in the geometric reasoning about
high-dimensional semi-algebraic sets.

## Execution Order

1. **PermutationFlowBlocker.lean** — close the 2 remaining sorries (geometric obligations)
2. Build: `lake build OSReconstruction.ComplexLieGroups`
3. Only after (1)-(2): continue into `Wightman/Reconstruction/WickRotation/*`
   blockers that depend on BHW closure.
