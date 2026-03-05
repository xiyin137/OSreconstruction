# ComplexLieGroups Module TODO

Last updated: 2026-02-27

Plan sync:
- Source recommendations: `claude_to_codex.md`
- Canonical execution plan: `docs/development_plan_systematic.md`
- Canonical BHW status: `docs/BHW_STATUS.md`
- Local permutation blocker status:
  `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/BLOCKER_STATUS.md`

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

### JostPoints.lean — 0 sorrys ✓
All `sorry`s removed in `JostPoints.lean`.

**PROVED:**
- `forwardJostSet_subset_extendedTube` (Jost's lemma) ✅ — Wick rotation maps ForwardJostSet into ExtendedTube
- `extendF_holomorphicOn` ✅ — extendF is holomorphic on ExtendedTube
- `extendF_eq_boundary_value` ✅ — extendF agrees with F on real Jost configurations
- `identity_theorem_totally_real` ✅ — identity theorem for totally real submanifolds
- `forwardJostSet_subset_jostSet` ✅ — ForwardJostSet ⊂ JostSet
- `jostSet_nonempty`, `forwardJostSet_nonempty`, `forwardJostSet_isOpen` ✅

### Connectedness/* — 1 sorry
| # | File | Line | Name | Status |
|---|------|------|------|--------|
| 1 | `Connectedness/BHWPermutation/PermutationFlow.lean` | 2156 | `iterated_eow_permutation_extension` | **1 local sorry hole** — remaining nontrivial permutation branch (`d > 0`, `n ≥ 2`, `σ ≠ 1`) via `hExtPerm` |

### GeodesicConvexity.lean — 0 sorrys ✓
The prior placeholder theorems (`cartan_exp_embedding`, `polar_decomposition`)
were removed from the active dependency chain. The file now contains proved
forward-cone/real-Lorentz infrastructure plus notes on deferred polar machinery.

NOTE: The false lemma `open_locally_path_connected_subset_preconnected` was DELETED
(GitHub issue #30). The counterexample is G = ℝ, S = (-2,-1) ∪ (-½,½) ∪ (1,2).
The previous `geodesic_convexity_forwardCone` statement was also REMOVED
(2026-02-25) after counterexample analysis.
See `test/proofideas_orbit_preconnected.lean` for planning notes
(heuristic; not a substitute for Lean proofs).

**PROVED (previously sorry):**
- `fullExtendF_well_defined` — reduced to `F_permutation_invariance`
- BHW Property 1 (holomorphicity) — inverse chart argument with EventuallyEq
- BHW Property 2 (F_ext = F on FT) — well-definedness + identity preimage
- BHW Property 3 (Lorentz invariance) — Lorentz group composition
- BHW Property 4 (permutation symmetry) — permutation composition + well-definedness
- **BHW Property 5 (uniqueness)** — identity theorem for product types + PET connected

Note: `nonemptyDomain_isPreconnected` is reduced to `orbitSet_isPreconnected`
using `isPreconnected_sUnion`. `complex_lorentz_invariance` is proved modulo
this geometric input.

New infrastructure (2026-02-22):
- `SCV.flattenCLE` — CLE from `Fin n → Fin m → ℂ` to `Fin (n*m) → ℂ`
- `analyticAt_of_differentiableOn_product` — Hartogs analyticity for product types
- `identity_theorem_product` — identity theorem for product types
- `complexLorentzAction_isOpenMap` — Lorentz action is open map
- `isOpen_extendedTube` — ET is open (union of open Lorentz images of FT)
- `isConnected_extendedTube` — ET is connected (continuous image of `G × FT`)
- `isOpen_permutedForwardTube` — PFT(π) is open
- `isOpen_permutedExtendedTube` — PET is open
- `adjacent_overlap_witness_exists` (`AdjacentOverlapWitness.lean`) — explicit overlap witness for `d ≥ 2`
- `nonemptyDomain_isOpen` (`Connectedness/ComplexInvariance/Core.lean`) — openness of
  `U = {Λ | ∃ w ∈ FT, Λ·w ∈ FT}` via product openness + projection
- `inOpenForwardCone_smul_pos` (`GeodesicConvexity.lean`) — positive scaling closure of V₊
- `productForwardCone_smul_pos`, `productForwardCone_convex`,
  `productForwardCone_nonempty`, `zero_not_mem_productForwardCone`,
  `productForwardCone_eowReady` (`DifferenceCoordinates.lean`) — packaged cone
  hypotheses for SCV edge-of-the-wedge applications
- `isOpen_productForwardConeReal`, `productForwardConeReal_smul_pos`,
  `productForwardConeReal_convex`, `productForwardConeReal_nonempty`,
  `zero_not_mem_productForwardConeReal` (`DifferenceCoordinates.lean`) — real
  cone-side variants of the product cone infrastructure
- `isOpen_flatProductForwardConeReal`, `flatProductForwardConeReal_smul_pos`,
  `flatProductForwardConeReal_convex`, `flatProductForwardConeReal_nonempty`,
  `zero_not_mem_flatProductForwardConeReal`,
  `flatProductForwardConeReal_eowReady` (`DifferenceCoordinates.lean`) —
  flattened real-cone package in the exact EOW theorem shape
- `edge_of_the_wedge_flat_instantiation` (`DifferenceCoordinatesSCV.lean`) —
  direct flattened-coordinate instantiation of
  `SCV.edge_of_the_wedge_theorem`
- `isOpen_pathComponentIn_of_eventually_joined`,
  `isOpen_orbitSet_pathComponent` (`Connectedness/ComplexInvariance/Core.lean`) — path-component
  openness infrastructure derived from local eventual joinability in `orbitSet`
- `orbitSet_mem_mul_ofReal_left`, `orbitSet_joined_one_ofReal`,
  `orbitSet_joined_mul_ofReal_left`,
  `ofReal_range_subset_pathComponentIn_orbitSet_one` (`Connectedness/ComplexInvariance/Core.lean`) —
  real-subgroup transport/connectedness infrastructure for orbit-set components
- `orbitSet_mem_mul_ofReal_right_of_stabilizes`,
  `orbitSet_joined_mul_ofReal_right_of_stabilizerPath`,
  `orbitSet_isPreconnected_of_doubleCoset_generation_with_stabilizerPath`
  (`Connectedness/ComplexInvariance/Core.lean`) — right-action/stabilizer-path
  orbit-set transport and a reduced double-coset preconnectedness criterion
- `toSOComplex_entry_00`, `toSOComplex_entry_succ0`,
  `toSOComplex_firstColEqE0_iff`, `fromSOComplex_toSOComplex`,
  `toSOComplex_fromSOComplex`, `continuous_fromSOComplex`
  (`Complexification.lean`) — exported Wick-rotation column/inverse/continuity
  infrastructure for stabilizer transport arguments
- `SOComplex.instContinuousMul`, `SOComplex.instContinuousInv`,
  `SOComplex.instIsTopologicalGroup` (`SOConnected.lean`) — topological-group
  instances for `SOComplex`, enabling direct use of continuous multiplication/
  inversion APIs in first-column-fiber transport arguments
- `SOComplex.isConnected_unitQuadric` (`SOConnected.lean`) — connectedness of
  `{v | ∑ vᵢ² = 1}` via first-column surjectivity and path-connectedness of
  `SOComplex`
- `SOComplex.firstColEqVec`, `SOComplex.isConnected_firstColEqVec_set`
  (`SOConnected.lean`) — connectedness of arbitrary fixed-first-column fibers
  over unit-quadric vectors via left-translation from the `e₀` fiber
- `wI0`, `stabilizerI0`, `mem_stabilizerI0_iff_firstColEqE0`,
  `stabilizerI0_eq_fromSO_image_firstCol`, `isConnected_stabilizerI0`
  (`Connectedness/ComplexInvariance/StabilizerI0.lean`) — connectedness of the
  canonical one-point stabilizer via the `SOComplex.firstColEqE0` model
- `firstColEqVecCLG`, `isConnected_firstColEqVecCLG_of_nonempty`
  (`Connectedness/ComplexInvariance/StabilizerI0.lean`) — connectedness of any
  nonempty fixed-first-column fiber in `SO⁺(1,m+1;ℂ)` by translating the
  connected `stabilizerI0` fiber
- `wScalarE0`, `mem_stabilizer_wScalarE0_iff_firstColEqE0`,
  `stabilizer_wScalarE0_eq_stabilizerI0`,
  `isConnected_stabilizer_wScalarE0`,
  `isConnected_stabilizer_of_eq_action_wScalarE0`
  (`Connectedness/ComplexInvariance/StabilizerI0.lean`) — scaled one-point
  stabilizer connectedness transport (`c e₀`, `c ≠ 0`)
- `rapidityElementD1`, `rapidityElementD1_mul`,
  `d1_exists_rapidityElement_principal_im_repr`,
  `d1_exists_rapidityElement_principal_im_strict_of_forwardTube`,
  `rapidityElementD1_real_preserves_forwardTube` (`D1OrbitSet.lean`) —
  exported `d=1` rapidity normal-form/decomposition infrastructure for reuse
  in permutation-overlap geometry
- `extendF_perm_eq_on_realJost`,
  `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`
  (`Connectedness/BHWPermutation/PermutationFlow.lean`) — local-Jost-witness
  ET-overlap identity-theorem infrastructure that avoids assuming global
  `JostSet ⊆ ExtendedTube`
- `eow_chain_adj_swap_of_midpoint`,
  `eow_chain_adj_swap_of_midCond`
  (`Connectedness/BHWPermutation/PermutationFlow.lean`) — right-adjacent
  midpoint-step infrastructure isolating the remaining geometric midpoint
  obligation in permutation-chain arguments

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

**Total: 1 sorry across 1 file** (`PermutationFlow.lean`: 1)

---

## Remaining Sorrys — Analysis

### `orbitSet_isPreconnected` (geometric)

**Goal:** O_w = {Λ ∈ G : Λ·w ∈ FT} is preconnected for each w ∈ FT.

**Why needed:** `nonemptyDomain_isPreconnected` reduces to this via
`isPreconnected_sUnion`, and `complex_lorentz_invariance` needs it.

**Why `domain_nonempty` (∀ Λ, D_Λ ≠ ∅) is FALSE:** boost(iπ) gives Λ with D_Λ = ∅.

**Independent status check (2026-02-25):**
- Repository history/branches (`main`, `bhw-phase-next`, `pr-29*`,
  `eliminate-bhw-axiom`) do not contain a completed non-`sorry` proof of this theorem.

**Update (2026-02-26):**
- The theorem is now resolved for `d = 0` (trivial group case) and `d = 1`
  (via `ComplexLieGroups/D1OrbitSet.lean`).
- The remaining open branch is `d ≥ 2` on the one-point orbit theorem (`n = 1`).
- `nonemptyDomain_isPreconnected` has been refactored with a proved reduction
  `n > 0 → n = 1` (`nonemptyDomain_eq_n1`), so only the one-point orbit geometry
  is now needed in downstream use (the `n`-dependence has been eliminated there).
- The previous placeholders were refactored into a single one-point geometric
  obligation in `Core.lean`: preconnectedness of canonical quadric-cone slices.
  This is now reduced to the nontrivial branch
  (`hquad_nonreal : ∀ c ≠ 0, c.im ≠ 0 → IsPreconnected (quadricConeSet_wScalarE0 c)`),
  with the `c.im = 0` branch proved by emptiness.
- `Connectedness/ComplexInvariance/OrbitSetN1Geometry.lean` now provides:
  - `quadricConeSet_wScalarE0_empty_of_c_im_zero`,
  - `quadricConeSet_wScalarE0_isPreconnected_of_c_im_zero`,
  - normalization lemma `quadricConeSet_wScalarE0_eq_scale_to_im_with_value`
    (scaling by `c` rewrites to a plain-imaginary cone condition at value `-(c^2)`).
- `test/orbitset_n1_infra_probe.lean` now records the exact `n = 1` closure
  packages that are sufficient:
  1) `IsConnected (stabilizer w)` + `PreconnectedSpace (orbitQuotTube w)`, or
  2) `IsConnected (stabilizer w)` + `IsOpenMap (orbitMap w)` +
     preconnected restricted orbit-image.

**New infrastructure (2026-02-25):**
- `ComplexLorentzGroup` now has:
  - `IsTopologicalGroup` (continuous multiplication/inversion),
  - `SigmaCompactSpace` (via closed embedding into matrix space).
- This unlocks use of sigma-compact/open-mapping and quotient-space tools in
  future orbit-map proofs (previously blocked by missing typeclass instances).
- `Connectedness/OrbitSetQuotient.lean` now includes
  `orbitSet_restricted_orbitMap_isQuotient_of_baireOrbit` and
  `orbitSet_isPreconnected_of_stabilizer_connected_and_baireOrbit`, giving a
  reusable Baire-orbit route from stabilizer connectedness to orbit-set
  preconnectedness once a `BaireSpace` instance on the orbit subtype is supplied.

**Open-mapping probe update (2026-02-26):**
- `test/orbit_open_mapping_transitive_probe.lean` now compiles a concrete
  `OrbitType` action model and confirms:
  - `isOpenMap_smul_of_sigmaCompact` applies on orbit subtypes once
    `BaireSpace OrbitType` is available.
  - `BaireSpace (G ⧸ stabilizer w)` is derivable from
    `QuotientGroup.isOpenQuotientMap_mk` via
    `IsOpenQuotientMap.baireSpace`.
- Remaining gap for this lane: a **topological bridge** (not just set-level
  equivalence) between orbit subtypes and quotient-by-stabilizer spaces, i.e.
  continuity/homeomorphism infrastructure around
  `MulAction.orbitEquivQuotientStabilizer`.

**Approaches:** See Proofideas/complex_lorentz_invariance.lean for detailed analysis.

**Numerical sanity check (2026-02-26):**
- Random search in `d = 2` also finds endpoint/segment failures for the removed
  one-parameter geodesic implication (`t=0` and `t=1` in cone does not force all
  `t ∈ [0,1]`), so that route is not recoverable by simply restricting to `d ≥ 2`.

### `iterated_eow_permutation_extension` (edge-of-the-wedge — CORE BHW blocker)

**Goal:** Build the iterated holomorphic extension data for arbitrary
permutations σ, so `eow_chain_adj_swap` can close the induction step.

**Current blocker:**
- The adjacent-swap helper currently gives only a local disjoint-union
  extension (`FT ∪ σFT`) and does not yet provide the generalized
  "extend from previously-built domain U_σ to U_(swap*σ)" infrastructure.
- Closing this requires a domain-iteration framework for EOW gluing
  (or a proof refactor that bypasses this formulation).

**Route exclusion (2026-02-26):**
- The midpoint-implication route is not viable. Compiled counterexamples in
  `test/midpoint_condition_counterexample_test.lean` and
  `test/midpoint_route_vacuous_test.lean` show the needed midpoint hypothesis
  is false already at `σ = 1` (for `d ≥ 2`, `n ≥ 2`), so this cannot be used to
  close `hExtPerm`.
- The global bridge `JostSet ⊆ ExtendedTube` is also not viable as a proof input.
  `test/jostset_et_counterexample_test.lean` compiles a counterexample
  (`jostSet_not_subset_extendedTube_counterexample`) for `n = 3` and any `d ≥ 1`.
  Any remaining route must use a weaker/local real-overlap condition rather than
  universal `JostSet` inclusion.

**Update (2026-02-26):**
- The theorem now has a completed `n ≤ 1` branch (trivial permutation case).
- It also has a completed `σ = 1` branch for all `n`.
- It also has a completed `d = 0` branch (ET-overlap for nontrivial `σ` is vacuous).
- The remaining open branch is `d > 0`, `n ≥ 2`, with `σ ≠ 1`.
- The unresolved local goal is exactly `hExtPerm`: ET-overlap invariance of
  `extendF` under `σ`, equivalent via
  `permInvariance_forwardTube_iff_extendF_overlap`.
- `PermutationFlow` now includes explicit chain-reduction infrastructure
  (`etAdj_chain_of_midCond`,
  `extendF_perm_overlap_of_adjSwap_connected_and_chain_hd2`,
  `extendF_perm_overlap_of_adjSwap_connected_and_midCond_hd2`), so the
  remaining gap is purely geometric (global ET-overlap control), not
  permutation-chain boilerplate.
- `test/proofideas_connectedness_blockers_2026_02_26.lean` formally isolates
  why the `midCond` route is not a standalone proof: it would be immediate
  under global permutation-invariance of `ExtendedTube`, which is exactly the
  behavior we cannot assume in the BHW setting.
- The `hJostET` route is now isolated as a strong wrapper layered over the
  new local-witness theorem; remaining obligations are reduced to geometric
  witness/connectedness inputs rather than global `JostSet` inclusion.

**Update (2026-02-28):**
- Added reusable seed-slice infrastructure in
  `Connectedness/BHWPermutation/SeedSlices.lean`:
  - `permSeedSet`, `permSeedSlice`
  - `permSeedSet_eq_iUnion_seedSlice`
  - `permSeedSlice_nonempty_iff_inv_mem_permForwardOverlapIndexSet`
  - `permSeedSet_eq_image_permForwardOverlapSet`
  - `permForwardOverlapSet_eq_image_permSeedSet`
  - `isConnected_permSeedSet_iff_permForwardOverlapSet`
- This formalizes the geometric decomposition
  `permOrbitSeedSet = ⋃_Λ (σFT ∩ ΛFT)` and pins down the remaining gap to
  connectedness of the corresponding nonempty-slice index set (not to basic set
  decomposition).

**Independent status check (2026-02-25):**
- Branch/history scan did not find a completed non-`sorry` version of this
  theorem either; earlier versions only moved the gap between helper lemmas.

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
          JostPoints.lean ✓
            forwardJostSet_subset_extendedTube ✓
            extendF_holomorphicOn ✓
            extendF_eq_boundary_value ✓
                     │
                     ▼
          GeodesicConvexity.lean ✓
            forward-cone / real-Lorentz infrastructure
                     │
                     ▼
          Connectedness/* (1 sorry)
            iterated_eow_permutation_extension [EOW iteration; `hExtPerm` gap]
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

1. **Connectedness/ComplexInvariance/Core.lean / geometric lane** — close `orbitSet_onePoint_isPreconnected` by
   proving the remaining `d ≥ 2` one-point quadric-cone preconnectedness nontrivial branch
   `hquad_nonreal : ∀ c ≠ 0, c.im ≠ 0 → IsPreconnected (quadricConeSet_wScalarE0 c)`.
2. **Connectedness/BHWPermutation/PermutationFlow.lean / EOW lane** — close `iterated_eow_permutation_extension`
   by proving `hExtPerm` for nontrivial `σ`, then discharge the theorem via
   `iterated_eow_permutation_extension_of_extendF_perm`.
3. Build: `lake build OSReconstruction.ComplexLieGroups`
4. Only after (1)-(3): continue into `Wightman/Reconstruction/WickRotation/*`
   blockers that depend on BHW closure.
