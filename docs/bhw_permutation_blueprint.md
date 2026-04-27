# BHW Permutation Blueprint

Purpose: this note records the BHW permutation / overlap-connectedness
infrastructure, with a narrow theorem-2 consumer contract.  The theorem-2
implementation entry point is now the direct BHW single-valuedness packet in
`docs/theorem2_locality_blueprint.md`.  The former fixed-`w`
forward-tube chamber packet in Sections 8-10 is archived as a rejected route.
The older generic permutation-flow blockers in Sections 1-7 are background
infrastructure only, not a substitute for the OS-paper locality route.

It should be read together with:
- `docs/theorem2_locality_blueprint.md`,
- `docs/scv_infrastructure_blueprint.md`.

## 0. Paper authority and theorem-2 scope

The BHW permutation lane is only a supplier inside the OS-paper route.  It must
not become an alternate reconstruction proof.  For theorem 2, this means:

1. OS II remains authoritative for the corrected `E -> R` analytic
   continuation and growth/temperedness package replacing the false OS I Lemma
   8.8 step;
2. OS I Section 4.5 is used only for the locality order
   `symmetry -> S'_n -> BHW -> S''_n -> Jost boundary locality`;
3. theorem 2 must consume Hall-Wightman/BHW as a single-valued continuation
   theorem on the permuted extended tube `S''_n`.  The former fixed-`w`
   adjacent chamber chain is not active: its documented edges require common
   permuted-forward-tube witnesses, and distinct permuted forward-tube sectors
   are disjoint;
4. the `d = 1` theorem-2 lane must remain the OS one-gap complex-edge route
   documented in `theorem2_locality_blueprint.md`, because the generic
   `blocker_iterated_eow_hExtPerm_d1_nontrivial` assumes locality and is
   circular for proving it.

## 1. Generic permutation-flow blocker surfaces

The still-open explicit blockers for the generic permutation-flow lane are:

1. `blocker_isConnected_permSeedSet_nontrivial`,
2. `blocker_iterated_eow_hExtPerm_d1_nontrivial`,

both in
`ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean`.

These are the two theorem slots preventing the fully general permutation-flow
route from being sorry-free.

Scope note for theorem 2: accepting these deferred blockers puts the
dimension-one case on the same footing as the higher-dimensional case for the
BHW permutation-flow endgame.  It does **not** automatically close the
non-circular OS-to-locality proof.  The second blocker assumes
`hF_local_dist : IsLocallyCommutativeWeak 1 W`, so it cannot be used to prove
the target locality theorem for `W := bvt_W OS lgc` unless that locality has
already been obtained non-circularly.  The OS route must get its `d = 1`
supplier from the separate one-dimensional complex-edge / PET theorem recorded
in `docs/theorem2_locality_blueprint.md`, not from this generic blocker lane.
So for theorem 2:

1. `blocker_isConnected_permSeedSet_nontrivial` may still feed the `d ≥ 2`
   chamber theorem;
2. `blocker_iterated_eow_hExtPerm_d1_nontrivial` remains generic BHW
   infrastructure only and is **not** a theorem-2 input;
3. the theorem-2 `d = 1` lane is the direct one-gap complex-edge route based on
   `bvt_F_acrOne_package`, not a reuse of the generic permutation-flow endgame.
4. this is not a taste-level route choice: it is forced by the OS I one-gap
   analysis and the §4.5 locality proof order recorded in
   `docs/os1_detailed_proof_audit.md`.

## 2. What is already proved

The BHW permutation lane already has substantial proved infrastructure:

1. `SeedSlices.lean` packages the seed-set / overlap-slice geometry,
2. `Adjacency.lean` packages the adjacent-swap EOW route,
3. `AdjacencyDistributional.lean` packages the distributional swap version,
4. `JostWitnessGeneralSigma.lean` constructs the general-σ Jost witness for
   the `d ≥ 2` branch,
5. `IndexSetD1.lean` packages the `d = 1` orbit-set geometry,
6. `PermutationFlow.lean` contains the full iteration skeleton and final BHW
   theorem wiring.

For the generic permutation-flow lane, the remaining work is not “build the
permutation theory from scratch.”  It is the two exact blockers above.  For
the theorem-2 lane, Sections 8-10 below are retained only to explain why the
fixed-`w` forward-tube gallery is not the route.

## 3. Blocker A: connectedness of the nontrivial seed set

The theorem

```lean
blocker_isConnected_permSeedSet_nontrivial
```

should be treated as a purely geometric/topological theorem.

Its exact role:

1. connectedness of `permSeedSet`,
2. transfer to connectedness of the forward-overlap index set,
3. use in the identity-theorem propagation step on overlap domains.

Documentation-standard theorem slots:

```lean
lemma permSeedSet_nonempty_of_jostWitness
lemma permSeedSet_pathConnected_of_seedSlices
lemma seedSlice_chain_connectedness
theorem blocker_isConnected_permSeedSet_nontrivial
```

For `d ≥ 2`, the existing general-σ Jost witness should be the basepoint input.
For `d = 1`, the route should pass through the dedicated orbit-set geometry in
`IndexSetD1.lean`.

### 3.1. Exact proof transcript for the `d ≥ 2` branch

The later Lean proof should be written as a literal chain:

1. use `JostWitnessGeneralSigma.lean` to choose one nontrivial base point
   `z₀ ∈ permSeedSet`,
2. identify the local seed slice through `z₀`,
3. prove every point of `permSeedSet` lies in some seed slice,
4. prove any two seed slices in the same combinatorial adjacency class overlap
   nontrivially,
5. build a finite adjacency chain from any point to the base slice,
6. conclude path connectedness by concatenating paths inside slices and across
   overlaps,
7. convert path connectedness to connectedness.

So the theorem slots should be thought of more concretely as:

```lean
lemma permSeedSet_basepoint_from_jostWitness
lemma mem_seedSlice_of_mem_permSeedSet
lemma seedSlice_overlap_of_adjacency
lemma seedSlice_chain_to_basepoint
lemma permSeedSet_pathConnected_of_seedSlice_chain
theorem blocker_isConnected_permSeedSet_nontrivial
```

The important implementation point is that the global connectedness theorem
should be the consumer; the real work lives in the slice-overlap combinatorics.

### 3.2. Exact proof transcript for the `d = 1` geometric side

The `d = 1` branch should not try to reuse the `d ≥ 2` Jost-witness geometry
verbatim. The correct route is:

1. translate `permSeedSet` membership into the one-dimensional orbit/index-set
   description from `IndexSetD1.lean`,
2. prove the relevant orbit-set is an interval or finite union of adjacent
   intervals in the line-order model,
3. prove the interval chain is connected,
4. transport that connectedness back to `permSeedSet`.

This means the later file should isolate:

```lean
lemma d1_permSeedSet_to_orbitIndexSet
lemma d1_orbitIndexSet_interval_connected
lemma d1_permSeedSet_connected
```

before mixing the result into permutation-flow endgame code.

## 4. Blocker B: the `d = 1` overlap-invariance bridge

The theorem

```lean
blocker_iterated_eow_hExtPerm_d1_nontrivial
```

is the missing `hExtPerm` input for the `d = 1` nontrivial permutation branch.

Its exact meaning:

1. if `z` and `σ · z` both lie in the extended tube,
2. and `F` satisfies the standard BHW hypotheses,
3. then `extendF F (σ · z) = extendF F z`.

The proof should be organized as:

1. reduce to overlap connectedness on the relevant forward-overlap set,
2. use the `d = 1` index-set connectedness package,
3. combine with the already-proved adjacent-swap / identity-theorem machinery,
4. conclude the permutation-invariance statement on overlap.

Documentation-standard theorem slots:

```lean
lemma d1_forwardOverlapIndexSet_connected
lemma d1_forwardOverlapSet_connected
lemma d1_extendF_perm_eq_on_overlap
theorem blocker_iterated_eow_hExtPerm_d1_nontrivial
```

### 4.1. Exact proof transcript for the overlap-invariance bridge

The later Lean proof should be written in the following exact order:

1. fix `z` with both `z` and `σ • z` in the extended tube,
2. place both points in the same connected forward-overlap component using the
   `d = 1` index-set geometry,
3. invoke the already-proved adjacent-swap extension theorem along that
   connected component,
4. obtain equality of `extendF` at the two endpoints,
5. repackage the equality in the exact `hExtPerm` record shape needed by
   `PermutationFlow.lean`.

So the consumer theorem slots should be:

```lean
lemma d1_points_lie_in_common_forwardOverlap_component
lemma d1_adjacentSwap_chain_preserves_extendF
lemma d1_extendF_perm_eq_on_overlap
theorem blocker_iterated_eow_hExtPerm_d1_nontrivial
```

The implementation should resist the temptation to prove a stronger global
permutation invariance theorem first. The blocker only needs the overlap
statement.

## 5. Exact dependency order

The later generic permutation-flow Lean implementation should proceed as:

1. prove the geometric connectedness blocker,
2. prove the `d = 1` overlap-invariance blocker,
3. close `iterated_eow_permutation_extension`,
4. then re-evaluate whether any downstream permutation theorem still needs its
   own wrapper.

### 5.1. Micro-order inside the later generic implementation

The exact order should be:

1. `d ≥ 2` slice-overlap connectedness lemmas,
2. `d = 1` orbit/index-set connectedness lemmas,
3. shared `permSeedSet` connectedness theorem,
4. `d = 1` common-component theorem for overlap points,
5. `d = 1` overlap-invariance theorem,
6. final `iterated_eow_permutation_extension` consumer step.

## 6. Lean-style endgame pseudocode

```lean
private theorem iterated_eow_permutation_extension [NeZero d] (n : ℕ) := by
  by_cases hσ : σ = 1
  · exact trivial_permutation_case ...
  · by_cases hd2 : 2 ≤ d
    · have hconn := blocker_isConnected_permSeedSet_nontrivial
        (d := d) n σ hσ hn
      exact extendF_perm_overlap_of_jostWitness_and_real_double_coset_generation
        (d := d) ... hconn
    · have hd1 : d = 1 := ...
      subst hd1
      exact blocker_iterated_eow_hExtPerm_d1_nontrivial
        (d := 1) n F hF_holo hF_lorentz W hF_bv_dist hF_local_dist σ hσ hn
```

## 7. Do not do this

1. Do not reopen the proved adjacent-swap machinery when the blocker is about
   nontrivial permutation flow.
2. Do not hide the `d ≥ 2` and `d = 1` branches inside one opaque theorem.
3. Do not mix numerical evidence with proof obligations in the later Lean code;
   numerical notes are sanity checks only.

## 8. Current readiness gate

This blueprint is not a license to start arbitrary theorem-2 production Lean by
itself. For theorem 2, the readiness gate is now:

1. do not implement
   `hallWightman_fixedPoint_endpointActiveGallery_of_two_le`,
   `petOrbitChamberChain_of_two_le`, or
   `petOrbitChamberConnected_of_two_le` as theorem-2 frontiers;
2. the documented common fixed-`w` forward-tube edge is impossible for distinct
   permutation labels, by the repo's permuted-forward-tube disjointness facts;
3. the active theorem-2 surface is the distributional Euclidean/Jost-anchored BHW
   single-valuedness theorem packet in
   `docs/theorem2_locality_blueprint.md`: first the corrected source
   branch-law theorem replacing the hF_perm-only
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`,
   then the proved assembly theorem
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry`, then the
   sector equality theorem
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry`, then the
   OS-specific
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`;
4. the generic permutation-flow files remain useful background infrastructure,
   but theorem 2 must not depend on a theorem whose proof assumes locality.

## 9. Recommended implementation size

Rough expected size:

1. connectedness blocker (`d ≥ 2` + `d = 1` geometry): 180-260 lines,
2. `d = 1` overlap-invariance blocker: 120-180 lines,
3. endgame consumer cleanup in `PermutationFlow.lean`: 20-50 lines.

For theorem 2, these sizes are historical guidance for the generic
permutation-flow lane.  The current docs-first blocker is more specific:
finish the distributional Euclidean/Jost-anchored BHW single-valuedness theorem transcript
before attempting the planned Slot-6/Slot-7 theorem surfaces.

## 10. Theorem-2 consumer contract

Theorem 2 does **not** consume the whole generic permutation-flow package.
The strict OS-route consumer packet is now narrower than the older monodromy
plan:

1. theorem 2 builds the OS-II-corrected analytic witness `bvt_F OS lgc n`;
2. OS-II Euclidean symmetry and branch/Schwinger matching supply the symmetric
   analytic datum on the permuted forward-tube family `S'_n`;
3. the source-backed BHW theorem extends that datum single-valuedly to the
   permuted extended tube `S''_n`;
4. Jost p. 83, second theorem, converts the symmetric boundary values into
   locality.

So for theorem 2 the exact source-facing BHW frontier is the
distributional Euclidean/Jost-anchored replacement for

```lean
BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry
```

Its proved PET-algebra assembly theorem is

```lean
BHW.permutedExtendedTube_extension_of_forwardTube_symmetry
```

Its derived sector equality theorem is

```lean
BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry
```

Its OS-specific consumer is

```lean
bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le
```

with target shape

```lean
∀ (π ρ : Equiv.Perm (Fin n))
  (z : Fin n → Fin (d + 1) → ℂ),
  z ∈ BHW.permutedExtendedTubeSector d n π →
  z ∈ BHW.permutedExtendedTubeSector d n ρ →
  bvt_selectedPETBranch (d := d) OS lgc n π z =
    bvt_selectedPETBranch (d := d) OS lgc n ρ z
```

The older target `petOrbitChamberConnected_of_two_le` is archived for theorem
2.  Its common-forward-tube finite-chain strengthening cannot be correct for
distinct adjacent labels.

Source ledger for this theorem packet:

1. OS I §4.5 fixes the order of imported analytic input. In the local OCR of
   `references/Reconstruction theorem I.pdf`, the locality paragraph first cites
   the Bargmann-Hall-Wightman theorem `[10]`, and only afterwards cites Ref.
   `[12]`, p. 83, second theorem.
2. Ref. [10] is Hall-Wightman (1951),
   "A theorem on invariant analytic functions with applications to
   relativistic quantum field theory". The local OCR audit supports using this
   source for complex Lorentz invariance, single-valued continuation to the
   extended tube, and spacelike uniqueness/determination statements. It does
   not directly state a permutation/transposition or fixed-`w` adjacent-gallery
   theorem.
3. Ref. [12] is Jost, *The general theory of quantized fields* (1965), p. 83,
   second theorem. This is the boundary-value theorem consumed later by
   theorem 2 after BHW single-valuedness, not the source of any Slot-6 chamber
   geometry.
   The local image-PDF audit identifies the cited theorem on printed page 83:
   Wightman-function properties except locality plus symmetry imply locality.
4. Consequently the next theorem-2 BHW theorem is the distributional
   Euclidean/Jost-anchored source compatibility theorem
   `BHW.hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`.
   The hF_perm-only branch-law surface is archived historical context, not a
   source theorem to close as stated.  The corrected compatibility theorem feeds the
   proved source-extension assembly theorem
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry`, with the
   derived sector equality
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` specialized
   to `bvt_F OS lgc n` by
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.  The public
   consumer is `bvt_F_petBranchIndependence_of_two_le`.
5. The exported chain theorem `petOrbitChamberChain_of_two_le` is archived for
   theorem 2.  It is not a verbatim numbered theorem in OS I or Hall-Wightman,
   and its documented common forward-tube-slice edge contradicts the repo's
   permuted-forward-tube disjointness facts for distinct adjacent labels.
6. Streater-Wightman Figure 2-4 is useful only as the standard adjacent
   common-real-environment geometry. Streater-Wightman Theorem 3-6 is not an
   input here, because its proof uses local commutativity and would be circular
   for theorem 2.
7. The local audit of Streater-Wightman Theorem 2-11 confirms that it is only
   the BHW analytic-continuation theorem: holomorphic tube functions with the
   stated Lorentz transformation law continue single-valuedly to the extended
   tube and transform under the proper complex Lorentz group. It does not state
   any permutation/transposition or fixed-`w` active-gallery result.
8. The nearby Streater-Wightman Section 2-4 discussion of permuted extended
   tubes proves only the adjacent common-real-environment fact for one adjacent
   transposition, using Figure 2-4. This is allowed local geometry but not the
   missing global finite gallery.

What is locally verified versus external:

1. The local OS, Hall-Wightman, and Streater-Wightman references verify the
   BHW-before-Jost order, the non-locality character of the complex-Lorentz
   extension theorem, Hall-Wightman's single-valued extended-tube continuation,
   and the adjacent common-real-environment geometry for one adjacent
   transposition.
2. The Hall-Wightman source is now available locally as
   `references/hall_wightman_invariant_analytic_functions_1957.pdf`; the OCR
   search supports extended-tube analytic continuation and single-valuedness.
   It does not provide, and the repo definitions do not permit, common
   fixed-`w` permuted-forward-tube overlaps for distinct labels.
3. The theorem-2 packet therefore uses the distributional Euclidean/Jost-anchored BHW source
   branch-law theorem that constructs one single-valued PET extension on
   `S''_n`, proves the extension theorem's PET algebra from it, and then takes
   sector branch equality as a corollary.  The approved Deep Research audit
   rejected the hF_perm-only generic source boundary: total values of `F` away
   from the ordered forward tube can satisfy the formal permutation hypothesis
   without constraining the analytic germ whose extended-tube branches must be
   compared.
4. Figure 2-4 may justify local common real environments for adjacent
   **extended** tubes.  It does not manufacture forward-tube overlaps.

The Slot-6 proof-doc contract is therefore the following mathematical
derivation:

1. state the distributional Euclidean/Jost-anchored BHW branch-law theorem replacing
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`
   in the local `BHW.PermutedExtendedTube` /
   `BHW.permutedExtendedTubeSector` language;
2. identify the OS-II-corrected selected branch family
   `bvt_selectedPETBranch (d := d) OS lgc n π` as the symmetric analytic datum
   on `S'_n`;
3. ensure the imported/source theorem has no `IsLocallyCommutativeWeak`
   hypothesis; the current repo surfaces named `bargmann_hall_wightman` and
   `BHW.bargmann_hall_wightman_theorem` take such a hypothesis and are
   circular for theorem 2;
4. specialize it using `bvt_F_holomorphic`,
   `bvt_F_restrictedLorentzInvariant_forwardTube`, `bvt_F_perm` as auxiliary
   formal symmetry data, and the OS-II Euclidean/Jost anchor package, then
   package the result as `bvt_F_petBranchIndependence_of_two_le`.

The equality theorem
`BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` is only the
branch-law corollary of the source extension theorem: if `Fpet` is the single
PET function and `z` lies in the `π`- and `ρ`-sectors, then both
`BHW.extendF F (fun k => z (π k))` and
`BHW.extendF F (fun k => z (ρ k))` are equal to `Fpet z`.

Implementation locus:

1. use the small source file
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceExtension.lean`;
2. the local support theorem
   `BHW.permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz`, which
   discharges branch holomorphicity from `BHW.extendF_holomorphicOn` after
   deriving complex-Lorentz overlap invariance from restricted real Lorentz
   invariance, is checked;
3. the generic branch-law, extension, and single-valuedness theorems now carry
   `BHW.SourceDistributionalAdjacentTubeAnchor` explicitly and are checked
   consumers of the one remaining source theorem;
4. prove or source-import only
   `BHW.hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`
   as the hard theorem-level frontier;
5. the OS layer now has
   `SelectedAdjacentDistributionalJostAnchorData` and the checked reindexing
   definition `bvt_F_distributionalJostAnchor_of_selectedJostData`; the next
   OS-side construction target is the genuine OS-II supplier
   `bvt_F_distributionalJostAnchor_of_OSII`.  The theorem-2 blueprint now fixes
   its exact Lean transcript:
   first prove the strengthened
   `BHW.os45_adjacent_singleChart_commonBoundaryValue`, returning one patch
   `V` that simultaneously carries Jost membership, both adjacent
   extended-tube memberships, and an
   `BHW.AdjacentOSEOWDifferenceEnvelope`.  The hard local theorem inside that
   Slot 1 proof is `BHW.os45_adjacent_commonBoundaryEnvelope`: it constructs the
   common OS45 chart, applies the pure-SCV local distributional EOW envelope
   theorem `SCV.local_distributional_edge_of_the_wedge_envelope`, and exports
   the holomorphic branch-difference function with the two trace identities.
   That SCV theorem must use truncated local wedges, a local continuous EOW
   lemma extracted from the Cauchy-polydisc proof, Streater-Wightman
   real-direction regularization, compact-subcone-uniform distributional
   boundary limits, kernel/nuclear-theorem recovery, translation covariance,
   compactly supported approximate identities, and explicit slow-growth bounds.
   The kernel-recovery layer is the exact pure-SCV package
   `SCV.complexTranslateSchwartz`, `SCV.schwartzTensorProduct₂`,
   `SCV.schwartzKernel₂_extension`, `SCV.realConvolutionTest`,
   `SCV.translationCovariantProductKernel_descends`,
   `SCV.distributionalHolomorphic_regular`, and the regularized-envelope
   lemmas `SCV.regularizedEnvelope_linearContinuousInKernel`,
   `SCV.regularizedEnvelope_translationCovariant`,
   `SCV.regularizedEnvelope_productKernel`,
   `SCV.regularizedEnvelope_kernelRepresentation`, and
   `SCV.regularizedEnvelope_deltaLimit_agreesOnWedges`; do not replace it with
   the homogeneous `SchwartzMap.productTensor ![φ, ψ]` API, the Wightman-side
   tensor/slice-integral files, or the QFT-facing
   `schwartz_nuclear_extension` axiom.  The currently checked SCV substrate in
   `SCV/DistributionalEOWKernel.lean` covers `SCV.complexTranslateSchwartz`,
   `SCV.schwartzTensorProduct₂`, `SCV.realConvolutionShearCLE`, and
   `SCV.complexRealFiberIntegralRaw`, plus `SCV.integrable_complexRealFiber`,
   `SCV.baseFDerivSchwartz`, and
   `SCV.exists_norm_pow_mul_complexRealFiberIntegralRaw_le` and
   `SCV.exists_integrable_bound_baseFDerivSchwartz`, plus
   `SCV.hasFDerivAt_complexRealFiberIntegralRaw`, the raw integral smoothness
   and decay theorems, `SCV.complexRealFiberIntegral`, and
   `SCV.realConvolutionTest` with its apply theorem and translation identity.
   The same file now also checks `SCV.complexRealFiberTranslateSchwartzCLM`,
   `SCV.complexRealFiberIntegral_fiberTranslate`,
   `SCV.complexRealFiberIntegral_schwartzTensorProduct₂`,
   `SCV.translateSchwartz_translateSchwartz`,
   `SCV.complexTranslateSchwartz_complexTranslateSchwartz`,
   `SCV.shearedProductKernelFunctional`, and
   `SCV.IsComplexRealFiberTranslationInvariant`, plus
   `SCV.complexRealFiberTranslate_shearedTensor_eq`.  The next target is the
   sheared product-kernel invariance theorem after the required density theorem
   is available, the mixed fiber-factorization theorem, and then the
   product-kernel extension and translation-covariant descent layer:
   `SCV.schwartzKernel₂_extension`,
   `SCV.translationCovariantProductKernel_descends`, and
   `SCV.distributionalHolomorphic_regular`.  The descent layer is pinned to
   the global covariance predicate
   `SCV.ProductKernelRealTranslationCovariantGlobal`; the local
   support-restricted covariance needed by the envelope is a later cutoff
   corollary, not the direct input to the global `Hdist`.
   A radial limit, a global-tube shortcut, a naive mollifier limit without the
   kernel step, a finite-order primitive shortcut, a polynomial-correction
   shortcut, or a pointwise-boundary shortcut is not sufficient.
   The coordinate and trace-membership prerequisites
   `BHW.configPermCLE`, `BHW.os45CommonChartCLE`,
   `BHW.wickRotate_ordered_mem_acrOne`,
   `BHW.adjacent_wick_traces_mem_acrOne`, and
   `BHW.os45CommonChart_real_mem_pulledRealBranchDomain_pair` are checked in
   `OSToWightmanLocalityOS45CommonChart.lean` and
   `OSToWightmanLocalityOS45TraceMembership.lean`; the remaining hard work is
   the pure-SCV local distributional envelope theorem and its OS45
   instantiation.  Slot 1 does not prove vanishing;
   the checked consumer kills the
   Wick trace using `bvt_F_acrOne_package` and transports zero to the real edge.
   After Slot 1, prove
   `BHW.sourceRealEnvironment_of_os45JostPatch` for the Gram image of that
   same patch; then build
   `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII` and pass it
   through the checked reindexing bridge.
   The checked SCV lemmas
   `BHW.sourceDistributionalUniquenessSet_of_isOpen_nonempty` and
   `BHW.sourceDistributionalUniquenessSet_of_contains_open` are only
   full-matrix sufficient criteria.  They do not supply the general OS
   anchor, because source Gram images are symmetric and, above the spacetime
   vector dimension, rank-bounded.  The remaining supplier geometry is to
   produce a Hall-Wightman real environment in the scalar-product variety; the
   production anchor now carries the variety-level predicate
   `BHW.sourceDistributionalUniquenessSetOnVariety`.  The OS supplier should
   take the environment `E` to be the whole Gram image of the selected OS45
   real patch and prove uniqueness by finding a smaller regular
   Hall-Wightman real environment inside `E`, then applying the checked
   monotonicity lemma
   `BHW.sourceDistributionalUniquenessSetOnVariety_mono`.  The checked
   regular-stratum definitions are `sourceGramExpectedDim`,
   `sourceConfigurationSpan`, `sourceComplexConfigurationSpan`,
   `SourceGramRegularAt`, `SourceComplexGramRegularAt`, and the concrete
   full-span template `sourceFullSpanTemplate`;
6. do not consume the top-level
   `BHWPermutation.PermutationFlow.bargmann_hall_wightman_theorem` for theorem
   2, because its current public statement carries
   `IsLocallyCommutativeWeak` / boundary-distribution inputs and is circular for
   theorem 2.  The lower-layer, non-circular BHW/PET support in
   `PermutedTubeMonodromy.lean` is permitted and is now the checked active entry
   point:
   `BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`
   and `BHW.F_permutation_invariance_of_petBranchIndependence`.

The restricted-real Lorentz input is intentional: it is the Hall-Wightman
source hypothesis.  Complex-Lorentz single-valued continuation on the extended
tube is the BHW output consumed by the theorem, not a replacement for the
source contract.
For local Lean APIs such as `BHW.extendF_holomorphicOn`, the required
forward-tube complex-Lorentz overlap invariance should be derived internally
from `BHW.complex_lorentz_invariance n F hF_holo hF_lorentz`.

The displayed generic hF_perm-only branch-law theorem in the theorem-2
blueprint is now historical API context, not a valid source boundary.  The
permuted-tube branch family is still
`F_π z = F (fun k => z (π k))`, but its symmetry as Hall-Wightman's `S'_n`
datum must be anchored on the Euclidean/Jost uniqueness set where the OS-II
Schwinger construction supplies both branch agreement and Schwinger
permutation symmetry.  A later internal proof may introduce a family-indexed
Hall-Wightman helper, but the theorem-2-facing source input should remain the
corrected branch-law theorem, not a raw hF_perm-only theorem.
The larger theorem
`BHW.permutedExtendedTube_extension_of_forwardTube_symmetry` is now the proved
PET-algebra assembly from that branch law.

The theorem-2 blueprint now fixes the only allowed private branch-law lemma
ladder:

```lean
source_permutedForwardBranch_holomorphicOn
source_permutedForwardBranch_restrictedLorentzInvariant
source_permutedForwardBranch_symmetric
hallWightman_source_permutedBranch_compatibility
```

The first three are elementary packaging of the symmetric `S'_n` datum.  The
last is the only non-elementary source-facing compatibility theorem: if one
PET point lies in two explicit sectors, the two `extendF` branch values agree.
The public branch-law theorem should then build `Fpet` mechanically with
`BHW.gluedPETValue`, `BHW.gluedPETValue_holomorphicOn`, and
`BHW.gluedPETValue_eq_of_mem_sector`.  It must not become a second public
wrapper or a second `sorry`.  The approved Deep Research check corrected the
source boundary: this compatibility shape is non-circular only when it is
proved from the distributional Euclidean/Jost-anchored Hall-Wightman datum, not from total
`hF_perm` alone.  Growth/temperedness remains routed to the upstream OS-II
boundary-value construction and is not added as a separate hypothesis to this
isolated identity-theorem step.

The theorem-2 blueprint now also gives the exact lower source package for
closing `hallWightman_source_permutedBranch_compatibility`.  The genuine
mathematical input is

```lean
hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor
```

which says that any two PET sector branches
`z ↦ BHW.extendF F (fun k => z (π k))` agree at a common PET-sector point.
Internally, its proof may produce a common scalar-product representative
`Φ (sourceMinkowskiGram d n z)`, but that `Φ` is a consequence, not an OS
input.  Its source proof is Hall-Wightman scalar-product theory plus
distributional edge-of-the-wedge
applied to the distributionally anchored symmetric permuted-tube datum `S'_n`:
define `sourceMinkowskiGram`, get branch scalar-product representatives, use
compact-test Schwinger symmetry and branch-boundary distribution matching on
adjacent permutation-indexed Jost real patches, apply uniqueness on the
scalar-product real environment, and conclude the branch law on `S''_n` as the
Hall-Wightman single-valued continuation theorem.  If an internal proof uses
adjacent patches plus cover connectivity, that geometry is part of the
source theorem proof and not a separate theorem-2 hypothesis.  A common
pointwise `Φ` is a consequence of this source theorem, not an OS input.

The Deep Research route-risk check
`v1_ChdUSW5yYWFuUkhNNlVfdU1QOE9YaGtRWRIXVElucmFhblJITTZVX3VNUDhPWGhrUVk`
specifically rejects treating
`BHW.petSectorFiber_adjacent_connected_of_two_le` as a theorem-2 prerequisite.
That fixed-point sector-fiber chain is not an OS/Hall-Wightman input and may be
false as a pointwise PET-geometry assertion.  Keep it out of the active route
unless it is later proved as an independent diagnostic theorem.

Do not make an ordinary
`BHW.extendF F (fun k => x (σ k)) = BHW.extendF F x` theorem the primary
source boundary.  It may be a corollary after the branch-level scalar-product
representative is known, but as a source input it hides the `S'_n` content and
risks over-reading the total `hF_perm` hypothesis on the ordered forward tube.

Do not replace this source step by the tempting base-extended-tube shortcut
`extendF F (fun k => z (τ k)) = extendF F z`.  The repo has private historical
lemmas proving such overlap statements only under stronger hypotheses tailored
to the old permutation-flow route.  From the current source hypotheses, a PET
overlap gives complex-Lorentz representatives of two permuted coordinates, but
it does not give that the permuted representative needed for a direct
forward-tube invariance argument remains in `ForwardTube d n`.  This is why the
strict OS II theorem-2 route consumes Hall-Wightman's single-valued
continuation on the symmetric `S'_n` datum and treats compatibility on `S''_n`
as the source theorem content.

These items are now the exact statement-level contract for the corrected BHW
theorem.  The unresolved Lean work is the distributional Euclidean/Jost-anchored analytic
proof of that theorem, or a separately approved theorem after the required
source and circularity audit, not the theorem-2 consumer surface.

The theorem-2 blueprint now gives the implementation packet for that source
proof in scalar-product coordinates.  The packet must be followed in this
order:

1. use `sourcePermuteComplexGram`, `sourceMinkowskiGram_perm`,
   `sourceExtendedTubeGramDomain`, `sourceDoublePermutationGramDomain`,
   `sourceRealMinkowskiGram_perm`, and `sourceRealGramComplexify_perm`;
2. build `SourceScalarRepresentativeData` for `extendF F` from the ordinary
   Hall-Wightman invariant analytic-function theorem.  The intended
   theorem-level source obligation is
   `hallWightman_exists_sourceScalarRepresentative_of_forwardTube_lorentz`,
   but it is deliberately quarantined in this blueprint until it has a checked
   proof or an explicitly approved source-import boundary;
3. convert `SourceDistributionalAdjacentTubeAnchor.compact_branch_eq` to
   pointwise equality on each real patch by compact-support uniqueness
   (checked in Lean);
4. rewrite that pointwise equality as adjacent seed equality for the scalar
   representative on each Gram environment (checked in Lean);
5. apply the Hall-Wightman scalar-overlap continuation theorem on `S''_n`;
6. close
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`
   by the documented scalar-domain proof transcript.  The production
   `SourceExtension.lean` module currently stops before this unresolved source
   gate and contains only sorry-free data/support lemmas.

The packaging is intentionally two-stage.  `SourceScalarRepresentativeData`
is local data for the ordinary extended-tube scalar image
`sourceExtendedTubeGramDomain d n`; the later Hall-Wightman theorem on
`M_n` / `S''_n` is a continuation theorem for that branch data, not a reason to
repackage the representative itself as globally defined source data.

For the proof doc to count as implementation-ready, step 5 must no longer be
treated as one opaque source theorem.  The theorem
`hallWightman_scalarOverlapContinuation_from_adjacentSeeds` is now understood
as a compressed package of three Hall-Wightman sub-obligations:

1. real-environment uniqueness for one adjacent scalar overlap component;
2. scalar-variety adjacent continuation from that local overlap to the full
   adjacent double-domain;
3. adjacent-transposition word propagation from one adjacent swap to a general
   permutation.

The theorem-2 blueprint now gives Lean-shaped statements and proof transcripts
for those three pieces.  Until the proof docs expose the exact overlap domains,
chain geometry, and permutation-word domain-membership lemmas needed by that
split, the source gate is not 100% ready for implementation.
It now also fixes the proof strategy for those suppliers: define the adjacent
overlap as a connected component of a Hall-Wightman real-environment
neighbourhood intersected with the adjacent double scalar domain; define the
seed cover as the union of such overlaps; obtain the adjacent-chain theorem
from connectedness plus finite-chain extraction on that open cover; treat
`sourcePermuteComplexGram_mul` and
`perm_word_of_adjacent_transpositions` as separate permutation algebra; and
replace the false naive `mul_mem_left/right` step with a stronger
word-chain supplier that records admissible intermediate scalar points for the
chosen adjacent word.  So the final passage from adjacent swaps to a general
permutation is no longer advertised as “pure algebra”; it is algebra plus
scalar-domain continuation geometry.  It also now fixes the normalization step from an
abstract adjacent transposition `τ` to a concrete consecutive swap
`Equiv.swap i ⟨i.val + 1, hi⟩`, and uses that normalization to define the seed
cover for `τ` as the union over permutation labels `π` of the corresponding
overlap components.
The route decision is now explicit: this adjacent-word package is retained
only as a possible internal decomposition.  The active theorem-2 contract is
the stronger global Hall-Wightman single-valued continuation theorem on the
connected scalar-product double domain, supplied by the local real-environment
overlap theorem and the adjacent scalar-domain continuation geometry.  The
route is now unique and the supplier theorem surfaces are fixed, but the proof
docs are not yet fully discharged until the remaining enlargement /
cover-reaching supplier `sourceDoublePermutationGramDomain_adjacent_chain` is
justified from the approved Hall-Wightman geometry.
The detailed theorem-2 blueprint now splits that further into the scalar-domain
reachability theorem `sourceAdjacentSeedCover_cover_doubleDomain` and reuse of
mathlib's `IsConnected.biUnion_of_reflTransGen` for the connected-union step.
It now also pins down the exact supporting theorem surfaces needed to make that
usable in Lean: `sourceAdjacentSeedCover_eq_union`,
`sourceAdjacentOverlapLabelSet`,
`exists_sourceAdjacentOverlapWitness_of_mem_doubleDomain`,
`mem_sourceAdjacentSeedCover_of_mem_doubleDomain`, and
`sourceAdjacentOverlapIndex_reflTransGen` on that active label set.  The
step-1 realization input to this witness theorem is now fixed at the checked
Lean surface `exists_sourceExtendedTube_realizations_of_mem_doubleDomain`.
Permutation-side theorem surfaces should now be stated against the existing
repo API of concrete swaps plus `BHW.Fin.Perm.adjSwap_induction`, not against
an abstract adjacent-transposition predicate except at the normalization step.
One more code-shape correction is now explicit: the final overlap object on
this route cannot honestly remain parameter-free in `(d,n,π,i,hi)` alone,
because it is built from a chosen Hall-Wightman local neighbourhood around the
anchor Gram environment.  So the current production parameter-free overlap
constant should be treated only as a placeholder surface.
Active implementation detail: keep
`sourceAdjacentPermutationGramOverlap` as the connected component around the
real Gram environment inside the adjacent double scalar-product domain.  The
seed-cover / chain layer is therefore not dead fallback bookkeeping; it is the
honest internal route for reaching arbitrary points of the adjacent double
domain unless a separate direct connectedness theorem is later proved.
The final active overlap object is therefore the `overlap` field inside
`SourceAdjacentOverlapWitness`; the old parameter-free
`sourceAdjacentPermutationGramOverlap d n π i hi` remains only a placeholder
surface in production Lean and should not be treated as the final theorem-2
API.
Also ruled out explicitly: do not identify that scalar double-domain with the
Gram-map image of the vector-valued adjacent overlap domain unless a separate
theorem proves common-configuration realizability.  The current scalar-domain
definition is weaker than that.

Current checked/unchecked boundary:

1. checked in production Lean:
   `sourceAnchor_compactBranchEq_pointwise_on_realPatch`,
   `sourceScalarRepresentative_adjacent_seed_eq_on_environment`,
   `sourceAdjacentPermutationGramOverlap_relOpen`,
   `gramEnvironment_complexify_mem_adjacentOverlap`,
   `permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz`;
2. quarantined to proof docs:
   `hallWightman_exists_sourceScalarRepresentative_of_forwardTube_lorentz`,
   the three split scalar-overlap continuation obligations,
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
   and the downstream PET branch-law / PET extension / sector single-valuedness
   consumers.

This is the source theorem itself, not a new wrapper.  It is also the point at
which any source import would need the explicit `AGENT.md` axiom/source-import
approval gate; the consumer theorems after it are already mechanical.

Existing global PET connectedness should also not be overread. The repository
already has useful theorems such as:

```lean
theorem BHW.permutedExtendedTubeSector_adjacent_overlap_nonempty
theorem BHW.permutedExtendedTube_isPreconnected
theorem BHW.isConnected_permutedExtendedTube
```

These prove ambient statements about the permuted extended-tube cover.  They
are not the BHW source theorem by themselves, and they do not revive the
fixed-`w` forward-tube gallery.  Likewise,
`BHW.gluedPETValue_holomorphicOn` assumes all-overlap compatibility as an
input.  The theorem-2 route is now decided: use the direct BHW
single-valuedness surface after the Hall-Wightman source branch law supplies
the single-valued `Fpet`, and do not cite Streater-Wightman Theorem 3-6 or any
theorem whose proof uses local commutativity.

The archived fixed-`w` packet below is not an implementation target:

```lean
def ActivePETOrbitLabel
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :=
  {σ : Equiv.Perm (Fin n) // (permLambdaSlice (d := d) n σ w).Nonempty}

def activePETOrbitAdj
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :
    ActivePETOrbitLabel d n w -> ActivePETOrbitLabel d n w -> Prop :=
  fun a b =>
    ∃ (i : Fin n) (hi : i.val + 1 < n),
      b.1 = a.1 * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      ((permLambdaSlice (d := d) n a.1 w) ∩
        (permLambdaSlice (d := d) n b.1 w)).Nonempty

structure PETOrbitChamberChain
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (σ : Equiv.Perm (Fin n)) where
  m : ℕ
  τ : Fin (m + 1) -> Equiv.Perm (Fin n)
  hstart : τ 0 = 1
  hend : τ ⟨m, Nat.lt_succ_self m⟩ = σ
  hstep :
    ∀ j : Fin m,
      ∃ (i : Fin n) (hi : i.val + 1 < n) (Λj : ComplexLorentzGroup d),
        τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩ =
          τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩ * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
        complexLorentzAction Λj w ∈
          PermutedForwardTube d n (τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩) ∧
        complexLorentzAction Λj w ∈
          PermutedForwardTube d n
            (τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩)

def PETOrbitChamberAdjStep
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :
    Equiv.Perm (Fin n) -> Equiv.Perm (Fin n) -> Prop :=
  fun π ρ =>
    ∃ (i : Fin n) (hi : i.val + 1 < n) (Λj : ComplexLorentzGroup d),
      ρ = π * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      complexLorentzAction Λj w ∈ PermutedForwardTube d n π ∧
      complexLorentzAction Λj w ∈ PermutedForwardTube d n ρ

theorem petOrbitChamberChain_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        PETOrbitChamberChain d n w σ

lemma mem_permForwardOverlapIndexSet_of_fixedPoint
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {w : Fin n -> Fin (d + 1) -> ℂ}
    (hw : w ∈ ForwardTube d n)
    {Λ : ComplexLorentzGroup d}
    (hΛ : complexLorentzAction Λ w ∈ PermutedForwardTube d n σ) :
    Λ ∈ permForwardOverlapIndexSet (d := d) n σ

theorem PETOrbitChamberChain.toReflTransGen
    {w : Fin n -> Fin (d + 1) -> ℂ}
    {σ : Equiv.Perm (Fin n)}
    (chain : PETOrbitChamberChain d n w σ) :
    Relation.ReflTransGen
      (petReachableLabelAdjStep (d := d) (n := n) w)
      (1 : Equiv.Perm (Fin n)) σ

noncomputable def PETOrbitChamberChain.ofReflTransGen
    {w : Fin n -> Fin (d + 1) -> ℂ}
    {σ : Equiv.Perm (Fin n)}
    (h :
      Relation.ReflTransGen
        (PETOrbitChamberAdjStep d n w)
        (1 : Equiv.Perm (Fin n)) σ) :
    PETOrbitChamberChain d n w σ
```

The theorem surfaces below are archived and rejected for theorem 2.  They are
kept only to document the old route and its failure mode: the edge relation
requires common membership in two distinct permuted forward tubes.

The following proof-local data theorem was the old mechanical consumer:

```lean
theorem hallWightman_fixedPoint_adjacentChainData_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        ∃ (m : ℕ) (τ : Fin (m + 1) -> Equiv.Perm (Fin n)),
          τ 0 = 1 ∧
          τ ⟨m, Nat.lt_succ_self m⟩ = σ ∧
          ∀ j : Fin m,
            ∃ (i : Fin n) (hi : i.val + 1 < n) (Λj : ComplexLorentzGroup d),
              τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩ =
                τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩ *
                  Equiv.swap i ⟨i.val + 1, hi⟩ ∧
              complexLorentzAction Λj w ∈
                PermutedForwardTube d n
                  (τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩) ∧
              complexLorentzAction Λj w ∈
                PermutedForwardTube d n
                  (τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩)
```

Then `petOrbitChamberChain_of_two_le` would have been the packing theorem for
that data.  This is not the theorem-2 route.

The rejected derived chamber theorem was:

```lean
theorem hallWightman_fixedPoint_endpointActiveGallery_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (hw : w ∈ ForwardTube d n)
    (σ : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (hΛ : complexLorentzAction Λ w ∈ PermutedForwardTube d n σ) :
    ∃ (m : ℕ) (α : Fin (m + 1) -> ActivePETOrbitLabel d n w),
      α 0 =
        one_mem_activePETOrbitLabel_of_forwardTube
          (d := d) (n := n) w hw ∧
      α ⟨m, Nat.lt_succ_self m⟩ =
        sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
          (d := d) (n := n) w σ Λ hΛ ∧
      ∀ j : Fin m,
        activePETOrbitAdj d n w
          (α ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩)
          (α ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩)
```

This rejected theorem would have carried the following geometry:

1. the chamber family is fixed over one base point `w`;
2. the vertices are only active labels with nonempty
   `permLambdaSlice (d := d) n σ w`;
3. an edge means an adjacent transposition plus one Lorentz transform `Λj`
   lying in both neighboring slices;
4. the endpoint witness `Λ` in the theorem-2 consumer is only used to make the
   target label active;
5. each gallery edge receives its own witness `Λj`.
6. no stronger all-active-label connectivity theorem should be confused with
   the OS I BHW theorem.

The following are explicitly insufficient as replacements:

- connectedness of `permForwardOverlapSet`, because it lets the base point
  vary;
- connectedness of a raw union of active slices, because its nerve may contain
  non-adjacent overlaps;
- an arbitrary adjacent-swap word in `Equiv.Perm (Fin n)`, because it need not
  stay in the active chamber family for the fixed `w`.

This archived packet is not the theorem-2 route.  The old consumer would have
been

```lean
BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected
```

from `PermutedTubeMonodromy.lean`.

The BHW file status must be read in two parts.

Implemented support in `PETOrbitChamberChain.lean` currently includes:

```lean
def permLambdaSlice
theorem mem_permLambdaSlice_iff
theorem permLambdaSlice_eq_orbitSet
theorem mem_petReachableLabelSet_iff_nonempty_permLambdaSlice
def ActivePETOrbitLabel
def activePETOrbitAdj
def one_mem_activePETOrbitLabel_of_forwardTube
def sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
def PETOrbitChamberAdjStep
theorem petOrbitChamberAdjStep_iff_exists_slice_overlap
theorem activePETOrbitAdj_implies_petOrbitChamberAdjStep
structure PETOrbitChamberChain
lemma mem_permForwardOverlapIndexSet_of_fixedPoint
theorem PETOrbitChamberChain.toReflTransGen
noncomputable def PETOrbitChamberChain.ofReflTransGen
```

Archived theorem surfaces that are **not** implemented by that support alone
and should not be implemented for theorem 2:

```lean
theorem hallWightman_fixedPoint_endpointActiveGallery_of_two_le
theorem hallWightman_fixedPoint_adjacentChainData_of_two_le
theorem petOrbitChamberChain_of_two_le
theorem petOrbitChamberConnected_of_two_le
```

Diagnostic-only corollary outside the current implementation gate:

```lean
theorem bhw_fixedPoint_chamberAdjacency_connected_of_two_le
```

The following archived diagnostic inventory mixes checked support with those
rejected theorem surfaces; do not read it as a compile-verified current export
list or as an implementation target:

```lean
theorem permForwardOverlap_connected_nontrivial
    [NeZero d]
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : σ ≠ 1) (hn : ¬ n <= 1) :
    IsConnected (permForwardOverlapSet (d := d) n σ)

lemma mem_permForwardOverlapIndexSet_of_fixedPoint
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {w : Fin n -> Fin (d + 1) -> ℂ}
    (hw : w ∈ ForwardTube d n)
    {Λ : ComplexLorentzGroup d}
    (hΛ : complexLorentzAction Λ w ∈ PermutedForwardTube d n σ) :
    Λ ∈ permForwardOverlapIndexSet (d := d) n σ

theorem petOrbitChamberChain_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        PETOrbitChamberChain d n w σ

theorem PETOrbitChamberChain.toReflTransGen
    {w : Fin n -> Fin (d + 1) -> ℂ}
    {σ : Equiv.Perm (Fin n)}
    (chain : PETOrbitChamberChain d n w σ) :
    Relation.ReflTransGen
      (petReachableLabelAdjStep (d := d) (n := n) w)
      (1 : Equiv.Perm (Fin n)) σ

noncomputable def PETOrbitChamberChain.ofReflTransGen
    {w : Fin n -> Fin (d + 1) -> ℂ}
    {σ : Equiv.Perm (Fin n)}
    (h :
      Relation.ReflTransGen
        (PETOrbitChamberAdjStep d n w)
        (1 : Equiv.Perm (Fin n)) σ) :
    PETOrbitChamberChain d n w σ

theorem petOrbitChamberConnected_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        Relation.ReflTransGen
          (petReachableLabelAdjStep (d := d) (n := n) w)
          (1 : Equiv.Perm (Fin n)) σ
```

Best theorem order for implementation:

```lean
def ActivePETOrbitLabel
def activePETOrbitAdj
def one_mem_activePETOrbitLabel_of_forwardTube
def sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
theorem activePETOrbitAdj_implies_petOrbitChamberAdjStep
lemma mem_permForwardOverlapIndexSet_of_fixedPoint
theorem hallWightman_fixedPoint_endpointActiveGallery_of_two_le
theorem hallWightman_fixedPoint_adjacentChainData_of_two_le
theorem petOrbitChamberChain_of_two_le
noncomputable def PETOrbitChamberChain.ofReflTransGen
theorem PETOrbitChamberChain.toReflTransGen
theorem petOrbitChamberConnected_of_two_le
```

The diagnostic corollary `bhw_fixedPoint_chamberAdjacency_connected_of_two_le`,
if a later consumer genuinely needs it, is proved after the strict packet by:

1. placing `1` and `σ` in `ActivePETOrbitLabel d n w`,
2. reading the derived finite chain data on that fixed orbit,
3. turning each adjacent active-label step into
   `PETOrbitChamberAdjStep d n w`,
4. packaging the resulting explicit chain as either
   `PETOrbitChamberChain d n w σ` or
   `Relation.ReflTransGen (PETOrbitChamberAdjStep d n w) 1 σ`.

The first theorem is the exact public wrapper over the blocker:

```lean
have hseed_conn :
    IsConnected (permOrbitSeedSet (d := d) n σ) := by
  simpa [permOrbitSeedSet] using
    blocker_isConnected_permSeedSet_nontrivial
      (d := d) n σ hσ hn
exact
  (isConnected_permOrbitSeedSet_iff_permForwardOverlapSet
    (d := d) n σ).1 hseed_conn
```

Verified status:

- this first helper is dimension-agnostic;
- it should therefore **not** carry an `_of_two_le` suffix;
- the actual dimension boundary, if any, must be justified later in the
  chamber-to-reachable-label geometry, not inserted here by naming convention.

Critical audit result:

- `permForwardOverlapSet (d := d) n σ` varies the **point** `w`;
- but theorem 2 needs geometry for one **fixed** `w` as the Lorentz transform
  varies across chambers;
- so a theorem whose only hypothesis is
  `IsConnected (permForwardOverlapSet (d := d) n σ)`
  is not yet the correct theorem surface for theorem 2.

The correct fixed-`w` chamber geometry is the slice

```lean
def permLambdaSlice
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : Fin n -> Fin (d + 1) -> ℂ) :
    Set (ComplexLorentzGroup d) :=
  {Λ : ComplexLorentzGroup d |
    complexLorentzAction Λ (permAct (d := d) σ w) ∈ ForwardTube d n}
```

with exact fixed-`w` identity

```lean
lemma mem_permLambdaSlice_iff
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (Λ : ComplexLorentzGroup d) :
    Λ ∈ permLambdaSlice (d := d) n σ w ↔
      complexLorentzAction Λ w ∈ PermutedForwardTube d n σ := by
  simpa [permLambdaSlice, PermutedForwardTube, permAct, lorentz_perm_commute]

theorem mem_petReachableLabelSet_iff_nonempty_permLambdaSlice
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (σ : Equiv.Perm (Fin n)) :
    σ ∈ petReachableLabelSet (d := d) (n := n) w ↔
      (permLambdaSlice (d := d) n σ w).Nonempty := by
  rw [mem_petReachableLabelSet_iff_exists_lorentz_mem_permutedForwardTube]
  constructor
  · rintro ⟨Λ, hΛ⟩
    exact ⟨Λ, (mem_permLambdaSlice_iff (d := d) n σ w Λ).mpr hΛ⟩
  · rintro ⟨Λ, hΛ⟩
    exact ⟨Λ, (mem_permLambdaSlice_iff (d := d) n σ w Λ).mp hΛ⟩

theorem petOrbitChamberAdjStep_iff_exists_slice_overlap
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (π ρ : Equiv.Perm (Fin n)) :
    PETOrbitChamberAdjStep d n w π ρ ↔
      ∃ (i : Fin n) (hi : i.val + 1 < n),
        ρ = π * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
        ((permLambdaSlice (d := d) n π w) ∩
          (permLambdaSlice (d := d) n ρ w)).Nonempty := by
  constructor
  · rintro ⟨i, hi, Λj, hρ, hπ, hρmem⟩
    refine ⟨i, hi, hρ, ?_⟩
    refine ⟨Λj, ?_, ?_⟩
    · exact (mem_permLambdaSlice_iff (d := d) n π w Λj).mpr hπ
    · exact (mem_permLambdaSlice_iff (d := d) n ρ w Λj).mpr hρmem
  · rintro ⟨i, hi, hρ, ⟨Λj, hπ, hρmem⟩⟩
    refine ⟨i, hi, Λj, hρ, ?_, ?_⟩
    · exact (mem_permLambdaSlice_iff (d := d) n π w Λj).mp hπ
    · exact (mem_permLambdaSlice_iff (d := d) n ρ w Λj).mp hρmem
```

This is the general-`d` analogue of the `d = 1` object `permLambdaSliceD1`.

So the theorem-2 route does **not** currently consume this fixed-`w` slice
geometry.  It consumes the distributional Euclidean/Jost-anchored BHW source branch-law
theorem, the proved source-extension assembly theorem, and the single-valued
sector-equality corollary on permuted extended-tube sectors documented in
`docs/theorem2_locality_blueprint.md`.

The checked monodromy reduction chain is:

```lean
theorem petReachableLabelSet_adjacent_connected_of_orbitChamberConnected
theorem petSectorFiber_adjacent_connected_of_reachableLabelConnected
theorem extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected
```

So theorem 2 should no longer treat any provisional theorem
`..._of_connectedForwardOverlap`, `petOrbitChamberChain_of_two_le`, or
`petOrbitChamberConnected_of_two_le` as the next implementation target.  The
next missing theorem is the distributional Euclidean/Jost-anchored source branch-law theorem
replacing
`BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`,
followed by the proved assembly theorem
`BHW.permutedExtendedTube_extension_of_forwardTube_symmetry`, the mechanical
sector equality theorem
`BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` and the
OS-specific specialization `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.

Archived implementation packet for the old blocker:

```lean
def ActivePETOrbitLabel
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :=
  {σ : Equiv.Perm (Fin n) // (permLambdaSlice (d := d) n σ w).Nonempty}

def activePETOrbitAdj
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :
    ActivePETOrbitLabel d n w -> ActivePETOrbitLabel d n w -> Prop :=
  fun a b =>
    ∃ (i : Fin n) (hi : i.val + 1 < n),
      b.1 = a.1 * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      ((permLambdaSlice (d := d) n a.1 w) ∩
        (permLambdaSlice (d := d) n b.1 w)).Nonempty

def one_mem_activePETOrbitLabel_of_forwardTube
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (hw : w ∈ ForwardTube d n) :
    ActivePETOrbitLabel d n w

def sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (σ : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (hΛ : complexLorentzAction Λ w ∈ PermutedForwardTube d n σ) :
    ActivePETOrbitLabel d n w

theorem activePETOrbitAdj_implies_petOrbitChamberAdjStep
    (w : Fin n -> Fin (d + 1) -> ℂ)
    {a b : ActivePETOrbitLabel d n w}
    (hab : activePETOrbitAdj d n w a b) :
    PETOrbitChamberAdjStep d n w a.1 b.1

```

The old candidate derived theorem
`hallWightman_fixedPoint_endpointActiveGallery_of_two_le` is archived here
only as a warning: its common-forward-tube edge is not a valid theorem-2
surface.
The theorem
`bhw_fixedPoint_chamberAdjacency_connected_of_two_le`
is outside the current implementation gate. If it is later needed as a
diagnostic corollary, it should be implemented only as the small local theorem
that:

1. uses `one_mem_activePETOrbitLabel_of_forwardTube` and
   `sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube` to place `1` and
   `σ` in the active subtype;
2. reads the derived finite chain data on that fixed orbit;
3. turns each adjacent active-label step into
   `PETOrbitChamberAdjStep d n w`;
4. packages the resulting explicit chain as either
   `PETOrbitChamberChain d n w σ` or
   `Relation.ReflTransGen (PETOrbitChamberAdjStep d n w) 1 σ`.

Checked local support already available:

1. `permLambdaSlice_eq_orbitSet` rewrites every fixed-`w` chamber slice as an
   orbit set.
2. For an active label `a`, choosing `Λa` from the slice gives a forward-tube
   witness for `permAct a.1 w`.
3. The public theorem
   `BHW.orbitSet_isPreconnected_of_forwardTube_witness`
   then gives preconnectedness of that orbit set once the usual stabilizer /
   orbit-image hypotheses are supplied.
4. This support may still be useful for a separate geometry investigation, but
   it is not the theorem-2 route unless the statements are redesigned around
   extended-tube sector membership.

The theorem-2 corollary of this section is therefore:

1. `blocker_isConnected_permSeedSet_nontrivial` is generic BHW permutation-flow
   infrastructure, not an active theorem-2 input;
2. `blocker_iterated_eow_hExtPerm_d1_nontrivial` is **not** a theorem-2 input,
   because it assumes the target locality statement in dimension one;
3. any theorem-2 proof doc or Lean file that uses monodromy must first supply a
   valid extended-tube sector-fiber theorem; the archived common-forward-tube
   gallery does not supply one;
4. the active proof doc should instead name the lower-layer BHW/PET
   single-valuedness theorem and verify that it has no locality hypothesis; in
   Lean this is the selected-witness theorem
   `bvt_F_extendF_petBranchIndependence_of_selectedAdjacentEdgeData`, whose
   remaining non-OS-field hypothesis is the explicit `hOrbit` PET
   reachable-label/connectivity statement.

Additional theorem-2 checkpoint note after local branch-pullback support:

- the file
  `OSToWightmanLocalityOS45BranchPullback.lean`
  gives a clean negative-side common-chart representation of the adjacent
  real-edge difference;
- that support is useful, but it does **not** bypass the theorem-2 consumer
  contract above;
- in particular, it does not justify replacing the BHW monodromy step by a
  naive identity theorem on a thin Wick subset.
