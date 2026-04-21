# BHW Permutation Blueprint

Purpose: this note is the implementation blueprint for the remaining BHW
permutation / overlap-connectedness lane.

It should be read together with:
- `docs/theorem2_locality_blueprint.md`,
- `docs/scv_infrastructure_blueprint.md`.

## 1. Live blocker surfaces

The still-open explicit blockers are:

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
supplier from a separate real-open edge theorem, a direct complex-edge/PET
boundary theorem, or an explicitly approved non-circular trust boundary.

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

So the remaining work is not “build the permutation theory from scratch.”
It is the two exact blockers above.

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

The later Lean implementation should proceed as:

1. prove the geometric connectedness blocker,
2. prove the `d = 1` overlap-invariance blocker,
3. close `iterated_eow_permutation_extension`,
4. then re-evaluate whether any downstream permutation theorem still needs its
   own wrapper.

### 5.1. Micro-order inside the later Lean implementation

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

## 8. What counts as implementation-ready

This blueprint should be considered ready only when:

1. the two blocker theorems are isolated,
2. the `d ≥ 2` and `d = 1` routes are clearly separated,
3. the existing proved BHW packages are treated as closed infrastructure,
4. the endgame theorem `iterated_eow_permutation_extension` has a visible
   dependency chain from the blockers.

## 9. Recommended implementation size

Rough expected size:

1. connectedness blocker (`d ≥ 2` + `d = 1` geometry): 180-260 lines,
2. `d = 1` overlap-invariance blocker: 120-180 lines,
3. endgame consumer cleanup in `PermutationFlow.lean`: 20-50 lines.

This blueprint is implementation-ready once those three chunks are treated as
the literal work units and no extra permutation wrapper theorem is inserted in
between.
