# BHW Permutation Blocker Status

This is the consolidated status note for the active blocker in
`BHWPermutation/PermutationFlow.lean`.

## Current Proof Split

In `iterated_eow_permutation_extension`, the nontrivial branch
(`σ ≠ 1`, `n ≥ 2`) now splits as:

1. `d = 0`: discharged by contradiction (`σ = 1` forced by ET-overlap in `d=0`).
2. `d ≥ 2`: reduced and wired through existing geometric/analytic infrastructure.
3. `d = 1`: still deferred through a dedicated blocker theorem.

Reference:
- `PermutationFlow.lean` around the `hExtPerm` construction
  (`~2231-2273` in current file).

## Active Deferred Lemmas

All current `sorry` dependence for this blocker is isolated in:

1. `blocker_isConnected_permSeedSet_nontrivial`
   in `PermutationFlowBlocker.lean`
   - statement: connectedness of `permSeedSet` for `σ ≠ 1`, `n ≥ 2`
   - used as shared connectivity input in both `d ≥ 2` and `d = 1` nontrivial branches.

2. `blocker_iterated_eow_hExtPerm_d1_nontrivial`
   in `PermutationFlowBlocker.lean`
   - statement: ET-overlap permutation invariance of `extendF` for `d=1`
   - used as the explicit deferred `d=1` bridge.

## What Is Closed vs Deferred

Closed in code:
- The `d ≥ 2` branch of the nontrivial `hExtPerm` path is now implemented:
  - uses `jostWitness_exists`,
  - converts seed connectedness to forward-overlap connectedness,
  - applies `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`.

Deferred:
- the shared seed connectedness blocker,
- the `d=1` overlap-invariance blocker.

Use this file for current local status and line-level orientation, with
`docs/BHW_STATUS.md` as the root canonical summary.
