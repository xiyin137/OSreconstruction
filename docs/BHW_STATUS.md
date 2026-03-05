# BHW Status (Canonical)

Last updated: 2026-03-05

This file is the canonical root/docs status for the Bargmann-Hall-Wightman
connectedness/permutation blocker path.

## Active Blockers

Current `ComplexLieGroups` blocker `sorry`s are isolated in:

1. `Connectedness/BHWPermutation/PermutationFlowBlocker.lean`
   - `blocker_isConnected_permSeedSet_nontrivial`
   - `blocker_iterated_eow_hExtPerm_d1_nontrivial`

These are the only remaining direct `sorry` lines under
`OSReconstruction/ComplexLieGroups`.

## Current Branch Split in `PermutationFlow`

In `iterated_eow_permutation_extension` nontrivial branch (`σ ≠ 1`, `n ≥ 2`):

1. `d = 0`: discharged by contradiction.
2. `d ≥ 2`: implemented via Jost witness + connectedness route
   (depends on `blocker_isConnected_permSeedSet_nontrivial`).
3. `d = 1`: deferred via
   `blocker_iterated_eow_hExtPerm_d1_nontrivial`.

## Where to Read Next

1. Root execution plan:
   - `docs/development_plan_systematic.md`
2. Local BHWPermutation status:
   - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/BLOCKER_STATUS.md`
