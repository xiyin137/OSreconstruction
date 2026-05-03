# BHW Status (Canonical)

Last updated: 2026-04-19

This file is the canonical root/docs status for the Bargmann-Hall-Wightman
connectedness/permutation blocker path.

## Active Blockers

Current `ComplexLieGroups` blocker `sorry`s are isolated in:

1. `Connectedness/BHWPermutation/PermutationFlowBlocker.lean`
   - direct `sorry`: `blocker_isConnected_permSeedSet_nontrivial`
   - direct `sorry`: `blocker_iterated_eow_hExtPerm_d1_nontrivial`

These are the only remaining direct `sorry` lines under
`OSReconstruction/ComplexLieGroups`.

## Current Branch Split in `PermutationFlow`

In `iterated_eow_permutation_extension` nontrivial branch (`σ ≠ 1`, `n ≥ 2`):

1. `d = 0`: discharged by contradiction.
2. `d ≥ 2`: implemented via Jost witness + connectedness route
   (depends on `blocker_isConnected_permSeedSet_nontrivial`).
3. `d = 1`: deferred via
   `blocker_iterated_eow_hExtPerm_d1_nontrivial`.

The two declarations in `PermutationFlowBlocker.lean` are validated deferred
BHW/permutation-flow theorem surfaces, with numerical diagnostics recorded in
their production docstrings.  They should not be treated as casual placeholders.

They also should not be repurposed as the non-circular OS theorem-2 supplier.
In particular, `blocker_iterated_eow_hExtPerm_d1_nontrivial` assumes
`hF_local_dist : IsLocallyCommutativeWeak 1 W`; using it to prove
`IsLocallyCommutativeWeak 1 (bvt_W OS lgc)` would be circular.  The OS §4.5
route therefore needs a separate dimension-one real-open edge theorem or a
direct dimension-one complex-edge boundary/PET theorem, as documented in
`docs/theorem2_locality_blueprint.md`.

## Where to Read Next

1. Root execution plan:
   - `docs/development_plan_systematic.md`
2. Local BHWPermutation status:
   - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/BLOCKER_STATUS.md`
