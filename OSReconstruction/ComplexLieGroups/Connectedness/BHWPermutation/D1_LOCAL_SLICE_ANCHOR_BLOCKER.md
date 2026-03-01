# d=1 Local Slice-Anchor Blocker

Last updated: 2026-03-01

This note records the exact remaining local blocker after refactoring
`deferred_d1_adjSwap_forward_open_anchor`.

## Active theorem

In
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlockers.lean`,
the remaining local `d=1` non-connective deferred theorem is:

- `deferred_eventually_slice_anchor_on_prepared_nhds_d1`

It asks for:

- fixed `τ`, `w0`, `Γ`, open `U`,
- prepared-domain condition
  `w ∈ U -> (w ∈ Ωτ and Γ·(τ·w) ∈ FT)`,
- conclusion:
  near `w0`, each prepared `w` admits some slice anchor `Λ₀` with
  `Λ₀·(τ·w) ∈ FT` and `F(Λ₀·(τ·w)) = F(w)`.

Current reductions already proved in code:

- if `τ = 1`, the theorem is fully proved (choose `Λ₀ = 1`);
- if `n ≤ 1`, the non-identity `τ` branch is impossible.

So the true deferred content is the nontrivial branch `n ≥ 2` and `τ ≠ 1`.

In code this is now isolated as:

- `blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial`
  in `PermutationFlowBlockers.lean`.

## Why this is now the right granularity

`PermutationFlow.lean` now proves wrappers reducing to this blocker module:

- `deferred_eventually_forward_eq_on_prepared_nhds_d1`
  from the above theorem via the existing proved propagation lemma
  `eventually_forward_eq_nhds_of_eventually_slice_anchor_d1`.
- `deferred_d1_adjSwap_forward_open_anchor` from that eventual forward equality.

So the old large wrapper blocker is reduced to one explicit local slice-anchor
input.

## Dependency chain

`deferred_eventually_slice_anchor_on_prepared_nhds_d1`
-> `deferred_eventually_forward_eq_on_prepared_nhds_d1`
-> `deferred_d1_adjSwap_forward_open_anchor`
-> `deferred_d1_adjSwap_open_anchor`
-> `deferred_d1_adjSwap_extendF_overlap`
-> `deferred_d1_leftAdjSwap_scheme_inputs`
-> `deferred_extendF_perm_overlap_d1_of_seedConnected`

## Current warning set

`PermutationFlow.lean` currently reports exactly:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_eventually_slice_anchor_on_prepared_nhds_d1`
4. `deferred_d1_forward_triple_nonempty_nge4`

## Suggested small-n attack order

1. Prove `n=2` specialized slice-anchor local theorem.
2. Prove `n=3` specialized slice-anchor local theorem.
3. Abstract common mechanism into general `n` theorem.

Keep midpoint routes disabled (known formal counterexamples in test files).
Use the already-proved EOW infrastructure only through prepared-domain
interfaces.
