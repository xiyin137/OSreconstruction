# d=1 Left-Adj Scheme Inputs: Precise Remaining Obligations

This note documents the exact mathematical content of:

- `deferred_d1_leftAdjSwap_scheme_inputs`
  in `PermutationFlow.lean`.

The theorem is currently the third active deferred item (the other two are seed-set
connectedness deferreds).

Implementation note:

- the trivial regime `n ≤ 1` is now fully discharged in code (both obligations
  are vacuous since there are no adjacent indices `i` with `i+1<n`).
- the remaining blocker content is exactly the nontrivial regime `n ≥ 2`.

## Statement Shape

For fixed `n, F` and standard hypotheses on `F`, the theorem asks for:

1. `hSwap`:
   For each adjacent swap `τ = swap(i,i+1)`,
   for all `z`,
   if `z ∈ ET` and `τ·z ∈ ET`, then
   `extendF(τ·z) = extendF(z)`.

2. `hAnchor`:
   For each permutation `σ` and adjacent swap `τ = swap(i,i+1)`,
   the step-anchor set
   `{ z | z ∈ D_(τ*σ) ∧ τ·z ∈ ET }`
   is nonempty.

Then `extendF`-invariance on ET-overlap for arbitrary `σ` is closed by
`extendF_perm_overlap_d1_of_leftAdjSwap_scheme_inputs`.

## Why This Is Not "Just Connectedness"

Connectedness of overlap domains is already packaged elsewhere and can be deferred
cleanly. The remaining issues are not automatic consequences:

- `hSwap` is a global adjacent-swap ET-overlap equality statement.
  Existing `Adjacency` routes that pass through a real-open anchor require a real
  spacelike overlap witness. In `d=1`, this witness is not currently available in
  production infrastructure.

- `hAnchor` is a step-anchor nonemptiness statement.
  Pairwise adjacent-sector overlap nonemptiness does not immediately imply this.

So these are independent geometric/analytic obligations in the current code.

## Known Formal Reductions Already in `PermutationFlow.lean`

- Triple witness <-> left-step anchor:
  - `leftAdj_anchor_nonempty_of_ET_triple`
  - `ET_triple_nonempty_of_leftAdj_anchor`

This means downstream induction plumbing is complete: once either formulation is
provided, the other is automatic.

## Immediate Engineering Consequence

The current blocker is best treated as two explicit workstreams:

1. A `d=1` adjacent-swap ET-overlap invariance route (`hSwap`) that does not rely
   on unavailable real-open witness assumptions.
2. A geometric step-anchor nonemptiness route (`hAnchor`) for `(σ, τ)`.

Until both are provided, the scheme route cannot close the final d=1 bridge.

## New Formal Checks (2026-03-01)

The following points are now concretely checked in `test/`:

- `test/witness_test.lean` compiles and gives an explicit **positive** witness in
  `d=1, n=2`:
  - `overlapWitness ∈ ForwardTube 1 2`,
  - `swap · overlapWitness ∈ ExtendedTube 1 2`.
  This confirms adjacent overlap nonemptiness in a concrete case, but it is
  **not** a counterexample to the global blocker.

- `test/proofideas_ih_composition.lean` compiles with one remaining `sorry`:
  `route_B_counterexample_statement`. Its Part 1/2/3 infrastructure typechecks
  (IH-to-`extendF`, composition, openness).

- Old midpoint-route assumptions are formally contradicted in:
  `test/midpoint_route_vacuous_test.lean` and
  `test/midpoint_condition_d1_counterexample_test.lean`.
  So midpoint-implication style closure should not be reused as a primary d=1 route.

- In `PermutationFlow.lean`, the `hAnchor` subgoal now has its `σ = 1` branch
  discharged directly via `leftAdj_anchor_nonempty_base`; only the
  nontrivial-`σ` branch remains deferred.

## Why Existing Adjacency Wrapper Is Not Enough in d=1

There is already a theorem
`extendF_adjSwap_eq_of_connected_forwardOverlap` in `Adjacency.lean`, but it
requires an explicit real spacelike witness `x0` with both:

- `realEmbed x0 ∈ ET`,
- `realEmbed (swap · x0) ∈ ET`.

In `d=1`, current infrastructure does not provide that witness for general
`n`, and the existing `d≥2` wrapper
`extendF_adjSwap_eq_of_connected_forwardOverlap_hd2` is explicitly dimension
restricted.

So deriving `hSwap` from that wrapper in `d=1` currently fails at witness
construction, not at connectedness plumbing.

## Heuristic Sanity Check (Numerical, Non-Formal)

A coarse external numerical search in `d=1, n=3` (sampling random complex
configurations and random complex rapidities) repeatedly found:

- nonempty anchor/triple for `σ = 1` and `σ = swap(0,1)`,
- no witness found for `σ = swap(1,2)`, `swap(0,2)`, and 3-cycles.

This is not a proof, but it is a warning sign that the current global
step-anchor requirement may be too strong as an induction input.

Practical consequence:

- before investing in heavy Lean proof search for the anchor package, verify the
  exact geometric truth of this `d=1` step-anchor condition for `n ≥ 3`.
