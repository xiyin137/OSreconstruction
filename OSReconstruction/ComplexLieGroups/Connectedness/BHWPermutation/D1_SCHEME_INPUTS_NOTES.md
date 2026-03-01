# d=1 Left-Adj Scheme Inputs: Precise Remaining Obligations

This note documents the exact mathematical content of the `d=1` scheme-input
block used by `PermutationFlow.lean` (with bridge reductions now extracted to
`LeftAdjAnchorBridge.lean`).

Companion note for the `n>=4` branch:

- `D1_NGE4_LINEAR_REDUCTION_NOTES.md` (same folder).

Current active deferred declarations in this block are:

- `deferred_d1_adjSwap_forward_open_anchor`
- `deferred_d1_forward_triple_nonempty_nontrivial`

The ET-form wrapper
`deferred_d1_ET_triple_nonempty_nontrivial` is now proved from this forward
form via `ET_triple_nonempty_iff_forward_triple_nonempty`.

The wrapper theorem `deferred_d1_leftAdjSwap_scheme_inputs` is now proved by
pairing those two inputs, so the blocker shape is explicit and minimal.

## Status Update (2026-03-01, `n=3, i=0` constructive branch landed)

New production witness infrastructure:

- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/D1N3Witnesses.lean`

New proved exports:

- `d1_n3_forward_triple_nonempty_i0_pairA`
- `d1_n3_forward_triple_nonempty_i0_pairB`
- `d1_n3_forward_triple_nonempty_i1_pairA`
- `d1_n3_forward_triple_nonempty_i1_pairB`

These two theorems cover all four nontrivial `σ` for `n=3` with adjacent
`τ = swap(0,1)`. They are now wired into
`deferred_d1_forward_triple_nonempty_nontrivial` in `PermutationFlow.lean`.

Practical consequence:

- the `n=3, i=0` sub-branch of
  `deferred_d1_forward_triple_nonempty_nontrivial` is no longer deferred.
- the full `n=3` branch of
  `deferred_d1_forward_triple_nonempty_nontrivial` is now constructive.
- remaining deferred geometry inside that theorem is now narrowed to:
  - `n≥4` only, isolated as
    `deferred_d1_forward_triple_nonempty_nge4`.

## Statement Shape

For fixed `n, F` and standard hypotheses on `F`, the block asks for:

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

Then ET-overlap permutation invariance is closed by:

- `extendF_perm_overlap_d1_of_leftAdjSwap_scheme_inputs`.

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

## Known Formal Reductions Already in `LeftAdjAnchorBridge.lean`

- Triple witness <-> left-step anchor:
  - `leftAdj_anchor_nonempty_of_ET_triple`
  - `ET_triple_nonempty_of_leftAdj_anchor`

- ET-triple witness <-> forward-triple witness (`d=1`):
  - `ET_triple_nonempty_iff_forward_triple_nonempty`

  So the hard geometric target in
  `deferred_d1_ET_triple_nonempty_nontrivial` is now normalized to:

  - `∃ w, w ∈ FT ∧ (swap·w) ∈ ET ∧ (σ·w) ∈ ET`.

This means downstream induction plumbing is complete: once either formulation is
provided, the other is automatic.

## Immediate Engineering Consequence

Treat the remaining work as two independent geometric workstreams:

1. close `deferred_d1_adjSwap_forward_open_anchor`,
2. close `deferred_d1_ET_triple_nonempty_nontrivial`.

The second item is now explicitly reduced (in Lean code) to finding a forward
triple witness as above.

Connectedness deferreds are separate and no longer mixed into this block.

## New Formal Checks (2026-03-01)

The following points are now concretely checked in `test/`:

- `test/witness_test.lean` compiles and gives an explicit **positive** witness in
  `d=1, n=2`:
  - `overlapWitness ∈ ForwardTube 1 2`,
  - `swap · overlapWitness ∈ ExtendedTube 1 2`.
  This confirms adjacent overlap nonemptiness in a concrete case, but it is
  **not** a counterexample to the global blocker.

- `test/proofideas_ih_composition.lean` compiles with no `sorry`.
  In particular, `route_B_counterexample_statement` is now a complete formal
  theorem showing `swap⁻¹·FT ⊄ ET` in `d=1` (pure-imaginary witness), while
  Part 1/2/3 IH-composition infrastructure typechecks.
  (IH-to-`extendF`, composition, openness).

- `test/proofideas_hswap_d1.lean` now compiles error-free with warning-only
  `sorry`s.
  Its current value is diagnostic:
  - it confirms several d=1 orbit calculations and a concrete `n=2` overlap
    witness pattern,
  - but it does not currently provide a production-ready proof of `hSwap`
    without adding assumptions (notably translation invariance).
  So it should be treated as idea scaffolding, not as a drop-in replacement for
  the mainline blocker.

- Old midpoint-route assumptions are formally contradicted in:
  `test/midpoint_route_vacuous_test.lean` and
  `test/midpoint_condition_d1_counterexample_test.lean`.
  So midpoint-implication style closure should not be reused as a primary d=1 route.

- `test/d1_no_real_witness_adjacent_general_test.lean` compiles with theorem
  `no_real_et_pair_swap_adjacent_d1_iPos`, formalizing:
  for adjacent `swap(i,i+1)` with `i.val ≠ 0`, there is no real configuration
  `x` with both `realEmbed x ∈ ET` and `realEmbed (swap·x) ∈ ET`.
  This is evidence that real-witness routes are over-strong in `d=1`.

- In `PermutationFlow.lean`, branch-level `hSwap`/`hAnchor` casework was removed
  from the scheme theorem and replaced by two explicit deferred declarations:
  `deferred_d1_adjSwap_forward_open_anchor` and
  `deferred_d1_ET_triple_nonempty_nontrivial`.

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

Implementation status (2026-03-01 update):

- `hSwap` is now proved in `PermutationFlow.lean` from:
  - connected forward-overlap transfer, and
  - one deferred nonempty forward-open-anchor input:
    `deferred_d1_adjSwap_forward_open_anchor`,
  then converted to ET-overlap open anchor by `extendF(w)=F(w)` on `FT`.
- the anchor side is reduced to one nontrivial deferred triple-witness lemma:
  `deferred_d1_ET_triple_nonempty_nontrivial`.

## EOW Infrastructure Status

The EOW infrastructure used in this area is already fully proven and available.
The blocker is not an unproved EOW lemma.

What fails is the midpoint-implication route in `d=1`:

- `test/midpoint_condition_d1_counterexample_test.lean` and
  `test/midpoint_route_vacuous_test.lean` provide formal counterexamples to the
  midpoint implication used by the old route.

So `hSwap` needs a non-midpoint closure route.

## Why EOW Alone Still Does Not Close `hSwap` in d=1

For adjacent swaps in `d=1`, the set

- `{ z | z ∈ FT ∧ swap·z ∈ FT }`

is empty (formalized in the midpoint counterexample tests via the adjacent-swap
FT obstruction). So there is no open region where direct EOW swap equality can
be anchored in the usual `FT ∩ swap⁻¹(FT)` way.

Equivalent reformulation:

- there is no pair `(w, Γ)` with `w ∈ FT`, `Γ·w ∈ FT`, and `Γ·(swap·w) ∈ FT`
  simultaneously (otherwise `z := Γ·w` and `swap·z = Γ·(swap·w)` would give a
  forbidden point in `FT ∩ swap⁻¹(FT)`).

So any successful `hSwap` proof must use a genuinely different anchor mechanism
than "apply EOW on a common FT overlap".

## Heuristic Sanity Check (Numerical, Non-Formal)

Updated random search (`d=1, n=3`) over complex configurations plus random
complex rapidities found explicit triple witnesses for all nontrivial tested
`(τ, σ)` pairs (with `τ` adjacent and `σ ≠ 1, τ`), including the previously
hard cases.

One explicit hard-case sample (`n=3`, `τ=(1,0,2)`, `σ=(2,1,0)`):

- witness `w`:
  - `w0 = (-5.34880039 + 1.85022413 i, -6.25977385 + 0.29854371 i)`
  - `w1 = (-1.06291772 + 4.55650344 i,  2.30762791 + 1.71591668 i)`
  - `w2 = (-3.05281942 + 7.50313545 i,  7.59363519 + 0.59244186 i)`
- `w ∈ FT` (checked numerically),
- `τ·w ∈ ET` witnessed by rapidity `θτ = -4 - 0.3403392041 i`,
- `σ·w ∈ ET` witnessed by rapidity `θσ = -4 - 0.5628686838 i`.

This is non-formal but gives a concrete target for any future explicit Lean
construction in the `n=3` subcase.

Update: this hard case now has a fully formal explicit witness in
`test/d1_forward_triple_witness_n3.lean`:

- theorem `witness3_forward_triple_hard_case` proves
  `w ∈ FT`, `τ·w ∈ ET`, `σ·w ∈ ET` for that `(n, τ, σ)` pair using rational
  complex Lorentz matrices.

Additional constructive data for all nontrivial `n=3` `(i,σ)` pairs is now
documented in:

- `D1_N3_FORWARD_TRIPLE_WITNESSES.md`

Typical hit counts in one run:

- `τ = swap(0,1)`: all nontrivial `σ` found (hardest at ~1736 samples),
- `τ = swap(1,2)`: all nontrivial `σ` found (hardest at ~16059 samples).

This is still not a proof, but it supports treating the triple-witness goal as
plausibly true and worth formalizing directly.

Additional `n=4` stress test (same style, reduced-budget sampling) gave mixed
results: several `(τ, σ)` cases were found quickly, but many sampled pairs had
no witness found within budget.

This is also non-formal, but it is a warning that the current global
left-adjacent anchor requirement may be significantly stronger than it first
appears for larger `n`.

Practical consequence (unchanged):

- before investing in heavy Lean proof search for the anchor package, verify the
  exact geometric truth of this `d=1` step-anchor condition for `n ≥ 3`.

## Additional Probe Update (2026-03-01, real-witness route)

`test/proofideas_hswap_d1.lean` currently compiles with warning-only `sorry`s,
but still has five unresolved proof declarations:

- `reducedW_independent_of_base`
- `reducedW_complex_lorentz_invariant`
- `hSwap_n2_d1_with_translation`
- `F_eq_of_lorentz_related_diff`

Update (same day): `diff_of_swap_lorentz` is now proved in that test file.
So this list is down to four unresolved declarations.

So this file remains idea scaffolding, not production infrastructure.

Separately, a bounded non-formal random search over real `d=1, n=3` samples
(`i=1` adjacent swap branch) with random complex rapidities found no example of:

- `x ∈ ET`,
- `swap(i,i+1)·x ∈ ET`,
- and spacelike separation at the swapped pair.

This is not a proof, but it is further evidence that the current real-witness
package used by `extendF_adjSwap_eq_of_connected_forwardOverlap` is likely
over-strong for the `d=1` branch, not just at `n=2`.

Recommended interpretation:

- keep connectedness obligations deferred as planned,
- treat the remaining `d=1` adjacent-swap closure as a complex-anchor/gluing
  task rather than a real-witness construction task.

## New Structural Insight (2026-03-01, linearized witness ansatz)

For future attacks on
`deferred_d1_forward_triple_nonempty_nge4`,
the following explicit `d=1` reduction is useful.

### Ansatz

Take witnesses of the form

- `w_k^0 = i T_k` (pure-imaginary time),
- `w_k^1 = R_k` (real space),

with real arrays `T, R`.

Then:

- `w ∈ FT` is equivalent to strict positivity of the `T`-steps:
  - `T_0 > 0`,
  - `T_k - T_{k-1} > 0` for `k > 0`.

### Pure-imaginary rapidity action becomes linear inequalities

For rapidity `θ = i b` in `d=1`,

- `cosh(i b) = cos b`,
- `sinh(i b) = i sin b`.

On the above ansatz, the transformed step imaginary-time is:

- `Im( (Λ_b · Δw)_0 ) = cos b * ΔT + sin b * ΔR`.

The transformed step spatial imaginary part vanishes in this ansatz, so
the cone condition reduces to:

- `cos b * ΔT + sin b * ΔR > 0` at each step.

Equivalently (for `cos b ≠ 0`, with `λ = tan b`):

- `ΔT + λ ΔR > 0` at each step.

So ET-membership of a permuted witness `π·w` can be tested by a finite system
of strict linear inequalities in step data of `(T, R)`.

### Rational 3-4-5 boosts

Using fixed boosts with `(cos b, sin b) = (4/5, ±3/5)`, the conditions become:

- plus branch: `4 ΔT + 3 ΔR > 0`,
- minus branch: `4 ΔT - 3 ΔR > 0`.

This avoids trigonometric constants and reduces each ET check to rational linear
inequalities.

### Why this matters

This converts the `n≥4` geometric witness problem into an explicit finite
real-inequality feasibility problem parameterized by `(n, i, σ)`, which is
substantially closer to a combinatorial construction than direct ET reasoning.

Current status:

- the full Lean infrastructure for this linearization was started but not yet
  landed in production (the reduction equations above are the stable part).
- this should be the next concrete proof-engineering route if we continue
  attacking the remaining `n≥4` branch directly.
- empirical LP feasibility checks (non-formal) are strong:
  - exhaustive `n=4` and `n=5` cases are feasible under this reduction,
  - random `n=6..10` samples are also feasible.
  See `D1_NGE4_LINEAR_REDUCTION_NOTES.md` for details.
