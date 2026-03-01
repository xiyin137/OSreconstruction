# d=1, n>=4 Forward-Triple Blocker: Linear Reduction Notes

This note targets the remaining theorem:

- `deferred_d1_forward_triple_nonempty_nge4`

in `PermutationFlow.lean`.

## Goal Restatement

For fixed `n >= 4`, adjacent `tau = swap(i,i+1)`, and nontrivial `sigma`,
construct:

- `w in ForwardTube 1 n`,
- `tau·w in ExtendedTube 1 n`,
- `sigma·w in ExtendedTube 1 n`.

## High-Leverage Ansatz

Use witnesses in the restricted form

- `w_k^0 = i T_k` (time component),
- `w_k^1 = R_k` (space component),

with real arrays `T, R : Fin n -> R`.

Then FT for `w` is exactly:

- `T_0 > 0`,
- `T_k - T_{k-1} > 0` for all `k>0`.

## Pure-Imaginary Rapidity Reduction

For rapidity `theta = i b` in `d=1`:

- `cosh(i b) = cos b`,
- `sinh(i b) = i sin b`.

Applied to one step `(i DeltaT, DeltaR)`:

- transformed step time-imaginary part:
  - `Im((Lambda_b Deltaw)_0) = cos b * DeltaT + sin b * DeltaR`,
- transformed step space-imaginary part:
  - `Im((Lambda_b Deltaw)_1) = 0`.

So forward-cone condition is equivalent to one scalar inequality per step:

- `cos b * DeltaT + sin b * DeltaR > 0`.

If `cos b != 0` and `lambda = tan b`, this is:

- `DeltaT + lambda DeltaR > 0`.

Hence ET-membership for a permuted witness `pi·w` is reduced to finite strict
linear inequalities in step differences of `(T,R)` for some `lambda`.

## Rational 3-4-5 Specialization

Using fixed `b` with `(cos b, sin b) = (4/5, ±3/5)`:

- plus branch: `4 DeltaT + 3 DeltaR > 0`,
- minus branch: `4 DeltaT - 3 DeltaR > 0`.

This removes transcendental constants and keeps all inequalities rational.

## Step Data Notation for a Permutation `pi`

Define permuted step differences:

- first step (`k=0`):
  - `DeltaT_pi(0) = T_{pi(0)}`
  - `DeltaR_pi(0) = R_{pi(0)}`
- subsequent steps (`k>0`):
  - `DeltaT_pi(k) = T_{pi(k)} - T_{pi(k-1)}`
  - `DeltaR_pi(k) = R_{pi(k)} - R_{pi(k-1)}`.

Then ET test for `pi·w` under a chosen branch/sign is exactly positivity of the
corresponding linear form on each `k`.

## What This Buys

The remaining geometric problem becomes:

1. choose `T` with FT-positive identity steps,
2. choose `R`,
3. prove two finite linear-positivity systems simultaneously:
   - one for `tau`,
   - one for `sigma`.

No ET decomposition or Lorentz-orbit search remains at this level.

## Suggested Lean Architecture

1. Add a small helper file (or private section) with:
   - `d1LinearWitness T R`,
   - explicit `3-4-5` boost matrices (`+` and `-`),
   - lemmas:
     - FT of `d1LinearWitness` from `T`-step positivity,
     - ET of `pi·d1LinearWitness` from linear step positivity.

2. Refactor `deferred_d1_forward_triple_nonempty_nge4` to reduce to a pure
   real-inequality existence theorem:
   - `deferred_exists_TR_for_tau_sigma_linearPos_nge4`.

3. Attack that reduced theorem combinatorially.

## Explicit Two-Branch Construction Candidate (New)

The LP pattern can be turned into a closed-form witness template that avoids
search over `(T,R)`:

1. Define a sigma-rank profile:

- `rank_sigma(k) := (sigma^{-1}(k)).val`.
- `B_k := 2 * (rank_sigma(k) + 1)`.

Then along sigma-order:

- `B_{sigma(0)} = 2 > 0`,
- `B_{sigma(m)} - B_{sigma(m-1)} = 2 > 0`.

So sigma-side positivity is automatic once the boost reads off the linear form
`B`.

2. Define an adjacent-swap profile `A` with one controlled negative natural step:

- `M := 2 * n`,
- `A_k := 2*n + M*k - (if i+1 <= k then M+1 else 0)`.

Natural increments:

- `A_k - A_{k-1} = M` for `k != i+1`,
- `A_{i+1} - A_i = -1`.

But along tau-order (`tau = swap(i,i+1)`), all required step differences are
strictly positive:

- regular steps: `M`,
- two crossing steps near the swap: `M-1`,
- swapped edge: `1`.

Hence tau-side positivity is encoded by `A`.

3. Realize `(A,B)` as Lorentz linear forms of `(T,R)` branchwise:

Use fixed rational 3-4-5 boosts:

- tau boost: linear form `4T + 3R` (matrix with entries `4/5`, `3i/5`),
- sigma boost plus branch: `3T + 4R`,
- sigma boost minus branch: `3T - 4R`.

Branch on rank order of `i, i+1` in `sigma^{-1}`:

- if `rank_sigma(i) > rank_sigma(i+1)`, use plus branch (`3T + 4R = B`),
- else use minus branch (`3T - 4R = B`).

Closed forms:

- plus branch:
  - `T = (4A - 3B)/7`,
  - `R = (4B - 3A)/7`.
- minus branch:
  - `T = (4A + 3B)/25`,
  - `R = (3A - 4B)/25`.

In both branches:

- `4T + 3R = A` (tau boost reads `A`),
- sigma boost reads `B`.

4. Why FT for `w=(iT,R)` is plausible with this template:

Natural `T` increments become affine combinations of `A` and `B` increments.
With `M=2n` and `B` built from rank differences (bounded by `2(n-1)`), all
non-special natural steps are positive by crude bounds.
At the special edge `k=i+1`, branch sign and the scale factor `2` in `B` force
strict positivity:

- plus branch uses `B_{i+1} - B_i <= -2`,
- minus branch uses `B_{i+1} - B_i >= 2`.

This is exactly where the LP branch condition appears.

## Lean Status of This Construction (2026-03-01)

Arithmetic core for this template has been validated in scratch:

- rank-based `B` difference bounds (`|Delta B| <= 2*(n-1)`),
- special-edge sign lemmas (`Delta B_{i+1}` has branch-dependent sign, with
  gap at least `2`),
- explicit `A` increment formula with single negative natural jump.

Remaining formal work is mostly normalization of `ForwardTube` goals after
applying the fixed boosts (i.e. reducing the cone inequalities to the already
proved `A/B` positivity statements in a clean reusable lemma).

Production update:

- the rank/arithmetic core has now been split into
  `D1Nge4LinearWitness.lean` (`d1Nge4_*` rank/A/B/T/R lemmas),
- `PermutationFlow.lean` keeps the `n>=4` geometric blocker theorem and imports
  this helper module.

## New Lean Progress (2026-03-01, later session)

Additional arithmetic infrastructure now in production
`D1Nge4LinearWitness.lean`:

- sigma-profile arithmetic:
  - `d1Nge4_B_at_sigma`
  - `d1Nge4_B_sigma_step_pos`
  - `d1Nge4_B_sigma_zero_pos`
  - `d1Nge4_B_bounds`
- branchwise closed-form witness functions:
  - `d1Nge4_Tplus`, `d1Nge4_Rplus`
  - `d1Nge4_Tminus`, `d1Nge4_Rminus`
  - with identities:
    - plus: `4T+3R=A`, `3T+4R=B`
    - minus: `4T+3R=A`, `3T-4R=B`
Interpretation:

- arithmetic reduction for the two branches is now reusable and isolated;
- remaining work in `deferred_d1_forward_triple_nonempty_nge4` is geometric
  witness assembly from these inequalities (FT/ET side conditions).

## Known Risk

Low-budget random search is not reliable in `n=4`:

- broad scans miss many cases,
- targeted dense scans recover some misses.

So this should be treated as a constructive inequality problem, not as
"random witness likely exists/doesn't exist".

## Empirical LP Feasibility (2026-03-01)

Non-formal but strong computational evidence with exact linear programming
(`scipy.optimize.linprog`, strict inequalities enforced as `>= 1` after scaling):

- exhaustive `n=4` over all nontrivial `(i, sigma)`:
  - feasible for all cases with lambda search on a small finite grid.
- exhaustive `n=5` over all nontrivial `(i, sigma)`:
  - feasible for all cases with the same finite lambda grid.
- random stress tests for `n=6..10`:
  - all sampled nontrivial cases feasible.

Notably, the LP data suggests a simplification:

- fixing `lambda_tau = 1` (so tau-side inequalities are just positivity of
  step differences of `T+R`), and searching only `lambda_sigma`, still appears
  feasible in all tested cases (`n=4..10` random, `n=5` exhaustive).
- exhaustive small-`n` data shows a sharper pattern:
  - `lambda_sigma` seems to need only two values, `{3/2, -2}`,
  - branch appears controlled by the relative order of `i` and `i+1` in
    `sigma` (positions in `sigma^{-1}`).

This points to a plausible proof architecture:

1. encode `tau` branch via monotonicity of one auxiliary sequence (`T+R`),
2. solve `sigma` branch by choosing a second parameter `lambda_sigma`,
3. keep FT by strict positivity of `T` identity steps.

Formal proof remains open, but this is now a sharply defined target.

Repro script added:

- `scripts/d1_linear_witness_lp.py`

This script checks feasibility of the reduced linear system and emits candidate
`(lambda_tau, lambda_sigma, T, R)` data for concrete instances.

Companion result snapshot:

- `D1_NGE4_LP_RESULTS.md`.
