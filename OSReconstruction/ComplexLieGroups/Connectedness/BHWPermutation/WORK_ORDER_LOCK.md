# WORK_ORDER_LOCK (d=1, n=2 blocker only)

## Scope Lock
This lock file tracks only the active analytic blocker for the `d=1, n=2` route.

- Active blocker theorem:
  - `blocker_d1N2PairedChartAnchorPair_fromSource_deferred`
  - File: `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlockers/Tail.lean`
- Route lock:
  - Lorentz-invariant-function route only.
  - No translation-invariance detour.
  - No new axioms.

## Current Lean State
- The entire `OSReconstruction/ComplexLieGroups` folder compiles.
- Remaining `sorry` frontiers in this branch are concentrated in `PermutationFlowBlockers/Tail.lean`.
- Current `d=1,n=2` status:
  - `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`
    is now a clean reduction theorem (no internal `sorry`).
  - the unique remaining analytic gap is isolated in
    `blocker_d1N2PairedChartAnchorPair_fromSource_deferred`:
    for each doubly witnessed quadric tuple, prove one anchored pair equality
    `F (d1N2SectionSwap ... wA) = F (d1N2SectionOrig ... vA)`.
  - existence and FT-membership of the witness-built anchors are already proved.
  - inside that lemma, the only deferred subgoal is now explicitly:
    `F (Γ · (swap · z)) = F z` with `z ∈ FT_{1,2}` and
    `Γ · (swap · z) ∈ FT_{1,2}`, where `Γ` is constructed from equal
    swapped invariants via `d1_exists_lorentz_of_sameInvariantQuad_of_nonzeroU0V0`.
- Wrapper cleanup status:
  - removed unused paired-chart equivalence wrappers from
    `PermutationFlowBlockers/Core.lean` to keep the blocker route minimal.
  - removed additional dead forwardizable/pair-swap equivalence wrappers in
    `PermutationFlowBlockers/Core.lean` (light-cone/section/witness-form and
    source/open-anchor adapters) that had no downstream references.
  - removed unused `d=1,n=2` EOW-package adapter cluster from
    `PermutationFlowBlockers/Core.lean`.
  - removed the now-unused connected-open-anchor bridge theorem in
    `PermutationFlowBlockers/Core.lean` after confirming zero downstream uses.
  - removed dead `Tail.lean` wrappers (`invariantModel`, pointwise-anchor, and
    source-open-anchor helpers) that had no call sites.
- no change to blocker mathematics; only proof-graph pruning.
- `PermutationFlowBlockers/Core.lean` is now reduced to 658 lines.

## Canonical Reduction Chain
From current theorems in `Core/Tail`:

1. `d1N2InvariantKernelSource f`
2. target blocker:
   - light-cone witness diff-zero on invariant quadric tuples
3. exact reduction already formalized:
   - enough to prove `blocker_d1N2PairedChartAnchorPair_fromSource_deferred`
     (one anchored pair equality per doubly witnessed tuple)
   - via `d1N2PairedChartAnchorConnected_of_exists_anchorPair`, this yields
     `d1N2PairedChartAnchorConnected (Classical.choose hsource)`
4. once paired-chart anchor is obtained, the blocker follows immediately through
   `d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_of_pairedChartAnchorConnected`.

## Mathematical Content of the Blocker
For `f : C^4 -> C`, prove:

- for all `q0 q1 p s` with `s^2 = 4(p^2 - q0 q1)`,
- if both `(q0,q1,p,s)` and `(q1,q0,p,-s)` admit light-cone witnesses in `FT_{1,2}`,
- then
  - `f q0 q1 p s - f q1 q0 p (-s) = 0`.

Equivalent involution form:

- `f(q0,q1,p,s) = f(q1,q0,p,-s)`
- on the doubly-witnessed locus of the invariant quadric.

## What Is Already Settled
- Invariant factorization exists on `FT_{1,2}`.
- Forwardizable/realizable/light-cone witness reformulations are in place.
- Source-level bridge lemmas between invariant equalities and forward equalities are in place.
- Obstruction that source data alone does not force full-quadric involution (`off-image` values) is formalized in:
  - `d1N2InvariantKernelSource_not_sufficient_for_quadricDiffZero`.

## Failed Routes / Guardrails (Do Not Reopen)
- EOW geometry/open-anchor route for `d=1,n=2` is not the closure path for this blocker.
- Proof attempts requiring fixed-anchor charts (`v0 = i` or `u0 = i` globally) are too rigid.
- Full-quadric identity theorem without realizability restrictions is false under current hypotheses.

Details are recorded in:
- `D1_N2_BLOCKER_AUDIT.md`
- `D1_N2_LORENTZ_INVARIANT_ROUTE.md`

## Work Plan (Execution Order)
1. Keep active blocker statement unchanged.
2. Prove paired-chart anchor connectivity from source package on variable charts.
3. Feed it into the existing reduction theorem to close blocker.
4. Re-run:
   - `lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlockers/Tail.lean`
   - `lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlockers.lean`
   - full folder compile for `OSReconstruction/ComplexLieGroups`.

## Parallel Falsification Track (Required)
Run this in parallel with constructive proof work to avoid proving a false target.

1. Counterexample target:
   - search for `f` and a doubly light-cone-witnessed quadric tuple
     `(q0,q1,p,s)` such that
     `f q0 q1 p s - f q1 q0 p (-s) ≠ 0`
     under `d1N2InvariantKernelSource f`.
2. Candidate pruning:
   - reject off-image tuples that are not realizable/light-cone-witnessed.
   - keep all checks on the exact blocker hypotheses, not weaker surrogates.
3. If a valid counterexample is found:
   - stop closure attempt, record witness in local docs and tests,
   - restate blocker theorem accordingly.
4. If no counterexample is found:
   - continue constructive route and keep search harness tests compiling.
5. Latest heuristic sweep status (2026-03-03):
   - reproducible script:
     `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/d1n2_counterexample_search.py`
   - run A (degree 3, 500 real constraints, 1200 forwardizable tuples, 20 nullspace combos):
     - antisym basis size: 27
     - nullspace dim under sampled local-comm constraints: 13
     - max observed `|g|` on sampled forwardizable tuples: `2.18e-11`
     - violations above `1e-6`: 0
   - run B (degree 4, 1200 real constraints, 1500 forwardizable tuples):
     - antisym basis size: 56
     - nullspace dim: 0 (no nonzero sampled antisymmetric ansatz survives)
   - run C (degree 5, 2200 real constraints, 2200 forwardizable tuples):
     - antisym basis size: 106
     - nullspace dim: 0 (no nonzero sampled antisymmetric ansatz survives)
   - run D (degree 6, 3200 real constraints, 2600 forwardizable tuples):
     - antisym basis size: 180
     - nullspace dim: 0 (no nonzero sampled antisymmetric ansatz survives)
   - no sampled counterexample found.

Counterexample harness file:
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/D1N2CounterexampleSearch.lean`
  - includes formal proposition `d1N2ActiveBlockerStatement`,
    formal counterexample predicate, and lemma
    `d1N2ActiveCounterexample_implies_not_statement`.

Proof-harness test files:
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/D1N2ReductionChain.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/D1N2SectionInvariants.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/D1N2ObstructionChecks.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/D1N2LocalAnchorTransport.lean`

## Notes for Collaborators
- This file intentionally omits d>=2 and n>=3 planning.
- If adding new docs, include only material directly tied to proving the active blocker or documenting a failed d=1,n=2 attempt/counterexample.
