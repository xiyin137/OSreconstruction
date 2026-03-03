# WORK_ORDER_LOCK (d=1, n=2 blocker only)

## Scope Lock
This lock file tracks only the active analytic blocker for the `d=1, n=2` route.

- Active blocker theorem:
  - `blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred`
  - File: `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlockers/Tail.lean`
- Route lock:
  - Lorentz-invariant-function route only.
  - No translation-invariance detour.
  - No new axioms.

## Invariant-Only Statement Lock (2026-03-03)
- The deferred core blocker must be stated only for the invariant kernel
  `f(q0,q1,p,s)` and invariant tuple predicates on `(q0,q1,p,s)`.
- In the deferred core theorem statement, do **not** mention:
  - `D1N2Config`
  - `ForwardTube`
  - `complexLorentzAction`
  - explicit Lorentz witnesses (`Γ`, `Λ`)
  - explicit coordinate witnesses (`z`, `y`, etc.)
- Forward/FT witness geometry must be encoded via invariant predicates only
  (for example `d1N2InvariantSectionWitnessPair`, realizability, forwardizable).
- Analytic/local-commutativity assumptions in the deferred core statement must be
  assumptions on the invariant kernel function `f` (function-level packaging),
  not coordinate-level transition statements.
- Coordinate-level bridges from source-field data to those function-level
  assumptions are wrapper lemmas and are outside the deferred core blocker.
- The deferred core theorem must include an explicit correction-condition
  hypothesis on `f` (in invariant variables), not assert swap symmetry with no
  analytic/correction premises.

## Bridge-Lemma Lock (2026-03-03 update)
- `hBridge` inside
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred`
  must be an assembly of explicit lemmas, not a hidden local `sorry`.
- Current bridge split in `Tail.lean`:
  1. `blocker_d1N2InvariantBridgeAnalyticity_fromSource_deferred`
  2. `blocker_d1N2InvariantBridgePreconnected_fromSource_deferred`
  3. `blocker_d1N2InvariantBridgeCorrection_fromSource_deferred`
- Semantic lock for (1):
  - it is a `DifferentiableOn ℂ` statement on the intrinsic witnessed locus;
  - it is not an analytic-extension claim.
- Numerical checks support only the intrinsic witness-inequality translation
  (section-coordinate FT inequalities ↔ invariant inequalities), not the full
  proofs of (1)-(3).

## Current Lean State
- The entire `OSReconstruction/ComplexLieGroups` folder compiles.
- Remaining `sorry` frontiers in this branch are concentrated in `PermutationFlowBlockers/Tail.lean`.
- Current `d=1,n=2` status:
  - `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`
    is now a clean reduction theorem (no internal `sorry`).
  - `blocker_d1N2PairedChartAnchorPair_fromSource_deferred` is now structural
    (no internal `sorry`) and reduces to forward witness equality.
  - active deferred front is split between:
    1. invariant-core theorem
       `blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred`,
    2. source-to-invariant bridge lemmas (analyticity/preconnectedness/correction)
       used by
       `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred`.
  - source-wrapper theorem
    `blocker_d1N2ForwardWitnessEq_fromSource_deferred` now has no `sorry`.
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
   - run E (degree 7, 4500 real constraints, 3200 forwardizable tuples):
     - antisym basis size: 290
     - nullspace dim: 0 (no nonzero sampled antisymmetric ansatz survives)
   - run F (degree 8, 6200 real constraints, 4200 forwardizable tuples):
     - antisym basis size: 440
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
