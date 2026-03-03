# d=1, n=2 Complete Blocker Proof Plan

## Target
Close:

- `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`
- file: `PermutationFlowBlockers/Tail.lean`

## Exact Remaining Gap
The theorem is already reduced to proving:

- `d1N2PairedChartAnchorConnected (Classical.choose hsource)`

Refined reduction now available:
- it is enough to produce one anchored chart pair per tuple via
  `d1N2PairedChartAnchorConnected_of_exists_anchorPair`.

## End-to-End Proof Skeleton
1. Unpack `hsource` into `F`, `hF_holo`, `hF_lorentz`, `hF_bv`, `hF_local`, `hf_onFT`.
2. Fix `(q0,q1,p,s)` on the quadric and define paired chart domain
   where both section points are in `FT`.
3. Define chart-difference function
   `g(v0,w0) = F(sectionSwap ... w0) - F(sectionOrig ... v0)`.
4. Prove `DifferentiableOn` of `g` on paired domain using existing section-pullback lemmas.
5. Construct a nonempty open totally-real anchor subset of paired domain where `g = 0`
   from local commutativity boundary data (`hF_local`) and explicit real chart formulas.
6. Apply identity propagation on the relevant connected component to conclude `g = 0`
   on all paired chart points needed by the blocker.
7. Use `d1N2PairedChartAnchorConnected_of_exists_anchorPair` to upgrade
   one-pair existence to full paired-chart anchor connectivity.
8. Finish blocker by the already-proved reduction theorem
   `d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_of_pairedChartAnchorConnected`.

## Lemmas To Add (Planned)
1. `d1N2SectionPairDiff_zero_on_anchor_from_localComm`
2. `d1N2SectionPairDiff_zero_on_component_from_identity`
3. `d1N2PairedChartAnchorConnected_of_source`

## Guardrails
- Stay on Lorentz-invariant-function route only.
- No translation-invariance detour.
- No new axioms.
- Keep statements restricted to the doubly witnessed locus.

## Parallel Counterexample Search
Run a concurrent falsification campaign on the exact blocker hypotheses:

1. Search for `f` with `d1N2InvariantKernelSource f` and a doubly witnessed
   quadric tuple violating swap-difference vanishing.
2. Reject off-image/non-witnessed tuples immediately.
3. Maintain executable search harness:
   - `ProofHarness/D1N2CounterexampleSearch.lean`.

## Test Matrix
The following dedicated tests are added to keep the plan executable:

1. `ProofHarness/D1N2ReductionChain.lean`
   - verifies reduction chain and type-level theorem interfaces.
2. `ProofHarness/D1N2SectionInvariants.lean`
   - verifies section invariant identities and reconstruction usage.
3. `ProofHarness/D1N2ObstructionChecks.lean`
   - keeps known obstructions/counterexamples explicit and checked.
4. `ProofHarness/D1N2LocalAnchorTransport.lean`
   - verifies local anchor transport/equivalence infrastructure used downstream.
5. `ProofHarness/D1N2CounterexampleSearch.lean`
   - pins the exact falsification target and non-realizable-candidate pruning checks.

## Completion Criterion
The blocker is closed when `Tail.lean` line for the theorem above has no `sorry`
and the full `OSReconstruction/ComplexLieGroups` tree compiles.
