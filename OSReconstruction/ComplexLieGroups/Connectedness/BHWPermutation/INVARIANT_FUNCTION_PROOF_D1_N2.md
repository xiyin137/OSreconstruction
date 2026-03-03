# Invariant Function Proof (d=1, n=2)

This is the primary local note for the blocker proof route.

## Problem
Given a sourced invariant kernel `f(q0,q1,p,s)`, prove swap involution on the doubly witnessed invariant locus:

- `f(q0,q1,p,s) - f(q1,q0,p,-s) = 0`
- under `s^2 = 4(p^2 - q0 q1)` and paired light-cone witness assumptions.

## Invariant Setup
- Invariants used: `q0, q1, p, s` with one algebraic relation.
- Independent invariant count is effectively 3; `s` records branch/sign data.
- Swap involution acts by
  - `(q0,q1,p,s) -> (q1,q0,p,-s)`.

## Working Function
Define
- `g(q0,q1,p,s) := f(q0,q1,p,s) - f(q1,q0,p,-s)`.

Goal is `g = 0` on the doubly witnessed locus.

## Formal Route in Lean
1. Start from `d1N2InvariantKernelSource f`.
2. Use existing reduction theorem in `PermutationFlowBlockers/Tail.lean`:
   - blocker follows from paired-chart anchor connectivity of sourced `F`.
3. Prove paired-chart anchor connectivity on variable charts.
4. Conclude blocker equation (`g=0`) on the target locus.

## Why Not Full Quadric
A formal theorem shows source package does not force `g=0` on the entire quadric for arbitrary off-image extensions of `f`.

Hence the proof target is intentionally the realizable/light-cone witnessed locus.

## Current Practical Focus
- construct and prove the remaining paired-chart anchor step,
- without adding extra axioms,
- and without detouring through unrelated d>=2 infrastructure.

## Source-to-Invariant Bridge Split (Current Tail State)
The source wrapper now factors through three explicit bridge lemmas in
`PermutationFlowBlockers/Tail.lean`:

1. `blocker_d1N2InvariantBridgeAnalyticity_fromSource_deferred`
2. `blocker_d1N2InvariantBridgePreconnected_fromSource_deferred`
3. `blocker_d1N2InvariantBridgeCorrection_fromSource_deferred`

These are assembled into the bridge package used by
`blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred`.

## Meaning of "Bridge Analyticity"
`bridgeAnalyticity` is a statement of `DifferentiableOn ℂ` for the invariant
swap-difference function on the intrinsic witnessed quadric locus.

It is not an analytic-continuation/extension claim to a larger ambient domain.

## Numerical Validation Scope
The numerical harness
`ProofHarness/d1n2_invariant_witness_equivalence.py` validates the intrinsic
witness inequalities used in the core theorem statement against the intended
section-coordinate `ForwardTube` inequalities on sampled data.

This numerical check supports the witness-inequality translation only; it does
not prove the three bridge lemmas above.
