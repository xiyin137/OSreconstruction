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
