# d=1, n=2 Lorentz-Invariant Route

## Objective
Close the blocker:

- `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`

using only Lorentz-invariant-function infrastructure.

## Locked Setup
- Domain: `d=1, n=2`.
- Invariant kernel: `f(q0,q1,p,s)`.
- Quadric relation: `s^2 = 4(p^2 - q0 q1)`.
- Swap involution on invariants:
  - `(q0,q1,p,s) -> (q1,q0,p,-s)`.

## Core Statement to Prove
On the doubly light-cone-witnessed locus:

- `f(q0,q1,p,s) - f(q1,q0,p,-s) = 0`.

This is the exact blocker statement; no coordinate-level forward-tube clauses appear in the target formula itself.

## Current Formal Reduction
Already in Lean:

- blocker theorem reduces to proving paired-chart anchor connectivity for the sourced field.
- once paired-chart anchor connectivity is available, blocker closes immediately.

So the true remaining gap is not algebraic rewriting, but analytic propagation on variable-chart domains.

## Route Skeleton (Invariant-Only)
1. Use source package to obtain `F` on `FT_{1,2}` and factorization through invariants on `FT` points.
2. Work with variable charts (`v0`/`w0` free), not fixed anchors.
3. Define the paired-chart difference function on the domain where both chart points are in `FT`.
4. Show this difference vanishes on an anchor set supplied by local commutativity boundary input.
5. Propagate vanishing via holomorphic identity mechanism on the relevant connected component.
6. Pull back to invariant tuples, yielding blocker equation.

## Why This Route
- It keeps the proof in invariant variables.
- It avoids known d=1 dead-ends from EOW-style fixed-anchor geometry.
- It matches existing reduction lemmas in `PermutationFlowBlockers/Core.lean`.

## Explicit Non-Goals
- Do not add translation invariance as a new assumption for this closure.
- Do not switch to d>=2 connectedness arguments.
- Do not assert full-quadric involution without realizability/light-cone witness hypotheses.

## Mathematical Cautions
- There are three algebraically independent invariants in `d=1,n=2`; `s` is branch data constrained by the quadric equation.
- Any identity theorem step must be applied on the correct domain (doubly realizable/light-cone witnessed), not on the entire quadric by default.

## Files
- Proof core: `PermutationFlowBlockers/Core.lean`, `PermutationFlowBlockers/Tail.lean`
- Canonical sketch notes: `INVARIANT_FUNCTION_PROOF_D1_N2.md`
- Failure/counterexample log: `D1_N2_BLOCKER_AUDIT.md`
