# Bargmann-Hall-Wightman Theorem: Gap Analysis

> Status note (2026-02-27): Historical document.
> `bargmann_hall_wightman` is now a theorem (not an axiom).
> For current blockers, use `docs/development_plan_systematic.md`.

## Status Summary

The Bargmann-Hall-Wightman (BHW) theorem (`bargmann_hall_wightman` in
`AnalyticContinuation.lean`) **cannot be proved** with current Mathlib/Lean 4
infrastructure. It is promoted to a named axiom.

## What the Theorem Says

Given a holomorphic function F on the forward tube T_n that is:
1. Invariant under the real restricted Lorentz group L+^up
2. Continuously extends to the real boundary (boundary values exist)
3. Boundary values satisfy local commutativity at spacelike-separated pairs

Then F extends to a unique holomorphic function F_ext on the permuted extended
tube T''_n, and the extension is:
1. Invariant under the full complex Lorentz group L+(C)
2. Symmetric under all permutations of the arguments
3. Unique (any holomorphic extension agreeing with F on T_n agrees with F_ext)

## Proof Structure

The proof has 4 steps:

| Step | Description | Status |
|------|-------------|--------|
| **1. Real -> Complex Lorentz** | Analytic continuation: F(Lambda*z) = F(z) for real Lambda extends to complex Lambda | **BLOCKED** |
| **2. Jost point matching** | Local commutativity gives F(pi*x) = F(x) at spacelike real points | **Available** (jost_lemma proved, hF_local hypothesis) |
| **3. Edge-of-the-wedge** | Glue functions on adjacent permuted tubes across Jost point boundaries | **Available** (edge_of_the_wedge proved theorem) |
| **4. Iterate over S_n** | Cover all permutations via adjacent transpositions | Feasible (combinatorics) |

## The Hard Blocker: Step 1

### What's needed

Step 1 requires proving that real Lorentz invariance implies complex Lorentz
invariance. The argument is:

1. **L+(C) is connected**: The proper complex Lorentz group SO+(1,d;C) is a
   connected complex Lie group. This is a non-trivial topological result —
   the real Lorentz group SO+(1,d;R) has 4 connected components, but its
   complexification is connected.

2. **Holomorphicity of the group action**: For fixed z in the forward tube,
   the map Lambda -> F(Lambda*z) is holomorphic on L+(C).

3. **Identity theorem on connected complex manifolds**: Since F(Lambda*z) = F(z)
   for all Lambda in the real Lorentz group (a totally real submanifold of
   L+(C)), and L+(C) is connected, the identity theorem gives F(Lambda*z) = F(z)
   for ALL Lambda in L+(C).

### What's missing from Mathlib

| Component | Description | Estimated effort |
|-----------|-------------|------------------|
| **Connectedness of SO+(1,d;C)** | Topological result about complex Lie groups | 300-500 LOC |
| **Complex manifold structure of L+(C)** | L+(C) as a complex analytic manifold | 500+ LOC |
| **Identity theorem on manifolds** | Extension of identity theorem from C^n to complex manifolds | 200-400 LOC |
| **Holomorphicity of group action** | Lambda -> F(Lambda*z) is holomorphic | 200-300 LOC |

**Total estimated effort: 1200-1700 LOC** of complex Lie group theory and
several complex variables not present in Mathlib.

## Available Infrastructure

The following components ARE available:

- `ComplexLorentzGroup d` — structure definition with metric-preserving and
  det = 1 conditions
- `ComplexLorentzGroup.ofReal` — embedding of real Lorentz group (proved)
- `ComplexLorentzGroup.ofEuclidean` — embedding of Euclidean rotations (proved)
- `ForwardTube`, `ComplexExtendedForwardTube`, `PermutedExtendedTube` —
  tube domain hierarchy (defined)
- `ForwardTube_subset_ComplexExtended` — inclusion (proved)
- `ComplexExtended_subset_Permuted` — inclusion (proved)
- `jost_lemma` — spacelike separation at Jost points (proved)
- `edge_of_the_wedge` — proved theorem (available for Step 3)

## Statement Refinements

### The boundary value problem (`hF_bv`)

The original formulation evaluated `F` directly at real points in `hF_local`:

```lean
F (fun k μ => (x k μ : ℂ)) -- F evaluated at a real point
```

**Problem:** Real points lie *outside* the forward tube. The forward tube
requires each successive imaginary difference Im(z_k - z_{k-1}) to lie in the
open forward light cone V₊. For real points, all imaginary parts are zero, and
0 ∉ V₊. So `F` is only holomorphic (and only physically meaningful) on the
forward tube, not at real boundary points.

Since `F` is formalized as a total function `(Fin n → Fin (d+1) → ℂ) → ℂ`
(with holomorphicity constrained to the forward tube via `DifferentiableOn`),
evaluating `F(x_ℂ)` returns an arbitrary "junk" value — whatever the total
function happens to assign outside the tube.

**Fix:** Add a `ContinuousWithinAt` hypothesis:

```lean
(hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
  ContinuousWithinAt F (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
```

This constrains `F(x_ℂ)` to equal the distributional boundary value
`lim_{ε→0⁺} F(x + iεη)` (the limit as we approach the real point from within
the forward tube). With `hF_bv` in place:
- `F(x_ℂ)` is the boundary value of F at x (right side of `hF_local`)
- `F(swap(x)_ℂ)` is the boundary value at swap(x) — also constrained by
  `hF_bv` applied to `x ∘ swap` (left side of `hF_local`)
- `hF_local` then states that these two boundary values agree at spacelike
  separation, which is the standard locality condition

This matches the physics: Wightman functions W_n(x_1,...,x_n) are
distributional boundary values of holomorphic functions on the forward tube,
and locality is a condition on these boundary values.

### Uniqueness of F_ext

The standard BHW theorem guarantees uniqueness of the holomorphic extension,
which follows from the identity theorem: any two holomorphic functions on the
connected permuted extended tube that agree on the forward tube (an open
subset) must agree everywhere. We include this as an explicit conclusion:

```lean
∀ (G : ...), DifferentiableOn ℂ G (PermutedExtendedTube d n) →
  (∀ z ∈ ForwardTube d n, G z = F z) →
  ∀ z ∈ PermutedExtendedTube d n, G z = F_ext z
```

### Adjacent transpositions generate S_n

The locality hypothesis uses adjacent transpositions `swap i (i+1)` rather
than arbitrary permutations or full Jost point conditions. This is sufficient
because adjacent transpositions generate the symmetric group S_n, and the
full permutation symmetry in the conclusion is derived by iterating over
a decomposition into adjacent transpositions.

## Mathematical Correctness of the Axiom

The BHW theorem is a well-established result in axiomatic QFT:

- **Original proof**: Bargmann, Hall, and Wightman (1957)
- **Standard reference**: Streater & Wightman, *PCT, Spin and Statistics*,
  Theorem 2-11 and surrounding discussion
- **Also**: Jost (1965), *The General Theory of Quantized Fields*, Ch. IV

The axiom statement matches the standard formulation:
- **Hypotheses**: holomorphicity on forward tube, real Lorentz invariance,
  continuous boundary extension (`hF_bv`), local commutativity at adjacent
  transpositions (`hF_local`)
- **Conclusion**: unique extension to permuted extended tube with complex
  Lorentz invariance and full permutation symmetry

The axiom is a true mathematical theorem whose proof requires infrastructure
(complex Lie group theory) not available in Mathlib.

## Impact on Project

BHW is sorry #2 on the critical path. It blocks:
- Sorry #6 (`constructedSchwinger_symmetric`) — E3 symmetry in R->E direction
- Sorry #13 (`lorentz_covariant`) — Lorentz covariance extraction in E->R
- Sorry #15 (`locally_commutative`) — Locality extraction in E->R

Promoting it to an axiom unblocks these downstream results (they can now
use BHW as a black box).

## References

- Bargmann, V., Hall, D., and Wightman, A.S. (1957). *On the group of
  analytic continuation of Wightman functions*. Nuovo Cimento 5, 1-14.
- Jost, R. (1965). *The General Theory of Quantized Fields*. AMS, Ch. IV.
- Streater, R.F. and Wightman, A.S. (2000). *PCT, Spin and Statistics, and
  All That*. Princeton University Press, Theorem 2-11.
