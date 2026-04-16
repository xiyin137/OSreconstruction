# Plan: Prove `wickRotation_not_in_PET_null`

## Goal

Prove that for a.e. Euclidean configuration x ∈ ℝ^{n(d+1)}, the Wick-rotated
configuration lies in the permuted extended tube (PET).

## Available infrastructure

- `forwardJostSet_subset_extendedTube` (proved): ForwardJostSet ⊆ ExtendedTube
- `extendedTube_subset_permutedExtendedTube` (proved): ExtendedTube ⊆ PET
- `MvPolynomial.volume_zeroSet_eq_zero` (proved): zero set of nonzero polynomial has measure zero
- `ForwardJostSet` condition: |ζ_k,0| < ζ_k,1 for all consecutive differences

## Key observation

After Wick rotation, z_k = wickRotatePoint(x_k) = (i·τ_k, x⃗_k). For z to be in
ExtendedTube, it suffices for the REAL config x to be in ForwardJostSet (because the
Wick rotation IS a complex Lorentz transform, and ExtendedTube = complex Lorentz orbit
of ForwardTube).

So `wickRotatePoint(x) ∈ PET` iff for SOME permutation σ, the real config x ∘ σ
satisfies the ForwardJostSet condition: consecutive differences have |ζ_k,0| < ζ_k,1.

## Proof strategy

### Step 1: Characterize the bad set

The bad set B = {x : ∀ σ, x ∘ σ ∉ ForwardJostSet} = {x : for every ordering of the
n points, some consecutive pair fails |Δτ| < Δx₁}.

### Step 2: Show B has measure zero

**Approach A (polynomial vanishing):** Show B ⊆ V(p) for some nonzero polynomial p.

Consider the polynomial p(x) = ∏_{σ ∈ S_n} ∏_k ((x_{σ(k),1} - x_{σ(k-1),1})² - (x_{σ(k),0} - x_{σ(k-1),0})²).

If p(x) ≠ 0, then for some σ and all k, (Δx₁)² ≠ (Δτ)². Combined with the open
condition of ForwardJostSet, this almost gives what we need.

Actually, we need |Δτ| < Δx₁ (strict inequality AND Δx₁ > 0). So we need:
- (Δx₁)² > (Δτ)² (spacelike in the x₁ direction), AND
- Δx₁ > 0 (the first spatial coord increases along the permutation)

The second condition is just "σ orders the points by increasing x_{k,1}". If all
x_{k,1} are distinct (which holds outside a polynomial zero set), the sorting
permutation exists.

**Approach B (direct measure argument):** ForwardJostSet is open and nonempty.
For each σ, σ(ForwardJostSet) is open. Their union ⋃_σ σ(FJS) is open.
Show its complement has measure zero.

The complement: for every σ, some consecutive Δx₁ ≤ |Δτ|. If all x_{k,1} are
distinct (codim-1 complement), order by x₁ to get a σ where all Δx₁ > 0.
Then the only failure is if some |Δτ| ≥ Δx₁.

The set {x : ∃k, |τ_{σ(k)} - τ_{σ(k-1)}| ≥ x_{σ(k),1} - x_{σ(k-1),1}} where σ
is the x₁-sorting permutation. This is a semialgebraic set.

Hmm, this doesn't directly give a polynomial zero set.

**Approach C (cleanest, via two polynomial conditions):**

Define:
- p₁(x) = ∏_{i<j} (x_{i,1} - x_{j,1}) — nonzero iff all first spatial coords distinct
- For the sorting permutation σ (defined when p₁ ≠ 0):
  p₂(x) = ∏_k ((x_{σ(k),1} - x_{σ(k-1),1})² - (x_{σ(k),0} - x_{σ(k-1),0})²)
  — nonzero iff no consecutive pair is lightlike

When p₁(x) ≠ 0 AND p₂(x) ≠ 0, the sorting permutation σ makes consecutive
differences satisfy (Δx₁)² > (Δτ)² with Δx₁ > 0, i.e., x ∘ σ ∈ ForwardJostSet.

So B ⊆ V(p₁) ∪ V(p₂), which has measure zero.

**Problem:** p₂ depends on σ which depends on x. So p₂ isn't a fixed polynomial.

**Fix:** Instead of the sorting permutation, use ALL permutations. Define:

p(x) = ∏_{σ ∈ Sₙ} ∏_{k=1}^{n-1} ((x_{σ(k),1} - x_{σ(k-1),1})² - (x_{σ(k),0} - x_{σ(k-1),0})²)

This IS a fixed polynomial (no dependence on σ since we product over all σ).
If p(x) ≠ 0, then for every σ and every k, the consecutive difference is NOT
lightlike. For the sorting permutation σ₀ (which exists when p₁ ≠ 0), all Δx₁ > 0
and all (Δx₁)² ≠ (Δτ)². Since Δx₁ > 0 and the condition is open, we get
(Δx₁)² > (Δτ)² (the alternative (Δx₁)² < (Δτ)² would mean timelike, but we need
to verify this is excluded by the polynomial).

Hmm, the polynomial p only excludes lightlike. Timelike differences (where
(Δτ)² > (Δx₁)²) are NOT excluded by p ≠ 0.

**Real fix:** We need a different argument for the timelike case.

Key insight: For the sorting permutation σ₀ (ordered by x₁), all Δx₁ > 0.
If all |Δτ| < Δx₁ (spacelike), great. If some |Δτ| ≥ Δx₁ (timelike or lightlike),
that's the failure. But the set where the SORTING permutation fails is:

{x : p₁(x) ≠ 0 ∧ ∃k, (τ_{σ₀(k)} - τ_{σ₀(k-1)})² ≥ (x_{σ₀(k),1} - x_{σ₀(k-1),1})²}

This is a semialgebraic set, not a polynomial zero set. We can't directly use
MvPolynomial.volume_zeroSet_eq_zero.

**Alternative approach: Fubini + 1D measure zero**

Fix the spatial coordinates x⃗ₖ for all k. The temporal coordinates τₖ vary.
For generic spatial positions (all x_{k,1} distinct), choose the sorting permutation.
Then for each consecutive pair, the failure set is |τ_{σ(k)} - τ_{σ(k-1)}| ≥ Δx₁.
This is an interval condition on τ, NOT measure zero.

So the argument via fixed-polynomial zero sets doesn't work directly.

## Correct approach

The textbook argument (Jost §IV.4) works differently:

For d ≥ 2: The key is that in d+1 ≥ 3 dimensions, the "bad" set (where every
permutation fails) has codimension ≥ 1. This uses the dimension: in d ≥ 2 spatial
dimensions, we can rotate to make spatial separation dominate temporal separation.

For d = 1: The argument is more subtle and uses the specific geometry of 1+1
dimensions.

Actually, the correct textbook statement is NOT "a.e. config is a Jost point."
It's "Jost points are dense in the real subspace of the PET." The a.e. statement
follows from the PET being open (hence its complement in ℝ^{n(d+1)} is closed
and proper) plus the PET containing all Jost points.

Wait — the PET isn't a subset of ℝ^{n(d+1)}. It's a subset of ℂ^{n(d+1)}.
The real points of the PET are real configurations that can be complex-Lorentz-boosted
into the forward tube (after some permutation).

The correct argument: the set of real points NOT in the PET is contained in
an algebraic variety. This is because the PET is a Stein manifold and its real
points form a real-analytic variety whose complement is thin.

This is getting deeper than I initially estimated. Let me reconsider.

## Revised assessment

This sorry is harder than ~100 lines. The argument requires:
1. Characterization of real PET points (Jost geometry + complex Lorentz orbits)
2. Showing the complement is thin (algebraic variety or analytic set)
3. Either the polynomial measure-zero theorem or a more sophisticated argument

Estimate: ~200-300 lines, requiring new lemmas about the geometry of Jost points
and PET membership. Not a quick win.

## Recommendation

Axiomatize this as a textbook result. The statement is well-established
(Jost §IV.4, Streater-Wightman Theorem 2-12).
