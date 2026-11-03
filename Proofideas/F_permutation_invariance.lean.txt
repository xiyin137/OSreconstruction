/-
# Proof Strategy: F_permutation_invariance

## Status (2026-02-22, updated)

### CRITICAL FINDING: JostSet definition issue

**The current `JostSet` (pairwise spacelike) is INSUFFICIENT for Jost's lemma.**

The theorem `jostSet_subset_extendedTube` as stated is FALSE. Counterexample:
  x_0 = (0, 1), x_1 = (0, -1) in 1+1 dimensions.
  Both spacelike ✓. x_1 - x_0 = (0, -2) spacelike ✓.
  But ζ_0 = (0,1), ζ_1 = (0,-2). Linear combination 2ζ_0 + ζ_1 = 0.
  Any complex Lorentz Λ with Im(Λ⁻¹·ζ_k) ∈ V⁺ for all k requires Im(2v_0 + v_1) ∈ V⁺,
  but 2v_0 + v_1 = 0 ∉ V⁺. Contradiction.

**Reason**: Jost's lemma requires the "Jost condition" (S-W eq. 2-92):
  ∀ λ_k ≥ 0 with Σλ > 0 : (Σ λ_k ζ_k)² < 0
where ζ_k are consecutive differences. This is STRONGER than pairwise spacelike.

Pairwise spacelike allows anti-parallel spacelike vectors whose positive combinations
can vanish, violating the Jost condition.

**Fix**: Use the Jost condition (positive independence of consecutive differences)
instead of pairwise spacelike. Equivalently: ∃ direction w ∈ ℝ^{d+1} such that
w · ζ_k > 0 for all k (positive half-space condition).

### Key insight from Gemini consultation:
**The standard BHW proof does NOT use the edge-of-the-wedge theorem for the
permutation step.** Instead, it uses:
1. Complex Lorentz invariance → extend F to the extended tube T'_n
2. Jost's lemma: totally spacelike real configurations ("Jost points") lie in T'_n
3. Locality: F = F∘σ on the Jost set (by hF_local at real spacelike configurations)
4. Identity theorem: F = F∘σ propagates from the Jost set to the full domain

### Why EOW doesn't directly apply (analysis from 2026-02-22):
The permuted tube σ·FT is NOT the "opposite tube" T(-C) of FT = T(C) in the
edge-of-the-wedge sense. Specifically, for σ = swap(i, i+1) in position variables:
- FT condition at i+1: Im(z_{i+1} - z_i) ∈ V⁺
- σ·FT condition at i+1: Im(z_i - z_{i+1}) = -Im(z_{i+1} - z_i) ∈ V⁺  (sign flip ✓)
- σ·FT condition at i: Im(z_{i+1} - z_{i-1}) = Im(ζ_i + ζ_{i+1}) ∈ V⁺  (MIXES variables!)
- σ·FT condition at i+2: Im(z_{i+2} - z_i) = Im(ζ_{i+1} + ζ_{i+2}) ∈ V⁺  (MIXES variables!)

The mixing at positions i and i+2 means:
- f⁻(ξ) for Im(ξ) ∈ -V⁺ is only defined when Im(ζ_i) + Im(ξ) ∈ V⁺, which
  constrains |Im(ξ)| relative to Im(ζ_i). So f⁻ is NOT defined on all of T(-V⁺).
- Our formalized EOW theorem requires f⁻ on the ENTIRE negative tube T(-V⁺).
- No choice of "subcone" works because V⁺ is unbounded and the constraint is
  parameter-dependent, not scale-invariant.

## Complex boost construction (Jost's lemma proof)

### Single vector case

For a purely spatial spacelike vector ζ = (0, a, 0, ..., 0) with a > 0:

The boost generator K₁ has entries:
  K₁[0,1] = K₁[1,0] = 1, all others 0.
K₁ ∈ so(1,d;ℝ) (satisfies K₁ᵀ η + η K₁ = 0).

Matrix exponential:
  K₁² = diag(1,1,0,...,0)
  exp(iα K₁) = I + i sin(α) K₁ + (cos(α) - 1) K₁²

Explicit entries:
  [0,0] = cos α,  [0,1] = i sin α
  [1,0] = i sin α, [1,1] = cos α
  [j,j] = 1 for j ≥ 2

Action on ζ = (0, a, 0, ...):
  exp(iα K₁) · ζ = (ia sin α, a cos α, 0, ...)
  Im part = (a sin α, 0, ..., 0) ∈ V⁺ for α ∈ (0, π), a > 0 ✓

So: set Λ = exp(-iα K₁), then w = Λ⁻¹ · ζ = exp(iα K₁) · ζ has Im(w) ∈ V⁺.
And Λ ∈ SO⁺(1,d;ℂ) via `expLieAlg`.

### Multiple vectors — positive half-space condition

For n consecutive differences ζ_k with spatial parts v_k ∈ ℝ^d:

If ∃ w ∈ ℝ^d with w · v_k > 0 for all k, then:
1. Apply real spatial rotation R ∈ SO(d) to align w with e₁.
   After rotation: (R v_k)₁ = w · v_k / |w| > 0.
2. Apply complex boost exp(-iα K₁).
   Result: Im(Λ⁻¹ · ζ_k) = ((R v_k)₁ sin α, 0, ..., 0) ∈ V⁺.

The direction w exists iff the v_k are "positively independent":
no nonneg linear combination Σ λ_k v_k = 0 with Σλ > 0.
This is exactly the Jost condition (for purely spatial vectors).

The real spatial rotation R_Lor ∈ SO(1,d;ℝ) ⊂ SO⁺(1,d;ℂ) just acts on spatial
indices. The full complex Lorentz transformation is Λ = R_Lor · exp(-iα K₁).

### Swap-compatible configurations

For swap(i, i+1), the permuted consecutive differences are:
  ζ'_k = ζ_k for k ∉ {i, i+1, i+2}
  ζ'_i = ζ_i + ζ_{i+1}
  ζ'_{i+1} = -ζ_{i+1}
  ζ'_{i+2} = ζ_{i+1} + ζ_{i+2}  (if exists)

Key issue: -ζ_{i+1} appears, so the original direction w (with w·v_{i+1} > 0)
gives w·(-v_{i+1}) < 0. Need a DIFFERENT direction w' for the permuted ordering.

**Construction that works for BOTH orderings** (d ≥ 2):

Take x_k = (0, k+1, 0, ..., 0) for k ≠ i+1
     x_{i+1} = (0, i+2, ε, 0, ..., 0)  for small ε > 0

Consecutive differences:
  ζ_k = (0, 1, 0, ...) for k ≠ i+1, i+2
  ζ_{i+1} = (0, 1, ε, ...)
  ζ_{i+2} = (0, 1, -ε, ...)

Original ordering: w = (1, 0) works (all first components = 1 > 0). ✓

Permuted ordering: ζ'_{i+1} = (0, -1, -ε, ...).
Direction w' = (1, -3/(2ε)):
  w'·(1, 0) = 1 > 0 ✓  (for k ≠ i, i+1, i+2)
  w'·(2, ε) = 2 - 3/2 = 1/2 > 0 ✓  (ζ'_i)
  w'·(-1, -ε) = -1 + 3/2 = 1/2 > 0 ✓  (ζ'_{i+1})
  w'·(2, -ε) = 2 + 3/2 = 7/2 > 0 ✓  (ζ'_{i+2}, if v_{i+2} = (1,-ε) + (1,0) = (2,-ε))
    Wait: ζ'_{i+2} = ζ_{i+1} + ζ_{i+2}. ζ_{i+1} = (0,1,ε), ζ_{i+2} = (0,1,-ε).
    So ζ'_{i+2} = (0, 2, 0). w'·(2, 0) = 2 > 0 ✓

Locality: ζ_{i+1} = (0, 1, ε) is spacelike (1 + ε² > 0), so hF_local applies. ✓

This configuration has an open neighborhood with the same properties (strict inequalities).

### Connectivity of T'_n ∩ σ⁻¹(T'_n)

This is needed for the identity theorem step.

**Path-connection argument**:
For z ∈ T'_n ∩ σ⁻¹(T'_n):
  z ∈ T'_n means z = Λ₁·w₁ with w₁ ∈ FT.
  σ·z ∈ T'_n means σ·z = Λ₂·w₂ with w₂ ∈ FT.
  Then σ·w₁ = Λ₁⁻¹·Λ₂·w₂ =: Λ₃·w₂ ∈ T'_n.

Path from z to w₁ ∈ FT:
  t ↦ Λ₁(t)·w₁ where Λ₁(t) deforms Λ₁ to Id in SO⁺(1,d;ℂ).
  Stays in T'_n: ✓ (each point is Λ₁(t)·w₁ ∈ T'_n).
  σ·(Λ₁(t)·w₁) = Λ₁(t)·(σ·w₁) = Λ₁(t)·Λ₃·w₂ ∈ T'_n: ✓

This path connects z to w₁ ∈ FT while staying in T'_n ∩ σ⁻¹(T'_n).
But we also need to connect w₁ to a Jost point through T'_n ∩ σ⁻¹(T'_n).
This part is harder and requires SO⁺(1,d;ℂ) connected (orbitSet sorry).

**Alternative**: Sorry connectivity; it depends on the same Lie group connectivity
as `orbitSet_isPreconnected`. This does NOT introduce a genuinely new sorry.

## Proof strategy: Jost point approach (NO EOW needed)

### Setup
- F holomorphic on FT, real Lorentz invariant, continuous boundary values (hF_bv),
  local commutativity (hF_local).
- Complex Lorentz invariance: F(Λ·z) = F(z) for z, Λ·z ∈ FT. (PROVED modulo orbitSet)
- extendF defined on ExtendedTube T'_n = ⋃_Λ Λ·FT, with extendF = F on FT.
  (PROVED: `extendF_eq_on_forwardTube`, `extendF_preimage_eq`)

### Step 1: Holomorphicity of extendF on T'_n
**Status: PROVED** (`extendF_holomorphicOn` in JostPoints.lean)

### Step 2: Jost's lemma — Jost-condition configurations lie in T'_n
**Status: PARTIALLY FORMALIZED (sorry on complex boost computation)**

Correct definition: `JostCondition` requires consecutive differences to be
positively independent (∃ direction w with w · v_k > 0 for all k).

Proof via complex boost: R_Lor · exp(-iα K₁) maps real Jost-condition configs
to ForwardTube. Needs matrix exponential computation (~200 LOC).

### Step 3: Boundary value agreement — extendF(x) = F(x_ℂ) on Jost set
**Status: PROVED** (`extendF_eq_boundary_value` in JostPoints.lean)

### Step 4: Locality on Jost set
**Status: Straightforward from hF_local (to be formalized)**

### Step 5: Identity theorem on T'_n ∩ σ⁻¹(T'_n)
**Status: Identity theorem PROVED; connectivity SORRY (same dependency as orbitSet)**

### Step 6: Conclude extendF_permutation_invariant_swap
**Status: To be formalized (structure clear)**

### Step 7: Wire into F_permutation_invariance
**Status: Structure clear; needs Steps 5-6**

## Required infrastructure (ordered by priority)

### Priority 1: Complex boost computation (for Jost's lemma)
- Define K₁ (boost generator) as a matrix
- Verify K₁ ∈ so(1,d;ℝ) (IsInLieAlgebra)
- Use expLieAlg to get exp(iα K₁) ∈ SO⁺(1,d;ℂ)
- Compute action formula: exp(iα K₁)·(0,a,0,...) = (ia sin α, a cos α, 0,...)
- Estimated: 200-300 LOC
- Alternative: sorry the action formula, focus on proof structure

### Priority 2: JostCondition definition + basic properties
- Define JostCondition (positive half-space condition on consecutive diffs)
- Prove: open set, nonempty, swap-compatible configs exist
- Estimated: 100-150 LOC

### Priority 3: Swap-compatible set construction
- For each swap(i,i+1): construct explicit open set in T'_n ∩ σ⁻¹(T'_n)
- Uses 2D perturbation (ε in second spatial direction)
- Estimated: 100-200 LOC

### Priority 4: Connectivity (or sorry)
- T'_n ∩ σ⁻¹(T'_n) connected — reduces to SO⁺(1,d;ℂ) connected
- Same dependency as orbitSet sorry; not a genuinely new obstacle
- Estimated: sorry for now, ~50 LOC

## Remaining sorrys after this work

1. `orbitSet_isPreconnected` — SO⁺(1,d;ℂ) orbit sets connected (Lie group theory)
2. `jostCondition_subset_extendedTube` — complex boost computation (matrix exp)
3. Connectivity of T'_n ∩ σ⁻¹(T'_n) — reduces to #1
4. PET preconnected — follows from #2 + #1

All reduce to: (a) complex boost computation, (b) Lie group connectivity.
These are the IRREDUCIBLE CORE of the BHW theorem.

## Impact on PET preconnected (sorry #3)

PET = T''_n = ⋃_τ ⋃_Λ Λ·(τ·FT).

The same Jost point argument shows: J ⊂ T'_n ∩ σ(T'_n) for each σ. So the
different "sectors" σ_k(T'_n) all contain J. Since T'_n ∪ σ(T'_n) is connected
(sharing J), iterating gives T''_n is connected.

So **Jost's lemma is the key infrastructure for BOTH F_permutation_invariance AND
PET preconnected**. Proving Jost's lemma would reduce all 3 Connectedness.lean sorrys
to just `orbitSet_isPreconnected`.
-/
