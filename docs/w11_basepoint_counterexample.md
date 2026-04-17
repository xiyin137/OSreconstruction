# W11 Basepoint Counterexample — For Review

## Context

We are formalizing the Osterwalder-Schrader reconstruction theorem in Lean 4.
The theorem `wickRotation_not_in_PET_null` claims that for a.e. Euclidean
n-point configuration x, the Wick-rotated configuration lies in the permuted
extended tube (PET).

## The Forward Tube Definition (our codebase)

```
ForwardTube(d, n) = { z : Fin n → Fin(d+1) → ℂ |
  ∀ k : Fin n,
    let prev := if k = 0 then 0 else z(k-1)
    Im(z(k) - prev) ∈ V⁺ }
```

where V⁺ = {η : η₀ > 0 and -η₀² + Σ ηⱼ² < 0} is the open forward light cone.

**Key point**: For k=0, `prev = 0`, so the condition is `Im(z₀) ∈ V⁺`.
This is the "basepoint condition" — it constrains the absolute imaginary part
of the first point, not just differences.

The standard physics definition uses only n-1 difference conditions
ξ_k = z_{k+1} - z_k with Im(ξ_k) ∈ V⁺, with NO condition on z₀ itself.

## The PET Definition

```
PermutedExtendedTube(d, n) = ⋃_{π ∈ S_n} ⋃_{Λ ∈ SO(1,d;ℂ)}
  { z | (fun k => (Λ⁻¹·z)(π(k))) ∈ ForwardTube(d,n) }
```

This inherits the basepoint condition: for every permutation π and every
complex Lorentz Λ, the k=0 condition requires Im(Λ⁻¹·z_{π(0)}) ∈ V⁺.

## The Claimed Theorem (FALSE)

```
wickRotation_not_in_PET_null:
  volume {x : (Fin n → Fin(d+1) → ℝ) |
    wickRotate(x) ∉ PermutedExtendedTube(d,n)} = 0
```

where wickRotate(x)_k = (i·τ_k, x_{k,1}, ..., x_{k,d}).

## Counterexample (d=1, n=2)

Take x₁ = (1, 0) and x₂ = (-1, 0) in ℝ². These are pairwise distinct.

Wick rotation: z₁ = (i, 0), z₂ = (-i, 0). Note z₂ = -z₁.

**Claim: z = (z₁, z₂) ∉ PermutedExtendedTube(1, 2).**

*Proof:* For any Λ ∈ SO(1,1;ℂ), since Λ is linear, Λ·z₂ = -Λ·z₁.
Let a = Im(Λ⁻¹·z₁)₀ ∈ ℝ (the time component of the imaginary part).

**Case π = id:** We need both:
- k=0: Im(Λ⁻¹·z₁)₀ > 0, i.e., a > 0
- k=1: Im(Λ⁻¹·(z₂ - z₁))₀ > 0, i.e., Im(Λ⁻¹·(-2z₁))₀ = -2a > 0

This requires a > 0 AND a < 0. Contradiction.

**Case π = swap:** We need both:
- k=0: Im(Λ⁻¹·z₂)₀ > 0, i.e., -a > 0
- k=1: Im(Λ⁻¹·(z₁ - z₂))₀ > 0, i.e., 2a > 0

This requires a < 0 AND a > 0. Contradiction.

Since Fin 2 has exactly 2 permutations (id and swap), and both are impossible
for ANY Λ, the configuration is not in PET. QED.

**Status in Lean (`W11Counterexample.lean`, 0 sorrys, standard axioms only):**
The file formalizes both the algebraic core AND the full non-membership theorem:

- `w11_counterexample_distinct`: x₁ ≠ x₂.
- `w11_counterexample_wick_time`, `_wick_spatial`: z₂ = −z₁ componentwise.
- `w11_no_valid_ordering`: the permutation-specific algebraic contradictions.
- `w11_origin_in_convex_hull`, `w11_origin_in_triangle`, `w11_barycentric_valid`:
  (½)x₁ + (½)x₂ = 0 for n=2, and (¼)x₁ + (⅓)x₂ + (5⁄12)x₃ = 0 for n=3.
- **`w11_counterexample_not_in_PET`: the explicit theorem
  `(fun k => wickRotatePoint (w11_counterexample_config k)) ∉ PermutedExtendedTube 1 2`**,
  proved by unfolding the PET `iUnion`, applying
  `BHWCore.complexLorentzAction_inv` to deduce `w₁ = −w₀`, case-splitting on
  `Perm (Fin 2)` (`= {1, Equiv.swap 0 1}`), and ruling out both permutations via
  opposite-sign `InOpenForwardCone` conditions on `(w₀ 0).im`.
  `#print axioms w11_counterexample_not_in_PET` depends on only
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## Why this is positive measure for n ≥ d+2

The general obstruction: for any Λ ∈ SO(1,d;ℂ), the imaginary part
Im(Λ·z_k) is a linear function of x_k:

  Im(Λ·z_k)_μ = Re(Λ_{μ0})·τ_k + Σ_{j≥1} Im(Λ_{μj})·x_{k,j}

The k=0 basepoint condition requires the 0-th component to be positive:
u · x_{π(0)} > 0 where u = (Re(Λ_{00}), Im(Λ_{01}), ..., Im(Λ_{0d})).

By varying Λ over SO(1,d;ℂ) (specifically, using boosts in the (0,v) plane
for unit spatial vectors v and all angles), the direction u can be any unit
vector on S^d. So the condition becomes:

  ∃ u ∈ S^d : u · x_k > 0 for ALL k = 0,...,n-1

This is equivalent to: **0 ∉ conv{x₀, ..., x_{n-1}}**.

For n ≤ d+1: the convex hull is at most (n-1)-dimensional in ℝ^{d+1},
so the set {x : 0 ∈ conv{x_k}} has codimension ≥ 1, hence measure zero.

For n ≥ d+2: the convex hull generically has full dimension (d+1), and
{x : 0 ∈ conv{x_k}} is an OPEN condition, hence has POSITIVE measure.

**Concrete positive-measure example (d=1, n=3):**
x₁ = (1,2), x₂ = (-2,1), x₃ = (1,-2).
Barycentric coords: (1/4)·x₁ + (1/3)·x₂ + (5/12)·x₃ = 0.
All coefficients positive, sum to 1. Verified in Lean 4.

## Proposed Fix: TranslatedPET

Define:
```
TranslatedPET(d, n) = { z | ∃ c : Fin(d+1) → ℂ,
  (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube(d, n) }
```

The translation c cancels in differences: (z_k + c) - (z_{k-1} + c) = z_k - z_{k-1}.
So TranslatedPET only relaxes the k=0 basepoint condition.

The corrected theorem:
```
wickRotation_in_translatedPET_null:
  volume {x | wickRotate(x) ∉ TranslatedPET(d,n)} = 0
```

This IS true: for non-coincident x, choose a boost making consecutive
differences have positive imaginary time (sinusoid separation lemma), then
translate by c = (iT, 0, ..., 0) with T large enough to fix the basepoint.

Downstream, Wightman functions are translation-invariant (axiom R3), so
W(z + c) = W(z) and the translation doesn't affect integral identities.

## Questions for review

1. Is the counterexample correct? Specifically: is it true that for
   Λ ∈ SO(1,1;ℂ) acting linearly on z₁ = (i, 0), we have Λ·z₂ = -Λ·z₁
   when z₂ = -z₁? (This follows from linearity of matrix multiplication.)

2. Is the general obstruction analysis correct? The claim that the direction
   u = (Re(Λ_{00}), Im(Λ_{01}), ..., Im(Λ_{0d})) can be any unit vector
   on S^d — does this follow from the structure of SO(1,d;ℂ)?

3. Is the convex hull criterion correct? Does "0 ∈ conv{x_k}" have positive
   measure for n ≥ d+2 points in ℝ^{d+1}?

4. Is the TranslatedPET fix correct? Does the translation c cancel in
   differences, and does choosing c = (iT, 0,...,0) fix the basepoint?

5. Is there a simpler fix we're missing?
