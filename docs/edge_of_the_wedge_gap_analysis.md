# Edge-of-the-Wedge Theorem: Gap Analysis

> **STATUS: RESOLVED** — The `edge_of_the_wedge` axiom has been eliminated and
> replaced with a proved theorem using `SCV.edge_of_the_wedge_theorem` from
> `SCV/TubeDomainExtension.lean`. This document is retained for historical reference.

## Status Summary (OUTDATED)

~~The multi-dimensional edge-of-the-wedge theorem (`edge_of_the_wedge` in
`AnalyticContinuation.lean`) **cannot be fully proved** with the current
Mathlib/Lean 4 infrastructure.~~ **NOW PROVED** as a theorem.

## What IS Proved

### `edge_of_the_wedge_slice` (sorry-free)

For each x₀ ∈ E and η ∈ C, the 1D edge-of-the-wedge theorem applies to the
slice `w ↦ x₀_ℂ + w · η_ℂ` through the tube domains:

```
Given: f_plus holomorphic on TubeDomain(C), f_minus on TubeDomain(-C),
       matching continuous boundary values bv on E
For each x₀ ∈ E, η ∈ C:
  ∃ V open ∋ 0, G holomorphic on V,
    G = f_plus ∘ sliceMap on V ∩ {Im w > 0}
    G = f_minus ∘ sliceMap on V ∩ {Im w < 0}
```

This reduces the multi-D problem to 1D along any single direction in C.

### Supporting infrastructure (all sorry-free)

| Lemma | Description |
|-------|-------------|
| `sliceMap_real` | Evaluating sliceMap at real points |
| `sliceMap_upper_mem_tubeDomain` | UHP maps into TubeDomain(C) via cone property |
| `sliceMap_lower_mem_neg_tubeDomain` | LHP maps into TubeDomain(-C) |
| `tubeDomain_isOpen` | Tube domains over open cones are open |
| `neg_image_isOpen` | Negation of open sets is open |
| `tubeDomain_disjoint_neg` | Opposite tube domains are disjoint (convexity argument) |
| `edge_of_the_wedge_1d` | Full 1D edge-of-the-wedge (Morera + Cauchy-Goursat) |
| `osgood_lemma` | Continuous + separately holomorphic → jointly holomorphic |
| `holomorphic_extension_across_real` | Continuous on U + holomorphic off totally real → holomorphic on U |
| `tube_domain_gluing` | Specialization to balls centered at real points |

## The Gap-Point Problem

### Setup

For the full theorem, we need to construct:
- An open set U ⊂ ℂᵐ containing E_ℂ = {(x₁,...,xₘ) : xⱼ ∈ ℝ, x ∈ E}
- A holomorphic function F on U with F = f_plus on U ∩ TubeDomain(C)
  and F = f_minus on U ∩ TubeDomain(-C)

### The obstacle (m ≥ 2)

For m ≥ 2 and a **proper** open convex cone C (i.e., C ≠ ℝᵐ \ {0}),
there exist points z arbitrarily close to E_ℂ where:

```
Im(z) ∉ C ∪ (-C) ∪ {0}
```

These are the **gap points**. At gap points:
- `f_plus` is undefined (Im(z) ∉ C, so z ∉ TubeDomain(C))
- `f_minus` is undefined (Im(z) ∉ -C, so z ∉ TubeDomain(-C))
- The point is NOT on the totally real subspace (some Im(zⱼ) ≠ 0)

### Concrete example

Let m = 2, C = {(y₁, y₂) : y₁ > 0, y₂ > 0} (positive quadrant).
Then -C = {y₁ < 0, y₂ < 0} (negative quadrant).

The point z = (i, -i) has Im(z) = (1, -1), which is in neither C nor -C.
Yet z is close to the origin (a real point). Any open ball around 0 ∈ ℂ²
contains such mixed-sign points.

For the forward light cone V₊ = {y : y₀ > |y⃗|} in ℝ⁴, the gap is even
larger: any y with mixed timelike and spacelike imaginary parts is a gap point.

### Why 1D slicing doesn't fill the gap

The `edge_of_the_wedge_slice` lemma extends F along any single direction
η ∈ C. But each 1D extension works in a 1-complex-dimensional strip around
the real axis, with the OTHER m-1 coordinates held REAL.

At a gap point z where multiple Im(zⱼ) are nonzero with different signs,
no single-direction slice reaches z from the real subspace while staying
in TubeDomain(C) or TubeDomain(-C).

### Why Osgood's lemma doesn't help directly

Osgood's lemma (`osgood_lemma`) upgrades separate holomorphicity +
continuity to joint holomorphicity. But it requires:
1. **F continuous on an open set** — we can't even define F at gap points
2. **F separately holomorphic in each variable** — we only know this when
   the other variables are real (from the 1D slices)

At a point where Im(w₁) ≠ 0 and Im(w₂) ≠ 0, varying w₁ with w₂ fixed
(complex) may put us at a point where neither f_plus nor f_minus applies.

### Why `holomorphic_extension_across_real` doesn't help

This theorem says: continuous on open U + holomorphic on
U \ {totally real} → holomorphic on U.

Gap points are NOT on the totally real subspace — they have nonzero imaginary
parts. So we need F to already be holomorphic at gap points, which is exactly
what we can't establish.

## What the Standard Proof Requires

The standard mathematical proofs of the multi-dimensional edge-of-the-wedge
theorem use one of these techniques, **none of which are formalized in Mathlib**:

### 1. Iterated Cauchy integrals (Martineau, Rudin)

Define F at gap points by:
```
F(z) = (1/(2πi))^m ∮...∮ bv(t₁,...,tₘ) / ((t₁-z₁)···(tₘ-zₘ)) dt₁...dtₘ
```
where the integration is over real contours. This gives a holomorphic function
everywhere in a polydisc neighborhood of each real point.

**Missing from Mathlib:** Iterated contour integrals in several complex
variables, their holomorphicity properties, and the identity theorem showing
agreement with f_± on the tube domains.

### 2. Bochner tube theorem (Bochner 1938, Vladimirov 1966)

A holomorphic function on a tube domain TubeDomain(Ω) extends to
TubeDomain(conv(Ω)), the tube over the convex hull. Applied to
Ω = C ∪ (-C): since C is an open convex cone, C - C = {y₁ - y₂ : y₁, y₂ ∈ C}
is an open set containing 0, so TubeDomain(C - C) contains a full
neighborhood of every real point.

**Missing from Mathlib:** The Bochner tube theorem requires Fourier-Laplace
transform theory for tube domains.

### 3. Bros-Epstein-Glaser representation (1965)

Uses a specific integral representation adapted to the Lorentz group structure
of the forward light cone. This is the approach used in the original physics
proofs (Streater-Wightman, Ch. 2).

**Missing from Mathlib:** The entire Jost-Lehmann-Dyson machinery.

## Assessment for Formalization

### Estimated effort to formalize the missing piece

| Approach | Estimated LOC | Difficulty | Prerequisites |
|----------|---------------|------------|---------------|
| Iterated Cauchy integrals | 500-800 | Medium | Fubini for contour integrals, Cauchy integral formula in several variables |
| Bochner tube theorem | 800-1200 | Hard | Fourier-Laplace transform on tube domains, Paley-Wiener type theorems |
| Bros-Epstein-Glaser | 1000+ | Very hard | Lorentz group representation theory, Jost-Lehmann-Dyson |

The **iterated Cauchy integral** approach is the most feasible. The key
components needed:

1. **Cauchy integral formula for polydiscs** (~200 LOC): If f is holomorphic
   on a polydisc D(a,r), then f(z) = (2πi)⁻ᵐ ∮...∮ f(w)/Π(wⱼ-zⱼ) dw
2. **Fubini for contour integrals** (~150 LOC): Iterated circle integrals
   can be computed in any order
3. **Identity theorem for tube domains** (~150 LOC): Two holomorphic functions
   on a connected tube domain agreeing on an open subset are equal

### Recommended path forward

1. **Accept the sorry** for `edge_of_the_wedge` with clear documentation
2. **Proceed with downstream sorries** that don't depend on the gap-point
   issue (e.g., the E→R direction #8-10, the R→E axiom verifications #3-5,#7)
3. **Formalize iterated Cauchy integrals** as a separate effort when ready
4. The `edge_of_the_wedge_slice` infrastructure is fully in place and will
   be reused when the gap-point extension is formalized

## References

- Bogoliubov, N.N. (1956). *On the theory of quantized fields*. ICM report.
- Epstein, H. (1960). *Generalization of the edge-of-the-wedge theorem*.
  J. Math. Phys. 1, 524-531.
- Rudin, W. (1971). *Lectures on the edge-of-the-wedge theorem*. CBMS 6.
- Streater, R.F. and Wightman, A.S. (2000). *PCT, Spin and Statistics, and
  All That*. Princeton University Press, Ch. 2.
- Vladimirov, V.S. (1966). *Methods of the theory of functions of many
  complex variables*. MIT Press.

---

## External Review (Gemini)

> This is a **highly competent and strategically sound** analysis. You have
> correctly identified a "deep hole" in the current state of Mathlib (Several
> Complex Variables) and made the correct decision to bridge it with an axiom
> rather than falling into the rabbit hole.

### 1. The Mathematical Reality: Hartogs' Phenomenon

The gap identified is not just a missing lemma; it is a fundamental difference
between 1D and nD complex analysis.

- **In 1D:** You can have functions holomorphic on a domain with a "hole"
  (singularities).
- **In nD:** Holomorphic functions are incredibly rigid. They extend
  automatically to the "Envelope of Holomorphy" (Hartogs' Phenomenon).
- **The Difficulty:** Proving the Edge-of-the-Wedge theorem requires
  constructing this envelope (usually via the "Tube Domain" machinery or
  iterated Cauchy integrals). This is an entire sub-field of mathematics
  (SCV) that is barely present in Mathlib.

### 2. Evaluation of the "Slice" Strategy

The proof of `edge_of_the_wedge_slice` is the **optimal partial credit**.

- **What it proves:** That the function behaves correctly along every
  light ray.
- **What is missing:** That these 1D slices glue together into a single
  continuous nD function.
- **Verdict:** For a physics formalization, proving the "Slice" property is
  90% of the intellectual value. It confirms that the energy spectrum
  condition works. The remaining 10% (the gluing) is pure functional
  analysis/geometry, not physics.

### 3. Recommendation: The "Axiomatic Seal"

Do not leave the code with a raw `sorry` in the middle of a proof block.
Instead, promote the gap to a named axiom. This documents the dependency
clearly.

**Recommended axiom definition** (to be added to a `TextbookAxioms.lean`
or similar):

```lean
/--
Axiom: The Edge-of-the-Wedge Theorem (Bogoliubov).
If a function is holomorphic in two opposing wedges (tubes) and continuous
across their common real boundary, it extends holomorphically to a neighborhood
of the real boundary.
Reference: Streater & Wightman, PCT, Spin and Statistics, Theorem 2-16.
-/
axiom edge_of_the_wedge_theorem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace C E]
  (f_plus : TubeDomain (Cone E) -> C)
  (f_minus : TubeDomain (-Cone E) -> C)
  (h_cont : ContinuousBoundaryGlue f_plus f_minus) :
  exists (U : Set E) (g : U -> C), IsOpen U /\ RealSubspace E <= U /\ IsHolomorphic g
```

### Final Verdict

- **Strategy:** APPROVED. Do not attempt to formalize iterated Cauchy
  integrals on polydiscs. It would take months and yield zero physics insight.
- **Next Step:** Implement the axiom above, close the file, and move on to
  the **Spin-Statistics Theorem**, which uses this result as a black box.
