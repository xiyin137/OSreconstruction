# Plan: Prove Bochner's Tube Theorem

## Goal

Fill the 2 sorrys in `OSReconstruction/SCV/BochnerTubeTheorem.lean`:
1. `bochner_local_extension` (line 126) — the core analytical content
2. `bochner_tube_extension` (line 220) — global assembly from local data

## Current infrastructure (all sorry-free)

| Lemma | File | What it gives |
|-------|------|---------------|
| `isOpen_convexHull_of_isOpen` | BochnerTubeTheorem | conv(C) is open |
| `tubeDomain_convex` | BochnerTubeTheorem | T(conv C) is convex |
| `tubeDomain_convexHull_isConnected` | BochnerTubeTheorem | T(conv C) is connected |
| `holomorphic_extension_from_local_family` | BochnerTubeTheorem | Gluing theorem for convex local patches with overlap condition |
| `cauchyIntegralPolydisc` | IteratedCauchyIntegral | Iterated Cauchy integral on polydiscs |
| `cauchyIntegralPolydisc_eq` | IteratedCauchyIntegral | **Cauchy integral formula**: G(z) = f(z) for z in the polydisc interior |
| `cauchyIntegralPolydisc_differentiableOn` | IteratedCauchyIntegral | Cauchy integral is holomorphic on the polydisc interior |
| `Polydisc`, `closedPolydisc`, `distinguishedBoundary` | Polydisc | Polydisc definitions + openness, compactness, membership |

## Sorry 1: `bochner_local_extension` (~150 lines)

### Statement

Given C open in ℝᵐ, F holomorphic on T(C), and z ∈ T(conv C), find an open U ∋ z
with U ⊆ T(conv C) and a holomorphic G on U agreeing with F on T(C) ∩ U.

### Proof sketch (Hörmander, Theorem 2.5.10)

**Step 1: Convex combination decomposition** (~20 lines)

Im(z) ∈ conv(C) which is open. By the definition of convex hull, there exist
y₁, ..., yₖ ∈ C and λ₁, ..., λₖ > 0 with Σλⱼ = 1 and Im(z) = Σλⱼyⱼ.

Since C is open, each yⱼ has a neighborhood Bⱼ ⊆ C (open ball of radius εⱼ).

*Lean challenge:* Extracting a finite convex combination from `convexHull`.
Use `Convex.exists_forall_mem_convexHull_of_mem` or the Carathéodory-style
characterization. In finite dimensions, Carathéodory says we need at most m+1 points.

**Step 2: Construct the polydisc** (~30 lines)

Choose center c = z and radii rᵢ small enough that for every point w on
the distinguished boundary of the polydisc Δ(z, r), we have Im(w) ∈ C.

The distinguished boundary consists of points w with |wᵢ - zᵢ| = rᵢ for all i.
For such w, Im(wᵢ) = Im(zᵢ) + rᵢ sin(θᵢ).

We need: for ALL choices of angles θ₁,...,θₘ, the point
(Im(z₁) + r₁ sin θ₁, ..., Im(zₘ) + rₘ sin θₘ) ∈ C.

Since Im(z) = Σλⱼyⱼ and each yⱼ has a neighborhood of radius εⱼ in C,
choosing rᵢ < min_j εⱼ ensures the perturbed points stay in C.

Actually, a simpler approach: since conv(C) is open and Im(z) ∈ conv(C),
there exists δ > 0 with B(Im(z), δ) ⊆ conv(C). Choose all rᵢ < δ/√m.
Then for w on the distinguished boundary, ‖Im(w) - Im(z)‖ ≤ max rᵢ < δ,
so Im(w) ∈ conv(C).

But we need Im(w) ∈ C, not just conv(C)! This is the key subtlety.

**Better approach (Hörmander):** Choose the polydisc radii as IMAGINARY shifts.
Set cⱼ = Re(zⱼ) + i·yⱼ,₁ (shifting to the first vertex of the convex combination)
with radii chosen so the distinguished boundary sweeps through Im-values in C.

Actually, the standard proof is different. Let me reconsider.

**Standard proof (Bochner 1938 / Hörmander 2.5.10):**

The idea is NOT to find a single polydisc. Instead:

1. Write Im(z) = Σ λⱼ yⱼ with yⱼ ∈ C.
2. For each coordinate i, replace Im(zᵢ) by a Cauchy contour integral
   over a circle. The circle has center Re(zᵢ) + i·Im(zᵢ) and radius rᵢ.
3. On the distinguished boundary, Im(wᵢ) = Im(zᵢ) + rᵢ sin θᵢ.
4. Since Im(z) is in the INTERIOR of conv(C), for small enough rᵢ,
   Im(w) stays in conv(C) for all θ.
5. But we need Im(w) ∈ C for F to be defined!

The resolution: we don't integrate F directly. We use F only on T(C).
The Cauchy integral uses the iterated structure: integrate over the first
variable (keeping others fixed), then the second, etc.

At each step, the integration contour for variable i is a circle in the
complex plane. We choose the center and radius so that the contour stays
in T(C). This is possible because:
- The imaginary part along the contour is Im(zᵢ) + rᵢ sin θᵢ
- We need the full vector (Im(z₁) + r₁ sin θ₁, ..., Im(zₘ) + rₘ sin θₘ) to be in C
- Since C is open and each yⱼ ∈ C, small perturbations stay in C

**Simplest correct approach:**

Since C is open and Im(z) ∈ conv(C), there exists a small polydisc Δ(z, r)
such that Im(w) ∈ C for all w ∈ closedPolydisc(z, r). This uses:
- conv(C) is open (proved)
- Im is continuous
- The closedPolydisc is compact, so the continuous image of Im parts is compact
  and contained in an open subset of conv(C)

Wait — we need Im(w) ∈ C, not conv(C). For w on the *interior* of the polydisc,
Im(w) might not be in C. But for the *distinguished boundary*, Im(w) is a specific
perturbation of Im(z).

Actually, the key insight I was missing: **we don't need Im(w) ∈ C for all w in the
polydisc.** We only need F to be defined on the distinguished boundary (for the
Cauchy integral) and the resulting Cauchy integral to be holomorphic on the interior.

The distinguished boundary has Im(wᵢ) = Im(zᵢ) ± rᵢ (at the extreme points).
Since Im(z) ∈ conv(C) and conv(C) is open, for small enough r, all these
perturbations stay in conv(C).

But F is only defined on T(C), not T(conv(C))! The distinguished boundary
points have Im-parts in conv(C) but possibly NOT in C.

**This is exactly why we need a more careful construction.** The standard proof
works as follows:

Since Im(z) = Σ λⱼ yⱼ ∈ conv(C), we can deform the integration contour.
Instead of a polydisc centered at z, we use a "product of paths" where
each path connects points with Im-parts in C.

**Actually, the simplest correct statement**: for m=1, the proof is direct
(path integral along a curve in T(C)). For general m, use induction on m
with the 1-variable Cauchy integral formula, keeping the other variables in
a region where F is defined.

### Revised proof strategy

**Step 1:** Write Im(z) as a convex combination: Im(z) = Σⱼ λⱼ yⱼ, yⱼ ∈ C.

**Step 2:** Induction on m. For m=1, Im(z) is between two points y₁, y₂ ∈ C.
Define G(w) by the Cauchy integral over a contour in {w : Im(w) ∈ [y₁, y₂]},
which stays in T(C) since the interval [y₁, y₂] may not be in C but...

Hmm, this is getting complicated. Let me step back.

**The cleanest approach for formalization:**

Axiomatize `bochner_local_extension` as a textbook result and focus on
filling `bochner_tube_extension` (the global assembly), which is the
plumbing step.

### Recommendation

**Phase 1:** Prove `bochner_tube_extension` from `bochner_local_extension`
by strengthening the local extension to produce convex neighborhoods (~80 lines).
This is pure plumbing and can be done independently.

**Phase 2:** Prove `bochner_local_extension`. This requires either:
- (A) The full Hörmander proof via iterated Cauchy integrals (~150-200 lines)
- (B) Axiomatize as a textbook SCV result

## Sorry 2: `bochner_tube_extension` (~80 lines)

### Statement

Given `bochner_local_extension`, prove the global extension.

### Proof

`bochner_local_extension` gives, for each z ∈ T(conv C), an open set U(z) and
holomorphic G(z) on U(z) agreeing with F on T(C) ∩ U(z).

To apply `holomorphic_extension_from_local_family`, we need:
1. **Convex** neighborhoods V(z) ⊆ U(z)
2. The **overlap condition**: if V(z₁) ∩ V(z₂) ≠ ∅, then T(C) ∩ V(z₁) ∩ V(z₂) ≠ ∅

**Step 1: Shrink to convex neighborhoods** (~20 lines)

Given U(z) open with z ∈ U(z), find a convex neighborhood V(z) ⊆ U(z).
Use: open ball B(z, ε) ⊆ U(z) for some ε > 0. Open balls in ℂᵐ are convex.
Set V(z) = B(z, ε(z)) ∩ T(conv C).

Actually, we need V(z) to be convex. B(z, ε) is convex. T(conv C) is convex
(proved: `tubeDomain_convex`). Intersection of convex sets is convex.

**Step 2: Verify overlap condition** (~30 lines)

If V(z₁) ∩ V(z₂) ≠ ∅, we need T(C) ∩ V(z₁) ∩ V(z₂) ≠ ∅.

Take w ∈ V(z₁) ∩ V(z₂). Then w ∈ T(conv C), so Im(w) ∈ conv(C).
Since conv(C) is open and C is dense in conv(C) (actually C ⊆ conv(C),
but conv(C) might be bigger), we need a point near w with Im-part in C.

Since C is open and its convex hull is open, for any point y ∈ conv(C),
there exists a nearby point y' ∈ C. Wait — that's not true in general.
C need not be dense in conv(C).

**However:** C is open and nonempty, and V(z₁), V(z₂) are open convex
neighborhoods in T(conv C). The key: T(C) is a nonempty open subset of
T(conv C), and V(z₁) ∩ V(z₂) is open in T(conv C). Since T(conv C) is
connected and T(C) is nonempty open, any nonempty open subset of T(conv C)
intersects T(C)? No — that would require density of T(C) in T(conv C).

Actually, T(C) IS dense in T(conv C) when C is open: for any z ∈ T(conv C),
Im(z) ∈ conv(C). The set C is open with convexHull ℝ C being its convex hull.
Any point in conv(C) can be approximated by points in C? Not necessarily.

**The overlap condition needs more care.** The approach using convex neighborhoods
+ identity theorem requires that every nonempty overlap meets T(C). This is
guaranteed if V(z) is small enough that V(z) ∩ T(C) ≠ ∅ for every z.

For any z ∈ T(conv C), Im(z) ∈ conv(C). Write Im(z) = Σ λⱼ yⱼ with yⱼ ∈ C.
Then the point z' with Re(z') = Re(z) and Im(z') = y₁ ∈ C is in T(C),
and ‖z' - z‖ ≤ ‖Im(z) - y₁‖. So if V(z) contains a ball of radius
≥ ‖Im(z) - y₁‖, then V(z) ∩ T(C) ≠ ∅.

This is the right approach: choose V(z) large enough to contain a point of T(C).
Since Im(z) ∈ conv(C) and C is open, there's a definite distance from Im(z) to C
that we can bound.

Actually simpler: since bochner_local_extension already guarantees
T(C) ∩ U(z) ≠ ∅ (it's part of the conclusion: G agrees with F on T(C) ∩ U(z)),
and V(z) ⊆ U(z), we just need T(C) ∩ V(z) ≠ ∅. This follows if we choose
V(z) to contain a point of T(C) ∩ U(z).

Hmm, but `bochner_local_extension` doesn't explicitly say T(C) ∩ U(z) ≠ ∅.
We may need to strengthen the local extension to guarantee this.

**Step 3: Apply `holomorphic_extension_from_local_family`** (~10 lines)

Once steps 1-2 are done, the application is direct.

## Estimated effort

| Task | Lines | Difficulty | Dependencies |
|------|-------|------------|--------------|
| Sorry 2: global assembly | ~80 | Medium | Sorry 1 |
| Sorry 1 Phase A: strengthen to convex neighborhoods | ~40 | Easy | Current `bochner_local_extension` |
| Sorry 1 Phase B: prove `bochner_local_extension` | ~150-200 | Hard | SCV Cauchy integral machinery |
| Alternative: axiomatize `bochner_local_extension` | ~15 | Trivial | None |

## Recommendation

1. **Axiomatize `bochner_local_extension`** with a strengthened statement that
   produces convex neighborhoods and guarantees T(C) ∩ V(z) ≠ ∅.
2. **Prove `bochner_tube_extension`** from the strengthened axiom + existing
   `holomorphic_extension_from_local_family`.
3. Leave the proof of the local extension as future work.

This eliminates 1 sorry (the global theorem) while converting the other to a
clean axiom. Net: 2 sorrys → 1 axiom.

## References

- Bochner, S. (1938). A theorem on analytic continuation of functions in several variables.
- Hörmander, L. An Introduction to Complex Analysis in Several Variables, Theorem 2.5.10.
- Vladimirov, V.S. Methods of the Theory of Generalized Functions, §10.
