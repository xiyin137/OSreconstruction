# Proving `edge_of_the_wedge` via Iterated Cauchy Integrals

> **STATUS: COMPLETED** — The `edge_of_the_wedge` axiom has been eliminated and
> replaced with a proved theorem using `SCV.edge_of_the_wedge_theorem` from
> `SCV/TubeDomainExtension.lean`. This document is retained for historical reference.

## Goal (ACHIEVED)

Eliminate the `edge_of_the_wedge` axiom in `AnalyticContinuation.lean` by proving
the multi-dimensional theorem from `edge_of_the_wedge_slice` (already sorry-free)
using iterated Cauchy integrals on polydiscs.

## The Gap

`edge_of_the_wedge_slice` gives, for each real point x₀ ∈ E and direction η ∈ C,
a 1D holomorphic extension G along the complex line w ↦ x₀ + wη. But for m ≥ 2,
there are **gap points** z near E where Im(z) ∉ C ∪ (-C) ∪ {0} — neither f_plus
nor f_minus is defined there, and no single 1D slice reaches them.

The standard fix: define F at gap points via iterated Cauchy integrals using the
boundary value bv as the integrand.

## Proof Strategy

### Step 0: Define polydiscs

```
Polydisc (c : Fin m → ℂ) (r : Fin m → ℝ) : Set (Fin m → ℂ) :=
  { z | ∀ i, ‖z i - c i‖ < r i }
```

For x₀ ∈ E, choose r > 0 small enough that the real polydisc
{t ∈ ℝᵐ : |tⱼ - x₀ⱼ| < r} ⊂ E. Then define F on the complex polydisc
Polydisc(x₀_ℂ, r) by the Cauchy integral.

### Step 1: Define F via iterated Cauchy integral

For w in a complex polydisc around x₀ ∈ E:

```
F(w) = (2πi)⁻ᵐ ∮_{|t₁-x₀₁|=r} ··· ∮_{|tₘ-x₀ₘ|=r}
         bv(Re t₁,...,Re tₘ) / ∏ⱼ(tⱼ - wⱼ) dt₁···dtₘ
```

where each ∮ is a `circleIntegral` (interval integral over [0,2π] via `circleMap`).

In Lean, this is m nested applications of `circleIntegral`:

```lean
def cauchyPolydisc (bv : (Fin m → ℝ) → ℂ) (x₀ : Fin m → ℝ) (r : ℝ)
    (w : Fin m → ℂ) : ℂ :=
  (2 * π * I)⁻¹ ^ m * iteratedCircleIntegral m (fun t =>
    bv (fun i => (t i).re) * ∏ i, (t i - w i)⁻¹) x₀ r
```

where `iteratedCircleIntegral` is defined by induction on m.

### Step 2: F is holomorphic on the polydisc

**Claim:** w ↦ F(w) is holomorphic (i.e., `DifferentiableOn ℂ F (Polydisc x₀ r)`).

**Proof approach:** Differentiate under the integral sign in each variable wⱼ.
For fixed w with |wⱼ - x₀ⱼ| < r, the integrand t ↦ bv(t) / ∏(tⱼ - wⱼ) is
a smooth function of wⱼ (since |tⱼ - x₀ⱼ| = r > |wⱼ - x₀ⱼ|, so tⱼ ≠ wⱼ),
and the derivative (tⱼ - wⱼ)⁻² is bounded on the circle.

Mathlib has: `HasDerivAt` for parameter-dependent integrals, and
`DifferentiableOn` for circle integrals with holomorphic dependence on a parameter.
Specifically, `hasDerivAt_integral_of_dominated_loc_of_lip` or the complex
differentiation lemmas in `CauchyIntegral.lean`.

### Step 3: F agrees with f_plus on TubeDomain(C) ∩ polydisc

**Claim:** For z in TubeDomain(C) ∩ Polydisc(x₀, r), F(z) = f_plus(z).

**Proof:**
1. f_plus is holomorphic on TubeDomain(C), which is open.
2. f_plus extends continuously to E (by hypothesis `hf_plus_bv`).
3. On real points t with |tⱼ - x₀ⱼ| = r (the integration contour),
   f_plus(t_ℂ) = bv(t) by the boundary value hypothesis.
4. The 1D Cauchy integral formula (already in Mathlib) gives: for each fixed
   t₂,...,tₘ on their circles, the inner integral in t₁ recovers f_plus.
5. By Fubini + induction on m, the full iterated integral equals f_plus(z).

Alternatively: both F and f_plus are holomorphic on the connected open set
TubeDomain(C) ∩ Polydisc(x₀, r), and they agree on a real open set
(where both equal bv). By the identity theorem, they agree everywhere on
this connected component.

### Step 4: F agrees with f_minus on TubeDomain(-C) ∩ polydisc

Symmetric to Step 3.

### Step 5: Glue local extensions

Each x₀ ∈ E gives an extension F_{x₀} on Polydisc(x₀, r(x₀)). On overlaps,
F_{x₀} and F_{x₁} agree on TubeDomain(C) ∩ overlap (both equal f_plus), so
by the identity theorem they agree on the full overlap. Define:

```
U = ⋃_{x₀ ∈ E} Polydisc(x₀, r(x₀))
F(z) = F_{x₀}(z) for any x₀ with z ∈ Polydisc(x₀, r(x₀))
```

This is well-defined, open, contains E_ℂ, and F is holomorphic on U.

### Step 6: Uniqueness

Any G holomorphic on U agreeing with f_plus on U ∩ TubeDomain(C) must equal F
on each Polydisc(x₀, r(x₀)) by the identity theorem (they agree on the open set
TubeDomain(C) ∩ Polydisc, which is nonempty since C ≠ ∅).

## Mathlib Building Blocks

### Available (no new development needed)

| Component | Mathlib Location | Used In |
|-----------|-----------------|---------|
| `circleIntegral` | `MeasureTheory.Integral.CircleIntegral` | Steps 1-3 |
| Cauchy integral formula (1D) | `Analysis.Complex.CauchyIntegral` | Step 3 |
| `DiffContOnCl` predicate | `Analysis.Calculus.DiffContOnCl` | Steps 2-3 |
| Fubini theorem | `MeasureTheory.Integral.SetIntegral` | Step 3 |
| `HasDerivAt` under integral | `Analysis.Calculus.ParametricIntegral` | Step 2 |
| Power series / analyticity | `Analysis.Complex.CauchyIntegral` | Step 2 |
| `circleMap` parametrization | `MeasureTheory.Integral.CircleIntegral` | Step 1 |

### Needs Development

| Component | Est. LOC | Difficulty | Notes |
|-----------|----------|------------|-------|
| `Polydisc` definition + basic API | 30-50 | Easy | Open, convex, product of balls |
| `iteratedCircleIntegral` definition | 40-60 | Easy | Induction on dimension |
| Fubini for iterated circle integrals | 80-120 | Medium | Circle integrals are interval integrals over [0,2π]; need to show joint integrability of continuous integrand on product of circles |
| Polydisc Cauchy formula | 100-150 | Medium | Induction on m: 1D Cauchy in innermost variable, Fubini to commute |
| Holomorphicity of Cauchy integral | 60-100 | Medium | Differentiate under the integral; bounded integrand on compact domain |
| Agreement with f_± | 50-80 | Easy-Medium | Identity theorem on connected tube ∩ polydisc |
| Gluing + well-definedness | 40-60 | Easy | Identity theorem on overlaps |

**Total estimate: 400-620 lines**

## Proof Skeleton in Lean

```lean
-- New file: OSReconstruction/SCV/PolydiscCauchy.lean

/-- A polydisc in ℂᵐ. -/
def Polydisc (c : Fin m → ℂ) (r : Fin m → ℝ) : Set (Fin m → ℂ) :=
  { z | ∀ i, ‖z i - c i‖ < r i }

theorem polydisc_isOpen : IsOpen (Polydisc c r) := ...
  -- Finite intersection of preimages of open balls

/-- Iterated circle integral: integrate f over m circles. -/
noncomputable def iteratedCircleIntegral :
    (m : ℕ) → ((Fin m → ℂ) → ℂ) → (Fin m → ℂ) → (Fin m → ℝ) → ℂ
  | 0, f, c, _ => f c  -- or: f (fun _ => 0), depending on convention
  | m+1, f, c, r =>
    ∮ z in C(c 0, r 0),
      iteratedCircleIntegral m (fun w => f (Fin.cons z w)) (Fin.tail c) (Fin.tail r)

/-- The Cauchy kernel on a polydisc. -/
def cauchyKernel (w : Fin m → ℂ) (t : Fin m → ℂ) : ℂ :=
  ∏ i, (t i - w i)⁻¹

/-- Cauchy integral representation on a polydisc. -/
def cauchyRepr (bv : (Fin m → ℝ) → ℂ) (c : Fin m → ℂ) (r : Fin m → ℝ)
    (w : Fin m → ℂ) : ℂ :=
  ((2 * π * I : ℂ)⁻¹) ^ m *
    iteratedCircleIntegral m (fun t => bv (fun i => (t i).re) * cauchyKernel w t) c r

/-- Cauchy formula for polydiscs: if f is holomorphic on Polydisc(c,r) and
    continuous on its closure, then f(w) = (2πi)⁻ᵐ ∮...∮ f(t)/∏(tⱼ-wⱼ) dt. -/
theorem cauchy_formula_polydisc
    (hf : DifferentiableOn ℂ f (Polydisc c r))
    (hf_cont : ContinuousOn f (closure (Polydisc c r)))
    (hw : w ∈ Polydisc c r) :
    f w = cauchyRepr (fun t => f (fun i => (t i : ℂ))) c r w := by
  -- Induction on m, using 1D Cauchy + Fubini
  sorry

/-- The Cauchy representation is holomorphic in w. -/
theorem cauchyRepr_differentiableOn
    (hbv : ContinuousOn bv (closure (realPolydisc c r))) :
    DifferentiableOn ℂ (cauchyRepr bv c r) (Polydisc c r) := by
  -- Differentiate under the integral sign
  sorry

/-- Main theorem: edge_of_the_wedge from cauchyRepr. -/
theorem edge_of_the_wedge_proof [conditions] :
    ∃ U F, IsOpen U ∧ E_ℂ ⊆ U ∧ DifferentiableOn ℂ F U ∧
      (∀ z ∈ U ∩ TubeDomain C, F z = f_plus z) ∧
      (∀ z ∈ U ∩ TubeDomain (-C), F z = f_minus z) := by
  -- U = ⋃ polydiscs, F = cauchyRepr on each
  -- Agreement via identity theorem
  sorry
```

## Key Risks and Mitigations

**Risk 1: Fubini for circle integrals.**
Circle integrals use `intervalIntegral` over [0, 2π] with the `circleMap`
parametrization. Applying Fubini requires showing the composed integrand is
in L¹ of the product measure. Since the integrand is continuous and the domain
is compact ([0,2π]ᵐ), this is automatic — but spelling it out in Lean requires
showing `Integrable` for the product, which involves `MeasureTheory.integral_prod`.
**Mitigation:** The integrand is continuous on a compact set, so `Continuous.integrable`
on `volume.restrict (Set.Icc 0 (2*π))` handles it.

**Risk 2: Identity theorem on Polydisc ∩ TubeDomain(C).**
We need this intersection to be connected (not just nonempty). A polydisc centered
at a real point x₀ intersected with TubeDomain(C) is connected because it's the
set {z : |zⱼ - x₀ⱼ| < r, Im(z) ∈ C}, which is path-connected (connect any two
points by first moving real parts, then imaginary parts within C).
**Mitigation:** Prove path-connectedness directly; convexity of C helps.

**Risk 3: Relating bv to f_plus on the integration contour.**
The Cauchy integral uses bv(Re t) on circles |tⱼ - x₀ⱼ| = r, but the contour
points are complex (not real). We need: as the contour degenerates to real points,
f_plus(t) → bv(Re t). This is exactly the boundary value hypothesis, but applied
at points on the circle (not at the center).
**Mitigation:** For circles of radius r in the real polydisc, all contour points
ARE real (Im = 0), so f_plus(t_ℂ) = bv(t) by continuity up to the boundary.
Actually — the circle in ℂ centered at x₀ⱼ ∈ ℝ passes through complex points.
We should instead integrate bv along real intervals and use the 1D Cauchy formula
with bv as boundary data. This requires a slightly different formulation: use
rectangular contours (Mathlib has `integral_boundary_rect_eq_zero`) or restrict
to real integration + Poisson kernel. **This needs more thought.**

**Alternative for Risk 3:** Instead of integrating bv on circles, define F
locally as f_plus (or f_minus) where available, and use `edge_of_the_wedge_slice`
to define F on the real subspace. Then use Osgood's lemma: F is continuous
(by construction + slice boundary values) and separately holomorphic in each
variable (by 1D Cauchy integral in that variable with the other variables held
at their current complex values — but this circularly requires F to be defined
at those complex values).

**Cleaner alternative:** Use the **Bochner-Martinelli kernel** instead of iterated
Cauchy. Or more simply: define F at a gap point z by choosing ANY η ∈ C such
that the 1D slice through z hits the tube, and use the slice extension. The
issue is showing this is independent of the choice of η — but that follows from
the identity theorem applied to the 1D extensions.

## Alternative: Slice-Based Construction

A potentially simpler approach that avoids iterated Cauchy integrals entirely:

1. For each gap point z near E, find a **finite collection** of 1D slices
   connecting z to points in TubeDomain(C) through intermediate real points.
2. Use `edge_of_the_wedge_slice` at each step to extend.
3. Show the result is independent of the path (identity theorem).
4. Show the resulting F is holomorphic (Osgood: continuous + separately holomorphic).

This avoids polydiscs entirely but requires:
- A geometric lemma: any point in a small ball around x₀ ∈ ℝᵐ can be reached
  from TubeDomain(C) by a chain of at most m 1D moves
- Continuity of F (from the slice boundary values)
- Osgood's lemma (already proved in the codebase)

This approach is closer to what we already have and may be **shorter** (~300 LOC).

## Recommendation

Start with the **slice-based construction** since it builds directly on
`edge_of_the_wedge_slice` and `osgood_lemma`, both already sorry-free.
Fall back to iterated Cauchy integrals only if the geometric connectivity
argument proves harder than expected.
