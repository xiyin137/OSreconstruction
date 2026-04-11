# Gemini Deep Think Reviews: Vladimirov-Tillmann Proof Plan

## Review 1 (2026-03-31)

### Assessment
Exceptionally well-designed and mathematically mature formalization plan. Successfully decomposes a monolithic textbook theorem into a clean DAG of four phases.

### Critical Issues Found

**Phase 1: Over-scoped**
- Mathlib 4 already has `ConvexCone.InnerDual`, `ProperCone`, bipolar theorem, Hahn-Banach separation
- Reduce from ~400 to ~100 lines of glue wrapping `IsCone`/`IsSalientCone` to Mathlib's bundled types

**Phase 2: 1D Slicing Trap**
- Restricting tempered distributions to 1D rays requires topological tensor products of Frechet test functions, which is heavily lacking in Mathlib
- Fix: Use Fourier-side ODE method instead (CR equations become distributional ODEs)

**Phase 3: Frechet Calculus Blocker**
- "z -> psi_z is holomorphic into Schwartz space" fails to typecheck: Mathlib's `Differentiable` requires `NormedAddCommGroup`/`NormedSpace`, but Schwartz space is Frechet
- Fix: Apply functional T first, show scalar F(z) = T(psi_z) is holomorphic via difference quotients + uniform seminorm bounds + Hartogs

**Phase 4: Spatial Primitive Blocker**
- Vladimirov's regularization F = D^k[G] requires multi-dimensional complex antiderivatives (Poincare lemma) — multi-month project
- Fix: Fourier-side ODE method. U_y = e^{-y.xi} U_0, support in C* from growth bounds, BV from DCT on Fourier side

**Cluster Property**
- Forward light cone is NOT a product cone; Poisson kernel does not factorize
- Defer this axiom elimination

### Revised Estimates
Phase 1: ~400 -> ~100 lines
Phase 2: ~350 -> ~250 lines
Phase 3: ~700 -> ~900 lines (added Schwartz limit verbosity)
Phase 4: ~900 -> ~750 lines (Fourier ODE simpler than spatial primitives)
Total: ~2350 -> ~2000 lines

---

## Review 2 (2026-03-31)

### Assessment
Updated plan is exceptional. Perfectly assimilated Lean 4 type-system constraints. Reduced implementation risk from "multi-month open research" to a bounded, deterministic software engineering task.

### Remaining Hidden Traps

**Trap 1: Dual Frechet Calculus in Phases 2 & 4**

The Fourier-side ODE workaround `d/dy_j U_y = -xi_j U_y` with solution `U_y = e^{-y.xi} U_0` has TWO issues:

1. Maps into S' are also not `Differentiable` (S' is not NormedSpace). Lean won't typecheck `d/dy_j U_y`.
2. Multiplying U_0 by `e^{-y.xi}` is globally ill-typed: `e^{-y.xi}` grows exponentially where `y.xi < 0`, so it's not a valid Schwartz multiplier.

**Fix: Scalarize & Compact Support**
- Fix phi in C_c^inf(R^m). The function xi -> e^{y.xi} phi(xi) is bounded (compact support) and belongs to S.
- Define scalar function g_phi(y) = <U_y, e^{y.xi} phi>
- Compute scalar derivative d/dy_j g_phi(y) using CR equations — evaluates to 0
- Conclude g_phi(y) is constant, defining <U_0, phi>
- Support deduction: pick phi supported outside C*. By separation, exists y in C with y.xi < -c < 0 on supp(phi). The test function e^{ty.xi} phi blows up as t -> inf, but Vladimirov bounds force polynomial bound on <U_ty, phi>. Exponential vs polynomial contradiction gives <U_0, phi> = 0.

**Trap 2: Phase 3 Difference Quotient**

Do NOT attempt algebraic Taylor expansions inside Schwartz seminorms. Multi-index calculus gets unreadable.

**Fix: Integral MVT**
```
(psi_{z+he_j} - psi_z)/h - d/dz_j psi_z = (1/h) integral_0^h (d/dz_j psi_{z+te_j} - d/dz_j psi_z) dt
```
Pass Schwartz seminorm through the integral via `norm_integral_le_integral_norm`. Uses existing `schwartzPsiZ_seminorm_horizontal_bound`.

**Trap 3: Phase 1 Topology**

Mathlib's `ProperCone.innerDual` and Hahn-Banach are written for `InnerProductSpace R E`. But `Fin m -> R` has L^inf norm by default, which has no inner product.

**Fix**: Cast to `EuclideanSpace R (Fin m)` or use `PiLp` type synonyms inside `SCV/DualCone.lean`.

### Final Verdict
DAG is rock solid, line estimates realistic (~2000), mathematical architecture immune to Lean 4's topological constraints. Cleared to begin execution on Phase 1.

---

## Review 3 (2026-03-31)

### Assessment
Masterclass in proof engineering for Lean 4. 99% ready for execution.

### Two Final Traps

**Trap 1: Phase 3 — Bochner integrals of Frechet spaces**

The integral MVT workaround writes `integral_0^1 (d/dz_j psi_{z+te_j} - d/dz_j psi_z) dt`. But Lean's Bochner integral (`∫ t, f t`) requires codomain to be `NormedSpace R`. SchwartzMap is Frechet, so `∫ t, (SchwartzMap) dt` fails typeclass synthesis and evaluates to junk (0).

**Fix — pointwise scalarization:**
1. Fix x in R^m and multi-indices alpha, beta
2. Define the purely scalar function `f(t) = x^beta * d^alpha_x [d/dz_j psi_{z+the_j}(x)]`
3. Apply standard 1D real-interval integral to f(t) natively in Lean
4. Apply `norm_integral_le_integral_norm` to the scalar integral
5. Bound the scalar integrand uniformly in x using `schwartzPsiZ_seminorm_horizontal_bound`
6. Take supremum over x outside the integral — proves Schwartz-topology convergence without ever integrating a Frechet-valued curve

**Trap 2: Phase 4 converse — S' upgrade blocker**

The scalarized ODE gives U_0 defined on C_c^inf. To upgrade to S', one would write `<U_0, psi> = <U_y, e^{y.xi} psi>`, but `e^{y.xi} psi(xi)` is NOT Schwartz (exponential growth). So the ODE method cannot prove U_0 is tempered.

**Fix — 1D ray integration (avoids both Poincare lemma AND Fourier traps):**
1. Fix eta in C. Approach boundary along ray y = t*eta, t > 0.
2. Vladimirov bound along ray: `|F(x+it*eta)| <= C(1+|x|)^N * t^{-q}`
3. Define 1D ray integral using `intervalIntegral`:
   `G_1(x,t) = integral_{t_0}^{t} F(x+i*tau*eta) * i dtau`
4. By CR equations: `(eta . nabla_x) G_1(x,t) = F(x+it*eta) - F(x+it_0*eta)`
5. Iterate q+1 times. The t^{-q} singularity integrates to t^1.
6. G_{q+1}(x,t) extends continuously to t=0 as H(x) with polynomial growth
7. H is continuous + polynomially bounded, so trivially defines a tempered distribution
8. Boundary value: `W = (eta . nabla_x)^{q+1} H + (smooth t_0 correction terms)`

Constructs W in S' directly in the spatial domain using only basic 1D real integrals.

### Final Verdict
10/10. All Lean 4 structural traps neutralized. Cleared to begin Phase 1.

---

## Review 4 (2026-03-31)

### Assessment
Absolute masterpiece of proof engineering. Mathematically rigorous, formally executable, perfectly optimized for Mathlib. Ready to code.

### Implementation Pro-Tips

**Pro-tip 1: Cauchy's formula for repeated integration (Phase 4)**

Defining iterated integrals in Lean requires recursive functions + Fubini-Tonelli swaps by induction = massive boilerplate. Bypass with Cauchy's formula for repeated integration:

```
G_k(x,t) = (i^k / (k-1)!) * integral_{t0}^{t} (t-tau)^{k-1} F(x+i*tau*eta) dtau
```

where k = floor(q) + 1. This is ONE integral, ONE `norm_integral_le_integral_norm`. The integrand `(t-tau)^{k-1} * tau^{-q}` is absolutely integrable since k > q. As t -> 0, converges cleanly to H(x).

**Pro-tip 2: Distributional derivatives by duality (Phase 4)**

H(x) is only continuous, not differentiable. Do NOT try to differentiate H in Lean (Sobolev spaces are a trap). Instead define W directly via integration by parts:

```
<W, phi> = (-1)^k * integral H(x) * ((eta . nabla_x)^k phi(x)) dx + <smooth t0 terms, phi>
```

Since phi is Schwartz, its k-th derivative is Schwartz. Integral of polynomially-bounded continuous H against Schwartz phi trivially converges. Defines W in S' in a few lines, bypassing differentiability entirely.

### Suggested PR Strategy

- **PR 1**: Phases 1+2 (~350 lines) — Geometry & Support (DualCone.lean + FourierSupportCone.lean)
- **PR 2**: Phase 3 (~900 lines) — Core Bridge (PaleyWienerSchwartz.lean)
- **PR 3**: Phase 4 (~750 lines) — Capstone (VladimirovTillmann.lean) — axiom removal

### Final Verdict
10/10. Transformed open-ended formalization research into deterministic software engineering. Cleared to begin.
