# Plan: Prove the Vladimirov-Tillmann Theorem

## Goal

Replace the `vladimirov_tillmann` axiom (`SCV/VladimirovTillmann.lean:85`) with a theorem, and prove its converse `vladimirov_boundary_value_existence`. Together these characterize the class of tube-holomorphic functions with tempered boundary values. This eliminates the project's most-used axiom and provides the converse needed for the boundary-value sorry in the OS reconstruction pipeline.

## The theorem

**Vladimirov-Tillmann** (Vladimirov, *Methods of SCV*, Theorem 25.5; Streater-Wightman, Theorems 2-6, 2-9):

Let C be an open convex salient cone in R^m, and T(C) = {z : Im(z) in C} the tube domain.

**Forward direction** (current axiom): If F is holomorphic on T(C) with tempered distributional boundary values W, then:
1. F has polynomial growth on compact subcones
2. F satisfies the global Vladimirov bound: `||F(z)|| <= C(1+||z||)^N (1+dist(Im z, dC)^{-1})^q`

**Converse direction** (needed for OS reconstruction): If F is holomorphic on T(C) with the global Vladimirov bound, then F has tempered distributional boundary values.

**Both directions** follow from the Fourier-Laplace representation: F belongs to this class iff F(z) = T(psi_z) where T is a tempered distribution with Fourier support in the dual cone C*.

## Lean 4 formalization blockers and workarounds

Two critical Lean 4 type-system issues affect the naive proof strategy.

### Blocker 1: Frechet calculus (Phase 3)

The natural statement "z -> psi_z is holomorphic into Schwartz space" cannot be expressed in Lean 4 because Mathlib's `Differentiable` typeclass requires `NormedAddCommGroup` and `NormedSpace`, but Schwartz space is a Frechet space (family of seminorms, not a single norm).

**Workaround**: Apply the functional T first. Show that the scalar function F(z) = T(psi_z) : C^m -> C is holomorphic by:
1. Form the complex difference quotient of F(z)
2. Move it inside T (by linearity)
3. Show the difference quotient of psi_z converges to d/dz_j psi_z in the Schwartz topology (bounded uniformly across all seminorms)
4. Use existing `schwartzPsiZ_seminorm_horizontal_bound` from `FourierLaplaceCore.lean`
5. Invoke `SCV/Osgood.lean` (Hartogs) to get joint holomorphicity from separate holomorphicity in each variable

### Blocker 2: Spatial primitives (Phase 4 converse)

The standard textbook proof of the converse uses Vladimirov's regularization: write F = D^k[G] where G has a uniform boundary approach. Formalizing this requires constructing a multi-dimensional complex antiderivative over an arbitrary cone, which needs the Poincare lemma for multi-variable complex path integration — a multi-month standalone project.

**Workaround: Fourier-side ODE method**. Bypass spatial primitives entirely:
1. Fix y in C. The global Vladimirov growth bound ensures F_y(x) = F(x+iy) has polynomial growth, so it defines a tempered distribution. Let U_y = FourierTransform[F_y].
2. The Cauchy-Riemann equations on F translate to a distributional ODE in Fourier space: `d/dy_j U_y(xi) = -xi_j U_y(xi)`
3. The solution is `U_y(xi) = e^{-y.xi} U_0(xi)` for a fixed distribution U_0 in S'
4. The global Vladimirov bound forces the multiplier `e^{-y.xi}` to not blow up, which strictly forces `supp(U_0) ⊆ C*`
5. The boundary value is the inverse Fourier transform of U_0. The limit as y -> 0 follows from DCT on the Fourier side, since `e^{-y.xi} <= 1` when `y in C` and `xi in C*`

This keeps us entirely in algebraic distribution manipulation and avoids structural SCV theorems.

### Note on cluster property

The plan originally included eliminating `distributional_cluster_lifts_to_tube` via the Poisson/Szego kernel factorization. However, the forward light cone is NOT a product cone, so the Poisson kernel does not factorize. This axiom elimination requires either restricting to product cones or formalizing generalized Bessel-function bounds. **Defer this** — focus on VT itself.

## Proof structure

### Phase 1: Dual cone glue (~100 lines)

**File**: `SCV/DualCone.lean` (new)

Mathlib already has extensive dual cone infrastructure:
- `Mathlib.Analysis.Convex.Cone.InnerDual` — `ConvexCone.innerDual`
- `Mathlib.Analysis.Convex.Cone.Proper` — `ProperCone` (closed, convex, pointed, solid)
- `ProperCone.innerDual_innerDual` — the bipolar theorem C** = closure(C)
- `ProperCone.hyperplane_separation'` — Hahn-Banach separation for cones

Since C is open, convex, salient, its closure is modeled by `ProperCone`. Phase 1 is **glue**, not construction from scratch:

**Bridge lemmas needed:**
- `IsCone_to_ConvexCone`: wrap unbundled `IsCone C` into Mathlib's bundled `ConvexCone`
- `IsSalientCone_to_ProperCone`: wrap `IsSalientCone (closure C)` into `ProperCone`
- `dualCone_nonempty_interior_of_salient`: if C is open convex salient, then C* has nonempty interior (via Mathlib's ProperCone API)
- `dualCone_separation`: for y not in closure(C), exists xi in C* separating (via Hahn-Banach)

**Lean 4 topology trap**: Mathlib's `ProperCone.innerDual` and Hahn-Banach require `InnerProductSpace R E`. But `Fin m -> R` has L^inf norm by default (no inner product). **Fix**: Use `EuclideanSpace R (Fin m)` or `PiLp 2 (fun _ : Fin m => R)` locally inside this file so Mathlib's `innerDual` triggers automatically.

### Phase 2: Multi-dimensional Fourier support (~250 lines)

**File**: `SCV/FourierSupportCone.lean` (new)

**Strategy**: Use the Fourier-side ODE method (from blocker 2 workaround) rather than 1D slicing. This avoids the trap of restricting tempered distributions to rays, which requires topological tensor products of Frechet test functions.

**Definition:**
```
HasFourierSupportInCone (C_star : Set (Fin m -> R)) (T : SchwartzMap ... ->L[C] C)
```

**Key theorem** (forward direction, via scalarized Fourier ODE):
Given F holomorphic on T(C) with BV W, show W has Fourier support in C*.

**Lean 4 trap**: Maps into S' are not `Differentiable` (S' is not NormedSpace), and multiplying a distribution by `e^{-y.xi}` is globally ill-typed (exponential growth, not a Schwartz multiplier).

**Fix — scalarize against compactly supported test functions:**
1. Fix phi in C_c^inf(R^m). Since phi has compact support, `xi -> e^{y.xi} phi(xi)` is bounded and in S.
2. Define the scalar function `g_phi(y) = <U_y, e^{y.xi} phi>` where U_y = FT[F_y].
3. Compute the scalar derivative `d/dy_j g_phi(y)` using CR equations on the scalar F under the integral sign — evaluates to 0.
4. Conclude `g_phi(y)` is constant in y, defining `<U_0, phi>`.
5. **Support deduction**: Pick phi supported strictly outside C*. By the separation theorem (Phase 1), there exists y in C with `y.xi < -c < 0` on supp(phi). The test function `e^{ty.xi} phi` blows up as t -> inf, but the Vladimirov bounds force `<U_{ty}, phi>` to be polynomially bounded. Exponential vs polynomial contradiction gives `<U_0, phi> = 0`, proving supp(U_0) in C*.

This is entirely scalar ODE + scalar contradiction, no Frechet calculus needed.

### Phase 3: Paley-Wiener-Schwartz bridge (~900 lines)

**File**: `SCV/PaleyWienerSchwartz.lean` (new)

The core theorem: Fourier support in C* implies the FL representation with growth bounds.

**Main theorem:**
```
theorem paley_wiener_schwartz_tube
    (C, hC_open, hC_conv, hC_cone, hC_salient)
    (T : SchwartzMap ... ->L[C] C)
    (hsupp : HasFourierSupportInCone (DualCone C) T) :
    let F := fun z => T (schwartzPsiZ z)
    DifferentiableOn C F (TubeDomain C) ∧
    HasFourierLaplaceRepr C F ∧
    [global Vladimirov growth bound]
```

**Proof sketch (using blocker 1 workaround):**

1. **Holomorphicity** (~300 lines): Show F(z) = T(psi_z) is holomorphic as a scalar map.
   - Fix z, compute difference quotient (F(z+h*e_j) - F(z))/h
   - Move inside T by linearity: T((psi_{z+h*e_j} - psi_z)/h)
   - Show (psi_{z+h*e_j} - psi_z)/h -> d/dz_j psi_z in Schwartz topology as h -> 0
   - **Lean 4 tactic**: Use pointwise-scalarized integral MVT (NOT multi-index Taylor, NOT Bochner integral of Schwartz curves — Lean's Bochner integral requires NormedSpace codomain, which Schwartz space isn't):
     - Fix x in R^m and multi-indices alpha, beta
     - Define scalar `f(t) = x^beta * d^alpha_x [d/dz_j psi_{z+the_j}(x)]`
     - Apply standard 1D scalar integral: remainder = `(1/h) integral_0^h (f(t) - f(0)) dt`
     - Apply `norm_integral_le_integral_norm` to this scalar integral
     - Bound integrand uniformly in x using `schwartzPsiZ_seminorm_horizontal_bound`
     - Take sup over x outside the integral — proves Schwartz-topology convergence
   - Get separate holomorphicity in each z_j, then apply Osgood/Hartogs (`SCV/Osgood.lean`)

2. **Growth estimate** (~300 lines): |F(x+iy)| = |T(psi_{x+iy})| <= ||T||_S * ||psi_{x+iy}||_S
   - Schwartz seminorms of psi_z: polynomial in x, dist(y,dC)^{-M} near boundary
   - Reuse `schwartzPsiZ_seminorm_horizontal_bound`
   - Combine to get global Vladimirov bound

3. **Boundary value recovery** (~300 lines): As epsilon -> 0+, smeared integral recovers T(f)
   - Use existing DCT infrastructure from `LaplaceSchwartz.lean`
   - `fourierLaplaceExt` formula: F(z) = T(FT[psi_z])

### Phase 4: Vladimirov-Tillmann proof (~750 lines)

**File**: `SCV/VladimirovTillmann.lean` (replace axiom with theorem)

**Forward direction** (BV -> growth) (~350 lines):
1. Given F holomorphic on T(C) with tempered BV W
2. By Phase 2 (Fourier ODE): W has Fourier support in C*
3. By Phase 3 (PW-Schwartz): F = W(psi_z) satisfies FL representation with growth bounds
4. Extract conclusions 1 and 2

**Converse direction** (growth -> BV) (~400 lines):
1. Given F holomorphic on T(C) with global Vladimirov growth
2. **1D ray integration method** (avoids both Poincare lemma AND Fourier S' upgrade trap):
   - Fix eta in C. Along ray y = t*eta: `|F(x+it*eta)| <= C(1+|x|)^N * t^{-q}`
   - Define 1D ray integral via `intervalIntegral`:
     `G_1(x,t) = integral_{t0}^{t} F(x+i*tau*eta) * i dtau`
   - By CR: `(eta . nabla_x) G_1(x,t) = F(x+it*eta) - F(x+it0*eta)`
   - Use **Cauchy's formula for repeated integration** (avoids recursive iterated integrals + Fubini boilerplate). Let k = floor(q)+1:
     ```
     G_k(x,t) = (i^k / (k-1)!) * integral_{t0}^{t} (t-tau)^{k-1} F(x+i*tau*eta) dtau
     ```
     ONE integral, ONE `norm_integral_le_integral_norm`. Integrand `(t-tau)^{k-1} * tau^{-q}` is absolutely integrable since k > q. Converges cleanly to H(x) as t -> 0.
   - H is continuous + polynomially bounded => defines a tempered distribution
   - Define boundary value W via **distributional derivative by duality** (do NOT differentiate H — it's only continuous, Sobolev spaces are a trap):
     ```
     <W, phi> = (-1)^k * integral H(x) * ((eta . nabla_x)^k phi(x)) dx
                + <smooth t0 correction, phi>
     ```
     Since phi is Schwartz, its k-th derivative is Schwartz. Integral of polynomially-bounded H against Schwartz trivially converges. Defines W in S' in a few lines.
   - This constructs W in S' using only 1D real integrals — no Poincare lemma, no Fourier multiplier traps
3. Produce `T : SchwartzMap ... ->L[C] C` and prove BV convergence

**Note on the Fourier ODE approach**: The scalarized ODE from Phase 2 gives U_0 on C_c^inf, but upgrading to S' fails because `e^{y.xi} psi(xi)` is not Schwartz (exponential growth). The ray integration method bypasses this entirely by staying in the spatial domain.

## Existing infrastructure to reuse

| File | What it provides | Used in |
|------|-----------------|---------|
| `SCV/FourierLaplaceCore.lean` | `schwartzPsiZ`, seminorm bounds, `fourierLaplaceExt` | Phase 3 |
| `SCV/LaplaceSchwartz.lean` | `HasFourierLaplaceRepr`, DCT arguments, linearity proofs | Phases 3-4 |
| `SCV/PaleyWiener.lean` | 1D `HasOneSidedFourierSupport` (reference, not directly reused) | Phase 2 |
| `SCV/TubeDomainExtension.lean` | `TubeDomain`, openness, connectedness | All phases |
| `SCV/DistributionalUniqueness.lean` | Mollification, translation operators | Phase 4 |
| `SCV/Osgood.lean` | Separate analyticity / Hartogs | Phase 3 |
| Mathlib `ConvexCone.InnerDual` | Dual cone, bipolar theorem, separation | Phase 1 |

## Dependencies between phases

```
Phase 1 (Dual Cone Glue)
    |
Phase 2 (Fourier Support via ODE)
    |
Phase 3 (PW-Schwartz Bridge)
    |
Phase 4 (VT Proof + Converse)
    |
Eliminates: vladimirov_tillmann axiom
Provides:   vladimirov_boundary_value_existence (converse)
```

## Estimated scope

| Phase | Lines | Difficulty | Key risk |
|-------|-------|-----------|----------|
| 1. Dual cone glue | ~100 | Low | Mathlib API matching |
| 2. Fourier support (ODE) | ~250 | Medium | Distributional ODE formalization |
| 3. PW-Schwartz bridge | ~900 | Hard | Schwartz seminorm limits for holomorphicity |
| 4. VT proof + converse | ~750 | Hard | Growth estimate bookkeeping |
| **Total** | **~2000** | | |

## PR strategy

- **PR 1**: Phases 1+2 (~350 lines) — `SCV/DualCone.lean` + `SCV/FourierSupportCone.lean`. Geometry and Fourier support foundation, independently useful.
- **PR 2**: Phase 3 (~900 lines) — `SCV/PaleyWienerSchwartz.lean`. The core bridge theorem, hardest pure-Lean engineering.
- **PR 3**: Phase 4 (~750 lines) — `SCV/VladimirovTillmann.lean`. Capstone: axiom elimination.

## Verification

After Phase 4:
1. `lake build OSReconstruction.SCV.VladimirovTillmann` — no axiom, builds clean
2. `#print axioms vladimirov_tillmann` — no `sorryAx` or custom axioms
3. `lake build OSReconstruction.Wightman.Reconstruction.Main` — downstream consumers still build
4. Axiom count reduced by 1 (VT); converse direction available for boundary-value sorry

## Deferred

- `distributional_cluster_lifts_to_tube` axiom elimination — requires Poisson kernel analysis for non-product cones (forward light cone). Separate project.

## References

- Vladimirov, *Methods of the Theory of Generalized Functions* (2002), Ch. II §14, Ch. V §25-26
- Hormander, *The Analysis of Linear PDOs I* (1990), §7.4
- Reed-Simon II, Theorem IX.16
- Streater & Wightman, *PCT, Spin and Statistics, and All That*, Theorems 2-6 and 2-9
