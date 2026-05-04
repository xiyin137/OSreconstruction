# Schwinger Cluster Theorem: Obstacle and Options

**Context.** We want to prove the cluster decomposition property for Wick-rotated boundary integrals (the Schwinger functions on OPTR-supported test functions) — `W_analytic_cluster_integral` in `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`. This document explains the obstacle we hit while pursuing the dominated-convergence-based approach (route i) and lays out three options for resolving it.

---

## What we want to prove

For a Wightman QFT `Wfn` and OPTR-supported test functions `f : SchwartzNPoint d n` and `g : SchwartzNPoint d m`, as the spatial shift `|⃗a| → ∞`:

$$\Big| \int F_{\text{ext}}(\text{wick}\,x) (f \otimes g_a)(x)\,dx - \Big(\int F_{\text{ext}}(\text{wick}\,x_n) f(x_n)\,dx_n\Big)\Big(\int F_{\text{ext}}(\text{wick}\,x_m) g(x_m)\,dx_m\Big)\Big| \to 0$$

where $g_a(x_m) := g(x_m - a)$ and $F_{\text{ext}}$ is the BHW analytic continuation of the Wightman 2-point function evaluated at Wick-rotated configurations.

---

## What we proved (route i, partial)

Branch: `r2e/permuted-forward-tube-cluster` (~140 lines proved).

1. **Pointwise cluster on a.e. configurations** (`W_analytic_BHW_cluster_pointwise_aux`, ~80 lines). For a.e. $(x_n, x_m)$ with all $(n+m)$ joint times distinct and positive, after the change of variable $u := x_m - a$:
   $$F_{\text{ext}}(\text{wick}(\text{append}\,x_n\,(u+a))) - F_{\text{ext}}(\text{wick}\,x_n) F_{\text{ext}}(\text{wick}\,u) \xrightarrow{|⃗a|\to\infty} 0$$
   This uses the textbook axiom `bhw_pointwise_cluster_permutedForwardTube` (Streater-Wightman Theorem 3-5) plus σ-permutation witnesses for the joint Wick-rotated configuration in the forward tube.

2. **Disconnected term integrability** (`cluster_disconnected_term_integrable`, ~30 lines). The product
   $$|F_{\text{ext}}(\text{wick}\,x_n) f(x_n)| \cdot |F_{\text{ext}}(\text{wick}\,u) g(u)|$$
   is integrable on `NPointDomain d n × NPointDomain d m`, by Fubini + the existing `wick_rotated_kernel_mul_zeroDiagonal_integrable`.

These are the *building blocks* for a dominated-convergence proof. The remaining work was supposed to be the dominator construction.

---

## The obstacle

To use Mathlib's dominated convergence theorem (`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`), we need a **single integrable function `D(x_n, u)` that bounds the difference integrand uniformly in `a` for all sufficiently large `|⃗a|`**:

$$\Big|\big(F_{\text{ext}}(\text{wick}(\text{append}\,x_n\,(u+a))) - F_{\text{ext}}(\text{wick}\,x_n) F_{\text{ext}}(\text{wick}\,u)\big) f(x_n) g(u)\Big| \leq D(x_n, u)$$

uniformly in `a`. The obstruction is in the joint kernel.

### The forward-tube growth bound

`hasForwardTubeGrowth_of_wightman` gives constants `C, N, q` such that on the forward tube,

$$\|F_{\text{ext}}(z)\| \cdot \mathrm{infDist}(z, \text{coincidence})^{q+1} \leq C(1 + \|z\|)^N.$$

For our joint Wick-rotated configuration $z = \text{wick}(\text{append}\,x_n\,(u+a))$:

- **Norm bound**: $\|z\| \leq \|x_n\| + \|u\| + |⃗a|$ (since spatial part of m-block contains $u + a$).
- **infDist bound**: For $|⃗a| > 2(\|x_n\|+\|u\|)$, cross-block distance $\geq |⃗a|/2$, so
  $\mathrm{infDist} \geq \min(\text{intra}_n, \text{intra}_u, |⃗a|/2)$.
  In the regime where $|⃗a|/2$ dominates: $\mathrm{infDist} \geq |⃗a|/2$.

Therefore in the large-$|⃗a|$ regime:

$$\|F_{\text{ext}}(z)\| \leq \frac{C(1+\|x_n\|+\|u\|+|⃗a|)^N}{(|⃗a|/2)^{q+1}} = O\big((1+|⃗a|)^N \cdot |⃗a|^{-(q+1)}\big) \cdot O((1+\|x_n\|)^N(1+\|u\|)^N)$$

(using $(1+a+b+c) \leq (1+a)(1+b)(1+c)$).

### Schwartz decay covers the test-function factors but not the parameter

The Schwartz seminorms of `f` give: for any `K`, $|f(x_n)| \leq C_K (1+\|x_n\|)^{-K}$. Similarly for `g(u)`.

Applying this to bound the integrand:

$$|\text{joint kernel}(z) \cdot f(x_n) g(u)| \leq C \cdot (1+\|x_n\|)^{N-K}(1+\|u\|)^{N-K} \cdot (1+|⃗a|)^N \cdot |⃗a|^{-(q+1)}$$

For `K > N + d + 1`, the `(1+\|x_n\|)^{N-K}(1+\|u\|)^{N-K}` factor is integrable in `(x_n, u)`. **But the `(1+|⃗a|)^N · |⃗a|^{-(q+1)} = O(|⃗a|^{N-q-1})` factor depends on `a`** and is *not bounded uniformly in `a`* unless `N ≤ q+1` (a mass-gap-style assumption).

### Why this is an actual obstruction

Mathlib's `tendsto_integral_filter_of_dominated_convergence` requires the dominator to be a single integrable function not depending on the parameter. We can write the integrand bound as `D(x_n, u) · h(a)` where `D` is integrable and `h` is unbounded — but DCT cannot use this form.

The Schwartz decay of `f, g` is in the *test-function-argument* directions (`x_n`, `u`), not in the parameter direction (`a`). There's no mechanism in route (i) to absorb the `(1+|⃗a|)^N` factor.

Moreover, the **pointwise** convergence we proved establishes the integrand goes to 0 *for each fixed* `(x_n, u)` — that's correct. But pointwise convergence + a-dependent dominator does not give convergence of the integral, which is what cluster requires.

### Mass gap saves it but isn't a generic hypothesis

If `Wfn` has a mass gap `m₀ > 0`, the spectral measure is supported in `{p : p² ≥ m₀²}`, and the analyticity-tube growth has `N ≤ q+1` (or even exponential decay), so the dominator becomes a-independent. Mass gap is true for many physical theories but is a *separate* hypothesis on `Wfn`, not implied by R0–R4. The cluster decomposition E4 does *not* require mass gap.

---

## Why textbooks don't have this problem

Glimm-Jaffe §19.4, Streater-Wightman §3.4, OS 1973 §3 all derive Schwinger cluster from Wightman cluster (R4). Their approach is **not** to apply dominated convergence directly to the Wick-rotated integral. Instead, they:

1. Build the **GNS Hilbert space** from R0–R2 (Wightman reconstruction).
2. Get **strongly continuous unitary translations** `U(a)` on it.
3. Apply **SNAG / Bochner** to extract the **joint spectral measure** `ρ` on momentum space, supported in `V⁺` (forward light cone) by R3.
4. Decompose `ρ = ρ_{vacuum} \cdot \delta_0 + \rho^T` where `ρ^T` is the **truncated** (connected) spectral measure.
5. R4 cluster ⇔ `ρ^T(\{0\}) = 0` (no atom at zero momentum in the truncated sector).
6. **Schwinger cluster follows by Riemann-Lebesgue** applied to `ρ^T` against the spatial Fourier kernel — no `(1+|⃗a|)^N` factor appears because the spectral integral has no kernel polynomial growth.

The key insight: **in spectral coordinates, the Wick-rotated integral is a pure spectral Fourier transform**, and its decay follows directly from spectral measure properties. The polynomial-growth obstruction is an artifact of working in *position-space coordinates* (which is what route (i) does).

---

## Three options

### Option (R1) Revive Källén-Lehmann infrastructure

We have a parked branch `r2e/kallen-lehmann-step1` with the spectral approach already started. It contains:

- `snag_theorem` axiom (Reed-Simon VIII.12) — joint spectral measure for unitary representations of `ℝ^{d+1}`. Already on main from PR #81.
- `vacuum_spectral_measure_W2` (axiom, Bochner application) — spectral measure of `W_2`.
- `W2_spectral_support_in_forwardCone` (axiom) — `μ ⊆ V⁺_closure`.
- `W2_spectral_atom_at_zero` (axiom) — atom at 0 equals `|W_1|²`.
- `kallen_lehmann_representation` (proved, 5-line theorem) — packages all of these.

What's needed to close cluster via this route:

1. **Truncated decomposition** for `W_n^T = W_n - \sum_\pi \prod W^T_{|\pi_i|}` over partitions (~few hundred lines, pure combinatorics).
2. **Spectral cluster lemma**: for finite Borel measure `ρ` on `ℝ^{d+1}` supported in `V⁺` with `ρ(\{0\}) = 0`, the spatial Fourier integral
   $\int \hat f(p) \hat g(p)^* e^{i\vec a \cdot \vec p}\,d\rho(p) \to 0$
   as `|⃗a| → ∞`. (~few hundred lines, Riemann-Lebesgue + spectral support.)
3. **Bridge from spectral cluster to Wick-rotated integral cluster** (~few hundred lines, uses analytic continuation properties).

**Cost estimate**: 6–9 weeks of focused work (per the parked KL plan doc).

**Pros**: Aligned with textbooks. Reusable infrastructure for mass gap, asymptotic completeness, particle interpretation. Already partially built.

**Cons**: Multi-week effort. Requires adding `truncated decomposition` machinery.

---

### Option (R2) Direct textbook axiom for Schwinger cluster

Add a single axiom that directly states the conclusion we want, citing the textbook proofs:

```lean
/-- **Schwinger cluster decomposition** (textbook axiom).

For Wightman functions satisfying R0–R4, the Wick-rotated boundary
integrals against OPTR-supported test functions cluster as the spatial
shift grows.

Reference: Streater-Wightman §3.4, Theorem 3-5; Glimm-Jaffe §19.4,
Theorem 19.4.1; Osterwalder-Schrader 1973, §3 (Axiom E4).

Proof sketch (deferred): R4 cluster on Wightman distributions + spectrum
condition R3 → spectral measure of the truncated 2-point function has no
zero-momentum atom → Riemann-Lebesgue gives Schwinger cluster on
Wick-rotated integrals. The polynomial-growth obstruction in
position-space coordinates is bypassed by working with the spectral
measure (cf. `OSReconstruction/Wightman/Spectral/KallenLehmann.lean`
on branch `r2e/kallen-lehmann-step1`). -/
axiom Schwinger_cluster_E4 :
  -- ... full statement of the cluster bound ...
  sorry
```

**Cost estimate**: ~1 hour (just write the axiom + audit table entry + Gemini-vet).

**Pros**: Closes the sorry immediately. Honest about what's textbook content. Aligns with the project's existing axiom-management discipline.

**Cons**: Adds one more axiom to the audit table. Doesn't build the spectral infrastructure that R1 would.

---

### Option (R3) Add mass-gap hypothesis to the cluster theorem

Restrict the cluster theorem statement to Wightman QFTs with a mass gap. Under this hypothesis, the polynomial-growth obstruction disappears because `N ≤ q+1` (or stronger exponential decay). Route (i)'s DCT argument then goes through.

```lean
theorem W_analytic_cluster_integral_with_mass_gap
    (Wfn : WightmanFunctions d) (h_mass_gap : ∃ m₀ > 0, ...)
    ...
```

**Cost estimate**: ~1–2 weeks (the existing route-i scaffolding works given the assumption).

**Pros**: Makes route (i) work without textbook axioms. Sufficient for many physical applications.

**Cons**: Severely limits applicability. The cluster theorem in its standard generic form (E4) does *not* require mass gap. Future users would have to prove mass gap separately for any concrete `Wfn`, which is itself non-trivial.

---

## Recommendation

**Option (R1) — revive KL infrastructure.** Reasons:

1. **Aligns with textbooks.** The spectral approach is what Streater-Wightman, Glimm-Jaffe, and OS 1973 actually use.
2. **Reusable.** The KL/spectral machinery is needed elsewhere too (mass gap, asymptotic completeness, R3 spectral form, Källén-Lehmann representation for higher-point functions, etc.).
3. **Already partially built.** The parked branch has SNAG axiomatized, vacuum spectral measure axiomatized, V⁺ support axiomatized, atom-at-zero axiomatized, and `kallen_lehmann_representation` proved. The remaining infrastructure (truncated decomposition, spectral cluster lemma, the bridge) is well-scoped.
4. **xi yin's review of PR #81** already accepted SNAG as a checkpoint axiom for exactly this purpose. The policy decision is in place.

**Fallback to (R2)** if R1 timeline isn't acceptable. The textbook citation is honest, the audit table grows by one well-cited axiom, and the cluster sorry closes immediately. Future work can then unaxiomatize the textbook claim by completing R1.

**Avoid (R3)** unless the cluster theorem's intended consumers all have mass gap (which they don't — OS reconstruction targets generic Wightman QFTs).

---

## What this means for current branches

- `r2e/permuted-forward-tube-cluster` (route i, 20 commits): the proven sub-lemmas (`exists_perm_wick_in_forwardTube_of_distinct_positive`, `W_analytic_BHW_cluster_pointwise_aux`, `cluster_disconnected_term_integrable`, `bhw_pointwise_cluster_permutedForwardTube` axiom) **remain useful** for either R1 or R2 — pointwise cluster bridges to the spectral measure setup. The Step D sub-lemmas (joint kernel polynomial bound, bounded-region DCT, tail bound) are blocked by this obstruction and should not be pursued further.
- `r2e/kallen-lehmann-step1` (route iii, 4 commits, parked): the spectral infrastructure to revive for R1.
- `main` (post-PR #81): SNAG axiom available; KL machinery can be reintroduced cleanly.

---

## References

- Streater, Wightman, *PCT, Spin and Statistics, and All That*, §3.4, Theorem 3-5 (Wightman cluster decomposition).
- Glimm, Jaffe, *Quantum Physics*, §19.4 Theorem 19.4.1 (Schwinger cluster from Wightman cluster).
- Osterwalder, Schrader, "Axioms for Euclidean Green's Functions", *Comm. Math. Phys.* 31 (1973), §3 (cluster derivation).
- Reed, Simon, *Methods of Modern Mathematical Physics, Vol. II*, §IX.8 (spectral support / V⁺).
- `docs/cluster_discharge_plan.md` (in this repo) — the route (i) plan, now flagged as architecturally insufficient.
- Branch `r2e/kallen-lehmann-step1` — KL infrastructure to revive for R1.
