# Cluster Discharge Plan — `W_analytic_cluster_integral`

**Status**: architecture closed, ~140 lines proved, ~330 lines remaining across 4 named sub-lemmas. Branch: `r2e/permuted-forward-tube-cluster` (16 commits, pushed to origin).

**Target sorry**: `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean::W_analytic_cluster_integral`.

**Statement**: For Wightman QFT and OPTR-supported test functions `f, g`,
$$\Big| \int F_\text{ext}(\text{wick}\,x) (f \otimes g_a)(x)\,dx - \Big(\int F_\text{ext}(\text{wick}\,x_n) f(x_n)\,dx_n\Big)\Big(\int F_\text{ext}(\text{wick}\,x_m) g(x_m)\,dx_m\Big)\Big| \to 0$$
as the spatial shift $|\vec a| \to \infty$.

This is the OS reconstruction Schwinger cluster property (E4) at the integral level.

---

## Architecture

The proof decomposes into three load-bearing pieces (proven), three sub-lemmas (sorry'd, with discharge plans), and a final combine step.

### Proven infrastructure

| Item | Location | Lines |
|---|---|---|
| `bhw_pointwise_cluster_permutedForwardTube` (axiom) | `SchwingerAxioms.lean` | textbook axiom — Streater-Wightman §2.4, Theorem 3-5 |
| `exists_perm_wick_in_forwardTube_of_distinct_positive` | `SchwingerAxioms.lean` | ~15 |
| `W_analytic_BHW_cluster_pointwise_aux` | `SchwingerAxioms.lean` | ~80 |
| `cluster_disconnected_term_integrable` | `SchwingerAxioms.lean` | ~30 |

### Sub-lemmas with discharge plans

| Item | Status | Discharge plan |
|---|---|---|
| `cluster_joint_kernel_polynomial_bound` | sorry | mirror `wick_rotated_kernel_mul_zeroDiagonal_integrable` (in `SchwingerTemperedness.lean`); shift-and-sort + infDist lower bound |
| `cluster_bounded_region_DCT` | sorry | `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` + proven pointwise cluster + uniform-on-B(M₀) dominator |
| `cluster_tail_bound` | sorry | Schwartz seminorm tail estimate + joint kernel polynomial bound |
| Outer combine | sorry | `integral_fin_append_split` + `integral_add_compl` + triangle inequality |

---

## The 6-step discharge plan

### Step A: a.e. distinct joint times — ✓ DONE

```lean
have hgood : ∀ᵐ (xy : NPointDomain d (n + m)) ∂volume,
    ∀ i j, i ≠ j → xy i 0 ≠ xy j 0 :=
  ae_pairwise_distinct_timeCoords
```

### Step B: σ-permutation witness — ✓ DONE

`exists_perm_wick_in_forwardTube_of_distinct_positive`: given a config with all-distinct positive times, `Tuple.sort` produces a permutation σ such that the σ-permuted Wick rotation lies in `ForwardTube`.

### Step C: Pointwise cluster — ✓ DONE

`W_analytic_BHW_cluster_pointwise_aux`: combines per-block + joint σ-witnesses + the permuted-tube axiom + the `wickRotatePoint_add` identity (using `a 0 = 0`) to produce the pointwise cluster bound for any config with distinct positive joint times.

### Step D: Uniform integrable dominator (~280 lines split into 3 sub-lemmas)

#### D2: `cluster_joint_kernel_polynomial_bound`

Mirror the technique in `SchwingerTemperedness.lean::wick_rotated_kernel_mul_zeroDiagonal_integrable` (~lines 1198–1300):

1. Extract `(C, N, q)` from `hasForwardTubeGrowth_of_wightman Wfn (n + m)`.
2. From a.e. distinct joint times, define `A := 1 + ∑ |joint_i 0|`, time-shift the joint config by `A` (uniform shift).
3. `π := Tuple.sort` on the shifted joint config.
4. Wick(joint_shifted ∘ π) ∈ `ForwardTube d (n+m)` via `euclidean_ordered_in_forwardTube`.
5. Bridge `F_ext(joint) = W_analytic_BHW(joint_shifted ∘ π)` via translation invariance + permutation invariance + ForwardTube agreement.
6. Apply forward-tube growth: `‖.‖ · infDist^{q+1} ≤ C(1+‖.‖)^N`.
7. infDist invariant under shift + permutation (each is an isometry preserving coincidence locus).
8. Inter-block lower bound: in the regime `|⃗a|² > 4(‖xy.1‖+‖xy.2‖)² + 4`, cross-block distance ≥ `|⃗a|/2`.
9. Combine + simplify.

**Key technical caveat**: the bound in this lemma is correct only when `|⃗a|/2 ≤ min(intra_n, intra_m)`. For small intra-block gaps, `infDist` is dominated by intra-block distances. The cluster proof handles this via `cluster_tail_bound` (D3), which uses Schwartz decay to dominate small intra-block configurations.

#### D3 / `cluster_bounded_region_DCT`

Apply Mathlib `tendsto_integral_filter_of_dominated_convergence` on the bounded set `B(M₀) := {(x_n, x_m) : ‖x_n‖+‖x_m‖ ≤ M₀}`. Inputs:

- **Pointwise convergence on B**: from `W_analytic_BHW_cluster_pointwise_aux` (proved).
- **Uniform-on-B integrable dominator**: on B with `|⃗a|` large, the joint kernel is uniformly bounded (since `‖z‖ ≤ M₀ + |⃗a| + const`, `infDist ≥ |⃗a|/2`). Schwartz norms of f, g give integrability.
- **Filter**: `Bornology.cobounded` on the spatial part of `a`.

Output: `Tendsto (λ a => ∫_B difference) cobounded (𝓝 0)` → `∃ R₁, ∀ |⃗a| > R₁, ‖∫_B difference‖ < δ`.

#### D4 / `cluster_tail_bound`

For any δ > 0, choose `M₀` large enough that `∫_{B(M₀)^c} difference < δ` uniformly in `a`. Combines:

- `cluster_joint_kernel_polynomial_bound` for the joint piece bound.
- Schwartz seminorm decay of f, g (taking K large enough to absorb the polynomial growth in `(‖x_n‖, ‖x_m‖, |⃗a|)`).
- For `|⃗a| > 1` and `‖x_n‖ + ‖x_m‖ > M₀`, the integrand decays like `(1+‖x_n‖)^{-(K-N)} (1+‖x_m‖)^{-(K-N)}`, integrable for `K > N + d`.

### Step E + F: Outer combine (~50 lines)

Inside `W_analytic_cluster_integral`, after extracting M₀ from `cluster_tail_bound` and R₁ from `cluster_bounded_region_DCT`:

1. **Fubini**: `LHS = ∫ F_ext(wick x) (f ⊗ g_a)(x) dx = ∫_n ∫_m F_ext(wick(append x_n x_m)) f(x_n) g_a(x_m) dx_m dx_n` via `integral_fin_append_split` (PR #72) + `tensorProduct_fin_append_apply`.

2. **g vs g_a collapse**: `∫_m K_m(wick x_m) g_a(x_m) dx_m = ∫_m K_m(wick x_m) g(x_m) dx_m` by spatial translation invariance of `K_m` (since `a 0 = 0` and `K_m(wick(x_m + a)) = K_m(wick x_m)`).

3. **Indicator decomposition**: `1 = indicator B + indicator B^c`, so the difference integrand splits.

4. **Triangle inequality**: `‖∫ D‖ ≤ ‖∫_B D‖ + ‖∫_{B^c} D‖ < ε/2 + ε/2 = ε`.

5. **Apply `hbounded` and `htail`** to get the two ε/2 bounds.

---

## Mathlib primitives identified

| Step | Primitive |
|---|---|
| Step A | `ae_pairwise_distinct_timeCoords` (in this codebase) |
| Step B | `Tuple.sort`, `euclidean_ordered_in_forwardTube` |
| Step C | `bhw_pointwise_cluster_permutedForwardTube` (axiom), `wickRotatePoint_add` |
| Step D2 | `hasForwardTubeGrowth_of_wightman`, `Tuple.sort`, `Metric.infDist`, `BHW.W_analytic_BHW.permutation_invariant` |
| Step D3 | `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` (`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:70`) |
| Step D4 | Schwartz seminorm bounds, integrability of (1+‖·‖)^{-K} on `Fin n → Fin (d+1) → ℝ` |
| Outer | `integral_fin_append_split` (PR #72), `MeasureTheory.integral_add_compl` (`Bochner/Set.lean:150`), `tensorProduct_fin_append_apply` |

---

## Audit table additions (for `README.md` "Current Status")

| Axiom | File:Line | Rating | Sources | Notes |
|-------|-----------|--------|---------|-------|
| `bhw_pointwise_cluster_permutedForwardTube` | SchwingerAxioms.lean | Standard | LP | Streater-Wightman Thm 3-5; derived from R4 + BHW symmetry |

---

## Effort estimate (calibrated to repo norms)

- D2 (joint kernel polynomial bound): **~120 lines**, 1–2 days focused.
- D3 (bounded-region DCT): **~80 lines**, 1 day focused.
- D4 (tail bound): **~80 lines**, 1 day focused.
- Outer combine: **~50 lines**, half day.

**Total: ~330 lines, ~4 focused days** to reach a sorry-free `W_analytic_cluster_integral`.

The ~140 lines of proved sub-pieces represent the hardest *mathematical* content — the architecture/orchestration is right and the remaining work is mechanical Lean engineering on top of named Mathlib primitives.

---

## References

* Streater-Wightman, *PCT, Spin and Statistics, and All That*, §2.4 + Theorem 3-5.
* Glimm-Jaffe, *Quantum Physics*, Chapter 19.
* Vladimirov, *Methods of the Theory of Generalized Functions*, §25.
* `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerTemperedness.lean::wick_rotated_kernel_mul_zeroDiagonal_integrable` — the pattern to mirror for D2.
