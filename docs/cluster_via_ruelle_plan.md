# Cluster theorem via Ruelle's bound + dominated convergence

Status: 2026-05-05. Vetted by Gemini deep-think (this round confirmed
Route (i) executes correctly with the right uniform bound).

Supersedes: `route_i_plan.md`, `wick_rotated_pairing_eq_W_plan.md`,
`cluster_routeA_plan.md`. (Files retained until execution starts so we
keep the trail of corrections; deleted once we begin coding.)

## Architecture

Single textbook axiom (Ruelle's bound) + honest integration theory.

```
[ruelle_analytic_cluster_bound] (Ruelle 1962 / Jost VI.1, AXIOM)
                |
                v
[uniform-in-a polynomial bound on F_ext(wick(x_n, x_m+a))]
                |
                v  (combined with Schwartz seminorms of f, g)
[a-independent integrable dominator H(x_n, x_m)]
                |
                v  (combined with pointwise analytic cluster)
[Mathlib MeasureTheory.tendsto_integral_of_dominated_convergence]
                |
                v
W_analytic_cluster_integral
```

## Step 1: the textbook axiom

**Ruelle's Cluster Theorem** (Ruelle 1962, also Jost *General Theory of
Quantized Fields* §VI.1, also Streater-Wightman §3.4):

For Wightman functions satisfying R0-R4, the analytic continuation of
the n+m-point function admits a *uniform-in-a* polynomial bound for
spatially-separated arguments:

```lean
axiom ruelle_analytic_cluster_bound
    {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d) (n m : ℕ) :
    ∃ (C : ℝ) (N : ℕ) (R : ℝ),
      0 < C ∧ 0 < R ∧
      ∀ (z₁ : Fin n → Fin (d + 1) → ℂ),
      ∀ (z₂ : Fin m → Fin (d + 1) → ℂ),
        z₁ ∈ ForwardTube d n →
        z₂ ∈ ForwardTube d m →
        ∀ (a : SpacetimeDim d), a 0 = 0 → ‖a⃗‖ > R →
          ‖(W_analytic_BHW Wfn (n + m)).val
              (Fin.append z₁ (fun k μ => z₂ k μ + (if μ = 0 then 0 else (a μ : ℂ))))‖
            ≤ C * (1 + ‖z₁‖ + ‖z₂‖) ^ N
```

The crucial property: **the constant `C` and exponent `N` are
independent of `a`**. This is what the standard `spectrum_condition`'s
polynomial bound DOES NOT give us.

**Reference**: Ruelle 1962, *On the asymptotic condition in quantum field
theory*, Helvetica Physica Acta 35. Also Jost, *The General Theory of
Quantized Fields* §VI.1. The bound is a consequence of the spectral gap
between the vacuum (P = 0) and the rest of the spectrum, induced by the
distributional cluster property R4.

## Step 2: pointwise analytic cluster

Pointwise convergence of `W_analytic(z₁, z₂ + a) → W_analytic(z₁) ·
W_analytic(z₂)` as `|⃗a| → ∞` for each fixed `(z₁, z₂)` in the
respective forward tubes. **Two paths**:

**Option (a)**: Derive from `Wfn.cluster` (R4 distributional) +
spectrum_condition's analytic continuation + edge-of-wedge. Check the
project's BHW infrastructure for `bhw_pointwise_cluster_forwardTube` or
analogous.

**Option (b)**: Axiomatize as a second textbook lemma,
`ruelle_analytic_cluster_pointwise`. Same citation as Step 1.

Decide based on what the project already has. If `bhw_pointwise_cluster_forwardTube`
or similar exists and applies, use option (a); otherwise option (b).

## Step 3: dominator construction

For OPTR-supported Schwartz `f, g`:

* Apply the substitution `y = x_m - a` (Lebesgue-invariant) so the
  integrand becomes `F_ext(wick(x_n, y + a)) · f(x_n) · g(y)`.
* By **Step 1's uniform bound** plus `‖wick z‖ = ‖z‖`:
  ```
  |F_ext(wick(x_n, y + a))| ≤ C(1 + ‖x_n‖ + ‖y‖)^N
  ```
  for `‖a⃗‖ > R`. Crucially, **no `a` factor**.
* Schwartz seminorms of `f, g` (orders `K, M` chosen with `K, M > N + d`):
  ```
  |f(x_n)| ≤ ‖f‖_K (1 + ‖x_n‖)^{-K},
  |g(y)|   ≤ ‖g‖_M (1 + ‖y‖)^{-M}.
  ```
* Combined dominator:
  ```
  H(x_n, y) := C ‖f‖_K ‖g‖_M (1 + ‖x_n‖)^{N - K} (1 + ‖y‖)^{N - M}.
  ```
  This is integrable on `NPointDomain d n × NPointDomain d m` for
  `K, M` sufficiently large, and **independent of `a`**.

## Step 4: dominated convergence

Apply `MeasureTheory.tendsto_integral_of_dominated_convergence`:

* Filter: `cobounded` on the spatial part of `a` (intersected with
  `a 0 = 0`).
* Functions: `F_a(x_n, y) := F_ext(wick(x_n, y+a)) · f(x_n) · g(y)`.
* Pointwise limit: by Step 2, `F_a → F_∞` where
  `F_∞(x_n, y) := F_ext(wick x_n) · F_ext(wick y) · f(x_n) · g(y)`.
* Uniform integrable bound: `H(x_n, y)` from Step 3.

The conclusion:
```
∫ F_a → ∫ F_∞ = (∫ F_ext(wick x_n) f) · (∫ F_ext(wick y) g)
```
as `|⃗a| → ∞` along spatial directions. The integral form on the LHS,
after undoing the `y = x_m - a` substitution, is exactly the
joint Wick-rotated integral `∫ F_ext(wick(x_n, x_m+a)) · (f ⊗ g_a)(x_n,
x_m) dx_n dx_m`.

Convert `Tendsto` to the `∃ R, ∀ |⃗a| > R, ‖...‖ < ε` form expected by
`W_analytic_cluster_integral` via `Metric.tendsto_atTop` or analogous.

## Effort estimate (per Gemini, vetted)

* **Step 1** (axiom statement + citation): ~10 lines.
* **Step 2** (pointwise cluster): ~30 lines if existing project lemma
  applies; ~20 lines axiom + 10 lines wrapper if axiomatized.
* **Step 3** (dominator construction): ~50–80 lines of seminorm
  bookkeeping.
* **Step 4** (DC application + Tendsto-to-ε form conversion): ~50–80 lines.

**Total: ~150–200 lines.** Tractable in a focused session.

## Risk points (vetted by Gemini round 2)

* Polynomial-growth obstruction: **resolved** by Ruelle's uniform bound
  (Step 1). The previous Route (i) attempt failed because we tried to
  use `spectrum_condition`'s a-DEPENDENT bound, which is too weak.
* Edge-of-wedge for pointwise cluster: **may already be in project**;
  if not, axiomatize separately.
* Hidden Lean engineering complexity: low risk — all primitives exist
  in Mathlib (`MeasureTheory.tendsto_integral_of_dominated_convergence`,
  Schwartz seminorms, `cobounded` filter on `Fin d → ℝ`).

## Cleanup once Step 1 is in place

* Delete `WickRotatedPairingEqW.lean` (false-bridge route; preserve
  `wick_OPTR_in_forwardTube` by moving to `BHWTranslation.lean`).
* Delete:
  - `wick_rotated_pairing_eq_W_plan.md`
  - `wick_rotated_pairing_eq_W_question_for_gemini.md`
  - `cluster_routeA_plan.md`
  - `route_i_plan.md`
* Convert `W_analytic_cluster_integral` (in `SchwingerAxioms.lean:3786`)
  from `theorem` with `sorry` to `theorem` proved via Steps 1-4 above.
* Add the axiom `ruelle_analytic_cluster_bound` to a suitable location,
  with full citation and the brief justification:
  > Ruelle's bound is the spectral-gap content of R4. It is the uniform-in-a
  > polynomial bound on `W_analytic` for spatially-separated configs. Without
  > it, the standard `spectrum_condition`'s a-dependent bound is too weak
  > for dominated convergence.
* Add to `docs/cluster_axiom_vetting.md` the round-3 Gemini verdict on
  this strategy.
