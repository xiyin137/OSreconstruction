# Codex task: prove `block_regulator_dominator_integrable` (the cluster-DCT crux lemma)

## Goal

Replace the single `sorry` in the theorem `block_regulator_dominator_integrable`
in
`OSReconstruction/Wightman/Reconstruction/WickRotation/RuelleClusterBound.lean`
with a complete Lean 4 / Mathlib proof. **Prove only this lemma.** Do not touch
`W_analytic_cluster_integral_via_ruelle` (the downstream consumer) or its `sorry`.

Work on branch `r2e/cluster-dct-flatness` (already checked out). Do not introduce
any `axiom`, `admit`, or new `sorry`. If you get genuinely stuck, leave the
smallest possible `sorry` at the precise sub-goal and report exactly what blocked
you (statement of the open sub-goal + which Mathlib API was missing).

## The lemma (current statement, already type-checks)

```lean
theorem block_regulator_dominator_integrable {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (C : ℝ) (N M : ℕ) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        C * (1 + ‖(fun k => wickRotatePoint (x k))‖) ^ N
          * (1 + (tubeBoundaryDist (fun k => wickRotatePoint (x k)))⁻¹) ^ M
          * ‖f x‖) := by
  sorry
```

## Why this is true (the math — this is the whole point)

This dominator looks non-integrable: the regulator `(1 + Δ⁻¹)^M` blows up where
consecutive Euclidean times coincide. The prior project analysis concluded
"dominated convergence is structurally impossible." **That is wrong**, because the
test function `f` is *flat* exactly on that singular set.

Key facts:
1. **`f` vanishes to infinite order on the coincidence diagonal.**
   `OrderedPositiveTimeRegion d n` (defined in
   `OSReconstruction/Wightman/Reconstruction/Core.lean:1561`) is
   `{ x | ∀ i, 0 < x i 0 ∧ ∀ j, i < j → x i 0 < x j 0 }` — an **open** set
   (strict inequalities). Since `tsupport f ⊆` this open set, `f ≡ 0` on its
   complement, in particular on the closed half-spaces `{x | x_{k,0} ≤ x_{k-1,0}}`
   for every `k`. Mathlib helper: `image_eq_zero_of_notMem_tsupport`
   (used elsewhere in this same file — grep it).

2. **The regulator is controlled by the within-block time gaps.**
   `tubeBoundaryDist` (defined at `RuelleClusterBound.lean:141`) is
   `⨅ k, Metric.infDist (Im(z_k − z_{k-1})) (openForwardConeSet d)ᶜ`.
   For `z = wickRotatePoint ∘ x`, the imaginary part of `z_k` is the vector
   `(x_{k,0}, 0, …, 0)` (Wick rotation sends Euclidean time to imaginary time;
   spatial parts stay real). So `Im(z_k − z_{k-1}) = (gap_k, 0, …, 0)` with
   `gap_k = x_{k,0} − x_{k-1,0}` (and `x_{-1} := 0`, i.e. `gap_0 = x_{0,0}`).
   The infDist of `(s,0,…,0)` (for `s>0`) to `(openForwardConeSet)ᶜ` equals
   `s/√2` for the standard forward cone `{y_0 > ‖y_spatial‖}`. Hence
   `tubeBoundaryDist(wick x) = (min_k gap_k)/√2` on OPTR, so
   `tubeBoundaryDist(wick x)⁻¹ = √2 · max_k gap_k⁻¹` there. (You may instead prove
   a one-sided bound `tubeBoundaryDist(wick x) ≥ c·min_k gap_k` if the exact
   identity is painful — a lower bound on `tubeBoundaryDist` gives an upper bound
   on its inverse, which is all the dominator needs.) **Check the exact
   definition of `openForwardConeSet d` and `wickRotatePoint` before fixing the
   constant `c`** — confirm the signature/normalisation rather than trusting
   `√2`.

3. **Reduce to single-gap terms.** `(1 + Δ⁻¹)^M ≤ 2^M (1 + Δ⁻ᴹ)` and
   `Δ⁻¹ = max_k gap_k⁻¹ ≤ Σ_k gap_k⁻¹`, so
   `(1 + Δ⁻¹)^M ≤ 2^M (1 + (Σ_k gap_k⁻¹)^M) ≤ 2^M (1 + n^{M-1} Σ_k gap_k⁻ᴹ)`.
   It therefore suffices to show, for each fixed `k`, that
   `x ↦ (1+‖wick x‖)^N · gap_k⁻ᴹ · ‖f x‖` is integrable (plus the trivial
   `(1+‖wick x‖)^N · ‖f x‖` term, which is integrable because `f` is Schwartz).

4. **Single-gap integrability via 1-D Taylor + flatness.** Fix `k`. Because
   `f ≡ 0` on `{gap_k ≤ 0}`, all `gap_k`-derivatives of `f` vanish at `gap_k = 0`.
   View `f` along the `gap_k` coordinate: by Taylor with integral/Lagrange
   remainder based at `0` (Mathlib `taylor_mean_remainder_lagrange` /
   `taylor_mean_remainder`, which are **1-D**, `ℝ → ℝ`/`ℝ → E`), for `gap_k = s > 0`:
   `‖f(x)‖ ≤ (s^M / M!) · sup_{σ ∈ [0,s]} ‖∂_{gap_k}^M f (x with gap_k ← σ)‖`.
   Hence `s⁻ᴹ ‖f(x)‖ ≤ (1/M!) · sup_{σ∈[0,1]} ‖(∂_{gap_k}^M f)(…)‖` for `s ≤ 1`,
   and the `M`-th derivative of a Schwartz function is Schwartz, so the RHS has
   rapid decay in all remaining coordinates ⇒ integrable on `{s ≤ 1} × rest`. On
   `{s ≥ 1}`, `gap_k⁻ᴹ ≤ 1` and `f` is Schwartz ⇒ integrable. Combine.

   `gap_k` is a *linear* coordinate `x ↦ x_{k,0} − x_{k-1,0}`; pick a linear
   measure-preserving change of variables making `gap_k` one axis (or integrate
   in the `x_{k,0}` variable directly with the others fixed, via
   `MeasureTheory.integral`/Fubini `Measure.prod` and Tonelli for the
   nonneg-integrand integrability bound). The Schwartz-derivative sup bound should
   come from the Schwartz seminorms: `SchwartzMap.le_seminorm` /
   `SchwartzMap.decay'` / `SchwartzMap.norm_iteratedFDeriv_le_seminorm`-style API
   (grep Mathlib `Mathlib/Analysis/Distribution/SchwartzSpace.lean`).

## Suggested decomposition (prove helpers first, then assemble)

1. `wick_imParts`: `(fun μ => (wickRotatePoint (x k) μ).im) = fun μ => if μ = 0 then x k 0 else 0` (or whatever the actual `wickRotatePoint` def gives — verify it).
2. `tubeBoundaryDist_wick_lower`: `tubeBoundaryDist (wick∘x) ≥ c · ⨅ k, gap_k` (or the exact identity), `c > 0`.
3. `schwartz_flat_on_halfspace`: from `tsupport f ⊆ OPTR`, derive `f ≡ 0` on `{x | x_{k,0} ≤ x_{k-1,0}}` and the vanishing of `gap_k`-derivatives there.
4. `single_gap_integrable`: `Integrable (fun x => (1+‖wick x‖)^N · gap_k⁻ᴹ · ‖f x‖)`.
5. Assemble via 3 (reduce regulator to sum of single-gap terms) + `Integrable.add`/`.const_mul`/bound by an integrable dominator (`Integrable.mono'`).

Helper lemmas may be added above the main theorem in the same file (or a small
new file imported by it) — your choice; keep names mathlib-style.

## Build / verify

- Targeted check (fast, re-elaborates source against built deps):
  `lake env lean -DmaxHeartbeats=800000 OSReconstruction/Wightman/Reconstruction/WickRotation/RuelleClusterBound.lean`
  Success = exit 0 with **no `error:`**; the only acceptable `sorry` warning is the
  pre-existing one in `W_analytic_cluster_integral_via_ruelle` (≈ line 763). Your
  lemma must have **no** `sorry` warning when done.
- If you change imports or upstream, run `lake build OSReconstruction.SCV.VladimirovTillmann` first to refresh deps (there is a known cross-module
  cache trap — a targeted single-module refresh can leave downstream oleans
  inconsistent; if you see a spurious type mismatch, do `lake clean` + full
  `lake build` to confirm before trusting it).

## Conventions / constraints

- Mathlib-ready style (snake_case theorems, 100-col, `by` ends the line, one
  tactic per line). No `axiom`/`admit`/new `sorry`. Prefer the right generality
  but do not over-engineer.
- Do NOT modify the statement of `block_regulator_dominator_integrable`,
  `tubeBoundaryDist`, `wickRotatePoint`, `OrderedPositiveTimeRegion`, or the RACH
  structure. Only add helper lemmas + fill the proof.
- This lemma is the linchpin of the whole cluster-theorem discharge: if it proves,
  the remaining work is routine `tendsto_integral_filter_of_dominated_convergence`
  plumbing. If some sub-step is genuinely false or needs a missing Mathlib result,
  that is critical information — report it precisely rather than papering over it.

## Deliverable

A compiling `RuelleClusterBound.lean` where `block_regulator_dominator_integrable`
is `sorry`-free, plus a short note listing: helper lemmas added, any Mathlib API
gaps hit, and (if anything remains) the exact open sub-goal.
