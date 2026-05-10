# `RuelleAnalyticClusterHypotheses.bound` vacuity concern

**Date**: 2026-05-08
**Surfaced during**: L4 (uniform polynomial bound) axiom-vetting via Gemini chat.
**Status (2026-05-08, later)**: **Repaired via Option A** (boundary-distance regulator). See "Resolution" at the bottom.
**Severity**: medium — pre-existing structural issue; resolved on branch `r2e/ruelle-l5-grind`.

## Summary

The `bound` field of `RuelleAnalyticClusterHypotheses` in
`OSReconstruction/Wightman/Reconstruction/WickRotation/RuelleClusterBound.lean:151–167`
was, as originally formulated, **mathematically unsatisfiable** for
any actual Wightman QFT. Adding a production axiom asserting it would
have introduced inconsistency (the system would prove `False`). The
conditional cluster theorem consuming `RuelleAnalyticClusterHypotheses`
was formally correct but its premise was vacuous in general — only
model-specific or boundary-restricted instances could supply it.

## The current bound

```lean
bound : ∃ (C : ℝ) (N : ℕ) (R : ℝ),
  0 < C ∧ 0 < R ∧
  ∀ (z₁ : Fin n → Fin (d + 1) → ℂ),
  ∀ (z₂ : Fin m → Fin (d + 1) → ℂ),
    z₁ ∈ ForwardTube d n →
    z₂ ∈ ForwardTube d m →
    ∀ (a : SpacetimeDim d), a 0 = 0 →
      (∑ i : Fin d, (a (Fin.succ i)) ^ 2) > R ^ 2 →
      (joint_config) ∈ PermutedExtendedTube d (n + m) →
      ‖(W_analytic_BHW Wfn (n + m)).val (joint_config)‖
        ≤ C * (1 + ‖z₁‖ + ‖z₂‖) ^ N
```

The constants `C, N` are quantified **outside** `∀ z₁, z₂`. The bound
must therefore hold uniformly over the entire forward tube, with the
polynomial only in `‖z‖` (which does not blow up at the tube boundary).

## Free-field counterexample

For `n = m = 2`, Wick's theorem gives
```
W_4(z₁,₁, z₁,₂, z₂,₁ + a, z₂,₂ + a)
  = W₂(z₁,₁, z₁,₂) · W₂(z₂,₁ + a, z₂,₂ + a)
  + W₂(z₁,₁, z₂,₁ + a) · W₂(z₁,₂, z₂,₂ + a)
  + W₂(z₁,₁, z₂,₂ + a) · W₂(z₁,₂, z₂,₁ + a)
```

The first term:
- Decomposes as a product where the `z₁`-only factor `W₂(z₁,₁, z₁,₂)`
  is independent of `a`.
- The free-field 2-point function `W₂(z, w) = ((z - w)² + m²)⁻¹` (with
  appropriate Lorentz signature) blows up as `(z₁,₁ - z₁,₂) → ∂V+`,
  which is allowed within `ForwardTube d 2` (the tube is open).
- For fixed `(z₂,₁, z₂,₂, a)`, sending `(z₁,₁ - z₁,₂)` toward `∂V+`
  drives `‖W_4‖ → ∞` while `(1 + ‖z₁‖ + ‖z₂‖)^N` stays bounded.

No global `(C, N)` can therefore witness the bound — the hypothesis
is unsatisfiable for the free scalar field.

## What the textbook actually says

**Streater-Wightman Theorem 3.1.1**:
```
‖W(z)‖ ≤ C · (1 + ‖z‖)^N · (1 + Δ(Im z)⁻¹)^M
```
where `Δ(y)` is the invariant distance of the imaginary-difference
variables to `∂V+`. The boundary-distance factor `Δ(y)⁻¹` is essential.

**Bogoliubov-Logunov-Todorov, Axiomatic QFT, Theorem 11.2**: same
shape, on the extended tube `T'`:
```
‖W(z)‖ ≤ C · (1 + ‖z‖)^N · dist(z, ∂T')⁻ᴷ
```

**Ruelle 1962 / Araki-Hepp-Ruelle 1962**: the cluster theorem proofs
work natively with **smeared** distributions (Schwartz test functions
absorb the boundary singularities), avoiding the pointwise bound issue
entirely. The pointwise version on the analytic side comes from the
Streater-Wightman polynomial-behavior theorem and inherits its
boundary-distance factor.

## Two repair options

### Option A — boundary-distance regulator (faithful to S-W)

Add the `Δ(Im z)⁻ᴹ` factor to the bound. Requires defining a
`tubeBoundaryDist : ForwardTube d n → ℝ` (or analog) and threading it
through the bound:
```lean
bound : ∃ (C : ℝ) (N M : ℕ) (R : ℝ),
  ... ‖W_analytic_BHW(joint_config)‖
    ≤ C * (1 + ‖z₁‖ + ‖z₂‖)^N
       * (1 + tubeBoundaryDist z₁⁻¹)^M
       * (1 + tubeBoundaryDist z₂⁻¹)^M
```

Pros: matches Streater-Wightman exactly; satisfiable for free fields.
Cons: requires defining `tubeBoundaryDist`; threads through downstream
consumers of `RuelleAnalyticClusterHypotheses`.

### Option B — quantifier reordering (compact-base form)

Move `∃ C, N` *inside* `∀ z₁, z₂` (or inside `∀ y₁, y₂` for fixed
imaginary parts):
```lean
bound : ∀ (z₁ : Fin n → ...) (z₂ : Fin m → ...),
  z₁ ∈ ForwardTube d n → z₂ ∈ ForwardTube d m →
  ∃ (C : ℝ) (N : ℕ) (R : ℝ),
    0 < C ∧ 0 < R ∧
    ∀ (a : SpacetimeDim d), a 0 = 0 →
      (∑ i, (a (Fin.succ i))^2) > R^2 →
      (joint_config) ∈ PET d (n + m) →
      ‖W_analytic_BHW(joint_config)‖ ≤ C * (1 + ‖z₁‖ + ‖z₂‖)^N
```

Pros: minimal-change refactor; satisfiable point-by-point
(`C, N` are allowed to blow up as `(z₁, z₂)` approach the boundary).
Cons: weaker than the textbook statement; the cluster-theorem
*proof* may need adjustment if it relied on pointwise-uniform
constants for downstream estimates (likely not — the cluster proof
fixes `(z₁, z₂)` and varies `a`).

## Recommendation

- **Short term** (this branch): document the issue (this file). Do
  *not* axiomatize `L4SpectralData` or any structurally-equivalent
  unconditional discharge — that would introduce inconsistency. Keep
  the conditional reduction `ruelle_analytic_cluster_bound_of` as
  scaffolding.
- **Medium term**: refactor `RuelleAnalyticClusterHypotheses.bound`
  to Option B (lower-cost change). Verify the cluster theorem proof
  still goes through with pointwise `C, N`. Coordinate with @xiyin137
  per `CLAUDE.md` shared-repo policy.
- **Long term**: prove the boundary-regulated bound (Option A form)
  from the Streater-Wightman polynomial-behavior theorem +
  `spectrum_condition`, removing the hypothesis entirely.

## Effect on the L4 file

`OSReconstruction/Wightman/Spectral/Ruelle/L4_UniformPolynomialBound.lean`
contains:

* `L4SpectralData` — a structural hypothesis whose shape mirrors
  `RuelleAnalyticClusterHypotheses.bound`. Defined for completeness;
  inherits the same satisfiability concern.
* `ruelle_analytic_cluster_bound_of` — the conditional reduction
  (proved). This is `(possibly-vacuous antecedent) → (possibly-vacuous
  conclusion)` and remains valid regardless of whether the antecedent
  is satisfiable.
* **No production axiom** (intentionally).

Once `RuelleAnalyticClusterHypotheses.bound` is repaired, both
`L4SpectralData` and the conditional reduction will be updated
to mirror the new shape, and a vetted production axiom can be
considered.

## Audit: the vacuity propagates through a chain (2026-05-08, follow-up to Option A)

After applying Option A to `RACH.bound`, follow-up audit established that
the same flawed bound shape appears in a **coordinated chain of project
sites**. The IBP rework for the cluster proof requires fixing all of
them. Importantly, the math is classical (Vladimirov / Streater-Wightman);
the gap is mechanical: the wrong shape was inherited through a chain of
theorems and one axiom hypothesis.

### The chain

```
exists_acrOne_productTensor_witness                              -- private theorem
  ↓                                                                  with sorry at line 66
  (OSToWightman.lean:38)                                             (claims unregulated bound)

schwinger_continuation_base_step_acrOne_assembly_with_translationInvariant
  ↓                                                                  -- transitively sorry'd
  (OSToWightman.lean:508)

full_analytic_continuation_with_acr_symmetry_growth
  ↓                                                                  -- transitively sorry'd
  (OSToWightman.lean:2515)

full_analytic_continuation_with_symmetry_growth
  ↓                                                                  -- transitively sorry'd
  (OSToWightman.lean:2553)

bv_implies_fourier_support                                       -- AXIOM: hypothesis is
  (VladimirovTillmann.lean:148)                                       the same wrong shape
```

All five claim or require the unregulated polynomial bound
`‖F z‖ ≤ C(1+‖z‖)^N` over the analytic-continuation domain. Per the
free-field counterexample (above), this is unsatisfiable for general
Wightman QFTs — so:

- Theorems #1-#4 are claimed but *cannot* be proved as stated.
  Each ends in (or transitively pulls in) `sorry`.
- Axiom #5 is consistent in isolation but its hypothesis is unsatisfiable —
  so it cannot be applied honestly anywhere.

### Smoking gun: `bv_implies_fourier_support` signature contradicts its docstring

The axiom's **docstring** (`VladimirovTillmann.lean:58-59`) states the
correct textbook hypothesis:
```
‖F(z)‖ ≤ C(1+‖z‖)^N · (1 + dist(Im z, ∂C)⁻¹)^q
```
*with* the regulator. Line 140 even says explicitly: "The compact-subset
polynomial growth hypothesis suffices for Vladimirov 25.1."

But the axiom **signature** (line 162-164) drops the regulator. The
codified hypothesis is therefore *stronger* than what the docstring
claims and *stronger* than what Vladimirov 25.1 actually requires.

### Fix path

A coordinated shape-propagation across the chain:

1. **Source theorem**: change `exists_acrOne_productTensor_witness`'s
   conclusion to include the regulator. Then its `sorry` becomes
   provable (matches the actual textbook content;
   Glaser-Streater-Wightman / Osterwalder-Schrader II / Glimm-Jaffe Ch. 6).
2. **Propagate**: update the three downstream theorems
   (`schwinger_continuation_base_step_..._translationInvariant`,
   `full_analytic_continuation_with_acr_symmetry_growth`,
   `full_analytic_continuation_with_symmetry_growth`) to thread
   the regulated bound.
3. **Axiom relaxation**: relax `bv_implies_fourier_support`'s
   `hF_growth` hypothesis to either the regulated form (matching
   docstring) or the compact-subset form (line 140's claim). Both
   are satisfiable; both suffice for Vladimirov 25.1 per its
   actual statement.

After these steps, the IBP rework for the cluster proof can use the
relaxed `bv_implies_fourier_support` to obtain `Tflat` from the
regulated `W_analytic_BHW`, then apply the standard Schwartz-pairing
argument (Streater-Wightman §3.4).

### Effort estimate (revised post-audit)

- Source-theorem shape change + sorry fill: 1 week (substantial OS
  analytic-continuation content, but standard literature).
- Propagation + axiom relaxation: 2-4 days (mechanical).
- Cluster-proof rework via Tflat dual pairing: 1-2 weeks.
- **Total: 2-4 weeks** with high confidence.

Worst case (~6 weeks): if `OSLinearGrowthCondition` itself needs
shape adjustment to support the regulated bound. Will report back if
scope grows.

### Why this audit matters beyond the cluster proof

The polynomial-bound chain feeds into the OS reconstruction's
analytic-continuation layer, used elsewhere in the project. Fixing
the shape propagation is orthogonal to L4 / Ruelle / cluster but
is load-bearing for any unconditional discharge that routes through
this chain.

## Resolution (2026-05-08, same day, Option A applied on `r2e/ruelle-l5-grind`)

Option A was implemented:

1. **`tubeBoundaryDist`** defined in `RuelleClusterBound.lean:166`:
   for `z : Fin n → Fin (d+1) → ℂ`, takes the minimum
   `Metric.infDist` of consecutive imaginary differences `Im(z_k -
   z_{k-1})` to the closed complement of the open forward cone
   `(openForwardConeSet d)ᶜ`. Returns `1` for `n = 0`.
2. **`RuelleAnalyticClusterHypotheses.bound`** updated to include the
   factor `(1 + (tubeBoundaryDist z₁)⁻¹)^M · (1 + (tubeBoundaryDist
   z₂)⁻¹)^M` with new exponent `M`. Now matches Streater-Wightman
   3.1.1 shape (and aligns with the proven
   `fourierLaplaceExtMultiDim_vladimirov_growth` in
   `OSReconstruction/SCV/PaleyWienerSchwartz.lean:3286`).
3. **`L4SpectralData`** updated to mirror the new shape; the
   conditional reduction `ruelle_analytic_cluster_bound_of`
   re-proved with the regulator.
4. **`wightman_l4_spectral_data_axiom`** was drafted as a production
   axiom shipping the polarized-Fourier representation in the
   regulated shape, then **withdrawn (2026-05-09)** after the PR-#86
   review by [@xiyin137](https://github.com/xiyin137): per the
   project's axiom discipline, new production axioms encode classical
   background infrastructure (SNAG, Bochner, Schwartz-Fubini,
   Vladimirov-style SCV/FA) rather than QFT-specific consequences
   such as the polarized representation of `W_analytic_BHW`. Only the
   conditional reduction `ruelle_analytic_cluster_bound_of` is shipped
   in PR #86; downstream consumers must supply `L4SpectralData`
   explicitly, or future work will discharge it as a theorem (see the
   audit's chain-of-fixes plan above).
5. **Active sorry**: `W_analytic_cluster_integral_via_ruelle`
   (`RuelleClusterBound.lean:718`) — the dominator-integrability
   step. The new dominator includes the regulator factor
   `(1 + (tubeBoundaryDist (wick z))⁻¹)^M` after Wick rotation,
   which becomes `min_k (x_k 0 - x_{k-1} 0)`-style for OPTR
   configs. For `M ≥ 1`, naive local integrability fails (the
   diagonal singularity is codim-1). Resolution requires IBP in
   the time differences, transferring derivatives onto Schwartz
   `f, g` — Streater-Wightman §3.4 / Ruelle 1962. This is its own
   ~1–2 week follow-up; the project Vladimirov-Tillmann
   infrastructure (`bv_implies_fourier_support`,
   `fl_representation_from_bv`, `fourierLaplaceExtMultiDim_*`)
   provides the building blocks.

Shipped in PR xiyin137#86 (open).

## References

* Streater, R. F., and Wightman, A. S. *PCT, Spin and Statistics, and
  All That*. Princeton University Press, 1964 (and reprints). §3.1
  (Theorem 3.1.1) and §3.4 (cluster theorem).
* Bogoliubov, N. N.; Logunov, A. A.; Todorov, I. T. *Introduction to
  Axiomatic Quantum Field Theory*. Benjamin, 1975. Theorem 11.2.
* Ruelle, D. "On the asymptotic condition in quantum field theory."
  *Helvetica Physica Acta* 35 (1962), 147–163.
* Araki, H.; Hepp, K.; Ruelle, D. "On the asymptotic behaviour of
  Wightman functions in space-like directions." *Helvetica Physica
  Acta* 35 (1962), 164–174.
* Glimm, J., and Jaffe, A. *Quantum Physics: A Functional Integral
  Point of View*. 2nd ed., Springer, 1987. Chapter 19.
