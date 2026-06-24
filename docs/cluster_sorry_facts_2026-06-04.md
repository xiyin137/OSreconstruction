# Corrected facts: what the cluster sorry actually is (2026-06-04)

Established by direct code reading on merged `main` (post #88), to correct the
plan docs and a `gemini-3-deep-think` verdict that were both answering a
different/larger question than the one the Lean sorry poses.

## The sorry is the limit–integral interchange, NOT the cluster decay

`W_analytic_cluster_integral_via_ruelle` (`RuelleClusterBound.lean:718`,
sorry at `:1076`) is **almost fully proved**:

- **Step 1** `h_change_of_var` (PROVED): the joint integral `J(a)` equals
  `∫ clusterIntegrand Wfn f g a p` over the product domain, via a single
  measure-preserving change of variables.
- **Step 2** `h_limit_eq_product` (PROVED): `∫ clusterLimitIntegrand = L_n·L_m`
  by Fubini (`integral_prod_mul`).
- **Step 3** `h_pointwise` (PROVED): for a.e. `p`,
  `clusterIntegrand(a,p) → clusterLimitIntegrand(p)` along the spatial-cobounded
  filter. This *is* the pointwise Araki–Hepp–Ruelle cluster decay — and it is
  supplied as the **hypothesis** `hRuelle.pointwise` (a field of
  `RuelleAnalyticClusterHypotheses`), not something we must reprove.
- **Steps 4–7** (the `sorry`): pass from pointwise convergence (Step 3) to
  convergence of the **integrals**, i.e. justify
  `∫ clusterIntegrand(a,·) → ∫ clusterLimitIntegrand = L_n·L_m`. A
  dominated-convergence / uniform-integrability step.

So the cluster *decay* is a given; the only missing piece is the **interchange
of limit and integral**.

## The dominator is a-uniform with only within-block regulators

`RuelleAnalyticClusterHypotheses.bound` (`:199–217`) gives, for `z₁∈ForwardTube n`,
`z₂∈ForwardTube m`, joint config in PET:
```
‖W_analytic_BHW(n+m)(joint a-config)‖
  ≤ C·(1+‖z₁‖+‖z₂‖)^N·(1+tubeBoundaryDist(z₁)⁻¹)^M·(1+tubeBoundaryDist(z₂)⁻¹)^M
```
Two facts read directly off the signature:

1. **a-uniform**: `a` does NOT appear on the RHS. The dominator
   `G(p) = C(1+‖wick p₁‖+‖wick p₂‖)^N (1+Δ(wick p₁)⁻¹)^M (1+Δ(wick p₂)⁻¹)^M
   |f(p₁)||g(p₂)|` is independent of `a`. (Earlier worry about `‖a‖`-growth of
   the dominator was unfounded.)
2. **Only within-block regulators**: separate `tubeBoundaryDist(z₁)` (f-block)
   and `tubeBoundaryDist(z₂)` (g-block). There is **NO junction regulator** —
   the cluster blocks are spatially separated, so the f↔g junction is spacelike
   and non-singular.

The **only** obstruction to using `G` as an L¹ dominator is the within-block
diagonal singularity `(1+Δ⁻¹)^M` (consecutive Euclidean times coinciding,
codim-1), non-integrable for `M ≥ 1`. The polynomial `(1+‖·‖)^N` is beaten by
Schwartz `f,g`.

## Why Gemini's verdict targets the wrong layer

`gemini-3-deep-think` (2026-06-04) declared Route 1 (single `Tflat`) dead via a
junction obstruction, ruled out block-wise distributional Fubini, and said the
only path (Route 2, GNS–Bochner) further needs the unbounded Wightman domain +
essential self-adjointness, plus the Araki–Hepp–Ruelle curvature lemma for
pointwise decay. Cross-checked against the code, those concerns are off the
critical path for THIS sorry:

- **Pointwise cluster decay** (Gemini's AHR-curvature "monumental hurdle") is
  already the hypothesis `hRuelle.pointwise`. We do not reprove it here.
- **Cobounded spatial decay machinery already exists and is PROVED conditionally**:
  `gns_orthogonal_spatial_cobounded_decay_of` (`L2_NoZeroMomentumAtom.lean:181`)
  reduces to `spectral_riemann_lebesgue` (`L5_SpectralRiemannLebesgue.lean:113`,
  PROVED, no sorry) given `L2SpectralData` — which encodes an **absolutely
  continuous spatial marginal**. AC is exactly what kills Gemini's
  singular-continuous-spectrum counterexample; the decay then follows by
  Riemann–Lebesgue, **no curvature lemma**. The QFT content is isolated in the
  (conditional, intentionally un-axiomatized) `L2SpectralData` hypothesis.
- The **junction obstruction is specific to the single-`Tflat` FL representation**
  (Route 1). It does not touch the IBP route below.

## The route the plan docs skipped: IBP in the time differences

`docs/ruelle_bound_vacuity_concern.md` (the earlier, more careful analysis)
already identified the correct resolution (Resolution §, item 5): **IBP in the
time differences, transferring the `M` derivatives off the singular
boundary-regulator kernel onto the Schwartz `f,g`** (Streater–Wightman §3.4 /
Ruelle 1962). This tames the within-block `(1+Δ⁻¹)^M` to an integrable
singularity at the cost of derivatives on `f,g` (which stay Schwartz), after
which ordinary dominated convergence closes Steps 4–7.

`docs/cluster_ibp_rework_plan.md` then **pivoted away** from IBP — first to the
single-`Tflat` dual pairing (killed by the junction), then to GNS–Bochner —
conflating "naive single-dominator DC fails" with "must leave the analytic
side." But IBP was never ruled out; it was deferred as "a 1–2 week follow-up."
It stays entirely on the analytic/measure side: **no `Tflat`, no analytic
Hilbert states, no unbounded operators, no junction.** Gemini's objections
(junction, Hilbert domain, AHR curvature) simply do not apply to it.

## The one genuine subtlety to settle before committing

Are `L_n, L_m` (and `J(a)`) finite as the **Lebesgue integrals** Lean writes
(`MeasureTheory.integral`), or do they need a distributional/regularized reading?
The single-block integrand `W_analytic(wick x)·f(x)` carries the same within-block
`(1+Δ⁻¹)^M` regulator, so its absolute integrability is exactly the question IBP
must also answer for the single blocks. Two possibilities:
- (i) the boundary value is genuinely less singular than the crude `bound`
  (the bound is an upper estimate; the true function may be locally integrable
  against Schwartz tests), or
- (ii) the integral must be read as a tempered-distribution pairing / IBP-regularized
  object.
Resolving this determines whether IBP is "make the dominator integrable" or
"reinterpret the integral." This is the precise question for the next Gemini
deep-think query (to be sent via the webpage).

## Bottom line

- The sorry is a **dominated-convergence interchange**, blocked solely by a
  within-block, a-uniform diagonal regulator.
- The **IBP-in-time-differences route** (analytic side, textbook S-W §3.4) is the
  most contained discharge and sidesteps every obstruction Gemini raised.
- The GNS–Bochner route remains a fallback; its hardest piece (`L2SpectralData`
  for Bochner-derived states) is a conditional hypothesis the project already
  isolates, and the decay lemma consuming it is already proved.
- **Next:** settle the L¹-vs-distributional integrability question for the
  single-block integrals, then scope the IBP discharge.
