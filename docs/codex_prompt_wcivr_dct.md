# Codex task: close `W_analytic_cluster_integral_via_ruelle` via dominated convergence

## Goal

Replace the single remaining `sorry` (currently at
`OSReconstruction/Wightman/Reconstruction/WickRotation/RuelleClusterBound.lean:1782`,
in the body of `theorem W_analytic_cluster_integral_via_ruelle`, line 1424) with a
complete Lean 4 / Mathlib proof. This is the last `sorry` in the file. Work on
branch `r2e/cluster-dct-flatness` (already checked out). No `axiom`/`admit`/new
`sorry`; if genuinely stuck, leave the smallest possible `sorry` at the exact
sub-goal and report what blocked you. The hard analytic input is **already
proved** — this is dominated-convergence plumbing.

## The goal state at the `sorry`

The theorem concludes (with `L_n`, `L_m` already `set` to the single-block
integrals):
```
∃ R > 0, ∀ a, a 0 = 0 → (∑ i, (a (Fin.succ i))^2) > R^2 →
  ∀ g_a, (∀ x, g_a x = g (· − a)) →
    ‖(∫ x : NPointDomain d (n+m), F_ext_on_translatedPET_total Wfn (wick x) * (f.tensorProduct g_a) x)
       − L_n * L_m‖ < ε
```

## What is ALREADY proved and in scope (use these — do not redo them)

- `set L_n` (line 1449), `set L_m` (line 1452): the single-block boundary integrals.
- `have h_change_of_var` (line 1462): for `a 0 = 0` and `g_a = g(·−a)`,
  `(∫ joint) = ∫ p, clusterIntegrand Wfn f g a p` over `NPointDomain d n × NPointDomain d m`.
- `have h_limit_eq_product` (line 1561): `∫ p, clusterLimitIntegrand Wfn f g p = L_n * L_m`.
- `have h_pointwise` (line 1589): `∀ᵐ p, Tendsto (fun a => clusterIntegrand Wfn f g a p) 𝓛 (𝓝 (clusterLimitIntegrand Wfn f g p))`,
  where the filter is
  `𝓛 := Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓ Bornology.cobounded (SpacetimeDim d)`.
- **`block_regulator_dominator_integrable`** (newly proved, same file, ≈ line 1178):
  for `f : SchwartzNPoint d n` with `tsupport f ⊆ OrderedPositiveTimeRegion d n`,
  and any `C N M`,
  `Integrable (fun x => C * (1+‖wick x‖)^N * (1+(tubeBoundaryDist (wick x))⁻¹)^M * ‖f x‖)`.
- `hRuelle.bound` (the `RuelleAnalyticClusterHypotheses.bound` field): for
  `z₁ ∈ ForwardTube d n`, `z₂ ∈ ForwardTube d m`, `a 0 = 0`,
  `(∑ i, (a (Fin.succ i))^2) > R^2`, and the appended `a`-config in
  `PermutedExtendedTube d (n+m)`,
  `‖W_analytic_BHW (n+m) (append z₁ (z₂ + spatial a))‖ ≤ C(1+‖z₁‖+‖z₂‖)^N (1+tubeBoundaryDist z₁⁻¹)^M (1+tubeBoundaryDist z₂⁻¹)^M`.
  (Exists `C N M R`, `C>0`, `R>0`.)
- Helper lemmas already used inside `h_pointwise` (grep them in this file and
  REUSE): `wick_OPTR_in_forwardTube`, `joint_wick_config_in_PET`,
  `joint_F_ext_eq_W_analytic`, `F_ext_on_translatedPET_total_eq_on_PET`,
  `image_eq_zero_of_notMem_tsupport`, and the `h_joint_PET_eventually` pattern.

## Proof plan

**(1) Reduce the goal to a `Tendsto`.** It suffices to prove
```
Tendsto (fun a : SpacetimeDim d => ∫ p, clusterIntegrand Wfn f g a p) 𝓛 (𝓝 (L_n * L_m))
```
because: by `h_change_of_var` the integrand equals the joint integral `J(a)` for
admissible `a, g_a`; and the `∃R, ∀a … < ε` goal is exactly the ε-statement of
this `Tendsto` unfolded on the filter `𝓛`. Convert `Tendsto … 𝓛 (𝓝 L)` to the
`∃R` form: `Metric.tendsto_nhds`/`(tendsto … 𝓝).eventually (Metric.ball …)` gives
`∀ᶠ a in 𝓛, ‖J(a) − L‖ < ε`; unfold `𝓛 = principal {a 0 = 0} ⊓ cobounded` and
`Metric.cobounded_eq_cocompact` to extract the `R` with
`{a | R < ‖a‖} ⊆ {spatial-sq > R²}`-style set membership. **The single-block decay
proof `gns_orthogonal_spatial_cobounded_decay_of` in
`OSReconstruction/Wightman/Spectral/Ruelle/L2_NoZeroMomentumAtom.lean` (≈ line 181)
does this exact `principal{a0=0} ⊓ cobounded` ↔ `‖a_spatial‖ > R` manipulation —
copy its pattern** (`Filter.mem_inf_of_left`, `Metric.cobounded_eq_cocompact`,
`Filter.mem_cocompact`, `isCompact_closedBall`). Mind `a 0 = 0 ⇒ ‖a‖ = ‖a_spatial‖`
and `(∑ (a (Fin.succ i))²) = ‖a_spatial‖²`.

**(2) Prove the `Tendsto` by `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`**
(`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`):
```
(bound : α → ℝ)
(hF_meas : ∀ᶠ a in 𝓛, AEStronglyMeasurable (clusterIntegrand Wfn f g a) volume)
(h_bound : ∀ᶠ a in 𝓛, ∀ᵐ p, ‖clusterIntegrand Wfn f g a p‖ ≤ bound p)
(bound_integrable : Integrable bound)
(h_lim : ∀ᵐ p, Tendsto (fun a => clusterIntegrand Wfn f g a p) 𝓛 (𝓝 (clusterLimitIntegrand Wfn f g p)))
⊢ Tendsto (fun a => ∫ p, clusterIntegrand … a p) 𝓛 (𝓝 (∫ p, clusterLimitIntegrand … p))
```
then rewrite the limit with `h_limit_eq_product`. Provide:
- `𝓛` is `IsCountablyGenerated` (principal ⊓ cobounded on a finite-dim normed
  space; `inferInstance` should work — cobounded = cocompact is countably
  generated).
- `h_lim` := `h_pointwise`.

**(3) The dominator `bound = G`.** Define
`G : NPointDomain d n × NPointDomain d m → ℝ`,
`G p = G₁ p.1 * G₂ p.2` with
`G₁ x = 2^N * C * (1+‖wick x‖)^N * (1+(tubeBoundaryDist (wick x))⁻¹)^M * ‖f x‖`,
`G₂ y =        (1+‖wick y‖)^N * (1+(tubeBoundaryDist (wick y))⁻¹)^M * ‖g y‖`,
where `C N M R` come from `hRuelle.bound`. (Put the `2^N C` constant on one
block.)
- `bound_integrable`: `G₁` and `G₂` are each integrable by
  `block_regulator_dominator_integrable` (with the appropriate constant). For the
  product over `volume.prod volume` use the product-integrability lemma
  (`MeasureTheory.Integrable.prod_mul` / `integrable_prod_mul`-style; grep
  Mathlib). Note `volume` on `NPointDomain d n × NPointDomain d m` is
  `volume.prod volume` (`rfl`, as used in `h_limit_eq_product`).

**(4) `h_bound`.** Need `∀ᶠ a in 𝓛, ∀ᵐ p, ‖clusterIntegrand a p‖ ≤ G p`. Take the
`R` from `hRuelle.bound`; `{a | R < ‖a‖} ∩ {a 0 = 0} ∈ 𝓛`. For such `a` and any
`p`:
- if `p.1 ∉ OPTR`: `f p.1 = 0` (via `image_eq_zero_of_notMem_tsupport hsupp_f`),
  so `clusterIntegrand a p = 0 ≤ G p` (`G ≥ 0`). Similarly `p.2 ∉ OPTR ⇒ g p.2 = 0`.
- if `p.1 ∈ OPTR ∧ p.2 ∈ OPTR`: `wick p.1 ∈ ForwardTube` and `wick p.2 ∈
  ForwardTube` (`wick_OPTR_in_forwardTube`); the appended `a`-config ∈ PET
  (reuse `joint_wick_config_in_PET` with the distinct-times a.e. set as in
  `h_pointwise`); apply `hRuelle.bound` to bound `‖W_analytic(joint)‖`, then
  `‖clusterIntegrand a p‖ = ‖W_analytic(joint)‖ · ‖f p.1‖ · ‖g p.2‖` and split
  `(1+‖z₁‖+‖z₂‖)^N ≤ 2^N (1+‖z₁‖)^N (1+‖z₂‖)^N` (prove via `add_pow_le`/`pow_le_pow_left`
  + `1+‖z₁‖+‖z₂‖ ≤ 2(1+‖z₁‖)(1+‖z₂‖)`) to land exactly under `G₁ p.1 · G₂ p.2`.
  Use `F_ext_on_translatedPET_total_eq_on_PET`/`joint_F_ext_eq_W_analytic` to move
  between `F_ext_on_translatedPET_total` (in `clusterIntegrand`) and
  `W_analytic_BHW` (in the bound), exactly as `h_pointwise` does.
  The `∀ᵐ p` (not `∀ p`) lets you intersect with the a.e. distinct-time set used
  for PET membership (`ae_pairwise_distinct_jointTimeCoords`, already imported in
  `h_pointwise`).

**(5) `hF_meas`.** `AEStronglyMeasurable (clusterIntegrand Wfn f g a)`:
`clusterIntegrand` is `(F_ext_on_translatedPET_total Wfn ∘ wick-append-translate) *
f * g`. `F_ext_on_translatedPET_total` should have a continuity/measurability
lemma (grep `F_ext_on_translatedPET_total` for `Continuous`/`Measurable`/
`AEStronglyMeasurable`); `wick`/append/translate are continuous; `f`,`g` are
continuous (`SchwartzMap.continuous`). Compose. If only a `.aestronglyMeasurable`
on the relevant domain is available, that suffices.

## Build / verify

- Targeted (fast): `lake env lean -DmaxHeartbeats=800000 OSReconstruction/Wightman/Reconstruction/WickRotation/RuelleClusterBound.lean` —
  success = exit 0, **no `error:` and no remaining `sorry` warning** in this file.
- Then `lake build OSReconstruction.Wightman.Reconstruction.WickRotation.RuelleClusterBound`
  (produces oleans). If anything cross-module looks off, `lake clean` + full
  `lake build` to rule out a stale-olean artifact.
- Finally confirm the axiom footprint: append (temporarily) and run
  `#print axioms OSReconstruction.W_analytic_cluster_integral_via_ruelle`; it must
  NOT contain `sorryAx`. It WILL legitimately list the project's named axioms that
  `W_analytic_BHW`, `F_ext_on_translatedPET_total`, and the `RuelleAnalyticClusterHypotheses`
  fields transitively depend on — that is expected; just ensure no `sorryAx`.
  Remove the `#print` line before finishing.

## Constraints

- Mathlib-ready style (snake_case, 100-col, `by` ends the line, one tactic/line,
  `·` bullets). No `axiom`/`admit`/new `sorry`. Do not modify the statement of
  `W_analytic_cluster_integral_via_ruelle`, `block_regulator_dominator_integrable`,
  `clusterIntegrand`, `clusterLimitIntegrand`, `RuelleAnalyticClusterHypotheses`,
  or any existing `have` in the proof — only replace the final `sorry` (you may add
  private helper lemmas above the theorem if useful).
- Reuse the existing helpers from `h_pointwise` rather than re-deriving PET
  membership / forward-tube / `F_ext = W_analytic` facts.
- If a Mathlib API you expect is missing (product integrability, a measurability
  lemma, the cobounded conversion), report the exact missing piece rather than
  working around it with an axiom.

## Deliverable

`RuelleClusterBound.lean` with **zero `sorry`**, `lake build` clean, and
`#print axioms W_analytic_cluster_integral_via_ruelle` free of `sorryAx`. Short
note: helper lemmas added, the product-integrability + cobounded-conversion lemma
names used, and any API gap hit.
