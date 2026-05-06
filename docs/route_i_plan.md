# Route (i) plan — `W_analytic_cluster_integral` via R4 + analytic cluster + DC

Status as of 2026-05-05. Supersedes both `cluster_routeA_plan.md` (off
critical path because it gave OS-reflected cluster) and
`wick_rotated_pairing_eq_W_plan.md` (based on a false bridge claim, per
Gemini's clarification on 2026-05-05).

## The theorem

`W_analytic_cluster_integral` (`SchwingerAxioms.lean:3786`):
```
∀ ε > 0, ∃ R > 0, ∀ a : SpacetimeDim d, a 0 = 0 → ‖a⃗‖² > R² →
  ∀ g_a : SchwartzNPoint d m, (∀ x, g_a x = g (x - a)) →
    ‖∫ F_ext_total Wfn (wick x) · (f.tensorProduct g_a)(x) dx
      - (∫ F_ext_total Wfn (wick x_n) · f(x_n) dx_n)
        · (∫ F_ext_total Wfn (wick x_m) · g(x_m) dx_m)‖ < ε
```

for OPTR-supported `f, g`.

## Why NOT the GNS class or W-to-integral bridge

* **Route A (GNS class)**: gives cluster of OS-reflected integral
  `∫ F_ext (f.osConj ⊗ g_a)`, not the un-reflected target. Off-path.
* **W-to-integral bridge**: claimed
  `∫ F_ext(wick x) f(x) dx = Wfn.W n f` for OPTR-supported Schwartz `f`.
  Per Gemini (2026-05-05): this equality is FALSE for general Schwartz.
  Concrete counterexample: for `W_analytic(z⁰) = e^{-im z⁰}`,
  Wightman gives `e^{-imt}` (oscillatory), Schwinger gives `e^{mt}`
  (exponential). So this route is broken.

## Route (i) strategy

**Step 1**: From R4 (`Wfn.cluster`, axiom field) + spectrum condition's
analytic continuation, derive **pointwise cluster** of the analytic
function `W_analytic_BHW Wfn (n+m)` at all interior forward-tube
configurations of the form `(z, z' + a)` as `|⃗a| → ∞`:

```
W_analytic_BHW Wfn (n+m) (z, z' + a) → W_analytic_BHW Wfn n (z) ·
                                       W_analytic_BHW Wfn m (z')
```

This is a pointwise statement at fixed `z, z'` in the respective forward
tubes, with `a` real and spatial-only.

**Step 2**: Specialize to Wick-rotated configs. For OPTR-supported `f, g`
and `a` spatial:
* `wick(x_n)` is in `ForwardTube d n` (by `wick_OPTR_in_forwardTube`).
* `wick(x_m + a) = wick(x_m) + (0, a⃗)` (the time component is
  unaffected by spatial `a`; the spatial is shifted by `a`).
* The joint Wick-rotated config `(wick x_n, wick(x_m + a))` is in
  `TranslatedPET d (n+m)` for OPTR-supported `f, g` with `a 0 = 0`.

The pointwise cluster from Step 1, restricted to these configs, gives
pointwise cluster of `F_ext_total Wfn (wick·)`.

**Step 3**: Apply dominated convergence to lift pointwise cluster to
integral cluster. This is where the polynomial-growth obstruction lives.

## The polynomial-growth obstruction

The spectrum condition gives:
```
‖W_analytic_BHW Wfn n‖(z) ≤ C · (1 + ‖z‖)^N    for z ∈ ForwardTube d n.
```

For our integrand at the joint Wick-rotated config:
```
F_ext_total Wfn (wick(x_n, x_m + a)) · f(x_n) · g(x_m - a)   (after a-substitution)
```

The polynomial bound on `F_ext_total` involves `‖wick(x_n, x_m + a)‖`,
which as a function of `(x_n, x_m)` can be split:
```
‖wick(x_n, x_m + a)‖ ≤ ‖x_n‖ + ‖x_m + a⃗‖ ≤ ‖x_n‖ + ‖x_m‖ + ‖a⃗‖.
```

Naive bound:
```
|integrand| ≤ C(1 + ‖x_n‖ + ‖x_m‖ + ‖a⃗‖)^N · |f(x_n)| · |g(x_m - a)|.
```

Substituting `y = x_m - a` (Lebesgue-invariant):
```
∫ F_ext(wick(x_n, y + a)) f(x_n) g(y) dx_n dy.
|integrand'| ≤ C(1 + ‖x_n‖ + ‖y + a⃗‖)^N · |f(x_n)| · |g(y)|.
```

Schwartz seminorm bounds on `f, g`:
```
|f(x_n)| ≤ ‖f‖_K (1 + ‖x_n‖)^{-K},
|g(y)|   ≤ ‖g‖_M (1 + ‖y‖)^{-M}.
```

Combined:
```
|integrand'| ≤ C ‖f‖_K ‖g‖_M (1 + ‖x_n‖ + ‖y + a⃗‖)^N
                              · (1 + ‖x_n‖)^{-K} (1 + ‖y‖)^{-M}.
```

For uniform-in-a integrable bound on `(x_n, y)`, the
`(1 + ‖y + a⃗‖)^N` factor is the problem: it grows as `|⃗a| → ∞` (for
fixed y).

## Resolution via split regions

Standard textbook approach (per Gemini's outline): split the integration
region by the relative size of `‖y‖` vs `‖a⃗‖`. For example:

* **Region A** (`‖y‖ ≤ ‖a⃗‖/2`): far from `-a⃗`. In this region,
  `‖y + a⃗‖ ≥ ‖a⃗‖/2 > 0`, but it's still polynomial in `‖a⃗‖`. Use
  Schwartz decay of `g(y)` doesn't help (y is bounded). The integrand
  is bounded by `C (1 + ‖a⃗‖)^N · (something integrable)`.

* **Region B** (`‖y‖ > ‖a⃗‖/2`): far from origin. Schwartz decay of
  `g(y)` gives `|g(y)| ≤ ‖g‖_M (1 + ‖a⃗‖/2)^{-M} ≤ C (1 + ‖a⃗‖)^{-M}`.
  This decay can absorb the polynomial growth `(1 + ‖a⃗‖)^N` if `M > N`.

The combined bound — both regions vanish in the limit `|⃗a| → ∞` — is
what makes dominated convergence apply.

**Concern**: this split-region argument requires careful book-keeping
in Lean. Possibly ~200–300 lines.

## Alternatives I've considered and why they don't work

1. **Direct uniform bound by polynomial × Schwartz decay.** Doesn't
   work because the `(1 + ‖a⃗‖)^N` factor doesn't get absorbed by
   ordinary Schwartz seminorms uniformly in a.

2. **Use translation invariance of `F_ext_total` to move `a` out of
   the integrand.** The project has
   `F_ext_on_translatedPET_total_translation_invariant` for GLOBAL
   translation by a constant `c` (applied uniformly to all n+m points).
   For our case, only the m-block is translated by `a` (relative to the
   n-block), which is NOT a global translation. So this doesn't apply
   directly.

3. **Refined polynomial bound from `hasForwardTubeGrowth_of_wightman`.**
   This gives `‖F_ext(z)‖ · infDist(z, coincidence)^{q+1} ≤ C(1 + ‖z‖)^N`,
   which accounts for the coincidence-locus singularity. For
   spatially-separated joint configs (`|⃗a| > R₀`), `infDist` is bounded
   below uniformly in `a`, so this just reduces to the standard
   polynomial bound — same obstruction.

## Estimated effort

* Step 1 (pointwise cluster of W_analytic from R4 + spectrum condition):
  the project may have `bhw_pointwise_cluster_forwardTube` or related,
  but it requires the joint config to be in ForwardTube globally, which
  the OPTR-supported f, g separately don't give. Need a permuted /
  TranslatedPET version. ~50–100 lines or use of existing infrastructure.

* Step 2 (specialization to Wick-rotated): mechanical, ~30 lines using
  `wick_OPTR_in_forwardTube` and translation properties of wickRotatePoint.

* Step 3 (dominated convergence with split-region dominator): the heart
  of the proof. ~200–300 lines if done from scratch in Mathlib's DC
  framework. The split-region setup requires care.

**Total: ~300–500 lines**, comparable to the original Route (i) attempt
which was abandoned because of this same obstruction.

## Risk points to vet with Gemini

1. **Pointwise cluster transfer**: is the analytic continuation of
   `W_n(f ⊗ g_a) - W_n(f) W_m(g) → 0` (R4 at distribution level) really
   pointwise cluster of W_analytic at each interior forward-tube point?
   What's the project's existing infrastructure for this transfer (e.g.,
   `bhw_pointwise_cluster_forwardTube`)?

2. **Split-region dominator**: does the Region-A / Region-B argument
   really close, or are there subtle issues (e.g., the Region-A bound
   `(1 + ‖a⃗‖)^N · (something integrable)` doesn't go to 0 in `a`
   without additional Schwartz decay of `f`)?

3. **Hidden obstruction**: is there something else specific to the
   project's `WightmanFunctions` setup (e.g., spectrum_condition's
   particular form) that makes this proof hard or impossible? The
   original Route (i) sorry was abandoned at this point — we should
   understand WHY.

4. **Realistic effort**: is 300–500 lines an honest estimate, or should
   we expect 1000+ given Mathlib's current DC infrastructure?

## Decision points after vetting

* If Gemini confirms the strategy works and effort is tractable: execute.
* If Gemini identifies a simpler argument we missed: pivot.
* If Gemini says it's genuinely hard (1000+ lines, deep Lean engineering):
  consider adopting `W_analytic_cluster_integral` as a textbook axiom
  with citation, treating it as on par with `Wfn.cluster` itself.

## What to retire

After this plan is vetted (regardless of outcome):

* `WickRotatedPairingEqW.lean` — based on false bridge.
  - Keep `wick_OPTR_in_forwardTube` (clean true lemma) — move to
    `BHWTranslation.lean` or similar.
  - Drop `g_deform`, `g_deform_one_eq_pairing`, the assembly, the joint
    bridge, and `W_analytic_cluster_integral_via_R4` (all conditional on
    a false claim).

* `wick_rotated_pairing_eq_W_plan.md` — false-bridge plan.

* `cluster_routeA_plan.md` — already marked superseded.

* The deletion shouldn't happen until this Route (i) plan is vetted —
  we want a forward path before we tear down the (broken) backward one.
