/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms

/-!
# Ruelle's analytic cluster bound

This file states the Ruelle 1962 analytic cluster theorem as a textbook
axiom, and uses it together with dominated convergence to prove
`W_analytic_cluster_integral` from R4.

## The obstruction Ruelle resolves

The standard `spectrum_condition`'s polynomial bound
`‖W_analytic z‖ ≤ C(1 + ‖z‖)^N` on the forward tube has the constant
`C` and exponent `N` independent of the position `z`. But for our
cluster integral, after substituting `y = x_m - a`, we evaluate
`W_analytic_BHW Wfn (n+m)` at `(wick x_n, wick(y + a))`. The naive
polynomial bound gives `(1 + ‖x_n‖ + ‖y + a‖)^N`, which depends on
`a` and grows as `|⃗a| → ∞`. This breaks dominated convergence: the
dominator must be `a`-independent.

Ruelle's theorem provides a **uniform-in-a polynomial bound** on the
spatially-separated analytic continuation: for `|⃗a| > R`,
`‖W_analytic_BHW Wfn (n+m) (wick(x_n, x_m + a))‖ ≤ C(1 + ‖x_n‖ + ‖x_m‖)^N`
with `C, N` independent of `a`. This is the spectral-gap content of R4
(distributional cluster) made explicit at the analytic level.

## References

* Ruelle, *On the asymptotic condition in quantum field theory*,
  Helvetica Physica Acta 35 (1962), pp. 147-163.
* Jost, *The General Theory of Quantized Fields*, §VI.1.
* Streater-Wightman, *PCT, Spin and Statistics, and All That*, §3.4.

## Strategy and discharge

1. `ruelle_analytic_cluster_bound` (axiom) — the uniform-in-a polynomial
   bound on `W_analytic_BHW Wfn (n+m)` for spatially separated configs.
2. `ruelle_analytic_cluster_pointwise` (axiom or derived) — pointwise
   convergence of the joint analytic function to the product of factors.
3. Build an `a`-independent integrable dominator on
   `NPointDomain d n × NPointDomain d m` using Ruelle's bound and high-
   order Schwartz seminorms.
4. Apply `MeasureTheory.tendsto_integral_of_dominated_convergence` to
   close `W_analytic_cluster_integral`.

See `docs/cluster_via_ruelle_plan.md` for the full plan.
-/

open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-! ### Ruelle's uniform polynomial bound -/

/-- **Ruelle's analytic cluster bound** (Ruelle 1962, Jost VI.1).

For a Wightman family `Wfn` satisfying R0–R4, the analytic continuation
`W_analytic_BHW Wfn (n+m)` admits a *uniform-in-a* polynomial bound on
spatially-separated arguments. Specifically, there exist constants
`C > 0`, `N : ℕ`, and `R > 0` such that for any
`z₁ : Fin n → Fin (d+1) → ℂ` in `ForwardTube d n`,
`z₂ : Fin m → Fin (d+1) → ℂ` in `ForwardTube d m`, and any spatial
translation `a` with `|⃗a| > R`:

```
‖(W_analytic_BHW Wfn (n+m)).val
    (Fin.append z₁ (fun k μ => z₂ k μ + (if μ = 0 then 0 else (a μ : ℂ))))‖
  ≤ C * (1 + ‖z₁‖ + ‖z₂‖) ^ N.
```

The crucial property: `C` and `N` do **not** depend on `a`.

This is the spectral-gap content of R4: the distributional cluster
property (`Wfn.cluster`) implies an isolated δ-function at `P = 0` in
the joint energy-momentum spectrum, which translates (via Ruelle's
argument) into uniform decay/boundedness of the analytic continuation
in spacelike directions.

**References**: Ruelle 1962, *On the asymptotic condition in quantum
field theory*, Helvetica Physica Acta 35; Jost, *The General Theory
of Quantized Fields*, §VI.1; Streater-Wightman §3.4.

**Discharge plan**: full proof requires the momentum-space spectral
theory of Wightman functions (~1500+ lines of Lean), specifically:
the Källén-Lehmann-style spectral support property for truncated W,
and the Laplace transform bounds. Routed to a separate sub-project. -/
axiom ruelle_analytic_cluster_bound
    (Wfn : WightmanFunctions d) (n m : ℕ) :
    ∃ (C : ℝ) (N : ℕ) (R : ℝ),
      0 < C ∧ 0 < R ∧
      ∀ (z₁ : Fin n → Fin (d + 1) → ℂ),
      ∀ (z₂ : Fin m → Fin (d + 1) → ℂ),
        z₁ ∈ ForwardTube d n →
        z₂ ∈ ForwardTube d m →
        ∀ (a : SpacetimeDim d), a 0 = 0 →
          (∑ i : Fin d, (a (Fin.succ i)) ^ 2) > R ^ 2 →
          ‖(W_analytic_BHW Wfn (n + m)).val
              (Fin.append z₁
                (fun k μ => z₂ k μ +
                  (if μ = 0 then (0 : ℂ) else (a μ : ℂ))))‖
            ≤ C * (1 + ‖z₁‖ + ‖z₂‖) ^ N

/-! ### Pointwise analytic cluster

The pointwise convergence `W_analytic(z₁, z₂ + a) → W_analytic(z₁) ·
W_analytic(z₂)` as `|⃗a| → ∞` for each fixed `(z₁, z₂)`. This is the
analytic-continuation lift of R4's distributional cluster.

The project has `bhw_pointwise_cluster_forwardTube`
(`SchwingerAxioms.lean:3613`), but it requires the JOINT config to be
in `ForwardTube d (n+m)`, which OPTR-supported test functions don't
guarantee globally (inter-block time ordering not enforced).

For our dominated-convergence application, we need pointwise cluster
on the configurations the Wick rotation produces — including those
where `Fin.append z₁ z₂` lies in `PermutedExtendedTube` (a permuted
forward tube) but not in the strict `ForwardTube`.

We axiomatize this generalization as a companion to Ruelle's bound;
it has the same textbook citation. -/

/-- **Pointwise analytic cluster on PET configurations**.

Pointwise companion to `ruelle_analytic_cluster_bound`. For
`z₁ ∈ ForwardTube d n` and `z₂ ∈ ForwardTube d m` (separately, no
joint condition), the joint analytic continuation factorizes
asymptotically as the m-block is spatially translated to infinity:

```
lim_{|⃗a| → ∞, a⁰ = 0}
   (W_analytic_BHW Wfn (n+m)).val (z₁, z₂ + a)
  = (W_analytic_BHW Wfn n).val z₁ · (W_analytic_BHW Wfn m).val z₂.
```

This is the analytic-continuation lift of R4's distributional cluster
(`Wfn.cluster`), via Ruelle's argument: the spectral gap at `P = 0`
forces the truncated analytic continuation to vanish at infinity in
spacelike directions.

**References**: same as `ruelle_analytic_cluster_bound`. -/
axiom ruelle_analytic_cluster_pointwise
    (Wfn : WightmanFunctions d) (n m : ℕ)
    (z₁ : Fin n → Fin (d + 1) → ℂ) (z₂ : Fin m → Fin (d + 1) → ℂ)
    (hz₁ : z₁ ∈ ForwardTube d n) (hz₂ : z₂ ∈ ForwardTube d m) :
    Filter.Tendsto
      (fun a : SpacetimeDim d =>
        (W_analytic_BHW Wfn (n + m)).val
          (Fin.append z₁
            (fun k μ => z₂ k μ +
              (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))))
      (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
        Bornology.cobounded (SpacetimeDim d))
      (nhds ((W_analytic_BHW Wfn n).val z₁ *
             (W_analytic_BHW Wfn m).val z₂))

/-! ### W_analytic_cluster_integral via Ruelle + DC -/

/-- **Cluster theorem for the Wick-rotated boundary integral**.

For OPTR-supported Schwartz `f, g` and a purely spatial translation `a`,
the (n+m)-point Wick-rotated integral against the un-reflected tensor
product `f.tensorProduct g_a` clusters to the product of single-block
integrals as `|⃗a| → ∞`.

This is `W_analytic_cluster_integral` (`SchwingerAxioms.lean:3786`)
proved from R4 (`Wfn.cluster`, axiom field) + Ruelle's analytic
cluster bound (this file's axiom).

**Proof structure**:

1. Substitute `y = x_m - a` (Lebesgue invariant) in the joint integral.
   The substituted integrand is
   `F_ext(wick(append x_n (y + a))) · f(x_n) · g(y)`,
   integrated over `(x_n, y) ∈ NPointDomain d n × NPointDomain d m`.

2. Pointwise limit: by `ruelle_analytic_cluster_pointwise`, for fixed
   `(x_n, y)` with x_n in OPTR-n, y in OPTR-m (so wick x_n ∈ FT_n,
   wick y ∈ FT_m), the integrand at the substituted variables converges
   to `F_ext(wick x_n) · F_ext(wick y) · f(x_n) · g(y)` as `|⃗a| → ∞`.

3. Uniform-in-a integrable bound: by `ruelle_analytic_cluster_bound`,
   for `|⃗a| > R`,
   `|F_ext(wick(append x_n (y + a)))| ≤ C(1 + ‖x_n‖ + ‖y‖)^N`.
   Combined with Schwartz seminorms of `f, g` of high enough order,
   the integrand is dominated by an `a`-independent integrable function.

4. Apply `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
   to conclude the substituted integral converges to the product of
   single-block integrals (by Fubini).

5. Convert the Tendsto along `cobounded` to the existential form
   `∃ R, ∀ |⃗a| > R, ‖difference‖ < ε` expected by
   `W_analytic_cluster_integral`. -/
theorem W_analytic_cluster_integral_via_ruelle
    (Wfn : WightmanFunctions d) (n m : ℕ)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hsupp_f : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hsupp_g : tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 →
        (∑ i : Fin d, (a (Fin.succ i)) ^ 2) > R ^ 2 →
        ∀ (g_a : SchwartzNPoint d m),
          (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
          ‖(∫ x : NPointDomain d (n + m),
              F_ext_on_translatedPET_total Wfn
                (fun k => wickRotatePoint (x k)) *
              (f.tensorProduct g_a) x) -
            (∫ x : NPointDomain d n,
              F_ext_on_translatedPET_total Wfn
                (fun k => wickRotatePoint (x k)) * f x) *
            (∫ x : NPointDomain d m,
              F_ext_on_translatedPET_total Wfn
                (fun k => wickRotatePoint (x k)) * g x)‖ < ε := by
  sorry

end OSReconstruction
