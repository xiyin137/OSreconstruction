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

/-! ### OPTR Wick rotation lands in the forward tube -/

/-- For OPTR-supported configurations, the Wick rotation lands in the
forward tube. Wrapper around `euclidean_ordered_in_forwardTube`. -/
theorem wick_OPTR_in_forwardTube
    (n : ℕ) (x : NPointDomain d n)
    (hx : x ∈ OrderedPositiveTimeRegion d n) :
    (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n :=
  euclidean_ordered_in_forwardTube x
    (fun k j hkj => (hx k).2 j hkj)
    (fun k => (hx k).1)

/-! ### Pi-instance bridge: HasTemperateGrowth for volume on NPointDomain

`NPointDomain d n = Fin n → Fin (d+1) → ℝ` is a *nested* Pi type. Mathlib's
`isAddHaarMeasure_volume_pi` provides `IsAddHaarMeasure` for FLAT Pi
`ι → ℝ`, but the instance doesn't propagate to nested Pi automatically.

The project already uses the workaround
`MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite`
(see `SchwingerTemperedness.lean:1489`); we adopt it as a project-level
instance so type-class synthesis works throughout. -/

/-- `(volume : Measure (NPointDomain d n))` is `IsAddHaarMeasure`. -/
instance NPointDomain.volume_isAddHaarMeasure (d n : ℕ) :
    (MeasureTheory.volume :
      MeasureTheory.Measure (NPointDomain d n)).IsAddHaarMeasure :=
  MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite

/-! ### Helper lemmas: Schwartz seminorms absorb polynomial growth -/

/-- For a Schwartz function `f` on a finite-dim real inner-product space,
the function `(1 + ‖x‖)^k · ‖f x‖` is integrable.

Proof: bound `(1 + ‖x‖)^k ≤ 2^(k-1) · (1 + ‖x‖^k)`, splitting into a
`‖f x‖` term (integrable: Schwartz functions are integrable) and a
`‖x‖^k · ‖f x‖` term (integrable by `SchwartzMap.integrable_pow_mul`). -/
lemma schwartz_integrable_add_pow_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : MeasureTheory.Measure E} [μ.HasTemperateGrowth]
    (f : SchwartzMap E ℂ) (k : ℕ) :
    MeasureTheory.Integrable
      (fun x : E => (1 + ‖x‖) ^ k * ‖f x‖) (μ := μ) := by
  -- Bound: (1 + ‖x‖)^k ≤ 2^(k-1) · (1 + ‖x‖^k).
  -- (Uses Mathlib's add_pow_le.)
  -- The dominator: 2^(k-1) · (‖f x‖ + ‖x‖^k · ‖f x‖). Each summand integrable.
  have h_dominator_int : MeasureTheory.Integrable
      (fun x : E => ((2 : ℝ) ^ (k - 1)) * (‖f x‖ + ‖x‖^k * ‖f x‖)) μ := by
    refine MeasureTheory.Integrable.const_mul ?_ _
    refine MeasureTheory.Integrable.add ?_ ?_
    · exact (f.integrable (μ := μ)).norm
    · exact f.integrable_pow_mul μ k
  -- Pointwise bound
  refine h_dominator_int.mono' ?_ ?_
  · -- AEStronglyMeasurable
    refine ((continuous_const.add continuous_norm).pow k).mul ?_ |>.aestronglyMeasurable
    exact f.continuous.norm
  · -- |(1+‖x‖)^k * ‖f x‖| ≤ 2^(k-1) * (‖f x‖ + ‖x‖^k * ‖f x‖)
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h_pos : (0 : ℝ) ≤ (1 + ‖x‖) ^ k * ‖f x‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h_pos]
    have h_apl := add_pow_le (zero_le_one (α := ℝ)) (norm_nonneg x) k
    -- h_apl : (1 + ‖x‖) ^ k ≤ 2^(k-1) * (1^k + ‖x‖^k)
    have h_apl' : (1 + ‖x‖) ^ k ≤ 2^(k-1) * (1 + ‖x‖^k) := by
      simpa using h_apl
    have h_fnonneg : 0 ≤ ‖f x‖ := norm_nonneg _
    calc (1 + ‖x‖) ^ k * ‖f x‖
        ≤ 2^(k-1) * (1 + ‖x‖^k) * ‖f x‖ := by
          exact mul_le_mul_of_nonneg_right h_apl' h_fnonneg
      _ = 2^(k-1) * (‖f x‖ + ‖x‖^k * ‖f x‖) := by ring

/-! ### Helper definitions for the cluster proof -/

/-- The `a`-parametrized integrand on `NPointDomain d n × NPointDomain d m`,
after the substitution `y = x_m - a`. Equals
`F_ext(wick(append x_n (y + a))) · f(x_n) · g(y)`. -/
noncomputable def clusterIntegrand
    (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (a : SpacetimeDim d) :
    NPointDomain d n × NPointDomain d m → ℂ :=
  fun p =>
    F_ext_on_translatedPET_total Wfn
      (Fin.append
        (fun k => wickRotatePoint (p.1 k))
        (fun k μ => wickRotatePoint (p.2 k) μ +
          (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) *
    (f p.1) * (g p.2)

/-- The limit integrand: factorized form `F_ext(wick x_n) · F_ext(wick y) ·
f(x_n) · g(y)`. -/
noncomputable def clusterLimitIntegrand
    (Wfn : WightmanFunctions d) {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) :
    NPointDomain d n × NPointDomain d m → ℂ :=
  fun p =>
    F_ext_on_translatedPET_total Wfn
      (fun k => wickRotatePoint (p.1 k)) *
    F_ext_on_translatedPET_total Wfn
      (fun k => wickRotatePoint (p.2 k)) *
    (f p.1) * (g p.2)

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
  -- The limit value: product of single-block integrals.
  set L_n : ℂ := ∫ x : NPointDomain d n,
      F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (x k)) * f x
    with hL_n
  set L_m : ℂ := ∫ x : NPointDomain d m,
      F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (x k)) * g x
    with hL_m
  -- Strategy: show the joint integral, viewed as a function of `a`, tends
  -- to L_n * L_m along the spatial-cobounded filter. Then convert to ε-R.
  --
  -- Step 1 (change of variables): the joint integral as a function of `a`
  -- equals the integral of `clusterIntegrand` over `NPointDomain d n ×
  -- NPointDomain d m` (after Fubini-split + Lebesgue-translation by `a`
  -- on the m-block).
  have h_change_of_var :
    ∀ (a : SpacetimeDim d), a 0 = 0 →
      ∀ (g_a : SchwartzNPoint d m),
        (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
        (∫ x : NPointDomain d (n + m),
            F_ext_on_translatedPET_total Wfn
              (fun k => wickRotatePoint (x k)) * (f.tensorProduct g_a) x) =
        ∫ p : NPointDomain d n × NPointDomain d m, clusterIntegrand Wfn f g a p := by
    sorry  -- Fubini + Lebesgue translation invariance
  -- Step 2 (Fubini on the limit): the limit integrand integrates to L_n · L_m.
  have h_limit_eq_product :
      (∫ p : NPointDomain d n × NPointDomain d m, clusterLimitIntegrand Wfn f g p)
        = L_n * L_m := by
    -- clusterLimitIntegrand factors: A(p.1) · B(p.2) where
    -- A(x) = F_ext(wick x) · f(x), B(y) = F_ext(wick y) · g(y).
    -- volume on the product = volume.prod volume (rfl), so apply
    -- Fubini-Tonelli's product formula `integral_prod_mul`.
    rw [show (MeasureTheory.volume :
        MeasureTheory.Measure (NPointDomain d n × NPointDomain d m)) =
      MeasureTheory.volume.prod MeasureTheory.volume from rfl]
    unfold clusterLimitIntegrand
    rw [hL_n, hL_m]
    -- Goal: ∫ p, (F_ext(wick p.1) * F_ext(wick p.2)) * f(p.1) * g(p.2)
    --       = (∫ x, F_ext(wick x) * f x) * (∫ y, F_ext(wick y) * g y)
    rw [show ((∫ x : NPointDomain d n,
          F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (x k)) * f x)
        * (∫ y : NPointDomain d m,
          F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (y k)) * g y))
        = ∫ p : NPointDomain d n × NPointDomain d m,
          (F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (p.1 k)) * f p.1) *
          (F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (p.2 k)) * g p.2)
        from (MeasureTheory.integral_prod_mul _ _).symm]
    congr 1
    ext p
    ring
  -- Step 3 (pointwise limit): for each (x_n, y) with x_n ∈ OPTR-n and
  -- y ∈ OPTR-m, the cluster integrand at parameter `a` tends to the limit
  -- integrand as |⃗a| → ∞ along {a 0 = 0} ⊓ cobounded.
  have h_pointwise :
      ∀ᵐ p : NPointDomain d n × NPointDomain d m,
        Filter.Tendsto (fun a => clusterIntegrand Wfn f g a p)
          (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
            Bornology.cobounded (SpacetimeDim d))
          (nhds (clusterLimitIntegrand Wfn f g p)) := by
    refine Filter.Eventually.of_forall (fun p => ?_)
    by_cases hp1 : p.1 ∈ OrderedPositiveTimeRegion d n
    · by_cases hp2 : p.2 ∈ OrderedPositiveTimeRegion d m
      · -- Both p.1, p.2 in OPTR: apply ruelle_analytic_cluster_pointwise.
        -- wick(p.1) ∈ ForwardTube d n, wick(p.2) ∈ ForwardTube d m.
        have hw1 : (fun k => wickRotatePoint (p.1 k)) ∈ ForwardTube d n :=
          wick_OPTR_in_forwardTube n p.1 hp1
        have hw2 : (fun k => wickRotatePoint (p.2 k)) ∈ ForwardTube d m :=
          wick_OPTR_in_forwardTube m p.2 hp2
        -- The Ruelle pointwise axiom gives Tendsto for W_analytic_BHW.
        have h_ruelle_pt :=
          ruelle_analytic_cluster_pointwise Wfn n m _ _ hw1 hw2
        -- F_ext_on_translatedPET_total = W_analytic_BHW on PET configs
        -- (joint config in PET via euclidean_distinct_in_permutedTube;
        --  single configs in ForwardTube ⊆ PET).
        -- Multiply both sides by `f(p.1) * g(p.2)` (constant in a).
        unfold clusterIntegrand clusterLimitIntegrand
        -- Routed: bridge `F_ext_on_translatedPET_total` with `W_analytic_BHW`
        -- on each of the three configs (joint, single n, single m), then
        -- transport h_ruelle_pt via Tendsto.const_mul × 2.
        sorry
      · -- p.2 ∉ OPTR-m: g(p.2) = 0 (by support hypothesis).
        have h_g_zero : (g : NPointDomain d m → ℂ) p.2 = 0 := by
          have h_notInTsupp :
              p.2 ∉ tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) :=
            fun hxts => hp2 (hsupp_g hxts)
          exact image_eq_zero_of_notMem_tsupport h_notInTsupp
        -- Both clusterIntegrand and clusterLimitIntegrand vanish: trivial.
        simp [clusterIntegrand, clusterLimitIntegrand, h_g_zero]
        exact tendsto_const_nhds
    · -- p.1 ∉ OPTR-n: f(p.1) = 0.
      have h_f_zero : (f : NPointDomain d n → ℂ) p.1 = 0 := by
        have h_notInTsupp :
            p.1 ∉ tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) :=
          fun hxts => hp1 (hsupp_f hxts)
        exact image_eq_zero_of_notMem_tsupport h_notInTsupp
      simp [clusterIntegrand, clusterLimitIntegrand, h_f_zero]
      exact tendsto_const_nhds
  -- Step 4 (dominator): construct a uniform-in-a integrable dominator on
  -- (NPointDomain d n × NPointDomain d m), valid for `|⃗a|` large enough.
  obtain ⟨C_R, N_R, R_R, hC_R_pos, hR_R_pos, h_ruelle⟩ :=
    ruelle_analytic_cluster_bound Wfn n m
  -- The dominator: C_R · (1+‖x_n‖+‖y‖)^N_R · |f(x_n)| · |g(y)|.
  -- Schwartz seminorms make this integrable when N_R is absorbed by f's
  -- and g's seminorms.
  have h_dominator_integrable :
      MeasureTheory.Integrable (fun p : NPointDomain d n × NPointDomain d m =>
        C_R * (1 + ‖p.1‖ + ‖p.2‖) ^ N_R * ‖f p.1‖ * ‖g p.2‖) := by
    -- A(x) = (1 + ‖x‖)^N_R · ‖f x‖ integrable on NPointDomain d n
    -- (using the IsAddHaarMeasure instance bridge above).
    have hA : MeasureTheory.Integrable
        (fun x : NPointDomain d n => (1 + ‖x‖) ^ N_R * ‖f x‖) :=
      schwartz_integrable_add_pow_mul (μ := MeasureTheory.volume) f N_R
    have hB : MeasureTheory.Integrable
        (fun y : NPointDomain d m => (1 + ‖y‖) ^ N_R * ‖g y‖) :=
      schwartz_integrable_add_pow_mul (μ := MeasureTheory.volume) g N_R
    -- A(p.1) · B(p.2) integrable on the product.
    have hAB : MeasureTheory.Integrable
        (fun p : NPointDomain d n × NPointDomain d m =>
          ((1 + ‖p.1‖)^N_R * ‖f p.1‖) * ((1 + ‖p.2‖)^N_R * ‖g p.2‖))
        (μ := MeasureTheory.volume.prod MeasureTheory.volume) :=
      hA.mul_prod hB
    -- Identify volume on the product with volume.prod volume.
    rw [show (MeasureTheory.volume :
        MeasureTheory.Measure (NPointDomain d n × NPointDomain d m)) =
      MeasureTheory.volume.prod MeasureTheory.volume from rfl]
    -- Bound the original by C_R · A(x) · B(y), using
    -- (1 + ‖x‖ + ‖y‖)^N_R ≤ (1 + ‖x‖)^N_R · (1 + ‖y‖)^N_R.
    refine (hAB.const_mul C_R).mono' ?_ ?_
    · -- AEStronglyMeasurable of the original.
      refine MeasureTheory.AEStronglyMeasurable.mul ?_ ?_
      refine MeasureTheory.AEStronglyMeasurable.mul ?_ ?_
      · -- Continuous: C_R · (1 + ‖p.1‖ + ‖p.2‖)^N_R
        refine ((continuous_const.add (continuous_norm.comp continuous_fst)).add
          (continuous_norm.comp continuous_snd)).pow N_R |>.const_mul C_R
          |>.aestronglyMeasurable
      · -- ‖f p.1‖ continuous
        exact (f.continuous.norm.comp continuous_fst).aestronglyMeasurable
      · exact (g.continuous.norm.comp continuous_snd).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun p => ?_)
      have h_C_pos : (0 : ℝ) ≤ C_R := le_of_lt hC_R_pos
      have h_fnonneg : (0 : ℝ) ≤ ‖f p.1‖ := norm_nonneg _
      have h_gnonneg : (0 : ℝ) ≤ ‖g p.2‖ := norm_nonneg _
      have h_p1_nonneg : (0 : ℝ) ≤ ‖p.1‖ := norm_nonneg _
      have h_p2_nonneg : (0 : ℝ) ≤ ‖p.2‖ := norm_nonneg _
      have h_lhs_nonneg : (0 : ℝ) ≤
          C_R * (1 + ‖p.1‖ + ‖p.2‖) ^ N_R * ‖f p.1‖ * ‖g p.2‖ := by positivity
      have h_rhs_pos : (0 : ℝ) ≤
          C_R * (((1 + ‖p.1‖)^N_R * ‖f p.1‖) * ((1 + ‖p.2‖)^N_R * ‖g p.2‖)) := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h_lhs_nonneg]
      -- Bound (1 + ‖p.1‖ + ‖p.2‖) ≤ (1 + ‖p.1‖) * (1 + ‖p.2‖) via mul_nonneg.
      have h_bound : (1 + ‖p.1‖ + ‖p.2‖) ≤ (1 + ‖p.1‖) * (1 + ‖p.2‖) := by
        nlinarith [mul_nonneg h_p1_nonneg h_p2_nonneg]
      have h_bound' : (1 + ‖p.1‖ + ‖p.2‖)^N_R ≤
          (1 + ‖p.1‖)^N_R * (1 + ‖p.2‖)^N_R := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + ‖p.1‖ + ‖p.2‖)
          h_bound N_R
      -- Multiply by `C_R * ‖f p.1‖ * ‖g p.2‖ ≥ 0` on both sides.
      have h_factor_nonneg : (0 : ℝ) ≤ C_R * ‖f p.1‖ * ‖g p.2‖ := by positivity
      have key :
          C_R * ‖f p.1‖ * ‖g p.2‖ * (1 + ‖p.1‖ + ‖p.2‖)^N_R ≤
          C_R * ‖f p.1‖ * ‖g p.2‖ * ((1 + ‖p.1‖)^N_R * (1 + ‖p.2‖)^N_R) :=
        mul_le_mul_of_nonneg_left h_bound' h_factor_nonneg
      have lhs_eq : C_R * (1 + ‖p.1‖ + ‖p.2‖)^N_R * ‖f p.1‖ * ‖g p.2‖ =
          C_R * ‖f p.1‖ * ‖g p.2‖ * (1 + ‖p.1‖ + ‖p.2‖)^N_R := by ring
      have rhs_eq : C_R * (((1 + ‖p.1‖)^N_R * ‖f p.1‖) * ((1 + ‖p.2‖)^N_R * ‖g p.2‖)) =
          C_R * ‖f p.1‖ * ‖g p.2‖ * ((1 + ‖p.1‖)^N_R * (1 + ‖p.2‖)^N_R) := by ring
      linarith [key, lhs_eq, rhs_eq]
  -- Step 5: apply DC to get Tendsto of the joint integral.
  have h_DC :
      Filter.Tendsto
        (fun a : SpacetimeDim d =>
          ∫ p : NPointDomain d n × NPointDomain d m, clusterIntegrand Wfn f g a p)
        (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
          Bornology.cobounded (SpacetimeDim d))
        (nhds (∫ p : NPointDomain d n × NPointDomain d m,
          clusterLimitIntegrand Wfn f g p)) := by
    -- The filter is IsCountablyGenerated:
    -- principal is auto-instance; cobounded on a metric space comes from
    -- comap (dist · 0) atTop, with atTop on ℝ countably generated.
    haveI hcb : (Bornology.cobounded (SpacetimeDim d)).IsCountablyGenerated := by
      rw [← Metric.comap_dist_right_atTop (0 : SpacetimeDim d)]
      infer_instance
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun p => C_R * (1 + ‖p.1‖ + ‖p.2‖) ^ N_R * ‖f p.1‖ * ‖g p.2‖) ?_ ?_
      h_dominator_integrable h_pointwise
    · -- AEStronglyMeasurable of clusterIntegrand a, eventually in a.
      refine Filter.Eventually.of_forall (fun a => ?_)
      unfold clusterIntegrand
      refine MeasureTheory.AEStronglyMeasurable.mul ?_
        (g.continuous.comp continuous_snd).aestronglyMeasurable
      refine MeasureTheory.AEStronglyMeasurable.mul ?_
        (f.continuous.comp continuous_fst).aestronglyMeasurable
      -- F_ext_on_translatedPET_total composed with the wick-rotated config
      -- is measurable (F_ext_total measurable + continuous composition).
      sorry
    · -- The eventually-in-a bound `‖clusterIntegrand a p‖ ≤ bound p` for
      -- `‖a⃗‖ > R_R` (where R_R is from Ruelle's bound).
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨{a : SpacetimeDim d | a 0 = 0 ∧
        (∑ i : Fin d, (a (Fin.succ i))^2) > R_R^2}, ?_, ?_⟩
      · -- This set is in `principal {a 0 = 0} ⊓ cobounded`. Decompose:
        -- {a 0 = 0} ∈ principal, (closedBall 0 R_R)ᶜ ∈ cobounded; their
        -- intersection is contained in {a | a 0 = 0 ∧ ‖a⃗‖² > R_R²}
        -- because (sup-norm) ‖a‖² ≤ ∑ |a i|², and for a 0 = 0,
        -- ∑ |a i|² = ∑_{i ≥ 1} (a (succ i))².
        rw [Filter.mem_inf_iff_superset]
        refine ⟨{a : SpacetimeDim d | a 0 = 0}, Filter.mem_principal_self _,
          (Metric.closedBall (0 : SpacetimeDim d) R_R)ᶜ, ?_, ?_⟩
        · exact (Metric.hasBasis_cobounded_compl_closedBall (0 : SpacetimeDim d)).mem_of_mem
            trivial
        · intro a ⟨ha₀, _hball⟩
          refine ⟨ha₀, ?_⟩
          -- Need: ‖a‖ > R_R + a 0 = 0 → ∑ (a (succ i))² > R_R².
          -- Pi sup-norm + nonneg max bound: routed to follow-up.
          sorry
      · intro a ha
        refine Filter.Eventually.of_forall (fun p => ?_)
        -- Bound |F_ext_total| by Ruelle, and combine with f, g norms.
        sorry
  -- Step 6: combine — joint integral tends to L_n * L_m.
  have h_joint_tendsto :
      Filter.Tendsto
        (fun a : SpacetimeDim d =>
          ∫ p : NPointDomain d n × NPointDomain d m, clusterIntegrand Wfn f g a p)
        (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
          Bornology.cobounded (SpacetimeDim d))
        (nhds (L_n * L_m)) := by
    rw [← h_limit_eq_product]
    exact h_DC
  -- Step 7: convert Tendsto along `principal {a 0 = 0} ⊓ cobounded` to
  -- the existential ε-R form. Strategy:
  -- (1) From h_joint_tendsto + ε > 0: ∀ᶠ a in filter, ‖F a - L_n L_m‖ < ε.
  -- (2) Decompose the filter membership: ∃ R₀, {a 0 = 0} ∩ (closedBall 0 R₀)ᶜ ⊆
  --     {a | ‖F a - L_n L_m‖ < ε}.
  -- (3) For a 0 = 0 + ‖a‖_sup > R₀: at least one spatial component exceeds R₀,
  --     so ∑ (a (succ i))² > R₀².
  -- (4) Set R := R₀ in the existential.
  --
  -- Plus: undo the change-of-variables (Step 1 sorry above) to identify the
  -- joint integral with `∫ x : NPointDomain d (n+m), F_ext (f.tensorProduct g_a) x`.
  --
  -- Filter manipulation + change-of-variables undoing. Routed to follow-up
  -- after Steps 1, 3 are filled.
  sorry

end OSReconstruction
