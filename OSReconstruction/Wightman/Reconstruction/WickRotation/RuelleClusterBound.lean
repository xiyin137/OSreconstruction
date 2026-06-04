/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import OSReconstruction.Wightman.Reconstruction.SchwingerOS

/-!
# Ruelle-conditional cluster bridge for the Wick-rotated boundary integral

This file packages the Ruelle 1962 / Araki-Hepp-Ruelle 1962 analytic
cluster content as a **conditional-hypothesis structure**
(`RuelleAnalyticClusterHypotheses Wfn n m`) and proves the cluster
theorem `W_analytic_cluster_integral` as a *conditional* result that
threads `hRuelle` through the dominated-convergence assembly.

**Trust boundary**: 0 new production axioms. The two textbook Ruelle
inputs (uniform polynomial bound + pointwise factorization on PET)
appear as named hypothesis fields of `RuelleAnalyticClusterHypotheses`,
not as Lean `axiom` declarations. Downstream consumers must supply a
value of this structure to invoke the cluster bridge — the trust
boundary is therefore visible at every call site.

## The obstruction Ruelle resolves

The standard `spectrum_condition`'s polynomial bound
`‖W_analytic z‖ ≤ C(1 + ‖z‖)^N` on the forward tube has the constant
`C` and exponent `N` independent of the position `z`. For our cluster
integral, after substituting `y = x_m - a`, we evaluate
`W_analytic_BHW Wfn (n+m)` at `(wick x_n, wick(y + a))`. The naive
polynomial bound gives `(1 + ‖x_n‖ + ‖y + a‖)^N`, which depends on
`a` and grows as `|⃗a| → ∞`. This breaks dominated convergence: the
dominator must be `a`-independent.

Ruelle's theorem provides a **uniform-in-a polynomial bound** on the
spatially-separated analytic continuation, on configs in the joint
analytic domain (PET): the constants are independent of `a`. This is
the spectral-gap content of R4 (distributional cluster) made explicit
at the analytic level, and we package it as a hypothesis structure
rather than as production axioms because:

* The statements are QFT-specific (mention `WightmanFunctions`,
  `W_analytic_BHW`, PET).
* The textbook proof reduces them to R4 + spectrum condition + a
  spectral chain (see `Proofideas/ruelle_blueprint.lean` for the
  L1–L7 proof roadmap).
* Until that chain is formalized, the trust boundary should be
  visible as named hypotheses, not folded into the production
  axiom inventory.

## References

* Ruelle, *On the asymptotic condition in quantum field theory*,
  Helvetica Physica Acta 35 (1962), pp. 147-163.
* Araki-Hepp-Ruelle, *On the asymptotic behaviour of Wightman
  functions in space-like directions*, Helv. Phys. Acta 35 (1962),
  Theorem 2.
* Jost, *The General Theory of Quantized Fields*, §VI.1.
* Streater-Wightman, *PCT, Spin and Statistics, and All That*, §3.4.

## Public theorems

* `RuelleAnalyticClusterHypotheses` — the conditional-input structure.
* `W_analytic_cluster_integral_via_ruelle` — the dominated-convergence
  assembly given the hypotheses.
* `W_analytic_cluster_integral` and `wickRotatedBoundaryPairing_cluster`
  — wrappers in standard Wick-rotated-boundary form.
* `schwinger_E4_cluster_OPTR_case` — the OPTR-restricted bridge to
  `OsterwalderSchraderAxioms.E4_cluster` shape.

See `docs/cluster_via_ruelle_plan.md` and `Proofideas/ruelle_blueprint.lean`
for the full plan; see `OSReconstruction/Wightman/Spectral/Ruelle/L5_SpectralRiemannLebesgue.lean`
for an inventoried frontier lemma in the proof chain.
-/

open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-! ### Ruelle hypotheses (textbook content as conditional structure)

The textbook content of Ruelle 1962 / Araki-Hepp-Ruelle 1962 (the
analytic cluster theorem on the standard forward tube, with
spectral-gap-driven uniform decay along spacelike directions) is
packaged here as a **conditional structure** rather than as production
axioms.

Downstream theorems in this file consume `RuelleAnalyticClusterHypotheses`
as an explicit parameter; the trust boundary is therefore visible at
every call site, and the cluster proof is a *conditional* result.

This is the project's preferred trust pattern for QFT-specific
textbook statements (per the axiom-gate policy): rather than extending
the production trusted core with QFT-level reconstruction assertions,
we keep them as named hypotheses that downstream callers can either
discharge from a future formalization or accept locally as project-side
inputs.

References for the underlying textbook content (no production-axiom
status):
* Ruelle 1962, *On the asymptotic condition in quantum field theory*,
  Helvetica Physica Acta 35.
* Araki-Hepp-Ruelle 1962, *On the asymptotic behaviour of Wightman
  functions in space-like directions*, Helv. Phys. Acta 35, 164,
  Theorem 2 (the pointwise version on the standard forward tube).
* Jost, *The General Theory of Quantized Fields*, §VI.1.
* Streater-Wightman §3.4.

The two field statements assume joint analytic-domain membership
(`PermutedExtendedTube d (n+m)`) where the underlying analytic
continuation is well-defined; the cluster proof discharges this via
`joint_wick_config_in_PET` for OPTR-supported Wick configurations with
AE-distinct joint times. -/

/-! ### Boundary-distance regulator

The polynomial bound on `W_analytic_BHW` over `ForwardTube` requires a
regulator that diverges as the imaginary differences approach `∂V+`,
matching Streater-Wightman Theorem 3.1.1. The regulator is defined as
the minimum `Metric.infDist` of consecutive imaginary differences to
the closed complement of the open forward cone (the cone boundary is
in this complement, so the distance is the distance to the cone
boundary).

For empty configurations (`n = 0`), the bound is vacuously trivial,
and the regulator is set to `1` (so that `1/regulator = 1`,
contributing no inverse-blow-up factor). -/

/-- The set of `η ∈ ℝ^{d+1}` lying in the open forward light cone. -/
def openForwardConeSet (d : ℕ) [NeZero d] : Set (Fin (d + 1) → ℝ) :=
  {η | InOpenForwardCone d η}

/-- The boundary-distance regulator: the minimum distance, over all
consecutive imaginary differences `Im(z_k - z_{k-1})`, of the difference
to the closed complement of the open forward cone. Returns `1` for the
empty configuration. -/
noncomputable def tubeBoundaryDist {d : ℕ} [NeZero d] {n : ℕ}
    (z : Fin n → Fin (d + 1) → ℂ) : ℝ :=
  if h : n = 0 then 1
  else
    have : NeZero n := ⟨h⟩
    ⨅ k : Fin n,
      Metric.infDist
        (fun μ : Fin (d + 1) =>
          (z k μ).im -
            (if hk : (k : ℕ) = 0 then 0
             else (z ⟨(k : ℕ) - 1, by omega⟩ μ).im))
        (openForwardConeSet d)ᶜ

/-- **Ruelle 1962 analytic cluster hypotheses** (conditional structure
holding the textbook content as named hypotheses, *not* as production
axioms).

* `bound`: uniform-in-`a` polynomial bound on the analytic continuation
  for spatially separated arguments, on configs in the joint analytic
  domain.
* `pointwise`: pointwise factorization as `|⃗a| → ∞` along spacelike
  directions, hypothesizing eventual joint-PET membership.

A `RuelleAnalyticClusterHypotheses Wfn n m` value can be supplied by:
1. A future formalization of Ruelle's argument from R4 + spectral
   support (~1500+ lines of momentum-space spectral theory; routed as
   a separate sub-project).
2. A textbook acceptance at the call site (locally `axiom` declaration
   if a downstream consumer wants production trust for a specific
   `Wfn`), which makes the trust boundary visible to that consumer
   rather than baked into this file's production surface.
3. A model-specific construction (e.g., free fields, generalized free
   fields, exactly solvable QFTs).

The structure deliberately keeps both fields' joint-PET hypotheses
explicit so the call-site obligations match the textbook statement:
the analytic continuation is meaningful only on PET. -/
structure RuelleAnalyticClusterHypotheses
    (Wfn : WightmanFunctions d) (n m : ℕ) : Prop where
  /-- Uniform-in-`a` polynomial bound (Ruelle 1962 / Streater-Wightman
  Theorem 3.1.1 / §3.4).

  There exist constants `C > 0`, `N M : ℕ`, `R > 0` such that for
  forward-tube `z₁, z₂` and spatial `a` with `|⃗a| > R`, *if* the
  appended config lies in the joint analytic domain (PET), the bound
  ```
    ‖W_analytic_BHW(joint)‖ ≤ C · (1 + ‖z₁‖ + ‖z₂‖)^N
                                · (1 + tubeBoundaryDist z₁⁻¹)^M
                                · (1 + tubeBoundaryDist z₂⁻¹)^M
  ```
  holds with `C, N, M` independent of `a`.

  The boundary-distance factors `(1 + Δ⁻¹)^M` are essential: without
  them, the bound is unsatisfiable for any actual Wightman QFT (free
  fields exhibit `1/(z-w)²`-style internal singularities as `Im(z-w) →
  ∂V+`, allowed within the open forward tube; the polynomial in norms
  alone cannot compensate). See `docs/ruelle_bound_vacuity_concern.md`
  for the analysis. -/
  bound : ∃ (C : ℝ) (N M : ℕ) (R : ℝ),
    0 < C ∧ 0 < R ∧
    ∀ (z₁ : Fin n → Fin (d + 1) → ℂ),
    ∀ (z₂ : Fin m → Fin (d + 1) → ℂ),
      z₁ ∈ ForwardTube d n →
      z₂ ∈ ForwardTube d m →
      ∀ (a : SpacetimeDim d), a 0 = 0 →
        (∑ i : Fin d, (a (Fin.succ i)) ^ 2) > R ^ 2 →
        (Fin.append z₁
            (fun k μ => z₂ k μ +
              (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) ∈
          PermutedExtendedTube d (n + m) →
        ‖(W_analytic_BHW Wfn (n + m)).val
            (Fin.append z₁
              (fun k μ => z₂ k μ +
                (if μ = 0 then (0 : ℂ) else (a μ : ℂ))))‖
          ≤ C * (1 + ‖z₁‖ + ‖z₂‖) ^ N
              * (1 + (tubeBoundaryDist z₁)⁻¹) ^ M
              * (1 + (tubeBoundaryDist z₂)⁻¹) ^ M
  /-- Pointwise analytic cluster (Araki-Hepp-Ruelle 1962 Theorem 2).

  For forward-tube `z₁, z₂` with eventual joint-PET membership of the
  appended config, the joint analytic continuation factorizes
  asymptotically along the spatial-cobounded filter. -/
  pointwise :
    ∀ (z₁ : Fin n → Fin (d + 1) → ℂ) (z₂ : Fin m → Fin (d + 1) → ℂ),
      z₁ ∈ ForwardTube d n → z₂ ∈ ForwardTube d m →
      (∀ᶠ a : SpacetimeDim d in
          Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
            Bornology.cobounded (SpacetimeDim d),
        (Fin.append z₁
            (fun k μ => z₂ k μ +
              (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) ∈
          PermutedExtendedTube d (n + m)) →
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

/-! ### Wick rotation preserves Pi sup-norm -/

/-- Wick rotation preserves the per-component norm: `|wick x μ| = |x μ|`. -/
theorem wickRotatePoint_norm_component (x : Fin (d+1) → ℝ) (μ : Fin (d+1)) :
    ‖wickRotatePoint x μ‖ = ‖x μ‖ := by
  by_cases hμ : μ = 0
  · subst hμ
    simp [wickRotatePoint, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs]
  · simp [wickRotatePoint, hμ, Complex.norm_real, Real.norm_eq_abs]

/-- Wick rotation preserves the Pi sup-norm at each spacetime point. -/
theorem wickRotatePoint_norm_eq (x : SpacetimeDim d) :
    ‖wickRotatePoint x‖ = ‖x‖ := by
  simp only [Pi.norm_def]
  congr 1
  apply Finset.sup_congr rfl
  intro μ _
  ext
  exact wickRotatePoint_norm_component x μ

/-- Lifted: Wick rotation per-point preserves the joint Pi sup-norm. -/
theorem wickRotate_norm_eq {k : ℕ} (x : NPointDomain d k) :
    ‖fun j => wickRotatePoint (x j)‖ = ‖x‖ := by
  simp only [Pi.norm_def]
  congr 1
  apply Finset.sup_congr rfl
  intro j _
  ext
  exact wickRotatePoint_norm_eq (x j)

/-! ### Joint config bridge: F_ext_on_translatedPET_total ↔ W_analytic_BHW

For OPTR-supported `p.1, p.2` and a purely-spatial translation `a`, the
joint Wick-rotated config lies in `PermutedExtendedTube d (n+m)`
provided the joint times are distinct (which holds a.e. in `(p.1, p.2)`,
since the diagonal set where times overlap is a measure-zero
sub-manifold).

The bridge then follows from `F_ext_on_translatedPET_total_eq_on_PET`,
which is a project-side lemma that does NOT depend on OPTR or
distinctness — just PET membership. -/

/-- The joint Wick-rotated config (with m-block spatially shifted) lies
in `PermutedExtendedTube d (n+m)` when the joint times are distinct
positive (which holds a.e. for OPTR-supported `p.1, p.2`).

Specifically uses `euclidean_distinct_in_permutedTube` applied to the
joint configuration — all (n+m) times are positive (from OPTR), and
distinctness is the additional AE hypothesis. The spatial shift by `a`
on the m-block does NOT affect the imaginary parts of the Wick rotation
(which only encode times via `μ = 0`), so PET membership reduces to the
`euclidean_distinct_in_permutedTube` argument. -/
theorem joint_wick_config_in_PET
    (n m : ℕ) (p₁ : NPointDomain d n) (p₂ : NPointDomain d m)
    (a : SpacetimeDim d) (ha₀ : a 0 = 0)
    (hp₁_pos : ∀ i : Fin n, p₁ i 0 > 0)
    (hp₂_pos : ∀ i : Fin m, p₂ i 0 > 0)
    (h_distinct_joint : ∀ i j : Fin (n + m), i ≠ j →
      Fin.append (fun k => p₁ k 0) (fun k => p₂ k 0) i ≠
      Fin.append (fun k => p₁ k 0) (fun k => p₂ k 0) j) :
    (Fin.append (fun k => wickRotatePoint (p₁ k))
                (fun k μ => wickRotatePoint (p₂ k) μ +
                  (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) ∈
      PermutedExtendedTube d (n + m) := by
  -- Define the underlying joint real config (with spatial-a shift on m-block).
  set xs : NPointDomain d (n + m) :=
    Fin.append p₁ (fun j => p₂ j + a) with hxs_def
  -- Show: joint complex config = (wickRotatePoint ∘ xs).
  have h_eq :
      (Fin.append (fun k => wickRotatePoint (p₁ k))
                  (fun k μ => wickRotatePoint (p₂ k) μ +
                    (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) =
      (fun k => wickRotatePoint (xs k)) := by
    funext k μ
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
    · -- k = Fin.castAdd m i', joint config gives wick(p₁ i'), xs gives wick(p₁ i').
      simp [Fin.append_left, hxs_def]
    · -- k = Fin.natAdd n j', joint config gives wick(p₂ j') + (0, a),
      -- xs gives wick(p₂ j' + a).
      simp [Fin.append_right, hxs_def]
      by_cases hμ : μ = 0
      · subst hμ
        simp [wickRotatePoint, ha₀]
      · simp [wickRotatePoint, hμ]
  rw [h_eq]
  -- Apply euclidean_distinct_in_permutedTube to xs.
  apply euclidean_distinct_in_permutedTube xs
  · -- distinct: xs i 0 ≠ xs j 0 for i ≠ j.
    intro i j hij
    have h_xs_time : ∀ k : Fin (n + m),
        xs k 0 = Fin.append (fun k => p₁ k 0) (fun k => p₂ k 0) k := by
      intro k
      refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
      · simp [hxs_def, Fin.append_left]
      · simp [hxs_def, Fin.append_right, ha₀]
    rw [h_xs_time, h_xs_time]
    exact h_distinct_joint i j hij
  · -- positive: xs i 0 > 0.
    intro k
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
    · simp [hxs_def, Fin.append_left]
      exact hp₁_pos i'
    · simp [hxs_def, Fin.append_right]
      have := hp₂_pos j'
      linarith [ha₀]

/-- **The joint F_ext bridge**: `F_ext_on_translatedPET_total =
W_analytic_BHW` on the joint Wick-rotated config (with spatial m-block
shift), for OPTR p.1, p.2 with distinct joint times.

Combines `joint_wick_config_in_PET` with
`F_ext_on_translatedPET_total_eq_on_PET`. Holds a.e. in (p.1, p.2). -/
theorem joint_F_ext_eq_W_analytic
    (Wfn : WightmanFunctions d) (n m : ℕ)
    (p₁ : NPointDomain d n) (p₂ : NPointDomain d m)
    (a : SpacetimeDim d) (ha₀ : a 0 = 0)
    (hp₁_pos : ∀ i : Fin n, p₁ i 0 > 0)
    (hp₂_pos : ∀ i : Fin m, p₂ i 0 > 0)
    (h_distinct_joint : ∀ i j : Fin (n + m), i ≠ j →
      Fin.append (fun k => p₁ k 0) (fun k => p₂ k 0) i ≠
      Fin.append (fun k => p₁ k 0) (fun k => p₂ k 0) j) :
    F_ext_on_translatedPET_total Wfn
      (Fin.append (fun k => wickRotatePoint (p₁ k))
                  (fun k μ => wickRotatePoint (p₂ k) μ +
                    (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) =
    (W_analytic_BHW Wfn (n + m)).val
      (Fin.append (fun k => wickRotatePoint (p₁ k))
                  (fun k μ => wickRotatePoint (p₂ k) μ +
                    (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) :=
  F_ext_on_translatedPET_total_eq_on_PET Wfn _
    (joint_wick_config_in_PET n m p₁ p₂ a ha₀ hp₁_pos hp₂_pos h_distinct_joint)

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

/-! ### AE-distinct joint times on `NPointDomain d n × NPointDomain d m`

For the joint Wick-rotated config to lie in PET, we need the joint times
(combined `Fin.append (p₁ · 0) (p₂ · 0)`) to be pairwise distinct. This
holds AE in `(p₁, p₂)`. -/

/-- The cross hyperplane `{p | p.1 i 0 = p.2 j 0}` has measure zero in
`NPointDomain d n × NPointDomain d m` under the product Lebesgue
measure. -/
private theorem measure_crossTimeEq_zero
    {d n m : ℕ} (i : Fin n) (j : Fin m) :
    (MeasureTheory.volume :
        MeasureTheory.Measure (NPointDomain d n × NPointDomain d m))
        {p | p.1 i 0 = p.2 j 0} = 0 := by
  let L : NPointDomain d n × NPointDomain d m →ₗ[ℝ] ℝ :=
    { toFun := fun p => p.1 i 0 - p.2 j 0
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  have hset :
      {p : NPointDomain d n × NPointDomain d m | p.1 i 0 = p.2 j 0} =
      (LinearMap.ker L : Set _) := by
    ext p; simp [L, LinearMap.mem_ker, sub_eq_zero]
  have hker_ne_top : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hzero : L = 0 := LinearMap.ker_eq_top.mp htop
    let p₁ : NPointDomain d n := fun k μ => if k = i ∧ μ = 0 then (1 : ℝ) else 0
    let p₂ : NPointDomain d m := 0
    have hLp : L (p₁, p₂) = 0 := by
      simpa using congrArg (fun f => f (p₁, p₂)) hzero
    have h_compute : L (p₁, p₂) = 1 := by
      show p₁ i 0 - p₂ j 0 = 1
      simp [p₁, p₂]
    rw [h_compute] at hLp
    norm_num at hLp
  rw [hset]
  haveI : (MeasureTheory.volume :
      MeasureTheory.Measure (NPointDomain d n × NPointDomain d m)).IsAddHaarMeasure := by
    show (MeasureTheory.volume.prod MeasureTheory.volume :
      MeasureTheory.Measure (NPointDomain d n × NPointDomain d m)).IsAddHaarMeasure
    exact MeasureTheory.Measure.prod.instIsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n))
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d m))
  exact MeasureTheory.Measure.addHaar_submodule _ (LinearMap.ker L) hker_ne_top

/-- AE pairwise distinctness of joint time coordinates: for almost every
`(p₁, p₂) ∈ NPointDomain d n × NPointDomain d m`, the joint time function
`Fin.append (fun k => p₁ k 0) (fun k => p₂ k 0)` is injective. -/
private theorem ae_pairwise_distinct_jointTimeCoords {d n m : ℕ} :
    ∀ᵐ (p : NPointDomain d n × NPointDomain d m) ∂MeasureTheory.volume,
      ∀ i j : Fin (n + m), i ≠ j →
        Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0) i ≠
        Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0) j := by
  -- For each pair (i, j) with i ≠ j, the bad set has measure zero.
  -- We split into within-1, within-2, and cross cases.
  have hbad : ∀ (q : {p : Fin (n + m) × Fin (n + m) // p.1 ≠ p.2}),
      (MeasureTheory.volume :
          MeasureTheory.Measure (NPointDomain d n × NPointDomain d m))
        {p : NPointDomain d n × NPointDomain d m |
          Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0) q.1.1 =
          Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0) q.1.2} = 0 := by
    rintro ⟨⟨i, j⟩, hij⟩
    -- Case-split via Fin.addCases.
    induction i using Fin.addCases with
    | left i' =>
      induction j using Fin.addCases with
      | left j' =>
        -- Within p.1: lift `measure_timeEq_zero` via the projection.
        have hi'j' : i' ≠ j' := by
          intro heq; apply hij; simp [heq]
        have hcyl :
            {p : NPointDomain d n × NPointDomain d m |
              Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0)
                (Fin.castAdd m i') =
              Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0)
                (Fin.castAdd m j')} =
            {x : NPointDomain d n | x i' 0 = x j' 0} ×ˢ
              (Set.univ : Set (NPointDomain d m)) := by
          ext p; simp [Fin.append_left]
        have hzero :
            (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n))
              {x : NPointDomain d n | x i' 0 = x j' 0} = 0 := by
          let L : NPointDomain d n →ₗ[ℝ] ℝ :=
            { toFun := fun x => x i' 0 - x j' 0
              map_add' := by intros; simp; ring
              map_smul' := by intros; simp; ring }
          have hset_eq :
              {x : NPointDomain d n | x i' 0 = x j' 0} =
              (LinearMap.ker L : Set _) := by
            ext x; simp [L, LinearMap.mem_ker, sub_eq_zero]
          have hker_ne_top : LinearMap.ker L ≠ ⊤ := by
            intro htop
            have hzero : L = 0 := LinearMap.ker_eq_top.mp htop
            have hji : j' ≠ i' := fun h => hi'j' h.symm
            have hval : L (fun k μ => if k = i' ∧ μ = 0 then (1 : ℝ) else 0) = 0 := by
              simpa using congrArg
                (fun f => f (fun k μ => if k = i' ∧ μ = 0 then (1 : ℝ) else 0)) hzero
            have : (1 : ℝ) = 0 := by simp [L, hji] at hval
            norm_num at this
          rw [hset_eq]
          exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume
            (LinearMap.ker L) hker_ne_top
        rw [hcyl,
          show (MeasureTheory.volume :
              MeasureTheory.Measure (NPointDomain d n × NPointDomain d m)) =
            MeasureTheory.volume.prod MeasureTheory.volume from rfl,
          MeasureTheory.Measure.prod_prod, hzero, zero_mul]
      | right j' =>
        -- Cross: p.1 i' 0 = p.2 j' 0.
        have hcyl :
            {p : NPointDomain d n × NPointDomain d m |
              Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0)
                (Fin.castAdd m i') =
              Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0)
                (Fin.natAdd n j')} =
            {p : NPointDomain d n × NPointDomain d m | p.1 i' 0 = p.2 j' 0} := by
          ext p; simp [Fin.append_left, Fin.append_right]
        rw [hcyl]
        exact measure_crossTimeEq_zero i' j'
    | right i' =>
      induction j using Fin.addCases with
      | left j' =>
        -- Cross (swapped): p.2 i' 0 = p.1 j' 0.
        have hcyl :
            {p : NPointDomain d n × NPointDomain d m |
              Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0)
                (Fin.natAdd n i') =
              Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0)
                (Fin.castAdd m j')} =
            {p : NPointDomain d n × NPointDomain d m | p.1 j' 0 = p.2 i' 0} := by
          ext p
          simp [Fin.append_left, Fin.append_right]
          exact eq_comm
        rw [hcyl]
        exact measure_crossTimeEq_zero j' i'
      | right j' =>
        -- Within p.2.
        have hi'j' : i' ≠ j' := by
          intro heq; apply hij; simp [heq]
        have hcyl :
            {p : NPointDomain d n × NPointDomain d m |
              Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0)
                (Fin.natAdd n i') =
              Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0)
                (Fin.natAdd n j')} =
            (Set.univ : Set (NPointDomain d n)) ×ˢ
              {y : NPointDomain d m | y i' 0 = y j' 0} := by
          ext p; simp [Fin.append_right]
        have hzero :
            (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d m))
              {y : NPointDomain d m | y i' 0 = y j' 0} = 0 := by
          let L : NPointDomain d m →ₗ[ℝ] ℝ :=
            { toFun := fun y => y i' 0 - y j' 0
              map_add' := by intros; simp; ring
              map_smul' := by intros; simp; ring }
          have hset_eq :
              {y : NPointDomain d m | y i' 0 = y j' 0} =
              (LinearMap.ker L : Set _) := by
            ext y; simp [L, LinearMap.mem_ker, sub_eq_zero]
          have hker_ne_top : LinearMap.ker L ≠ ⊤ := by
            intro htop
            have hzero : L = 0 := LinearMap.ker_eq_top.mp htop
            have hji : j' ≠ i' := fun h => hi'j' h.symm
            have hval : L (fun k μ => if k = i' ∧ μ = 0 then (1 : ℝ) else 0) = 0 := by
              simpa using congrArg
                (fun f => f (fun k μ => if k = i' ∧ μ = 0 then (1 : ℝ) else 0)) hzero
            have : (1 : ℝ) = 0 := by simp [L, hji] at hval
            norm_num at this
          rw [hset_eq]
          exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume
            (LinearMap.ker L) hker_ne_top
        rw [hcyl,
          show (MeasureTheory.volume :
              MeasureTheory.Measure (NPointDomain d n × NPointDomain d m)) =
            MeasureTheory.volume.prod MeasureTheory.volume from rfl,
          MeasureTheory.Measure.prod_prod, hzero, mul_zero]
  -- Combine over all (finitely many) bad pairs.
  have hall :
      ∀ᵐ (p : NPointDomain d n × NPointDomain d m) ∂MeasureTheory.volume,
        ∀ q : {p : Fin (n + m) × Fin (n + m) // p.1 ≠ p.2},
          Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0) q.1.1 ≠
          Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0) q.1.2 := by
    simpa using
      ((Set.toFinite (Set.univ :
          Set {p : Fin (n + m) × Fin (n + m) // p.1 ≠ p.2})).eventually_all
        (l := MeasureTheory.ae (MeasureTheory.volume :
          MeasureTheory.Measure (NPointDomain d n × NPointDomain d m)))
        (p := fun q => fun p : NPointDomain d n × NPointDomain d m =>
          Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0) q.1.1 ≠
          Fin.append (fun k : Fin n => p.1 k 0) (fun k : Fin m => p.2 k 0) q.1.2)).2
        (fun q _ => MeasureTheory.compl_mem_ae_iff.mpr (hbad q))
  filter_upwards [hall] with p hp i j hij
  exact hp ⟨⟨i, j⟩, hij⟩

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

/-! ### Time-gap flatness for the Ruelle regulator -/

private def ruelleTimeGap {n : ℕ} (x : NPointDomain d n) (k : Fin n) : ℝ :=
  if hk : (k : ℕ) = 0 then x k 0
  else x k 0 - x ⟨(k : ℕ) - 1, by omega⟩ 0

private def ruelleGapBoundaryPoint {n : ℕ} (x : NPointDomain d n) (k : Fin n) :
    NPointDomain d n :=
  Function.update x k
    (Function.update (x k) 0
      (if hk : (k : ℕ) = 0 then 0 else x ⟨(k : ℕ) - 1, by omega⟩ 0))

private lemma continuous_tubeBoundaryDist {n : ℕ} :
    Continuous (fun z : Fin n → Fin (d + 1) → ℂ => tubeBoundaryDist (d := d) z) := by
  by_cases hn : n = 0
  · subst hn
    simpa [tubeBoundaryDist] using
      (continuous_const : Continuous (fun _ : Fin 0 → Fin (d + 1) → ℂ => (1 : ℝ)))
  · haveI : NeZero n := ⟨hn⟩
    simp [tubeBoundaryDist, hn]
    rw [show
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          ⨅ k : Fin n,
            Metric.infDist
              (fun μ : Fin (d + 1) =>
                (z k μ).im -
                  (if k = 0 then 0
                   else (z ⟨(k : ℕ) - 1, by omega⟩ μ).im))
              (openForwardConeSet d)ᶜ) =
        (Finset.univ.inf' Finset.univ_nonempty fun k =>
          fun z : Fin n → Fin (d + 1) → ℂ =>
            Metric.infDist
              (fun μ : Fin (d + 1) =>
                (z k μ).im -
                  (if k = 0 then 0
                   else (z ⟨(k : ℕ) - 1, by omega⟩ μ).im))
              (openForwardConeSet d)ᶜ) by
      funext z
      rw [Finset.inf'_apply]
      exact Eq.symm (Finset.inf'_univ_eq_ciInf fun k =>
        Metric.infDist
          (fun μ : Fin (d + 1) =>
            (z k μ).im -
              (if k = 0 then 0
               else (z ⟨(k : ℕ) - 1, by omega⟩ μ).im))
          (openForwardConeSet d)ᶜ)]
    exact Continuous.finset_inf' Finset.univ_nonempty
      (fun k _ => by
        refine (Metric.continuous_infDist_pt (s := (openForwardConeSet d)ᶜ)).comp ?_
        refine continuous_pi fun μ => ?_
        by_cases hk : k = 0
        · simp [hk]
          fun_prop
        · simp [hk]
          fun_prop)

private lemma ruelleTimeGap_pos_of_mem_orderedPositiveTimeRegion {n : ℕ}
    {x : NPointDomain d n} (hx : x ∈ OrderedPositiveTimeRegion d n) (k : Fin n) :
    0 < ruelleTimeGap (d := d) x k := by
  unfold ruelleTimeGap
  by_cases hk : (k : ℕ) = 0
  · simp [hk, (hx k).1]
  · simp [hk]
    let km1 : Fin n := ⟨(k : ℕ) - 1, by omega⟩
    have hlt : km1 < k := by
      rw [Fin.lt_def]
      simp [km1]
      omega
    exact (hx km1).2 k hlt

private lemma ruelleGapBoundaryPoint_not_mem_orderedPositiveTimeRegion {n : ℕ}
    (x : NPointDomain d n) (k : Fin n) :
    ruelleGapBoundaryPoint (d := d) x k ∉ OrderedPositiveTimeRegion d n := by
  intro h
  unfold ruelleGapBoundaryPoint at h
  by_cases hk : (k : ℕ) = 0
  · have := (h k).1
    simp [hk] at this
  · let km1 : Fin n := ⟨(k : ℕ) - 1, by omega⟩
    have hlt : km1 < k := by
      rw [Fin.lt_def]
      simp [km1]
      omega
    have hne : km1 ≠ k := hlt.ne
    have := (h km1).2 k hlt
    simp [hk, km1, hne] at this

private lemma ruelleGapBoundaryPoint_sub_apply {n : ℕ}
    (x : NPointDomain d n) (k j : Fin n) (μ : Fin (d + 1)) :
    (x - ruelleGapBoundaryPoint (d := d) x k) j μ =
      if j = k ∧ μ = 0 then ruelleTimeGap (d := d) x k else 0 := by
  unfold ruelleTimeGap ruelleGapBoundaryPoint
  by_cases hj : j = k
  · by_cases hμ : μ = 0
    · subst hμ
      by_cases hk : (k : ℕ) = 0 <;> simp [hj, hk]
    · by_cases hk : (k : ℕ) = 0 <;> simp [hj, hk, hμ]
  · by_cases hk : (k : ℕ) = 0 <;> simp [hk, hj]

private lemma norm_sub_ruelleGapBoundaryPoint_le {n : ℕ}
    (x : NPointDomain d n) (k : Fin n) :
    ‖x - ruelleGapBoundaryPoint (d := d) x k‖ ≤ |ruelleTimeGap (d := d) x k| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
  intro μ
  rw [Real.norm_eq_abs]
  rw [ruelleGapBoundaryPoint_sub_apply]
  split_ifs <;> simp

private lemma iteratedFDeriv_eq_zero_of_notMem_orderedPositiveTimeRegion {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    ∀ r x, x ∉ OrderedPositiveTimeRegion d n →
      iteratedFDeriv ℝ r (f : NPointDomain d n → ℂ) x = 0 := by
  intro r x hxout
  by_contra hne
  have hx_support :
      x ∈ Function.support (iteratedFDeriv ℝ r (f : NPointDomain d n → ℂ)) := by
    simpa [Function.mem_support, hne]
  exact hxout
    (hf ((support_iteratedFDeriv_subset (𝕜 := ℝ) (n := r) (f := ⇑f)) hx_support))

set_option maxHeartbeats 800000 in
private theorem ruelle_timeGap_weighted_flatness_bound_explicit {n : ℕ}
    (f : SchwartzNPoint d n)
    (hf : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (P m : ℕ) (k : Fin n) :
    ∀ x : NPointDomain d n,
      0 < ruelleTimeGap (d := d) x k →
      ruelleTimeGap (d := d) x k ≤ 1 →
      (1 + ‖x‖) ^ P * ‖f x‖ ≤
        (2 ^ (P + P) * ((Finset.Iic (P, m + 1)).sup
            (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)) f /
          (Nat.factorial m : ℝ)) *
          (ruelleTimeGap (d := d) x k) ^ (m + 1) := by
  let sem := (Finset.Iic (P, m + 1)).sup
    (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)
  let A : ℝ := 2 ^ (P + P) * sem f
  let A0 : ℝ := 2 ^ P * sem f
  intro x hgap_pos hgap_le_one
  let c : NPointDomain d n := ruelleGapBoundaryPoint (d := d) x k
  let v : NPointDomain d n := x - c
  let L : ℝ →L[ℝ] NPointDomain d n :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let g : ℝ → ℂ :=
    (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c)) ∘ L
  have hshift_contDiff :
      ∀ r : ℕ, ContDiff ℝ r
        (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c)) :=
    fun r => by
      simpa using ((f : SchwartzNPoint d n).smooth r).comp (contDiff_id.add contDiff_const)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using (ContDiff.comp_continuousLinearMap (g := L) (hf := hshift_contDiff r))
  have hc_out : c ∉ OrderedPositiveTimeRegion d n := by
    simpa [c] using ruelleGapBoundaryPoint_not_mem_orderedPositiveTimeRegion (d := d) x k
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro r _hr
    have hr_zero :
        iteratedDerivWithin r g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff r).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ r g 0 =
            (iteratedFDeriv ℝ r
              (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c))
              (L 0)).compContinuousLinearMap fun _ : Fin r => L := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c))
            (hshift_contDiff r) (x := 0) (i := r) le_rfl
      have hzeroF :
          iteratedFDeriv ℝ r (f : NPointDomain d n → ℂ) (L 0 + c) = 0 := by
        have hzero := iteratedFDeriv_eq_zero_of_notMem_orderedPositiveTimeRegion
          (d := d) f hf r c hc_out
        simpa [L, ContinuousLinearMap.smulRight_apply] using hzero
      rw [hcomp, iteratedFDeriv_comp_add_right, hzeroF]
      simp
    rw [hr_zero]
    exact smul_zero _
  have hv_norm_le_gap : ‖v‖ ≤ ruelleTimeGap (d := d) x k := by
    have hv := norm_sub_ruelleGapBoundaryPoint_le (d := d) x k
    have habs : |ruelleTimeGap (d := d) x k| = ruelleTimeGap (d := d) x k :=
      abs_of_pos hgap_pos
    simpa [v, c, habs] using hv
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          (A / (1 + ‖x‖) ^ P) * (ruelleTimeGap (d := d) x k) ^ (m + 1) := by
    intro t ht
    have hsem_bound :
        (1 + ‖L t + c‖) ^ P *
            ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ ≤
          A0 := by
      simpa [A0, sem] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := ℂ) (m := (P, m + 1)) (k := P) (n := m + 1)
          le_rfl le_rfl f (L t + c))
    have hx_le_seg : 1 + ‖x‖ ≤ 2 * (1 + ‖L t + c‖) := by
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hx_eq : x = L t + c + ((1 - t) • v) := by
        simp [L, v, c, ContinuousLinearMap.smulRight_apply, sub_eq_add_neg]
        module
      have hnorm_diff : ‖(1 - t) • v‖ ≤ 1 := by
        calc
          ‖(1 - t) • v‖ = |1 - t| * ‖v‖ := by
            simp [norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * ruelleTimeGap (d := d) x k := by
            have habs_le : |1 - t| ≤ 1 := by
              rw [abs_of_nonneg (by linarith)]
              linarith
            gcongr
          _ ≤ 1 := by simpa using hgap_le_one
      calc
        1 + ‖x‖ = 1 + ‖L t + c + ((1 - t) • v)‖ := by rw [hx_eq]
        _ ≤ 1 + (‖L t + c‖ + ‖(1 - t) • v‖) := by
          gcongr
          exact norm_add_le (L t + c) ((1 - t) • v)
        _ ≤ 1 + (‖L t + c‖ + 1) := by gcongr
        _ ≤ 2 * (1 + ‖L t + c‖) := by
          ring_nf
          nlinarith [norm_nonneg (L t + c)]
    have hpow_pos : 0 < (1 + ‖x‖) ^ P := by positivity
    have hD :
        ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ ≤
          A / (1 + ‖x‖) ^ P := by
      rw [le_div_iff₀ hpow_pos]
      have hpow_cmp :
          (1 + ‖x‖) ^ P ≤ (2 : ℝ) ^ P * (1 + ‖L t + c‖) ^ P := by
        calc
          (1 + ‖x‖) ^ P ≤ (2 * (1 + ‖L t + c‖)) ^ P := by
            exact pow_le_pow_left₀ (by positivity) hx_le_seg P
          _ = (2 : ℝ) ^ P * (1 + ‖L t + c‖) ^ P := by rw [mul_pow]
      calc
        ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ *
            (1 + ‖x‖) ^ P
            ≤ ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ *
                ((2 : ℝ) ^ P * (1 + ‖L t + c‖) ^ P) := by
              gcongr
        _ = (2 : ℝ) ^ P *
              ((1 + ‖L t + c‖) ^ P *
                ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖) := by
              ring
        _ ≤ (2 : ℝ) ^ P * A0 := by gcongr
        _ = A := by
          calc
            (2 : ℝ) ^ P * A0 =
                ((2 : ℝ) ^ P * (2 : ℝ) ^ P) * sem f := by
                  simp [A0]
                  ring
            _ = A := by
              simp [A, pow_add]
    have hL : ‖L‖ ≤ ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
      simpa [L, ContinuousLinearMap.smulRight_apply, Real.norm_eq_abs, norm_smul, mul_comm] using
        (norm_smul s v)
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
      ((hg_contDiff (m + 1)).contDiffAt) ht,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcomp :
        iteratedFDeriv ℝ (m + 1) g t =
          (iteratedFDeriv ℝ (m + 1)
            (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c))
            (L t)).compContinuousLinearMap fun _ : Fin (m + 1) => L := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c))
          (hshift_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp, iteratedFDeriv_comp_add_right]
    calc
      ‖(iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)).compContinuousLinearMap
          (fun _ : Fin (m + 1) => L)‖ ≤
          ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ *
            ∏ _ : Fin (m + 1), ‖L‖ := by
              exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ (A / (1 + ‖x‖) ^ P) * ∏ _ : Fin (m + 1), ‖L‖ := by gcongr
      _ = (A / (1 + ‖x‖) ^ P) * ‖L‖ ^ (m + 1) := by simp
      _ ≤ (A / (1 + ‖x‖) ^ P) * (ruelleTimeGap (d := d) x k) ^ (m + 1) := by
          gcongr
          exact hL.trans hv_norm_le_gap
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := (A / (1 + ‖x‖) ^ P) * (ruelleTimeGap (d := d) x k) ^ (m + 1))
      (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hg_one : g 1 = f x := by
    simp [g, L, v, c, ContinuousLinearMap.smulRight_apply, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc]
  have hpow_nonneg : 0 ≤ (1 + ‖x‖) ^ P := by positivity
  calc
    (1 + ‖x‖) ^ P * ‖f x‖ =
        (1 + ‖x‖) ^ P * ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
          rw [hg_one]
          simp [hTaylor_zero]
    _ ≤ (1 + ‖x‖) ^ P *
          (((A / (1 + ‖x‖) ^ P) * (ruelleTimeGap (d := d) x k) ^ (m + 1)) *
            (1 - (0 : ℝ)) ^ (m + 1) / (((Nat.factorial m : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left (by simpa [hTaylor_zero] using hrem) hpow_nonneg
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) *
          (ruelleTimeGap (d := d) x k) ^ (m + 1) := by
          have hpow_ne : (1 + ‖x‖) ^ P ≠ 0 := by positivity
          field_simp [hpow_ne, Nat.cast_ne_zero]
          ring

private theorem inOpenForwardCone_of_pureTime_perturbation {d : ℕ} [NeZero d]
    (t : ℝ) (ht : 0 < t) (w : Fin (d + 1) → ℝ)
    (hw : ∀ μ, |w μ - (if μ = 0 then t else 0)| < t / (d + 2 : ℝ)) :
    InOpenForwardCone d w := by
  have hw0 : t * (d + 1 : ℝ) / (d + 2 : ℝ) < w 0 := by
    have h0 := hw 0
    simp at h0
    have h0' := abs_lt.mp h0
    have hdpos : (0 : ℝ) < d + 2 := by positivity
    have htmp : t - t / (d + 2 : ℝ) < w 0 := by linarith
    have heq : t - t / (d + 2 : ℝ) = t * (d + 1 : ℝ) / (d + 2 : ℝ) := by
      field_simp [hdpos.ne']
      ring
    simpa [heq] using htmp
  have hw0_pos : 0 < w 0 := by
    have : 0 < t * (d + 1 : ℝ) / (d + 2 : ℝ) := by positivity
    linarith
  have hspatial : ∀ i : Fin d, (w i.succ) ^ 2 < (t / (d + 2 : ℝ)) ^ 2 := by
    intro i
    have hi := hw i.succ
    simp only [Fin.succ_ne_zero, if_false, sub_zero] at hi
    have hi' := abs_lt.mp hi
    nlinarith
  have hspatial_sum : MinkowskiSpace.spatialNormSq d w ≤
      (d : ℝ) * (t / (d + 2 : ℝ)) ^ 2 := by
    unfold MinkowskiSpace.spatialNormSq
    calc
      ∑ i : Fin d, (w i.succ) ^ 2 ≤ ∑ _i : Fin d, (t / (d + 2 : ℝ)) ^ 2 := by
        exact Finset.sum_le_sum (fun i _ => le_of_lt (hspatial i))
      _ = (d : ℝ) * (t / (d + 2 : ℝ)) ^ 2 := by
        simp [Finset.sum_const]
  refine ⟨hw0_pos, ?_⟩
  rw [MinkowskiSpace.minkowskiNormSq_decomp]
  have hmain : MinkowskiSpace.spatialNormSq d w < (w 0) ^ 2 := by
    calc
      MinkowskiSpace.spatialNormSq d w ≤ (d : ℝ) * (t / (d + 2 : ℝ)) ^ 2 :=
        hspatial_sum
      _ < (t * (d + 1 : ℝ) / (d + 2 : ℝ)) ^ 2 := by
        have hdlt : (d : ℝ) < (d + 1 : ℝ) ^ 2 := by nlinarith
        have hsqpos : 0 < (t / (d + 2 : ℝ)) ^ 2 := by positivity
        have heq :
            (t * (d + 1 : ℝ) / (d + 2 : ℝ)) ^ 2 =
              ((d + 1 : ℝ) ^ 2) * (t / (d + 2 : ℝ)) ^ 2 := by
          ring
        rw [heq]
        nlinarith
      _ < (w 0) ^ 2 := by
        have haux : 0 ≤ t * (d + 1 : ℝ) / (d + 2 : ℝ) := by positivity
        nlinarith [hw0, hw0_pos, haux]
  nlinarith

private lemma infDist_pureTime_openForwardConeSet_compl_lower
    (t : ℝ) (ht : 0 < t) :
    t / (d + 2 : ℝ) ≤
      Metric.infDist (fun μ : Fin (d + 1) => if μ = 0 then t else 0)
        (openForwardConeSet d)ᶜ := by
  have hcompl_nonempty : ((openForwardConeSet d)ᶜ : Set (Fin (d + 1) → ℝ)).Nonempty := by
    exact ⟨0, fun h => by
      have h0 := h.1
      simp [openForwardConeSet, InOpenForwardCone] at h0⟩
  refine (Metric.le_infDist hcompl_nonempty).2 ?_
  intro u hu
  by_contra hlt
  have hdist :
      dist (fun μ : Fin (d + 1) => if μ = 0 then t else 0) u < t / (d + 2 : ℝ) := by
    linarith
  have hu_cone : u ∈ openForwardConeSet d := by
    dsimp [openForwardConeSet]
    apply inOpenForwardCone_of_pureTime_perturbation (t := t) ht
    intro μ
    have hcoord :
        |u μ - (if μ = 0 then t else 0)| ≤
          ‖u - (fun μ : Fin (d + 1) => if μ = 0 then t else 0)‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm (u - (fun μ : Fin (d + 1) => if μ = 0 then t else 0)) μ
    have hnorm :
        ‖u - (fun μ : Fin (d + 1) => if μ = 0 then t else 0)‖ < t / (d + 2 : ℝ) := by
      simpa [dist_eq_norm, norm_sub_rev] using hdist
    exact lt_of_le_of_lt hcoord hnorm
  exact hu hu_cone

private lemma wick_imaginary_consecutiveDiff_eq_timeGap {n : ℕ} [NeZero n]
    (x : NPointDomain d n) (k : Fin n) :
    (fun μ : Fin (d + 1) =>
      (wickRotatePoint (x k) μ).im -
        (if k = 0 then 0
         else (wickRotatePoint (x ⟨(k : ℕ) - 1, by omega⟩) μ).im)) =
      fun μ : Fin (d + 1) => if μ = 0 then ruelleTimeGap (d := d) x k else 0 := by
  funext μ
  by_cases hk : k = 0
  · subst k
    by_cases hμ : μ = 0 <;> simp [wickRotatePoint, ruelleTimeGap, hμ]
  · have hkNat : ¬ (k : ℕ) = 0 := fun h => hk (Fin.ext h)
    by_cases hμ : μ = 0 <;> simp [wickRotatePoint, ruelleTimeGap, hk, hkNat, hμ]

private lemma tubeBoundaryDist_wick_lower_of_timeGap_le {n : ℕ} [NeZero n]
    (x : NPointDomain d n) (s : ℝ)
    (hs_pos : 0 < s) (hs_le : ∀ k : Fin n, s ≤ ruelleTimeGap (d := d) x k) :
    s / (d + 2 : ℝ) ≤ tubeBoundaryDist (d := d) (fun k => wickRotatePoint (x k)) := by
  have hn : n ≠ 0 := NeZero.ne n
  simp [tubeBoundaryDist, hn]
  refine le_ciInf ?_
  intro k
  rw [wick_imaginary_consecutiveDiff_eq_timeGap]
  have hgap_pos : 0 < ruelleTimeGap (d := d) x k := lt_of_lt_of_le hs_pos (hs_le k)
  calc
    s / (d + 2 : ℝ) ≤ ruelleTimeGap (d := d) x k / (d + 2 : ℝ) := by
      exact div_le_div_of_nonneg_right (hs_le k) (by positivity)
    _ ≤ Metric.infDist
        (fun μ : Fin (d + 1) => if μ = 0 then ruelleTimeGap (d := d) x k else 0)
        (openForwardConeSet d)ᶜ :=
      infDist_pureTime_openForwardConeSet_compl_lower (d := d) _ hgap_pos

private lemma regulator_small_timeGap_bound (M : ℕ) {s δ : ℝ}
    (hs_pos : 0 < s) (hs_le : s ≤ 1) (hδ : s / (d + 2 : ℝ) ≤ δ) :
    (1 + δ⁻¹) ^ M * s ^ (M + 1) ≤ (d + 3 : ℝ) ^ M := by
  have hden_pos : (0 : ℝ) < d + 2 := by positivity
  have hlower_pos : 0 < s / (d + 2 : ℝ) := div_pos hs_pos hden_pos
  have hδ_pos : 0 < δ := lt_of_lt_of_le hlower_pos hδ
  have hinv : δ⁻¹ ≤ (s / (d + 2 : ℝ))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hlower_pos hδ
  have hmul_inv : δ⁻¹ * s ≤ (d + 2 : ℝ) := by
    calc
      δ⁻¹ * s ≤ (s / (d + 2 : ℝ))⁻¹ * s := by gcongr
      _ = (d + 2 : ℝ) := by
        field_simp [hs_pos.ne', hden_pos.ne']
  have hterm : (1 + δ⁻¹) * s ≤ (d + 3 : ℝ) := by
    calc
      (1 + δ⁻¹) * s = s + δ⁻¹ * s := by ring
      _ ≤ 1 + (d + 2 : ℝ) := by gcongr
      _ = (d + 3 : ℝ) := by ring
  calc
    (1 + δ⁻¹) ^ M * s ^ (M + 1) = ((1 + δ⁻¹) * s) ^ M * s := by
      rw [pow_succ', mul_pow]
      ring
    _ ≤ (d + 3 : ℝ) ^ M * 1 := by
      gcongr
    _ = (d + 3 : ℝ) ^ M := by ring

private lemma regulator_large_timeGap_bound (M : ℕ) {δ : ℝ}
    (hδ : (1 : ℝ) / (d + 2 : ℝ) ≤ δ) :
    (1 + δ⁻¹) ^ M ≤ (d + 3 : ℝ) ^ M := by
  have hden_pos : (0 : ℝ) < d + 2 := by positivity
  have hlower_pos : 0 < (1 : ℝ) / (d + 2 : ℝ) := div_pos zero_lt_one hden_pos
  have hδ_pos : 0 < δ := lt_of_lt_of_le hlower_pos hδ
  have hinv : δ⁻¹ ≤ ((1 : ℝ) / (d + 2 : ℝ))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hlower_pos hδ
  have hterm : 1 + δ⁻¹ ≤ (d + 3 : ℝ) := by
    calc
      1 + δ⁻¹ ≤ 1 + ((1 : ℝ) / (d + 2 : ℝ))⁻¹ := by gcongr
      _ = (d + 3 : ℝ) := by
        field_simp [hden_pos.ne']
        ring
  exact pow_le_pow_left₀ (by nlinarith [inv_nonneg.mpr hδ_pos.le]) hterm M

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

/-- **Single-block flatness ⇒ the regulated dominator is integrable.**

The Ruelle bound's boundary-distance regulator `(1 + tubeBoundaryDist(wick x)⁻¹)^M`
blows up as consecutive Euclidean times coincide (the codim-1 diagonal
`{x_{k,0} = x_{k-1,0}}`). Earlier analysis (`docs/ruelle_bound_vacuity_concern.md`,
`docs/cluster_ibp_rework_plan.md`) concluded the dominator is not `L¹` and that
dominated convergence is therefore "structurally impossible" — but that overlooks
that the test function `f` is **flat** on exactly that diagonal: `tsupport f ⊆
OrderedPositiveTimeRegion d n`, and the latter is OPEN (strict inequalities
`0 < x_i0 < x_j0`), so `f` vanishes to infinite order on `∂OPTR ⊇ {gap_k = 0}`.

Consequently `(1 + Δ⁻¹)^M · ‖f‖` is integrable after all:
- `tubeBoundaryDist(wick x) ≥ c · min_k gap_k` for the within-block gaps
  `gap_k = x_{k,0} − x_{k-1,0}` (Wick rotation sends Euclidean time to imaginary
  time; the imaginary difference vector is `(gap_k, 0, …, 0)`, whose distance to
  `(openForwardConeSet)ᶜ` is `gap_k / √2`).
- `(1 + Δ⁻¹)^M ≤ 2^M (1 + Σ_k gap_k⁻ᴹ)`, reducing to single-gap terms.
- For each `k`: `f ≡ 0` on `{gap_k ≤ 0}`, so by 1-D Taylor along `gap_k` with all
  derivatives vanishing at `0`,
  `gap_k^{-M} ‖f(x)‖ ≤ (1/M!) · sup_{σ∈[0,gap_k]} ‖∂_{gap_k}^M f(σ, rest)‖`,
  and `∂^M f` is Schwartz, hence the RHS is integrable (uniformly down to and
  across the diagonal, including at infinity, by Schwartz decay in `rest`).

With this dominator integrable, `W_analytic_cluster_integral_via_ruelle` closes by
ordinary `tendsto_integral_filter_of_dominated_convergence` — no IBP, no
distributional restatement, no GNS/Hilbert machinery. -/
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
  classical
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  by_cases hn0 : n = 0
  · subst n
    have hbase :
        MeasureTheory.Integrable
          (fun x : NPointDomain d 0 => (1 + ‖x‖) ^ N * ‖f x‖) :=
      schwartz_integrable_add_pow_mul (f := f) N
    have hconst :
        (fun x : NPointDomain d 0 =>
          C * (1 + ‖(fun k => wickRotatePoint (x k))‖) ^ N
            * (1 + (tubeBoundaryDist (fun k => wickRotatePoint (x k)))⁻¹) ^ M
            * ‖f x‖) =
        fun x : NPointDomain d 0 =>
          (C * (1 + (1 : ℝ)⁻¹) ^ M) * ((1 + ‖x‖) ^ N * ‖f x‖) := by
      funext x
      rw [wickRotate_norm_eq]
      simp [tubeBoundaryDist]
      ring
    rw [hconst]
    exact hbase.const_mul (C * (1 + (1 : ℝ)⁻¹) ^ M)
  · haveI : NeZero n := ⟨hn0⟩
    let D : ℕ := Module.finrank ℝ (NPointDomain d n)
    let P : ℕ := N + D + 2
    let flatC : ℝ :=
      2 ^ (P + P) *
        ((Finset.Iic (P, M + 1)).sup
          (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)) f /
        (Nat.factorial M : ℝ)
    let regC : ℝ := (d + 3 : ℝ) ^ M
    let smallC : ℝ := |C| * flatC * regC
    let largeC : ℝ := |C| * regC
    have hflatC_nonneg : 0 ≤ flatC := by
      positivity
    have hregC_nonneg : 0 ≤ regC := by
      positivity
    have hsmallC_nonneg : 0 ≤ smallC := by
      positivity
    have hlargeC_nonneg : 0 ≤ largeC := by
      positivity
    have hD_lt : (D : ℝ) < (D + 2 : ℕ) := by
      push_cast
      linarith
    have htail_int :
        MeasureTheory.Integrable
          (fun x : NPointDomain d n => (1 + ‖x‖) ^ (-(↑(D + 2) : ℝ)))
          MeasureTheory.volume :=
      integrable_one_add_norm hD_lt
    have hdom_int :
        MeasureTheory.Integrable
          (fun x : NPointDomain d n =>
            smallC * (1 + ‖x‖) ^ (-(↑(D + 2) : ℝ)) +
              largeC * ((1 + ‖x‖) ^ N * ‖f x‖)) := by
      exact (htail_int.const_mul smallC).add
        ((schwartz_integrable_add_pow_mul (f := f) N).const_mul largeC)
    refine hdom_int.mono' ?_ ?_
    · have hcont_wick :
          Continuous (fun x : NPointDomain d n => fun k => wickRotatePoint (x k)) := by
        apply continuous_pi
        intro k
        apply continuous_pi
        intro μ
        by_cases hμ : μ = 0
        · simp [wickRotatePoint, hμ]
          fun_prop
        · simp [wickRotatePoint, hμ]
          fun_prop
      have hcont_wick_norm :
          Continuous (fun x : NPointDomain d n => ‖(fun k => wickRotatePoint (x k))‖) :=
        hcont_wick.norm
      have hcont_tube :
          Continuous (fun x : NPointDomain d n =>
            tubeBoundaryDist (d := d) (fun k => wickRotatePoint (x k))) := by
        exact continuous_tubeBoundaryDist (d := d) |>.comp hcont_wick
      refine (((continuous_const.mul
        ((continuous_const.add hcont_wick_norm).pow N)).measurable.mul ?_).mul
          f.continuous.norm.measurable).aestronglyMeasurable
      exact (hcont_tube.measurable.inv.const_add 1).pow_const M
    · refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx_optr : x ∈ OrderedPositiveTimeRegion d n
      · obtain ⟨kmin, _hk_mem, hkmin⟩ :=
          Finset.exists_min_image (Finset.univ : Finset (Fin n))
            (fun k => ruelleTimeGap (d := d) x k) Finset.univ_nonempty
        let s : ℝ := ruelleTimeGap (d := d) x kmin
        have hs_pos : 0 < s := by
          simpa [s] using ruelleTimeGap_pos_of_mem_orderedPositiveTimeRegion
            (d := d) hx_optr kmin
        have hs_le : ∀ k : Fin n, s ≤ ruelleTimeGap (d := d) x k := by
          intro k
          simpa [s] using hkmin k (Finset.mem_univ k)
        let δ : ℝ := tubeBoundaryDist (d := d) (fun k => wickRotatePoint (x k))
        have hδ_lower : s / (d + 2 : ℝ) ≤ δ := by
          simpa [δ] using tubeBoundaryDist_wick_lower_of_timeGap_le (d := d) x s hs_pos hs_le
        have hδ_pos : 0 < δ := by
          have hden_pos : (0 : ℝ) < d + 2 := by positivity
          exact lt_of_lt_of_le (div_pos hs_pos hden_pos) hδ_lower
        have hwick : ‖(fun k => wickRotatePoint (x k))‖ = ‖x‖ :=
          wickRotate_norm_eq (d := d) x
        have htarget_abs :
            ‖C * (1 + ‖(fun k => wickRotatePoint (x k))‖) ^ N
                * (1 + (tubeBoundaryDist (fun k => wickRotatePoint (x k)))⁻¹) ^ M
                * ‖f x‖‖ =
              |C| * (1 + ‖x‖) ^ N * (1 + δ⁻¹) ^ M * ‖f x‖ := by
          rw [Real.norm_eq_abs]
          simp only [hwick, δ]
          rw [abs_mul, abs_mul, abs_mul]
          have hpoly_nonneg : 0 ≤ (1 + ‖x‖) ^ N := by positivity
          have hreg_nonneg : 0 ≤ (1 + δ⁻¹) ^ M := by
            have hbase : 0 ≤ 1 + δ⁻¹ := by
              nlinarith [inv_nonneg.mpr hδ_pos.le]
            exact pow_nonneg hbase M
          rw [abs_of_nonneg hpoly_nonneg, abs_of_nonneg hreg_nonneg,
            abs_of_nonneg (norm_nonneg (f x))]
        by_cases hs_small : s ≤ 1
        · have hflat :=
            ruelle_timeGap_weighted_flatness_bound_explicit (d := d) f hf P M kmin
              x hs_pos hs_small
          have hflat_div :
              (1 + ‖x‖) ^ N * ‖f x‖ ≤
                flatC * s ^ (M + 1) / (1 + ‖x‖) ^ (D + 2) := by
            have hden_pos : 0 < (1 + ‖x‖) ^ (D + 2) := by positivity
            rw [le_div_iff₀ hden_pos]
            calc
              ((1 + ‖x‖) ^ N * ‖f x‖) * (1 + ‖x‖) ^ (D + 2)
                  = (1 + ‖x‖) ^ P * ‖f x‖ := by
                    simp [P]
                    rw [pow_add]
                    ring
              _ ≤ flatC * s ^ (M + 1) := by
                    simpa [flatC, s] using hflat
          have hreg_small :
              (1 + δ⁻¹) ^ M * s ^ (M + 1) ≤ regC := by
            simpa [regC] using regulator_small_timeGap_bound (d := d) M hs_pos hs_small hδ_lower
          calc
            ‖C * (1 + ‖(fun k => wickRotatePoint (x k))‖) ^ N
                * (1 + (tubeBoundaryDist (fun k => wickRotatePoint (x k)))⁻¹) ^ M
                * ‖f x‖‖
                = |C| * (1 + ‖x‖) ^ N * (1 + δ⁻¹) ^ M * ‖f x‖ :=
                  htarget_abs
            _ = |C| * (1 + δ⁻¹) ^ M * ((1 + ‖x‖) ^ N * ‖f x‖) := by ring
            _ ≤ |C| * (1 + δ⁻¹) ^ M *
                  (flatC * s ^ (M + 1) / (1 + ‖x‖) ^ (D + 2)) := by
                    gcongr
            _ = |C| * flatC *
                  ((1 + δ⁻¹) ^ M * s ^ (M + 1)) /
                  (1 + ‖x‖) ^ (D + 2) := by ring
            _ ≤ |C| * flatC * regC / (1 + ‖x‖) ^ (D + 2) := by
                  gcongr
            _ = smallC * (1 + ‖x‖) ^ (-(↑(D + 2) : ℝ)) := by
                  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
                  field_simp
                  ring
            _ ≤ smallC * (1 + ‖x‖) ^ (-(↑(D + 2) : ℝ)) +
                  largeC * ((1 + ‖x‖) ^ N * ‖f x‖) := by
                    have hlarge_term :
                        0 ≤ largeC * ((1 + ‖x‖) ^ N * ‖f x‖) := by positivity
                    linarith
        · have hs_one_le : (1 : ℝ) ≤ s := le_of_not_ge hs_small
          have hδ_one_lower : (1 : ℝ) / (d + 2 : ℝ) ≤ δ := by
            calc
              (1 : ℝ) / (d + 2 : ℝ) ≤ s / (d + 2 : ℝ) := by
                exact div_le_div_of_nonneg_right hs_one_le (by positivity)
              _ ≤ δ := hδ_lower
          have hreg_large : (1 + δ⁻¹) ^ M ≤ regC := by
            simpa [regC] using regulator_large_timeGap_bound (d := d) M hδ_one_lower
          calc
            ‖C * (1 + ‖(fun k => wickRotatePoint (x k))‖) ^ N
                * (1 + (tubeBoundaryDist (fun k => wickRotatePoint (x k)))⁻¹) ^ M
                * ‖f x‖‖
                = |C| * (1 + ‖x‖) ^ N * (1 + δ⁻¹) ^ M * ‖f x‖ :=
                  htarget_abs
            _ ≤ |C| * (1 + ‖x‖) ^ N * regC * ‖f x‖ := by
                  gcongr
            _ = largeC * ((1 + ‖x‖) ^ N * ‖f x‖) := by
                  simp [largeC]
                  ring
            _ ≤ smallC * (1 + ‖x‖) ^ (-(↑(D + 2) : ℝ)) +
                  largeC * ((1 + ‖x‖) ^ N * ‖f x‖) := by
                    have hsmall_tail :
                        0 ≤ smallC * (1 + ‖x‖) ^ (-(↑(D + 2) : ℝ)) := by
                      positivity
                    linarith
      · have hf_zero : (f : NPointDomain d n → ℂ) x = 0 := by
          have h_notInTsupp :
              x ∉ tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) :=
            fun hxts => hx_optr (hf hxts)
          exact image_eq_zero_of_notMem_tsupport h_notInTsupp
        have hdom_nonneg :
            0 ≤ smallC * (1 + ‖x‖) ^ (-(↑(D + 2) : ℝ)) +
              largeC * ((1 + ‖x‖) ^ N * ‖f x‖) := by
          positivity
        calc
          ‖C * (1 + ‖(fun k => wickRotatePoint (x k))‖) ^ N
              * (1 + (tubeBoundaryDist (fun k => wickRotatePoint (x k)))⁻¹) ^ M
              * ‖f x‖‖ = 0 := by
                simp [hf_zero]
          _ ≤ smallC * (1 + ‖x‖) ^ (-(↑(D + 2) : ℝ)) +
              largeC * ((1 + ‖x‖) ^ N * ‖f x‖) := hdom_nonneg

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
    (hRuelle : RuelleAnalyticClusterHypotheses Wfn n m)
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
    -- Strategy: use a single measure-preserving change of variables
    --   J : NPD n × NPD m → NPD (n+m), J(p) = v_a + Fin.append p.1 p.2
    -- where v_a := Fin.append 0 (fun _ μ => if μ=0 then 0 else a μ)
    -- is the spatial-only shift on the m-block. Then
    --   ∫ x, G(x) = ∫ p, G(J p)  (measure-preservation)
    -- and the integrand at J(p) simplifies to clusterIntegrand a p.
    intro a ha₀ g_a hg_a
    -- The change-of-variables map.
    let v_a : NPointDomain d (n + m) :=
      Fin.append (0 : NPointDomain d n)
        (fun _ μ => if μ = 0 then (0 : ℝ) else a μ)
    let e_append : NPointDomain d n × NPointDomain d m ≃ᵐ NPointDomain d (n + m) :=
      (MeasurableEquiv.finAddProd n m (Fin (d + 1) → ℝ)).symm
    let e_trans : NPointDomain d (n + m) ≃ᵐ NPointDomain d (n + m) :=
      MeasurableEquiv.addLeft v_a
    let J : NPointDomain d n × NPointDomain d m ≃ᵐ NPointDomain d (n + m) :=
      e_append.trans e_trans
    have hJ_mp : MeasureTheory.MeasurePreserving J
        (MeasureTheory.volume.prod MeasureTheory.volume) MeasureTheory.volume := by
      have h_append_mp : MeasureTheory.MeasurePreserving e_append
          (MeasureTheory.volume.prod MeasureTheory.volume) MeasureTheory.volume :=
        (MeasureTheory.volume_preserving_finAddProd n m (Fin (d + 1) → ℝ)).symm
      have h_trans_mp : MeasureTheory.MeasurePreserving e_trans
          MeasureTheory.volume MeasureTheory.volume :=
        MeasureTheory.measurePreserving_add_left MeasureTheory.volume v_a
      exact h_append_mp.trans h_trans_mp
    have hJ_apply : ∀ p : NPointDomain d n × NPointDomain d m,
        J p = v_a + Fin.append p.1 p.2 := by
      intro p
      change v_a + (MeasurableEquiv.finAddProd n m (Fin (d + 1) → ℝ)).symm p =
        v_a + Fin.append p.1 p.2
      congr 1
      exact MeasurableEquiv.finAddProd_symm_apply n m p.1 p.2
    -- Apply measure-preserving change of variables.
    have h_cov : (∫ x : NPointDomain d (n + m),
            F_ext_on_translatedPET_total Wfn
              (fun k => wickRotatePoint (x k)) * (f.tensorProduct g_a) x) =
        ∫ p, F_ext_on_translatedPET_total Wfn
              (fun k => wickRotatePoint (J p k)) *
            (f.tensorProduct g_a) (J p) ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
      (hJ_mp.integral_comp' _).symm
    rw [show (MeasureTheory.volume :
        MeasureTheory.Measure (NPointDomain d n × NPointDomain d m)) =
      MeasureTheory.volume.prod MeasureTheory.volume from rfl]
    rw [h_cov]
    -- Now show the integrand equals clusterIntegrand a p.
    congr 1
    funext p
    rw [hJ_apply]
    -- Identify v_a + Fin.append p.1 p.2 = Fin.append p.1 p'.2 where
    --   p'.2 j μ := p.2 j μ + (if μ=0 then 0 else a μ).
    have h_append_eq :
        v_a + Fin.append p.1 p.2 =
        Fin.append p.1
          (fun j μ => p.2 j μ + (if μ = 0 then (0 : ℝ) else a μ)) := by
      funext k μ
      refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
      · simp [v_a, Fin.append_left]
      · simp [v_a, Fin.append_right, add_comm]
    -- Wick rotation of the joint config: matches inner_config p.
    have h_wick_eq :
        (fun k => wickRotatePoint ((v_a + Fin.append p.1 p.2) k)) =
        Fin.append (fun k => wickRotatePoint (p.1 k))
          (fun k μ => wickRotatePoint (p.2 k) μ +
            (if μ = 0 then (0 : ℂ) else (a μ : ℂ))) := by
      funext k μ
      refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
      · simp [v_a, Fin.append_left]
      · simp [v_a, Fin.append_right]
        by_cases hμ : μ = 0
        · subst hμ
          simp [wickRotatePoint]
        · simp [wickRotatePoint, hμ]
          ring
    -- Tensor product evaluation: f ⊗ g_a applied to the appended config.
    have h_tensor_eq :
        (f.tensorProduct g_a) (v_a + Fin.append p.1 p.2) = f p.1 * g p.2 := by
      rw [h_append_eq, SchwartzMap.tensorProduct_fin_append_apply]
      -- Goal: f p.1 * g_a (fun j μ => p.2 j μ + (if μ=0 then 0 else a μ)) = f p.1 * g p.2
      congr 1
      rw [hg_a]
      congr 1
      funext j μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [ha₀]
      · simp [hμ]
    rw [h_wick_eq, h_tensor_eq]
    unfold clusterIntegrand
    ring
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
    filter_upwards [ae_pairwise_distinct_jointTimeCoords (d := d) (n := n) (m := m)]
      with p h_distinct_joint
    by_cases hp1 : p.1 ∈ OrderedPositiveTimeRegion d n
    · by_cases hp2 : p.2 ∈ OrderedPositiveTimeRegion d m
      · -- Both p.1, p.2 in OPTR: apply ruelle_analytic_cluster_pointwise.
        -- wick(p.1) ∈ ForwardTube d n, wick(p.2) ∈ ForwardTube d m.
        have hw1 : (fun k => wickRotatePoint (p.1 k)) ∈ ForwardTube d n :=
          wick_OPTR_in_forwardTube n p.1 hp1
        have hw2 : (fun k => wickRotatePoint (p.2 k)) ∈ ForwardTube d m :=
          wick_OPTR_in_forwardTube m p.2 hp2
        -- Positivity of times from OPTR.
        have hp1_pos : ∀ i : Fin n, p.1 i 0 > 0 := fun i => (hp1 i).1
        have hp2_pos : ∀ i : Fin m, p.2 i 0 > 0 := fun i => (hp2 i).1
        -- Joint-PET membership eventually-in-`a`: from h_distinct_joint
        -- we get joint PET for all `a` with `a 0 = 0`.
        have h_joint_PET_eventually : ∀ᶠ a : SpacetimeDim d in
            Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
              Bornology.cobounded (SpacetimeDim d),
            (Fin.append (fun k => wickRotatePoint (p.1 k))
                (fun k μ => wickRotatePoint (p.2 k) μ +
                  (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) ∈
              PermutedExtendedTube d (n + m) := by
          refine Filter.eventually_iff_exists_mem.mpr
            ⟨{a : SpacetimeDim d | a 0 = 0}, ?_, ?_⟩
          · exact Filter.mem_inf_of_left (Filter.mem_principal_self _)
          · intro a ha₀
            exact joint_wick_config_in_PET n m p.1 p.2 a ha₀ hp1_pos hp2_pos
              h_distinct_joint
        -- Ruelle pointwise hypothesis gives Tendsto for W_analytic_BHW.
        have h_ruelle_pt :=
          hRuelle.pointwise _ _ hw1 hw2 h_joint_PET_eventually
        unfold clusterIntegrand clusterLimitIntegrand
        -- Bridge: F_ext_on_translatedPET_total = W_analytic_BHW on each config.
        -- Single n-config: wick(p.1) ∈ ForwardTube ⊆ PET.
        have h_single_n :
            F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (p.1 k)) =
            (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (p.1 k)) :=
          F_ext_on_translatedPET_total_eq_on_PET Wfn _
            ((ForwardTube_subset_ComplexExtended d n |>.trans
              (ComplexExtended_subset_Permuted d n)) hw1)
        have h_single_m :
            F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (p.2 k)) =
            (W_analytic_BHW Wfn m).val (fun k => wickRotatePoint (p.2 k)) :=
          F_ext_on_translatedPET_total_eq_on_PET Wfn _
            ((ForwardTube_subset_ComplexExtended d m |>.trans
              (ComplexExtended_subset_Permuted d m)) hw2)
        -- Joint config: distinct positive times → PET.
        have h_joint : ∀ a : SpacetimeDim d, a 0 = 0 →
            F_ext_on_translatedPET_total Wfn
              (Fin.append (fun k => wickRotatePoint (p.1 k))
                (fun k μ => wickRotatePoint (p.2 k) μ +
                  (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) =
            (W_analytic_BHW Wfn (n + m)).val
              (Fin.append (fun k => wickRotatePoint (p.1 k))
                (fun k μ => wickRotatePoint (p.2 k) μ +
                  (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) :=
          fun a ha₀ =>
            joint_F_ext_eq_W_analytic Wfn n m p.1 p.2 a ha₀ hp1_pos hp2_pos
              h_distinct_joint
        -- Transport h_ruelle_pt via congruence on the filter:
        -- on the AE set {a 0 = 0} ⊓ cobounded (in fact on ALL of {a 0 = 0}),
        -- F_ext_total(joint) = W_analytic_BHW(joint).
        have h_filter_eq : ∀ᶠ a in
            Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
              Bornology.cobounded (SpacetimeDim d),
            (W_analytic_BHW Wfn (n + m)).val
              (Fin.append (fun k => wickRotatePoint (p.1 k))
                (fun k μ => wickRotatePoint (p.2 k) μ +
                  (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) =
            F_ext_on_translatedPET_total Wfn
              (Fin.append (fun k => wickRotatePoint (p.1 k))
                (fun k μ => wickRotatePoint (p.2 k) μ +
                  (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) := by
          have h_in_principal : {a : SpacetimeDim d | a 0 = 0} ∈
              Filter.principal {a : SpacetimeDim d | a 0 = 0} :=
            Filter.mem_principal_self _
          have h_in_inf : {a : SpacetimeDim d | a 0 = 0} ∈
              Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
                Bornology.cobounded (SpacetimeDim d) :=
            Filter.mem_inf_of_left h_in_principal
          exact Filter.eventually_iff_exists_mem.mpr
            ⟨_, h_in_inf, fun a ha => (h_joint a ha).symm⟩
        -- Transport: replace W_analytic with F_ext via congruence.
        rw [h_single_n, h_single_m]
        refine ((h_ruelle_pt.congr' h_filter_eq).mul_const (f p.1)).mul_const (g p.2)
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
  -- Step 4–7: dominator + dominated convergence + ε-R conversion.
  --
  -- BLOCKED ON RACH.bound REFACTOR (2026-05-08): the bound shape was
  -- updated to include the Streater-Wightman boundary-distance
  -- regulator `(1 + (tubeBoundaryDist z)⁻¹)^M` after the previous
  -- shape was found unsatisfiable for any Wightman QFT (free-field
  -- counterexample via Wick decomposition; see
  -- `docs/ruelle_bound_vacuity_concern.md`).
  --
  -- The previous dominator `C_R · (1+‖p₁‖+‖p₂‖)^N_R · ‖f(p₁)‖ · ‖g(p₂)‖`
  -- is no longer typed correctly: the new bound delivers the regulator
  -- factor `(1 + (tubeBoundaryDist (wick p))⁻¹)^M_R` as well.
  --
  -- ### Fillability case for this `sorry`
  --
  -- The math is classical (Streater-Wightman §3.4 / Ruelle 1962 /
  -- Araki-Hepp-Ruelle 1962): use the **Schwartz dual pairing**
  -- instead of a pointwise dominator.
  --
  --   1. By `fl_representation_from_bv` (existing project axiom in
  --      `OSReconstruction/SCV/VladimirovTillmann.lean`):
  --        `W_analytic_BHW(z) = (FL Tflat)(z)`
  --      for some tempered distribution `Tflat` on the dual cone
  --      (where `Tflat : SchwartzMap → ℂ` is a `ContinuousLinearMap`).
  --   2. The cluster integrand
  --        `W_analytic_BHW(joint(wick p₁, wick p₂ + (0,a))) · f(p₁) · g(p₂)`
  --      integrates over `(p₁, p₂)` to
  --        `Tflat(ψ_a)`
  --      where `ψ_a ∈ Schwartz(dual)` is constructed by Fubini-pairing
  --      `(f ⊗ g_a)` with the Wick-rotated kernel.
  --   3. Continuity of `Tflat` on Schwartz:
  --        `‖Tflat ψ‖ ≤ ‖Tflat‖ · ‖ψ‖_{seminorm}`.
  --   4. `‖ψ_a‖_{seminorm}` is uniformly bounded in `a` by translation-
  --      invariance of Schwartz seminorms (`g_a(x) := g(x - a)`).
  --   5. → uniform `ε`-R conclusion, no pointwise dominator needed.
  --
  -- ### Available Lean infrastructure
  --
  -- * `bv_implies_fourier_support` (axiom, VladimirovTillmann.lean:148)
  --   — produces `Tflat` from polynomial-bounded boundary value.
  -- * `fl_representation_from_bv` (axiom, same file:392)
  --   — gives `W = FL extension of Tflat`.
  -- * `fourierLaplaceExtMultiDim_vladimirov_growth` (PROVED in
  --   PaleyWienerSchwartz.lean:3286) — the regulated growth bound.
  -- * Mathlib has Schwartz-Fubini and Schwartz-CLM continuity in the
  --   standard form needed for steps (2)–(4).
  --
  -- ### Identified gap
  --
  -- `bv_implies_fourier_support`'s **hypothesis** asks for the
  -- *unregulated* polynomial growth on the tube — the same shape just
  -- shown unsatisfiable. The companion theorem
  -- `full_analytic_continuation_with_symmetry_growth`
  -- (`OSToWightman.lean:2553`) is supposed to supply this growth for
  -- OS-derived Wightman functions, but `#print axioms` shows it
  -- depends on `sorryAx` — i.e., it is not actually proved either.
  -- So the polynomial-bound chain has hidden vacuity.
  --
  -- The IBP rework therefore likely also requires either:
  --   (a) supplying the unregulated bound on a regularized subdomain
  --       where it actually holds, or
  --   (b) relaxing `bv_implies_fourier_support`'s hypothesis to accept
  --       the regulated form (which IS satisfiable). Vladimirov's
  --       Theorem 25.1 only requires tempered BV; the unregulated
  --       polynomial bound was over-strong.
  --
  -- Option (b) is the cleaner fix. The regulated bound is available
  -- as the conditional structure `L4SpectralData` (see
  -- `OSReconstruction/Wightman/Spectral/Ruelle/L4_UniformPolynomialBound.lean`)
  -- and the conditional reduction `ruelle_analytic_cluster_bound_of`
  -- there. There is intentionally NO production axiom discharging
  -- `L4SpectralData` (a draft `wightman_l4_spectral_data_axiom` was
  -- withdrawn 2026-05-09 per PR-#86 review: no QFT-specific production
  -- axioms). The IBP rework therefore takes either an explicit
  -- `L4SpectralData Wfn n m` parameter at this site, or a future
  -- proved theorem discharging it via the SCV / FL infrastructure
  -- (`bv_implies_fourier_support` + `fl_representation_from_bv` +
  -- `fourierLaplaceExtMultiDim_vladimirov_growth`).
  --
  -- ### Estimate
  --
  -- 1–2 weeks if option (b) works as expected; 2–4 weeks if a
  -- separate audit/fix of the polynomial-bound chain is needed first.
  -- Tracked as a separate follow-up; this PR is the structure-only
  -- refactor of `RACH.bound`.
  sorry

/-! ### Public-facing theorems

The OS-side cluster theorem and its `wickRotatedBoundaryPairing` wrapper.
Originally stated as sorry-stubs in `SchwingerAxioms.lean`; they live here
because the proof goes through `W_analytic_cluster_integral_via_ruelle`,
which depends on infrastructure (forward-tube measure-preservation,
joint config bridge) only available in this file. -/

/-- **Cluster theorem for the Wick-rotated boundary integral**
(Ruelle 1962 / Araki-Hepp-Ruelle 1962, also Glimm-Jaffe Ch 19,
Streater-Wightman §3.4).

For OPTR-supported `f, g`, the (n+m)-point Wick-rotated integral against
`f ⊗ g_a` (with `g_a` the spatial translate of `g` by `a`) clusters to
the product of single-block integrals as `‖a⃗‖ → ∞`.

This is the **analytic-cluster ingredient** for OS axiom E4 on the
Wick-rotated boundary side: the (n+m)-integral form for `f ⊗ g_a` with
both factors OPTR-supported.

**Scope vs. the public E4 surface.** The full
`OsterwalderSchraderAxioms.E4_cluster` field
(`SchwingerOS.lean`) is stated for arbitrary
`ZeroDiagonalSchwartz` tests and an explicit joint-test witness
`fg_a : ZeroDiagonalSchwartz d (n+m)`. The OPTR-restricted
specialization that matches `E4_cluster`'s shape exactly (modulo
OPTR support hypotheses) is `schwinger_E4_cluster_OPTR_case` below.
Discharging the *full* `E4_cluster` field additionally requires a
reduction from arbitrary `ZeroDiagonalSchwartz` tests to the
OPTR-supported subset (e.g., density of OPTR-supported in
`ZeroDiagonalSchwartz` plus continuity of the Schwinger functional);
that extension is left for follow-up. -/
theorem W_analytic_cluster_integral (Wfn : WightmanFunctions d) (n m : ℕ)
    (hRuelle : RuelleAnalyticClusterHypotheses Wfn n m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hsupp_f : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hsupp_g : tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
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
                (fun k => wickRotatePoint (x k)) * g x)‖ < ε :=
  W_analytic_cluster_integral_via_ruelle Wfn n m hRuelle f g hsupp_f hsupp_g ε hε

/-- Cluster of the Wick-rotated boundary pairing for OPTR-supported test
functions (the `wickRotatedBoundaryPairing` form of
`W_analytic_cluster_integral`).

Same scope caveat as `W_analytic_cluster_integral`: this is the
analytic-cluster ingredient for E4, not the full
`OsterwalderSchraderAxioms.E4_cluster` field — see that theorem's
docstring for the bridging work needed. -/
theorem wickRotatedBoundaryPairing_cluster (Wfn : WightmanFunctions d)
    (n m : ℕ) (hRuelle : RuelleAnalyticClusterHypotheses Wfn n m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hsupp_f : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hsupp_g : tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        ∀ (g_a : SchwartzNPoint d m),
          (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
          ‖wickRotatedBoundaryPairing Wfn (n + m) (f.tensorProduct g_a) -
            wickRotatedBoundaryPairing Wfn n f *
            wickRotatedBoundaryPairing Wfn m g‖ < ε := by
  simp only [wickRotatedBoundaryPairing]
  exact W_analytic_cluster_integral Wfn n m hRuelle f g hsupp_f hsupp_g ε hε

/-! ### Bridge to the public `OsterwalderSchraderAxioms.E4_cluster` surface

The cluster theorems above are stated for OPTR-supported `SchwartzNPoint`
inputs. The public `E4_cluster` field on `OsterwalderSchraderAxioms`
(`SchwingerOS.lean:792`) is a stronger surface: arbitrary
`ZeroDiagonalSchwartz` tests + an explicit joint-test witness
`fg_a : ZeroDiagonalSchwartz d (n+m)` related to `f, g_a` via
`splitFirst / splitLast`.

The theorem `schwinger_E4_cluster_OPTR_case` below provides the
OPTR-restricted *specialization* of `E4_cluster` for the Schwinger
functions constructed from a `WightmanFunctions` package
(`constructSchwingerFunctions`). It matches the shape of
`E4_cluster` exactly, modulo the additional OPTR support hypotheses on
`f, g`. Discharging the *full* `E4_cluster` field requires a separate
bridge from arbitrary `ZeroDiagonalSchwartz` tests to OPTR-supported
ones (e.g., density of OPTR in `ZeroDiagonalSchwartz` plus continuity
of the Schwinger functional). That extension is left for follow-up. -/

/-- **Schwinger E4 cluster for OPTR-supported tests** —
matches the shape of `OsterwalderSchraderAxioms.E4_cluster`
(`SchwingerOS.lean:792`) for the Schwinger functions constructed from a
`WightmanFunctions` package, restricted to OPTR-supported `f, g`.

The output is the same factorization conclusion that `E4_cluster`
demands: `∃ R > 0, ∀ a (spatial, |a⃗| > R), ∀ g_a (translate of g),
∀ fg_a (joint witness), ‖S(n+m) fg_a - S n f · S m g‖ < ε`.

The bridge:
1. Apply `wickRotatedBoundaryPairing_cluster` to `f.1, g.1` (using the
   OPTR support hypotheses).
2. Use `tensorProduct_apply` plus the `fg_a` witness identity
   `fg_a.1 x = f.1 (splitFirst x) * g_a.1 (splitLast x)` to identify
   `fg_a.1 = f.1.tensorProduct g_a.1` as `SchwartzNPoint` via
   `SchwartzMap.ext`.
3. Unfold `constructSchwingerFunctions` to `wickRotatedBoundaryPairing`. -/
theorem schwinger_E4_cluster_OPTR_case
    (Wfn : WightmanFunctions d) (n m : ℕ)
    (hRuelle : RuelleAnalyticClusterHypotheses Wfn n m)
    (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m)
    (hsupp_f : tsupport ((f.1 : SchwartzNPoint d n) :
      NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hsupp_g : tsupport ((g.1 : SchwartzNPoint d m) :
      NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (ε : ℝ) (hε : ε > 0) :
    ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 →
        (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        ∀ (g_a : ZeroDiagonalSchwartz d m),
          (∀ x : NPointDomain d m, g_a.1 x = g.1 (fun i => x i - a)) →
          ∀ (fg_a : ZeroDiagonalSchwartz d (n + m)),
            (∀ x : NPointDomain d (n + m),
              fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)) →
            ‖constructSchwingerFunctions Wfn (n + m) fg_a -
              constructSchwingerFunctions Wfn n f *
              constructSchwingerFunctions Wfn m g‖ < ε := by
  obtain ⟨R, hR, hcluster⟩ :=
    wickRotatedBoundaryPairing_cluster Wfn n m hRuelle f.1 g.1 hsupp_f hsupp_g ε hε
  refine ⟨R, hR, ?_⟩
  intro a ha₀ ha_large g_a hg_a fg_a hfg_a
  -- Apply the cluster theorem at the SchwartzNPoint level using g_a.1.
  have hcl := hcluster a ha₀ ha_large g_a.1 hg_a
  -- Identify fg_a.1 with f.1.tensorProduct g_a.1 via the witness identity
  -- and tensorProduct_apply.
  have h_fg_eq : (fg_a.1 : SchwartzNPoint d (n + m)) = f.1.tensorProduct g_a.1 := by
    apply SchwartzMap.ext
    intro x
    rw [hfg_a, SchwartzMap.tensorProduct_apply]
  -- Unfold constructSchwingerFunctions and rewrite using h_fg_eq.
  show ‖wickRotatedBoundaryPairing Wfn (n + m) fg_a.1 -
      wickRotatedBoundaryPairing Wfn n f.1 *
      wickRotatedBoundaryPairing Wfn m g.1‖ < ε
  rw [h_fg_eq]
  exact hcl

end OSReconstruction
