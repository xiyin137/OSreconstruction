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
  /-- Uniform-in-`a` polynomial bound (Ruelle 1962 / Streater-Wightman §3.4).

  There exist constants `C > 0, N, R > 0` such that for forward-tube
  `z₁, z₂` and spatial `a` with `|⃗a| > R`, *if* the appended config
  lies in the joint analytic domain (PET), the bound holds with
  `C, N` independent of `a`. -/
  bound : ∃ (C : ℝ) (N : ℕ) (R : ℝ),
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
  -- Step 4 (dominator): construct a uniform-in-a integrable dominator on
  -- (NPointDomain d n × NPointDomain d m), valid for `|⃗a|` large enough.
  obtain ⟨C_R, N_R, R_R, hC_R_pos, hR_R_pos, h_ruelle⟩ :=
    hRuelle.bound
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
      -- F_ext_on_translatedPET_total composed with the joint Wick-rotated
      -- config. Decompose:
      --   joint p k μ = (T_v ∘ finAddProd.symm) p k μ
      -- where T_v(x) := v + x with v := Fin.append 0 (fun _ μ => if μ=0 then 0 else a μ),
      -- and finAddProd.symm (p₁, p₂) = Fin.append p₁ p₂.
      -- Both T_v and finAddProd.symm are measure-preserving.
      -- The kernel `F_ext_total ∘ wick` is AEStronglyMeasurable on
      -- volume of NPD (n+m) by `bhw_euclidean_kernel_measurable`.
      -- Compose via `AEStronglyMeasurable.comp_measurePreserving`.
      let v_a : NPointDomain d (n + m) :=
        Fin.append (0 : NPointDomain d n)
          (fun _ μ => if μ = 0 then (0 : ℝ) else a μ)
      have hT_mp : MeasureTheory.MeasurePreserving
          (fun x : NPointDomain d (n + m) => v_a + x)
          MeasureTheory.volume MeasureTheory.volume :=
        MeasureTheory.measurePreserving_add_left MeasureTheory.volume v_a
      have hJ₀_mp : MeasureTheory.MeasurePreserving
          (fun p : NPointDomain d n × NPointDomain d m =>
            Fin.append p.1 p.2)
          (MeasureTheory.volume.prod MeasureTheory.volume) MeasureTheory.volume := by
        have h_eq : (fun p : NPointDomain d n × NPointDomain d m =>
            Fin.append p.1 p.2) =
            ((MeasurableEquiv.finAddProd n m (Fin (d + 1) → ℝ)).symm :
              NPointDomain d n × NPointDomain d m → NPointDomain d (n + m)) := by
          funext p
          rw [MeasurableEquiv.finAddProd_symm_apply]
        rw [h_eq]
        exact (MeasureTheory.volume_preserving_finAddProd n m
          (Fin (d + 1) → ℝ)).symm
      have hJ_mp : MeasureTheory.MeasurePreserving
          (fun p : NPointDomain d n × NPointDomain d m =>
            v_a + Fin.append p.1 p.2)
          (MeasureTheory.volume.prod MeasureTheory.volume) MeasureTheory.volume :=
        hT_mp.comp hJ₀_mp
      have h_kernel : MeasureTheory.AEStronglyMeasurable
          (fun x : NPointDomain d (n + m) =>
            F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (x k)))
          MeasureTheory.volume :=
        bhw_euclidean_kernel_measurable Wfn
      have h_composed : MeasureTheory.AEStronglyMeasurable
          (fun p : NPointDomain d n × NPointDomain d m =>
            F_ext_on_translatedPET_total Wfn
              (fun k => wickRotatePoint ((v_a + Fin.append p.1 p.2) k)))
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        h_kernel.comp_measurePreserving hJ_mp
      -- Show the target function equals h_composed's argument.
      have h_eq :
          (fun p : NPointDomain d n × NPointDomain d m =>
            F_ext_on_translatedPET_total Wfn
              (Fin.append (fun k => wickRotatePoint (p.1 k))
                (fun k μ => wickRotatePoint (p.2 k) μ +
                  (if μ = 0 then (0 : ℂ) else (a μ : ℂ))))) =
          (fun p : NPointDomain d n × NPointDomain d m =>
            F_ext_on_translatedPET_total Wfn
              (fun k => wickRotatePoint ((v_a + Fin.append p.1 p.2) k))) := by
        funext p
        congr 1
        funext k
        refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
        · -- n-block: v_a is 0 here, append gives p.1 i'
          simp [v_a, Fin.append_left]
        · -- m-block: v_a adds spatial shift, append gives p.2 j'
          funext μ
          simp [v_a, Fin.append_right]
          by_cases hμ : μ = 0
          · subst hμ
            simp [wickRotatePoint]
          · simp [wickRotatePoint, hμ]
            ring
      rw [show (MeasureTheory.volume :
          MeasureTheory.Measure (NPointDomain d n × NPointDomain d m)) =
        MeasureTheory.volume.prod MeasureTheory.volume from rfl, h_eq]
      exact h_composed
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
        · intro a ⟨ha₀, hball⟩
          refine ⟨ha₀, ?_⟩
          -- ‖a‖ > R_R (sup-norm) and a 0 = 0 → ∑ (a (succ i))² > R_R².
          have h_norm : ‖a‖ > R_R := by
            simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hball
          -- Pi sup-norm: ∃ i with ‖a i‖ > R_R. For a 0 = 0, i ≠ 0, so i = succ j.
          have h_exists : ∃ i : Fin (d + 1), R_R < ‖a i‖ := by
            by_contra h_neg
            push_neg at h_neg
            haveI : Nonempty (Fin (d + 1)) := ⟨0⟩
            have h_le : ‖a‖ ≤ R_R := (pi_norm_le_iff_of_nonempty _).mpr h_neg
            linarith
          obtain ⟨i, hi⟩ := h_exists
          -- i ≠ 0: since |a 0| = 0 < R_R < ‖a i‖.
          have hi_ne_zero : i ≠ 0 := by
            intro hi₀
            rw [hi₀, ha₀] at hi
            simp at hi
            linarith [hR_R_pos]
          -- i = Fin.succ j for some j.
          obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hi_ne_zero
          -- |a (succ j)| > R_R, so (a (succ j))² > R_R².
          rw [← hj] at hi
          have h_sq : (a (Fin.succ j))^2 > R_R^2 := by
            have h_abs : R_R < |a (Fin.succ j)| := hi
            have h_R_nonneg : (0 : ℝ) ≤ R_R := le_of_lt hR_R_pos
            calc R_R^2 < (|a (Fin.succ j)|)^2 :=
                  pow_lt_pow_left₀ h_abs h_R_nonneg two_ne_zero
              _ = (a (Fin.succ j))^2 := sq_abs _
          -- Sum over Fin d: ∑ ≥ (a (succ j))² > R_R².
          calc R_R^2 < (a (Fin.succ j))^2 := h_sq
            _ ≤ ∑ i : Fin d, (a (Fin.succ i))^2 := by
                exact Finset.single_le_sum (f := fun i => (a (Fin.succ i))^2)
                  (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      · intro a ha
        filter_upwards [ae_pairwise_distinct_jointTimeCoords (d := d) (n := n) (m := m)]
          with p h_distinct_joint
        -- ha : a 0 = 0 ∧ ∑ (a (succ i))² > R_R².
        -- We bound `‖clusterIntegrand a p‖` by the dominator.
        unfold clusterIntegrand
        -- Three-way case split on whether p.1 ∈ OPTR-n and p.2 ∈ OPTR-m.
        by_cases hp1 : p.1 ∈ OrderedPositiveTimeRegion d n
        · by_cases hp2 : p.2 ∈ OrderedPositiveTimeRegion d m
          · -- Both in OPTR: apply Ruelle's bound.
            have hw1 : (fun k => wickRotatePoint (p.1 k)) ∈ ForwardTube d n :=
              wick_OPTR_in_forwardTube n p.1 hp1
            have hw2 : (fun k => wickRotatePoint (p.2 k)) ∈ ForwardTube d m :=
              wick_OPTR_in_forwardTube m p.2 hp2
            have hp1_pos : ∀ i : Fin n, p.1 i 0 > 0 := fun i => (hp1 i).1
            have hp2_pos : ∀ i : Fin m, p.2 i 0 > 0 := fun i => (hp2 i).1
            -- Joint PET membership: the joint Wick-rotated config (with
            -- spatial m-block shift) lies in PET when joint times are
            -- distinct (established by h_distinct_joint via AE).
            have h_joint_PET :
                (Fin.append (fun k => wickRotatePoint (p.1 k))
                  (fun k μ => wickRotatePoint (p.2 k) μ +
                    (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) ∈
                  PermutedExtendedTube d (n + m) :=
              joint_wick_config_in_PET n m p.1 p.2 a ha.1 hp1_pos hp2_pos
                h_distinct_joint
            -- Apply Ruelle's bound to the joint analytic continuation.
            have h_ruelle_bound :=
              h_ruelle (fun k => wickRotatePoint (p.1 k))
                (fun k => wickRotatePoint (p.2 k)) hw1 hw2 a ha.1 ha.2 h_joint_PET
            -- Use ‖wick z‖ = ‖z‖ to convert Ruelle's bound to dominator form.
            rw [wickRotate_norm_eq, wickRotate_norm_eq] at h_ruelle_bound
            -- Bridge F_ext_on_translatedPET_total ↔ W_analytic_BHW on the joint
            -- config via joint_F_ext_eq_W_analytic (uses h_distinct_joint).
            have h_bridge :
                F_ext_on_translatedPET_total Wfn
                  (Fin.append (fun k => wickRotatePoint (p.1 k))
                    (fun k μ => wickRotatePoint (p.2 k) μ +
                      (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) =
                (W_analytic_BHW Wfn (n + m)).val
                  (Fin.append (fun k => wickRotatePoint (p.1 k))
                    (fun k μ => wickRotatePoint (p.2 k) μ +
                      (if μ = 0 then (0 : ℂ) else (a μ : ℂ)))) :=
              joint_F_ext_eq_W_analytic Wfn n m p.1 p.2 a ha.1 hp1_pos hp2_pos
                h_distinct_joint
            -- Bound ‖F_ext_total ... * f p.1 * g p.2‖.
            rw [h_bridge]
            -- Goal: ‖W_analytic_BHW(joint) * f(p.1) * g(p.2)‖ ≤ dominator
            -- Use norm_mul to split, then h_ruelle_bound on the W_analytic factor.
            rw [norm_mul, norm_mul]
            -- Goal: ‖W_analytic(joint)‖ * ‖f(p.1)‖ * ‖g(p.2)‖ ≤
            --       C_R * (1 + ‖p.1‖ + ‖p.2‖)^N_R * ‖f(p.1)‖ * ‖g(p.2)‖
            have h_fg_nonneg : (0 : ℝ) ≤ ‖f p.1‖ * ‖g p.2‖ := by positivity
            have h_factor_nonneg : (0 : ℝ) ≤ ‖f p.1‖ := norm_nonneg _
            have h_g_nonneg : (0 : ℝ) ≤ ‖g p.2‖ := norm_nonneg _
            calc ‖(W_analytic_BHW Wfn (n + m)).val
                    (Fin.append (fun k => wickRotatePoint (p.1 k))
                      (fun k μ => wickRotatePoint (p.2 k) μ +
                        (if μ = 0 then (0 : ℂ) else (a μ : ℂ))))‖
                  * ‖f p.1‖ * ‖g p.2‖
                ≤ (C_R * (1 + ‖p.1‖ + ‖p.2‖) ^ N_R) * ‖f p.1‖ * ‖g p.2‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right h_ruelle_bound h_factor_nonneg)
                    h_g_nonneg
              _ = C_R * (1 + ‖p.1‖ + ‖p.2‖) ^ N_R * ‖f p.1‖ * ‖g p.2‖ := by ring
          · -- p.2 ∉ OPTR-m: g(p.2) = 0, integrand = 0, bound trivial.
            have h_g_zero : (g : NPointDomain d m → ℂ) p.2 = 0 :=
              image_eq_zero_of_notMem_tsupport (fun hxts => hp2 (hsupp_g hxts))
            simp [h_g_zero]
        · -- p.1 ∉ OPTR-n: similar.
          have h_f_zero : (f : NPointDomain d n → ℂ) p.1 = 0 :=
            image_eq_zero_of_notMem_tsupport (fun hxts => hp1 (hsupp_f hxts))
          simp [h_f_zero]
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
  -- Step 7: convert Tendsto to ∃ R bound form.
  -- (1) From h_joint_tendsto + ε > 0: ∀ᶠ a in filter, ‖F a - L_n L_m‖ < ε.
  have h_event : ∀ᶠ a : SpacetimeDim d in
      Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
        Bornology.cobounded (SpacetimeDim d),
      ‖(∫ p : NPointDomain d n × NPointDomain d m, clusterIntegrand Wfn f g a p) -
        L_n * L_m‖ < ε := by
    have h_metric : Filter.Tendsto
        (fun a : SpacetimeDim d =>
          (∫ p : NPointDomain d n × NPointDomain d m, clusterIntegrand Wfn f g a p) -
          L_n * L_m)
        (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
          Bornology.cobounded (SpacetimeDim d))
        (nhds 0) := by
      simpa using h_joint_tendsto.sub_const (L_n * L_m)
    rw [Metric.tendsto_nhds] at h_metric
    have := h_metric ε hε
    simpa [dist_zero_right] using this
  -- (2) Decompose: get R₀ such that {a 0 = 0} ∩ (closedBall 0 R₀)ᶜ ⊆ S_ε.
  rw [Filter.eventually_iff_exists_mem] at h_event
  obtain ⟨S, hS_mem, hS_bound⟩ := h_event
  rw [Filter.mem_inf_iff_superset] at hS_mem
  obtain ⟨T₁, hT₁_mem, T₂, hT₂_mem, hT_sub⟩ := hS_mem
  rw [Filter.mem_principal] at hT₁_mem
  obtain ⟨R₀, _, hR₀_sub⟩ :=
    (Metric.hasBasis_cobounded_compl_closedBall (0 : SpacetimeDim d)).mem_iff.mp hT₂_mem
  -- (3) Choose R := max R₀ 1 · (d + 1), ensuring R > 0 and the spatial-sum-squared
  --     condition implies ‖a‖_sup > R₀.
  set R₁ : ℝ := max R₀ 1 with hR₁_def
  have hR₁_pos : 0 < R₁ := lt_max_of_lt_right one_pos
  refine ⟨R₁ * (d + 1), by positivity, fun a ha₀ ha_large g_a hg_a => ?_⟩
  -- (4) Show `a ∈ T₁ ∩ T₂` to invoke hS_bound.
  have ha_in_T₁ : a ∈ T₁ := hT₁_mem ha₀
  have ha_in_T₂ : a ∈ T₂ := by
    apply hR₀_sub
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
    -- Spatial bound: ∑ (a (succ i))² ≤ d · ‖a‖² (sum of d terms each ≤ ‖a‖²).
    have h_each : ∀ i : Fin d, (a (Fin.succ i))^2 ≤ ‖a‖^2 := fun i => by
      calc (a (Fin.succ i))^2 = (|a (Fin.succ i)|)^2 := (sq_abs _).symm
        _ ≤ ‖a‖^2 := pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm a _) 2
    have h_sum_le : (∑ i : Fin d, (a (Fin.succ i))^2) ≤ (d : ℝ) * ‖a‖^2 := by
      calc ∑ i : Fin d, (a (Fin.succ i))^2 ≤ ∑ _i : Fin d, ‖a‖^2 :=
            Finset.sum_le_sum (fun i _ => h_each i)
        _ = (d : ℝ) * ‖a‖^2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    -- Combine with ha_large: d · ‖a‖² ≥ ∑ > (R₁ (d+1))² ≥ R₁² · d.
    have h_d_pos : (0 : ℝ) < d := by
      have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
      exact_mod_cast this
    have h_R₁_nonneg : (0 : ℝ) ≤ R₁ := le_of_lt hR₁_pos
    have h_norm_nonneg : (0 : ℝ) ≤ ‖a‖ := norm_nonneg _
    have h_R₀_le_R₁ : R₀ ≤ R₁ := le_max_left R₀ 1
    -- Key: d · ‖a‖² > (R₁ (d+1))² ≥ d · R₁² (using (d+1)² ≥ d).
    have h_norm_sq : R₁^2 < ‖a‖^2 := by
      have h1 : (R₁ * ((d : ℝ) + 1))^2 < (d : ℝ) * ‖a‖^2 := by
        have h_sum_gt : (R₁ * ((d : ℝ) + 1))^2 <
            ∑ i : Fin d, (a (Fin.succ i))^2 := ha_large
        linarith [h_sum_gt, h_sum_le]
      -- (R₁ (d+1))² ≥ R₁² · d (using (d+1)² ≥ d).
      have h_R₁_sq_le : (d : ℝ) * R₁^2 ≤ (R₁ * ((d : ℝ) + 1))^2 := by
        nlinarith [sq_nonneg R₁, sq_nonneg (((d : ℝ) + 1)), h_d_pos]
      -- Combine: d · R₁² < d · ‖a‖², divide by d.
      have h2 : (d : ℝ) * R₁^2 < (d : ℝ) * ‖a‖^2 :=
        lt_of_le_of_lt h_R₁_sq_le h1
      exact lt_of_mul_lt_mul_left h2 h_d_pos.le
    -- ‖a‖² > R₁² → ‖a‖ > R₁ (both nonneg).
    have h_norm_gt_R₁ : R₁ < ‖a‖ := by
      nlinarith [h_norm_sq, h_R₁_nonneg, h_norm_nonneg]
    linarith
  -- Bound the cluster integral via hS_bound.
  have h_in_S : a ∈ S := hT_sub ⟨ha_in_T₁, ha_in_T₂⟩
  have h_cluster_bound : ‖(∫ p : NPointDomain d n × NPointDomain d m,
      clusterIntegrand Wfn f g a p) - L_n * L_m‖ < ε := hS_bound a h_in_S
  -- Convert via h_change_of_var: joint integral = cluster integrand integral.
  rw [h_change_of_var a ha₀ g_a hg_a]
  exact h_cluster_bound

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
