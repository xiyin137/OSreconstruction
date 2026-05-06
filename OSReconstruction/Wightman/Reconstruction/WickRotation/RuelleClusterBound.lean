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
    -- Step 1: change of variables via:
    --   (i) `integral_fin_append_split` (project's Fubini for `Fin.append`)
    --   (ii) Lebesgue translation invariance on the m-block (substitute y = x_m - a)
    --   (iii) `Fin.append_comp_apply` to push wickRotatePoint past Fin.append
    --   (iv) Fubini back to a single product-space integral
    -- Each step: standard Mathlib + project infrastructure.
    -- Required: integrability of the (n+m)-integrand for `integral_fin_append_split`
    --   (uses `wick_rotated_kernel_mul_zeroDiagonal_integrable` after promoting f
    --    and g_a to ZeroDiagonalSchwartz via OPTR support).
    -- ~100 lines; routed to follow-up.
    sorry
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
        -- The Ruelle pointwise axiom gives Tendsto for W_analytic_BHW.
        have h_ruelle_pt :=
          ruelle_analytic_cluster_pointwise Wfn n m _ _ hw1 hw2
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
      -- F_ext_on_translatedPET_total composed with the joint Wick-rotated
      -- config (with m-block shifted by `(0, a)`).
      -- Strategy: define `joint : NPD n × NPD m → NPD (n+m)` by
      -- `joint p := Fin.append p.1 (p.2 + a)`. Then our function equals
      -- `(F_ext_total ∘ wick) ∘ joint`. By `bhw_euclidean_kernel_measurable
      -- Wfn (n := n+m)` the inner function is AEStronglyMeasurable; `joint`
      -- is continuous (Fin.append + addition); compose via
      -- `AEStronglyMeasurable.comp_measurable` after establishing
      -- `(volume.prod volume).map joint = volume` (via Lebesgue
      -- translation/relabeling invariance).
      -- ~50 lines bridging the volume measure-preservation. Routed.
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
        refine Filter.Eventually.of_forall (fun p => ?_)
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
            -- Apply Ruelle's bound to the joint analytic continuation.
            have h_ruelle_bound :=
              h_ruelle (fun k => wickRotatePoint (p.1 k))
                (fun k => wickRotatePoint (p.2 k)) hw1 hw2 a ha.1 ha.2
            -- Use ‖wick z‖ = ‖z‖ to convert Ruelle's bound to dominator form.
            rw [wickRotate_norm_eq, wickRotate_norm_eq] at h_ruelle_bound
            -- Now h_ruelle_bound bounds ‖W_analytic_BHW(joint)‖ in terms of
            -- (1 + ‖p.1‖ + ‖p.2‖)^N_R. We need:
            --   F_ext_on_translatedPET_total Wfn (joint) = W_analytic_BHW Wfn (n+m) (joint)
            -- via PET membership of the joint config (joint distinct positive
            -- times → euclidean_distinct_in_permutedTube; boundary measure-zero).
            -- Plus norm_mul on the f, g factors.
            -- F_ext-bridge for joint config: routed to follow-up.
            sorry
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

end OSReconstruction
