/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.WickRotationBridge
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup

/-!
# OS to Wightman Analytic Continuation Core

This file contains Phase 3 of the `E'→R'` reconstruction chain:

- the base-step analytic continuation on the first tube domain
- the slice geometry and interleaved bookkeeping around `schwinger_continuation_base_step`
- the inductive restriction from `ACR(1)` to the forward tube

The semigroup, Hilbert-space, and one-variable holomorphic bridge infrastructure
now lives in `OSToWightmanSemigroup.lean`. The downstream boundary-value and
transfer package lives in `OSToWightmanBoundaryValues.lean`. The specialized
two-point continuation/spectral reduction ladder now lives in
`OSToWightmanTwoPoint.lean`.

Important status note: the public base-step surface in this file has been
corrected to the time-parametric OS II shape, where the time variables are
analytic and the spatial variables are treated as parameters. The remaining root
blocker is therefore split:

- build the time-parametric witness in
  `schwinger_continuation_base_step_timeParametric`;
- justify the later private full-holomorphic upgrade still consumed by the
  downstream restriction chain in
  `schwinger_continuation_spatial_upgrade_of_timeWitness`.
-/

open scoped Classical NNReal
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]
/- Phase 3: Analytic continuation from Euclidean to Minkowski.

    The analytic continuation proceeds inductively. Starting from Schwinger functions
    S_n defined on Euclidean configurations, we extend to complex times.

    **Inductive structure** (OS II, Theorem 4.1):
    - A₀: S_k(ξ) is analytic on {ξ ∈ ℝ^k : ξⱼ > 0 for all j}
    - Aᵣ: S_k has analytic continuation to the region C_k^(r) ⊂ ℂ^k
      where r of the ξ-variables are complexified
    - After n = d + 1 steps, reach the full forward tube

    **Key estimate** (OS II, Theorem 4.2): At each step, the linear growth
    condition E0' provides the bounds needed for the continuation. -/

/-- The region C_k^(r) from OS II: the domain after r steps of analytic continuation.
    C_k^(0) = {ξ ∈ ℝ^k : Im = 0, ξᵢ₀ > 0} (positive real Euclidean domain)
    C_k^(r+1) = {z ∈ ℂ^{k(d+1)} : Im(z_i,μ - z_{i-1,μ}) > 0 for all i, μ ≤ r}
      (open forward tube in the first r+1 spacetime directions; no constraint on μ > r).

    **Key property**: For r ≥ 1, C_k^(r) is an OPEN subset of ℂ^{k(d+1)}
    (strict positivity of imaginary parts ⟹ open). This ensures `DifferentiableOn ℂ`
    on C_k^(r) is genuine holomorphicity, not a vacuous condition.

    **Note**: C_k^(d+1) is the tube over a positive orthant in difference
    coordinates, not yet the Wightman forward tube. The active reconstruction
    chain in this file no longer uses the old Bochner/orbit route, so we do not
    build further geometry on that path here.

    The regions are monotone in the reverse direction for `r ≥ 1`:
      C_k^(r+1) ⊆ C_k^(r),
    since each step adds one more imaginary-positivity constraint. Also
    `C_k^(0)` is disjoint from `C_k^(r)` for r ≥ 1 (`C_k^(0)` has Im = 0,
    while `C_k^(r)` requires Im > 0 in at least one direction). -/
def AnalyticContinuationRegion (d k r : ℕ) [NeZero d] :
    Set (Fin k → Fin (d + 1) → ℂ) :=
  match r with
  | 0 => -- Base: positive Euclidean domain (all Im = 0, Euclidean times positive)
    { z | (∀ i : Fin k, ∀ μ : Fin (d + 1), (z i μ).im = 0) ∧
          (∀ i : Fin k, (z i 0).re > 0) }
  | r + 1 => -- Open forward tube in first r+1 spacetime directions;
    -- no constraint on remaining directions (μ > r), giving an open set.
    { z | ∀ i : Fin k,
        ∀ μ : Fin (d + 1), μ.val ≤ r →
          let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
          (z i μ - prev μ).im > 0 }

/-- Each individual coordinate positivity condition in the r+1 analytic continuation region
    defines an open set. This is the building block for `isOpen_analyticContinuationRegion_succ`. -/
private theorem isOpen_acr_coord {d k r : ℕ} (i : Fin k) (μ : Fin (d + 1)) :
    IsOpen { z : Fin k → Fin (d + 1) → ℂ |
      μ.val ≤ r →
        let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
        (z i μ - prev μ).im > 0 } := by
  by_cases hμ : μ.val ≤ r
  · by_cases hi : i.val = 0
    · have hcont : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z i μ).im := by
        simpa using (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i)))
      simpa [hμ, hi] using isOpen_lt continuous_const hcont
    · let j : Fin k := ⟨i.val - 1, by omega⟩
      have hi' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z i μ).im := by
        simpa using (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i)))
      have hj' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z j μ).im := by
        simpa [j] using (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply j)))
      simpa [hμ, hi, j, Complex.sub_im, sub_pos] using isOpen_lt hj' hi'
  · simp [hμ]

/-- For r ≥ 1, the analytic continuation region C_k^(r+1) is open. The strict imaginary-part
    positivity conditions are open conditions, and the region is a finite intersection of them. -/
theorem isOpen_analyticContinuationRegion_succ {d k r : ℕ} [NeZero d] :
    IsOpen (AnalyticContinuationRegion d k (r + 1)) := by
  suffices h :
      AnalyticContinuationRegion d k (r + 1) =
        ⋂ i : Fin k, ⋂ μ : Fin (d + 1),
          { z : Fin k → Fin (d + 1) → ℂ |
            μ.val ≤ r →
              let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
              (z i μ - prev μ).im > 0 } by
    rw [h]
    exact isOpen_iInter_of_finite (fun i : Fin k =>
      isOpen_iInter_of_finite (fun μ : Fin (d + 1) =>
        isOpen_acr_coord (d := d) (k := k) (r := r) i μ))
  ext z
  simp [AnalyticContinuationRegion]

private theorem differentiable_unflattenCfg_local (k d : ℕ) :
    Differentiable ℂ (BHW.unflattenCfg k d :
      (Fin (k * (d + 1)) → ℂ) → (Fin k → Fin (d + 1) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  rw [differentiable_pi]
  intro μ
  simpa [BHW.unflattenCfg] using (differentiable_apply (finProdFinEquiv (i, μ)))

private theorem differentiable_fromDiffFlat_local (k d : ℕ) :
    Differentiable ℂ (BHW.fromDiffFlat k d) := by
  unfold BHW.fromDiffFlat
  exact (BHW.diffCoordEquiv k d).symm.differentiable.comp
    (differentiable_unflattenCfg_local k d)

private theorem differentiable_flattenCfg_local (k d : ℕ) :
    Differentiable ℂ (BHW.flattenCfg k d :
      (Fin k → Fin (d + 1) → ℂ) → (Fin (k * (d + 1)) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  let p : Fin k × Fin (d + 1) := finProdFinEquiv.symm i
  let projInner :
      (Fin k → Fin (d + 1) → ℂ) → (Fin (d + 1) → ℂ) := fun z => z p.1
  let evalInner :
      (Fin k → Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
    ContinuousLinearMap.proj (R := ℂ) p.1
  have hconst :
      Differentiable ℂ
        (fun _ : (Fin k → Fin (d + 1) → ℂ) =>
          (ContinuousLinearMap.proj (R := ℂ) p.2 :
            (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) :=
    differentiable_const _
  simpa [BHW.flattenCfg, p] using
    (hconst.clm_apply
      (by simpa [projInner, evalInner] using
        (differentiable_apply p.1 : Differentiable ℂ projInner)))

private theorem differentiable_toDiffFlat_local (k d : ℕ) :
    Differentiable ℂ (BHW.toDiffFlat k d) := by
  unfold BHW.toDiffFlat
  exact (differentiable_flattenCfg_local k d).comp
    (BHW.diffCoordEquiv k d).differentiable

/-! ### First-step region as a tube over positive time-differences -/

/-- The flattened cone for `C_k^(1)`: only the time-difference coordinates are
    constrained to have positive imaginary part. -/
private def FlatPositiveTimeDiffReal (k d : ℕ) : Set (Fin (k * (d + 1)) → ℝ) :=
  {u | ∀ i : Fin k, 0 < u (finProdFinEquiv (i, 0))}

private theorem isOpen_flatPositiveTimeDiffReal (k d : ℕ) :
    IsOpen (FlatPositiveTimeDiffReal k d) := by
  simp only [FlatPositiveTimeDiffReal, Set.setOf_forall]
  exact isOpen_iInter_of_finite (fun i : Fin k =>
    isOpen_lt continuous_const (continuous_apply (finProdFinEquiv (i, 0))))

/-- Membership in the first-step flattened tube depends only on the imaginary parts
of the time-difference coordinates. -/
private theorem mem_tubeDomain_flatPositiveTimeDiffReal_iff {k d : ℕ}
    (z : Fin (k * (d + 1)) → ℂ) :
    z ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d) ↔
      ∀ i : Fin k, 0 < (z (finProdFinEquiv (i, (0 : Fin (d + 1))))).im := by
  change (fun p => (z p).im) ∈ FlatPositiveTimeDiffReal k d ↔ _
  simp [FlatPositiveTimeDiffReal]

/-- OS-II-faithful first-step witness surface on the flattened positive-time-difference
tube: continuous on the tube and holomorphic only in the time-difference coordinates,
with the spatial coordinates treated as parameters. -/
def IsTimeHolomorphicFlatPositiveTimeDiffWitness {k d : ℕ}
    (G : (Fin (k * (d + 1)) → ℂ) → ℂ) : Prop :=
  ContinuousOn G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) ∧
    ∀ z ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d), ∀ i : Fin k,
      DifferentiableOn ℂ
        (fun w => G (Function.update z (finProdFinEquiv (i, (0 : Fin (d + 1)))) w))
        {w : ℂ | 0 < w.im}

/-- `C_k^(1)` is exactly the tube over the positive time-difference cone in
    flattened difference coordinates. -/
private theorem acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff {d k : ℕ} [NeZero d]
    (z : Fin k → Fin (d + 1) → ℂ) :
    z ∈ AnalyticContinuationRegion d k 1 ↔
      BHW.toDiffFlat k d z ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d) := by
  constructor
  · intro hz
    change (fun i => ((BHW.toDiffFlat k d z) i).im) ∈ FlatPositiveTimeDiffReal k d
    intro i
    have htime : 0 < (BHW.diffCoordEquiv k d z i 0).im := by
      by_cases hi : i.val = 0
      · have h0 := hz i 0 (Nat.le_refl 0)
        have h0' : 0 < (z i 0).im := by
          simpa [hi] using h0
        simpa [BHW.diffCoordEquiv_apply, hi] using h0'
      · have h1 := hz i 0 (Nat.le_refl 0)
        have h1' : 0 < (z i 0 - z ⟨i.val - 1, by omega⟩ 0).im := by
          simpa [hi, Complex.sub_im, sub_pos] using h1
        simpa [BHW.diffCoordEquiv_apply, hi] using h1'
    simpa [FlatPositiveTimeDiffReal, BHW.toDiffFlat, BHW.flattenCfg] using htime
  · intro hz
    change (fun i => ((BHW.toDiffFlat k d z) i).im) ∈ FlatPositiveTimeDiffReal k d at hz
    simp only [AnalyticContinuationRegion, Set.mem_setOf_eq]
    intro i μ hμ
    have hμ0 : μ = 0 := Fin.ext (Nat.eq_zero_of_le_zero hμ)
    subst hμ0
    have hflat : 0 < ((BHW.toDiffFlat k d z) (finProdFinEquiv (i, 0))).im :=
      hz i
    have hdiff : 0 < (BHW.diffCoordEquiv k d z i 0).im := by
      simpa [BHW.toDiffFlat, BHW.flattenCfg] using hflat
    by_cases hi : i.val = 0
    · simpa [BHW.diffCoordEquiv_apply, hi] using hdiff
    · have h1 : 0 < (z i 0 - z ⟨i.val - 1, by omega⟩ 0).im := by
        simpa [BHW.diffCoordEquiv_apply, hi] using hdiff
      simpa [hi, Complex.sub_im, sub_pos] using h1

/-- Embed spatial coordinates into spacetime with zero time component. -/
def spatialEmbed {d : ℕ} (y : Fin d → ℝ) : SpacetimeDim d :=
  Fin.cons 0 y

@[simp] theorem spatialEmbed_zero {d : ℕ} (y : Fin d → ℝ) :
    spatialEmbed y 0 = 0 := by
  simp [spatialEmbed]

/-- Extract the real parts of the spatial-difference coordinates in the `k = 2`
flattened witness picture. -/
def extractDiffSpatialRe {d : ℕ}
    (u : Fin (2 * (d + 1)) → ℂ) : Fin d → ℝ :=
  fun i => (u (finProdFinEquiv (⟨1, by omega⟩, i.succ))).re

/-- The spatially-parameterized `k = 2` semigroup witness. This isolates the
dependence on the complex time parameter `z` and the real spatial-difference
parameter `y`. -/
def twoPointSpatialWitness {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (z : ℂ) (y : Fin d → ℝ) : ℂ :=
  let g_translated := SCV.translateSchwartz (-spatialEmbed y) g
  let hg_translated_pos : tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
    have hsup : (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp only [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, g_translated, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed y) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  let hg_translated_compact : HasCompactSupport (g_translated : SpacetimeDim d → ℂ) := by
    simpa [g_translated, Function.comp, SCV.translateSchwartz_apply] using
      hg_compact.comp_homeomorph (Homeomorph.addRight (-spatialEmbed y))
  OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
    (PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
      hχ₀_pos)
    (PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)
      hg_translated_pos)
    z

/-- The OS Hilbert-space vector obtained from the spatially translated one-point
test `g`. This isolates the `y`-dependence of the `k = 2` semigroup witness
into a single vector-valued map. -/
def twoPointTranslatedOnePointVector {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (y : Fin d → ℝ) : OSHilbertSpace OS :=
  let g_translated := SCV.translateSchwartz (-spatialEmbed y) g
  let hg_translated_pos : tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
    have hsup : (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp only [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, g_translated, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d g_translated : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed y) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single 1
          (onePointToFin1CLM d g_translated : SchwartzNPoint d 1)
          hg_translated_pos⟧)) : OSHilbertSpace OS))

/-- A Hilbert-space-valued map is continuous once all mixed inner products
against fixed basepoints vary continuously and the norm is constant. This is
the abstract topological reduction used for the `k = 2` translated-vector
continuity step. -/
private theorem continuous_of_continuous_inner_const_norm
    {α : Type*} [TopologicalSpace α]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (v : α → E)
    (hnorm : ∀ a b : α, ‖v a‖ = ‖v b‖)
    (hinner : ∀ a : α, Continuous fun b => @inner ℂ E _ (v a) (v b)) :
    Continuous v := by
  rw [continuous_iff_continuousAt]
  intro a
  have hnormsq_cont :
      ContinuousAt (fun b : α => ‖v b - v a‖ ^ 2) a := by
    have hEq :
        (fun b : α => ‖v b - v a‖ ^ 2) =
          fun b : α => 2 * ‖v a‖ ^ 2 - 2 * RCLike.re (@inner ℂ E _ (v a) (v b)) := by
      funext b
      have hsub := @norm_sub_sq ℂ E _ _ _ (v b) (v a)
      have hswap :
          RCLike.re (@inner ℂ E _ (v b) (v a)) =
            RCLike.re (@inner ℂ E _ (v a) (v b)) := by
        simpa using inner_re_symm (𝕜 := ℂ) (v b) (v a)
      calc
        ‖v b - v a‖ ^ 2
            = ‖v b‖ ^ 2 - 2 * RCLike.re (@inner ℂ E _ (v b) (v a)) + ‖v a‖ ^ 2 := hsub
        _ = ‖v a‖ ^ 2 - 2 * RCLike.re (@inner ℂ E _ (v a) (v b)) + ‖v a‖ ^ 2 := by
              rw [hnorm b a, hswap]
        _ = 2 * ‖v a‖ ^ 2 - 2 * RCLike.re (@inner ℂ E _ (v a) (v b)) := by ring
    rw [hEq]
    refine Continuous.continuousAt ?_
    have hinner_re : Continuous fun b : α => RCLike.re (@inner ℂ E _ (v a) (v b)) := by
      exact RCLike.continuous_re.comp (hinner a)
    fun_prop
  have hnorm_cont :
      ContinuousAt (fun b : α => Real.sqrt (‖v b - v a‖ ^ 2)) a :=
    hnormsq_cont.sqrt
  have hdist_cont :
      ContinuousAt (fun b : α => dist (v b) (v a)) a := by
    simpa [dist_eq_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg, norm_nonneg] using hnorm_cont
  rw [show ContinuousAt v a ↔ Filter.Tendsto v (nhds a) (nhds (v a)) from Iff.rfl]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hdist_tendsto :
      Filter.Tendsto (fun b : α => dist (v b) (v a)) (nhds a) (nhds 0) := by
    simpa using hdist_cont.tendsto
  rw [Metric.tendsto_nhds] at hdist_tendsto
  specialize hdist_tendsto ε hε
  filter_upwards [hdist_tendsto] with b hb
  simpa using hb

/-- For a fixed base spatial translation `y₀`, the mixed OS Hilbert pairing
with the translated one-point vector varies continuously in the second
translation parameter. This is the scalar continuity half of the remaining
`k = 2` step-B gap. -/
theorem continuous_translateSchwartz_spatial
    {d : ℕ} [NeZero d]
    (g : SchwartzSpacetime d)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    Continuous fun y : Fin d → ℝ =>
      SCV.translateSchwartz (-spatialEmbed y) g := by
  have htrans : Continuous fun t : SpacetimeDim d => SCV.translateSchwartz t g := by
    rw [continuous_iff_continuousAt]
    intro t₀
    exact SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport g hg_compact t₀
  let cembed : (Fin d → ℝ) →L[ℝ] Fin (d + 1) → ℝ :=
    ContinuousLinearMap.finCons
      (M := fun _ : Fin (d + 1) => ℝ)
      (0 : (Fin d → ℝ) →L[ℝ] ℝ)
      (ContinuousLinearMap.id ℝ (Fin d → ℝ))
  have hcembed : Continuous fun y : Fin d → ℝ => spatialEmbed y := by
    simpa [spatialEmbed, cembed] using cembed.continuous
  refine htrans.comp ?_
  simpa using hcembed.neg

/-- For a fixed base spatial translation `y₀`, the mixed OS Hilbert pairing
with the translated one-point vector varies continuously in the second
translation parameter. This is the scalar continuity half of the remaining
`k = 2` step-B gap. -/
theorem continuous_inner_twoPointTranslatedOnePointVector
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (y₀ : Fin d → ℝ) :
    Continuous fun y =>
      @inner ℂ (OSHilbertSpace OS) _
        (twoPointTranslatedOnePointVector (d := d) OS g hg_pos y₀)
        (twoPointTranslatedOnePointVector (d := d) OS g hg_pos y) := by
  let g₀ := SCV.translateSchwartz (-spatialEmbed y₀) g
  have hg₀_pos :
      tsupport (((onePointToFin1CLM d g₀ : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have htranslate_pos :
        ∀ y : Fin d → ℝ,
          tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
              SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
      intro y
      have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
      have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
          SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
        (((translateSchwartzNPoint (d := d) (spatialEmbed y)
          (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
        ext x
        simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
          translateSchwartzNPoint_apply, sub_eq_add_neg]
      rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
          SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
        tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
          (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
        congr_arg tsupport hsup]
      exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (d := d) (spatialEmbed y) ha0
        (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
    simpa [g₀] using htranslate_pos y₀
  let f₀ : SchwartzNPoint d 1 := onePointToFin1CLM d g₀
  let v₀ : OSHilbertSpace OS :=
    twoPointTranslatedOnePointVector (d := d) OS g hg_pos y₀
  have htrans : Continuous fun t : SpacetimeDim d => SCV.translateSchwartz t g := by
    rw [continuous_iff_continuousAt]
    intro t₀
    exact SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport g hg_compact t₀
  have hshift : Continuous fun y : Fin d → ℝ =>
      SCV.translateSchwartz (-spatialEmbed y) g := by
    let cembed : (Fin d → ℝ) →L[ℝ] Fin (d + 1) → ℝ :=
      ContinuousLinearMap.finCons
        (M := fun _ : Fin (d + 1) => ℝ)
        (0 : (Fin d → ℝ) →L[ℝ] ℝ)
        (ContinuousLinearMap.id ℝ (Fin d → ℝ))
    have hcembed : Continuous fun y : Fin d → ℝ => spatialEmbed y := by
      simpa [spatialEmbed, cembed] using cembed.continuous
    refine htrans.comp ?_
    simpa using hcembed.neg
  have hone : Continuous fun y : Fin d → ℝ =>
      (onePointToFin1CLM d) (SCV.translateSchwartz (-spatialEmbed y) g) := by
    exact (onePointToFin1CLM d).continuous.comp hshift
  let hterm : (Fin d → ℝ) → ZeroDiagonalSchwartz d 2 := fun y =>
    ⟨f₀.osConjTensorProduct
        ((onePointToFin1CLM d) (SCV.translateSchwartz (-spatialEmbed y) g)),
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (n := 1) (m := 1)
        (f := f₀)
        (g := (onePointToFin1CLM d) (SCV.translateSchwartz (-spatialEmbed y) g))
        hg₀_pos
        (by
          have htranslate_pos :
              tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                  SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
            have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
            have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
              (((translateSchwartzNPoint (d := d) (spatialEmbed y)
                (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
              ext x
              simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
                translateSchwartzNPoint_apply, sub_eq_add_neg]
            rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
              tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
                (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
              congr_arg tsupport hsup]
            exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
              (d := d) (spatialEmbed y) ha0
              (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
          exact htranslate_pos)⟩
  have hbase :
      Continuous (fun y : Fin d → ℝ =>
        f₀.osConjTensorProduct ((onePointToFin1CLM d) (SCV.translateSchwartz (-spatialEmbed y) g))) := by
    simpa [SchwartzNPoint.osConjTensorProduct] using
      (SchwartzMap.tensorProduct_continuous_right f₀.osConj).comp hone
  have hterm_cont : Continuous hterm := by
    exact hbase.subtype_mk (fun y =>
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) (n := 1) (m := 1)
        (f := f₀)
        (g := (onePointToFin1CLM d) (SCV.translateSchwartz (-spatialEmbed y) g))
        hg₀_pos
        (by
          have htranslate_pos :
              tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                  SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
            have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
            have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
              (((translateSchwartzNPoint (d := d) (spatialEmbed y)
                (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
              ext x
              simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
                translateSchwartzNPoint_apply, sub_eq_add_neg]
            rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
                SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
              tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
                (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
              congr_arg tsupport hsup]
            exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
              (d := d) (spatialEmbed y) ha0
              (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
          exact htranslate_pos))
  let hscalar : (Fin d → ℝ) → ℂ := fun y => OS.S 2 (hterm y)
  have hscalar_cont : Continuous hscalar :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2).continuous.comp hterm_cont
  convert hscalar_cont using 1
  ext y
  let gy := SCV.translateSchwartz (-spatialEmbed y) g
  have hgy_pos :
      tsupport (((onePointToFin1CLM d gy : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
    have hsup : (((onePointToFin1CLM d gy : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp [gy, onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d gy : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed y) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  let Fy : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d gy : SchwartzNPoint d 1) hgy_pos
  let F₀ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d g₀ : SchwartzNPoint d 1) hg₀_pos
  have hvy :
      twoPointTranslatedOnePointVector (d := d) OS g hg_pos y =
        (((show OSPreHilbertSpace OS from (⟦Fy⟧)) : OSHilbertSpace OS)) := by
    simp [twoPointTranslatedOnePointVector, Fy, gy]
  have hv₀ :
      v₀ = (((show OSPreHilbertSpace OS from (⟦F₀⟧)) : OSHilbertSpace OS)) := by
    simp [v₀, twoPointTranslatedOnePointVector, F₀, g₀]
  change @inner ℂ (OSHilbertSpace OS) _ v₀
      (twoPointTranslatedOnePointVector (d := d) OS g hg_pos y) = hscalar y
  rw [hv₀, hvy, UniformSpace.Completion.inner_coe, OSPreHilbertSpace.inner_eq]
  rw [PositiveTimeBorchersSequence.osInner]
  change OSInnerProduct d OS.S
      (BorchersSequence.single 1 (onePointToFin1CLM d g₀ : SchwartzNPoint d 1))
      (BorchersSequence.single 1 (onePointToFin1CLM d gy : SchwartzNPoint d 1)) = hscalar y
  rw [OSInnerProduct_single_single (d := d) (S := OS.S) (hlin := OS.E0_linear)
    (n := 1) (m := 1) (f := onePointToFin1CLM d g₀) (g := onePointToFin1CLM d gy)]
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence
        (f₀.osConjTensorProduct (onePointToFin1CLM d gy)) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := 1) (m := 1)
      (f := f₀)
      (g := onePointToFin1CLM d gy)
      hg₀_pos hgy_pos
  rw [show ZeroDiagonalSchwartz.ofClassical
      (SchwartzNPoint.osConjTensorProduct (onePointToFin1CLM d g₀) (onePointToFin1CLM d gy)) =
      hterm y by
        apply Subtype.ext
        simp [hterm, f₀, gy, hvanish]]

private theorem onePointToFin1_translate_spatial_tsupport_subset
    {d : ℕ} [NeZero d]
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (y : Fin d → ℝ) :
    tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
        SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
  have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
      SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
    (((translateSchwartzNPoint (d := d) (spatialEmbed y)
      (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
    ext x
    simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
      translateSchwartzNPoint_apply, sub_eq_add_neg]
  rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
      SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
    tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
      (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
    congr_arg tsupport hsup]
  exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
    (d := d) (spatialEmbed y) ha0
    (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos

private theorem translate_osConjTensorProduct_eq_of_spatial_local
    {d n m : ℕ} [NeZero d]
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (x : NPointDomain d (n + m)) :
    ((translateSchwartzNPoint (d := d) a f).osConjTensorProduct
      (translateSchwartzNPoint (d := d) a g)) x =
      (f.osConjTensorProduct g) (fun i => x i - a) := by
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, translateSchwartzNPoint_apply]
  congr
  · ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeReflectionN, splitFirst, timeReflection, ha0]
    · simp [timeReflectionN, splitFirst, timeReflection, hμ]

/-- The self-pair Schwinger functional of a positive-time one-point test is
invariant under simultaneous spatial translation of both factors. This is the
two-point OS-translation identity underlying constant norm for the translated
one-point Hilbert vector. -/
theorem schwinger_self_pair_onePoint_translate_spatial_eq
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (y y₀ : Fin d → ℝ) :
    let g₀ := SCV.translateSchwartz (-spatialEmbed y₀) g
    let gy := SCV.translateSchwartz (-spatialEmbed y) g
    let f₀ : SchwartzNPoint d 1 := onePointToFin1CLM d g₀
    let fy : SchwartzNPoint d 1 := onePointToFin1CLM d gy
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (fy.osConjTensorProduct fy)) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (f₀.osConjTensorProduct f₀)) := by
  dsimp
  let a : SpacetimeDim d := spatialEmbed y - spatialEmbed y₀
  let f₀ : SchwartzNPoint d 1 :=
    (onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y₀) g) : SchwartzNPoint d 1)
  let fy : SchwartzNPoint d 1 :=
    (onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) : SchwartzNPoint d 1)
  have ha0 : a 0 = 0 := by
    simp [a, spatialEmbed_zero]
  have hf₀_pos :
      tsupport ((f₀ : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆ OrderedPositiveTimeRegion d 1 := by
    have hsup : (((f₀ : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y₀)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp [f₀, onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, sub_eq_add_neg]
    rw [show tsupport (((f₀ : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y₀)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed y₀) (spatialEmbed_zero y₀) _ hg_pos
  have hfy_eq :
      translateSchwartzNPoint (d := d) a
        f₀ = fy := by
    ext x
    simp [a, f₀, fy, onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
      translateSchwartzNPoint_apply, sub_eq_add_neg]
    abel_nf
  have hfy_pos :
      tsupport ((fy : SchwartzNPoint d 1) : NPointDomain d 1 → ℂ) ⊆ OrderedPositiveTimeRegion d 1 := by
    simpa [hfy_eq] using
      (translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
        (d := d) a ha0
        f₀
        hf₀_pos)
  have hvanish₀ :
      VanishesToInfiniteOrderOnCoincidence (f₀.osConjTensorProduct f₀) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := 1) (m := 1)
      (f := f₀)
      (g := f₀)
      hf₀_pos hf₀_pos
  have hvanishy :
      VanishesToInfiniteOrderOnCoincidence (fy.osConjTensorProduct fy) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (n := 1) (m := 1)
      (f := fy)
      (g := fy)
      hfy_pos hfy_pos
  let z₀ : ZeroDiagonalSchwartz d 2 := ⟨_, hvanish₀⟩
  let zy : ZeroDiagonalSchwartz d 2 := ⟨_, hvanishy⟩
  have hshift :
      ∀ x, zy.1 x = z₀.1 (fun i => x i + (-a)) := by
    intro x
    simpa [z₀, zy, hfy_eq, sub_eq_add_neg] using
      (translate_osConjTensorProduct_eq_of_spatial_local
        (d := d) (n := 1) (m := 1) a ha0 f₀ f₀ x)
  have hS₀ : OS.S 2 z₀ = OS.S 2 zy := by
    exact OS.E1_translation_invariant 2 (-a) z₀ zy hshift
  have hS : OS.S 2 zy = OS.S 2 z₀ := hS₀.symm
  have hzy :
      ZeroDiagonalSchwartz.ofClassical (fy.osConjTensorProduct fy) = zy := by
    simpa [zy] using
      (ZeroDiagonalSchwartz.ofClassical_of_vanishes
        (f := fy.osConjTensorProduct fy) hvanishy)
  have hz₀ :
      ZeroDiagonalSchwartz.ofClassical (f₀.osConjTensorProduct f₀) = z₀ := by
    simpa [z₀] using
      (ZeroDiagonalSchwartz.ofClassical_of_vanishes
        (f := f₀.osConjTensorProduct f₀) hvanish₀)
  rw [hzy, hz₀]
  exact hS

/-- Spatial translation does not change the OS Hilbert norm of the translated
one-point vector. This is the norm-control half of the remaining `k = 2`
step-B gap. -/
theorem norm_twoPointTranslatedOnePointVector_eq
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (y y₀ : Fin d → ℝ) :
    ‖twoPointTranslatedOnePointVector (d := d) OS g hg_pos y‖ =
      ‖twoPointTranslatedOnePointVector (d := d) OS g hg_pos y₀‖ := by
  let gy := SCV.translateSchwartz (-spatialEmbed y) g
  let g₀ := SCV.translateSchwartz (-spatialEmbed y₀) g
  have hgy_pos :
      tsupport (((onePointToFin1CLM d gy : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    simpa [gy] using
      onePointToFin1_translate_spatial_tsupport_subset
        (d := d) g hg_pos y
  have hg₀_pos :
      tsupport (((onePointToFin1CLM d g₀ : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    simpa [g₀] using
      onePointToFin1_translate_spatial_tsupport_subset
        (d := d) g hg_pos y₀
  let Fy : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d gy : SchwartzNPoint d 1) hgy_pos
  let F₀ : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d g₀ : SchwartzNPoint d 1) hg₀_pos
  let vy : OSPreHilbertSpace OS := (⟦Fy⟧ : OSPreHilbertSpace OS)
  let v₀ : OSPreHilbertSpace OS := (⟦F₀⟧ : OSPreHilbertSpace OS)
  have hy :
      twoPointTranslatedOnePointVector (d := d) OS g hg_pos y =
        (((show OSPreHilbertSpace OS from (⟦Fy⟧)) : OSHilbertSpace OS)) := by
    simp [twoPointTranslatedOnePointVector, Fy, gy]
  have hy₀ :
      twoPointTranslatedOnePointVector (d := d) OS g hg_pos y₀ =
        (((show OSPreHilbertSpace OS from (⟦F₀⟧)) : OSHilbertSpace OS)) := by
    simp [twoPointTranslatedOnePointVector, F₀, g₀]
  rw [hy, hy₀, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  have hinner :
      @inner ℂ (OSPreHilbertSpace OS) _ vy vy =
        @inner ℂ (OSPreHilbertSpace OS) _ v₀ v₀ := by
    rw [OSPreHilbertSpace.inner_eq, OSPreHilbertSpace.inner_eq]
    change OSInnerProduct d OS.S
        (BorchersSequence.single 1 (onePointToFin1CLM d gy : SchwartzNPoint d 1))
        (BorchersSequence.single 1 (onePointToFin1CLM d gy : SchwartzNPoint d 1)) =
      OSInnerProduct d OS.S
        (BorchersSequence.single 1 (onePointToFin1CLM d g₀ : SchwartzNPoint d 1))
        (BorchersSequence.single 1 (onePointToFin1CLM d g₀ : SchwartzNPoint d 1))
    rw [OSInnerProduct_single_single (d := d) (S := OS.S) (hlin := OS.E0_linear)
      (n := 1) (m := 1) (f := onePointToFin1CLM d gy) (g := onePointToFin1CLM d gy)]
    rw [OSInnerProduct_single_single (d := d) (S := OS.S) (hlin := OS.E0_linear)
      (n := 1) (m := 1) (f := onePointToFin1CLM d g₀) (g := onePointToFin1CLM d g₀)]
    simpa [gy, g₀] using
      (schwinger_self_pair_onePoint_translate_spatial_eq
        (d := d) OS g hg_pos y y₀)
  have hsq :
      ‖vy‖ ^ 2 = ‖v₀‖ ^ 2 := by
    have hsqC :
        ((‖vy‖ ^ 2 : ℝ) : ℂ) = ((‖v₀‖ ^ 2 : ℝ) : ℂ) := by
      simpa [inner_self_eq_norm_sq] using hinner
    exact Complex.ofReal_injective hsqC
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hEq | hEq
  · exact hEq
  · linarith [norm_nonneg vy, norm_nonneg v₀, hEq]

/-- Continuity of the translated one-point OS Hilbert vector in the spatial
translation parameter. This is the remaining vector-valued analytic heart behind
joint continuity of the corrected `k = 2` witness. -/
theorem continuous_twoPointTranslatedOnePointVector
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (g : SchwartzSpacetime d)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    Continuous (twoPointTranslatedOnePointVector (d := d) OS g hg_pos) := by
  refine continuous_of_continuous_inner_const_norm
    (v := twoPointTranslatedOnePointVector (d := d) OS g hg_pos) ?_ ?_
  · intro y y₀
    exact norm_twoPointTranslatedOnePointVector_eq
      (d := d) OS g hg_pos y y₀
  · intro y₀
    simpa using
      (continuous_inner_twoPointTranslatedOnePointVector
        (d := d) OS g hg_pos hg_compact y₀)

/-- On the right half-plane, the spatially-parameterized `k = 2` witness is the
matrix element of `osTimeShiftHilbertComplex` against a fixed left vector and
the translated one-point right vector. -/
theorem twoPointSpatialWitness_eq_inner_osTimeShiftHilbertComplex
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (z : ℂ) (hz : 0 < z.re) (y : Fin d → ℝ) :
    twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact z y =
      @inner ℂ (OSHilbertSpace OS) _
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
                hχ₀_pos⟧)) : OSHilbertSpace OS))
        (osTimeShiftHilbertComplex (d := d) OS lgc z
          (twoPointTranslatedOnePointVector (d := d) OS g hg_pos y)) := by
  let x : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
            hχ₀_pos⟧)) : OSHilbertSpace OS))
  let v : OSHilbertSpace OS := twoPointTranslatedOnePointVector (d := d) OS g hg_pos y
  have hg_translated_pos : tsupport
      (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed y) 0 = 0 := spatialEmbed_zero y
    have hsup : (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
        SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp only [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, sub_eq_add_neg]
    rw [show tsupport (((onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) :
        SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) =
      tsupport (((translateSchwartzNPoint (d := d) (spatialEmbed y)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) from
      congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (spatialEmbed y) ha0
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  have hspec :
      twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact z y =
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          x v z := by
    simpa [x, v, twoPointSpatialWitness, twoPointTranslatedOnePointVector] using
      (OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
        (d := d) (OS := OS) (lgc := lgc)
        ((show PositiveTimeBorchersSequence d from
          PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
            hχ₀_pos))
        ((show PositiveTimeBorchersSequence d from
          PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d (SCV.translateSchwartz (-spatialEmbed y) g) : SchwartzNPoint d 1)
            hg_translated_pos))
        z hz)
  have hinner :
      @inner ℂ (OSHilbertSpace OS) _ x
        (osTimeShiftHilbertComplex (d := d) OS lgc z v) =
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        x v z :=
    osTimeShiftHilbertComplex_inner_eq (d := d) OS lgc x v z hz
  exact hspec.trans hinner.symm

/-- Once the translated one-point OS Hilbert vector is known to vary
continuously in the spatial parameter, joint continuity of the spatially
parameterized `k = 2` witness follows from joint continuity of
`osTimeShiftHilbertComplex`. -/
theorem continuousOn_twoPointSpatialWitness_of_continuous_twoPointTranslatedOnePointVector
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hcont_vec : Continuous (twoPointTranslatedOnePointVector (d := d) OS g hg_pos)) :
    ContinuousOn (fun p : ℂ × (Fin d → ℝ) =>
      twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact p.1 p.2)
      ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
  let x : OSHilbertSpace OS :=
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1))
            hχ₀_pos⟧)) : OSHilbertSpace OS))
  let Φ : ℂ × (Fin d → ℝ) → ℂ × OSHilbertSpace OS :=
    fun p => (p.1, twoPointTranslatedOnePointVector (d := d) OS g hg_pos p.2)
  have hΦcont : Continuous Φ := by
    refine Continuous.prodMk continuous_fst ?_
    exact hcont_vec.comp continuous_snd
  have hΦmaps :
      Set.MapsTo Φ ({z : ℂ | 0 < z.re} ×ˢ Set.univ)
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    intro p hp
    exact ⟨hp.1, trivial⟩
  have heval :
      ContinuousOn
        (fun p : ℂ × (Fin d → ℝ) =>
          osTimeShiftHilbertComplex (d := d) OS lgc p.1
            (twoPointTranslatedOnePointVector (d := d) OS g hg_pos p.2))
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    simpa [Φ] using
      (continuousOn_osTimeShiftHilbertComplex_jointly (d := d) OS lgc).comp
        hΦcont.continuousOn hΦmaps
  have hinner :
      ContinuousOn
        (fun p : ℂ × (Fin d → ℝ) =>
          @inner ℂ (OSHilbertSpace OS) _ x
            (osTimeShiftHilbertComplex (d := d) OS lgc p.1
              (twoPointTranslatedOnePointVector (d := d) OS g hg_pos p.2)))
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) :=
    (innerSL ℂ x).continuous.comp_continuousOn heval
  refine hinner.congr ?_
  intro p hp
  simpa [x] using
    (twoPointSpatialWitness_eq_inner_osTimeShiftHilbertComplex
      (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact p.1 hp.1 p.2)

/-- Corrected `k = 2` flat witness candidate: it depends on the time-difference
coordinate holomorphically and on the spatial-difference coordinates through a
real spatial translation parameter. -/
def twoPointCorrectedWitness {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (u : Fin (2 * (d + 1)) → ℂ) : ℂ :=
  twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
    (-Complex.I * u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))))
    (extractDiffSpatialRe u)

/-- The corrected flat witness is obtained from the spatially-parameterized
two-point witness by Wick-rotating the time-difference coordinate and reading
off the real parts of the spatial-difference coordinates. -/
theorem twoPointCorrectedWitness_eq_twoPointSpatialWitness
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (u : Fin (2 * (d + 1)) → ℂ) :
    twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u =
      twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (-Complex.I * u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))))
        (extractDiffSpatialRe u) := by
  rfl

/-- The corrected `k = 2` witness is holomorphic in the difference-time slot. -/
theorem differentiableOn_twoPointCorrectedWitness_time
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (u : Fin (2 * (d + 1)) → ℂ) :
    DifferentiableOn ℂ
      (fun w => twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (Function.update u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) w))
      {w : ℂ | 0 < w.im} := by
  have hextract : ∀ w : ℂ,
      extractDiffSpatialRe
        (Function.update u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) w) =
      extractDiffSpatialRe u := by
    intro w
    ext i
    simp only [extractDiffSpatialRe]
    have hne : finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (0 : Fin (d + 1))) ≠
        finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (i : Fin d).succ) := by
      intro heq
      have := (Prod.mk.inj (finProdFinEquiv.injective heq)).2
      exact absurd this (Fin.succ_ne_zero i).symm
    simp [Function.update, hne, Ne.symm hne]
  let y₀ := extractDiffSpatialRe u
  let g₀ := SCV.translateSchwartz (-spatialEmbed y₀) g
  have hg₀_pos : tsupport (((onePointToFin1CLM d g₀ : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
    have ha0 : (spatialEmbed y₀) 0 = 0 := spatialEmbed_zero _
    have hsup : (((onePointToFin1CLM d g₀ : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) =
      (((translateSchwartzNPoint (d := d) (spatialEmbed y₀)
        (onePointToFin1CLM d g : SchwartzNPoint d 1)) : NPointDomain d 1 → ℂ)) := by
      ext x
      simp only [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
        translateSchwartzNPoint_apply, g₀, sub_eq_add_neg]
    rw [show tsupport _ = tsupport _ from congr_arg tsupport hsup]
    exact translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) _ ha0 _ hg_pos
  have hfun_eq : (fun w => twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
      (Function.update u (finProdFinEquiv ((⟨1, by omega⟩ : Fin 2), (0 : Fin (d + 1)))) w)) =
    (fun w => OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
      (PositiveTimeBorchersSequence.single 1
        (SchwartzNPoint.osConj (d := d) (n := 1) (onePointToFin1CLM d χ₀)) hχ₀_pos)
      (PositiveTimeBorchersSequence.single 1 (onePointToFin1CLM d g₀) hg₀_pos)
      (-Complex.I * w)) := by
    ext w
    simp only [twoPointCorrectedWitness, hextract w, Function.update_self]
    rfl
  rw [hfun_eq]
  exact OSReconstruction.differentiableOn_comp_neg_I_mul
    (OSInnerProductTimeShiftHolomorphicValue_differentiableOn (d := d) OS lgc _ _)

/-- The corrected `k = 2` witness is constant in the center-time slot. -/
theorem differentiableOn_twoPointCorrectedWitness_centerTime
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (u : Fin (2 * (d + 1)) → ℂ) :
    DifferentiableOn ℂ
      (fun w => twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (Function.update u (finProdFinEquiv ((⟨0, by omega⟩ : Fin 2), (0 : Fin (d + 1)))) w))
      {w : ℂ | 0 < w.im} := by
  have hconst : ∀ w : ℂ,
      twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (Function.update u (finProdFinEquiv ((⟨0, by omega⟩ : Fin 2), (0 : Fin (d + 1)))) w) =
      twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u := by
    intro w
    simp only [twoPointCorrectedWitness]
    congr 1
  simp_rw [hconst]
  exact differentiableOn_const _

/-- The corrected `k = 2` witness already satisfies the time-slice
holomorphicity part of the flattened positive-time-difference witness surface. -/
theorem twoPointCorrectedWitness_timeSliceDifferentiableOn
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (u : Fin (2 * (d + 1)) → ℂ)
    (_hu : ∀ j : Fin 2, 0 < (u (finProdFinEquiv (j, (0 : Fin (d + 1))))).im)
    (i : Fin 2) :
    DifferentiableOn ℂ
      (fun w => twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
        (Function.update u (finProdFinEquiv (i, (0 : Fin (d + 1)))) w))
      {w : ℂ | 0 < w.im} := by
  fin_cases i
  · simpa using
      differentiableOn_twoPointCorrectedWitness_centerTime
        (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u
  · simpa using
      differentiableOn_twoPointCorrectedWitness_time
        (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u

/-- Joint continuity of the spatially-parameterized `k = 2` semigroup witness on
the right-half-plane times the real spatial-difference parameter. This is the
remaining analytic heart of step B. -/
theorem continuousOn_twoPointSpatialWitness
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    ContinuousOn (fun p : ℂ × (Fin d → ℝ) =>
      twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact p.1 p.2)
      ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
  exact continuousOn_twoPointSpatialWitness_of_continuous_twoPointTranslatedOnePointVector
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
    (continuous_twoPointTranslatedOnePointVector (d := d) OS g hg_pos hg_compact)

/-- Continuity of the corrected `k = 2` witness on the flattened positive-time
difference tube. This isolates the remaining analytic part of step B. -/
theorem continuousOn_twoPointCorrectedWitness
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ)) :
    ContinuousOn (twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact)
      (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d)) := by
  let Φ : (Fin (2 * (d + 1)) → ℂ) → ℂ × (Fin d → ℝ) :=
    fun u =>
      (-Complex.I * u (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))),
        extractDiffSpatialRe u)
  have hΦcont : Continuous Φ := by
    refine Continuous.prodMk (continuous_const.mul (continuous_apply _)) ?_
    refine continuous_pi ?_
    intro i
    exact Complex.continuous_re.comp (continuous_apply _)
  have hΦmaps :
      Set.MapsTo Φ (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d))
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    intro u hu
    refine ⟨?_, trivial⟩
    rw [Set.mem_setOf_eq, OSReconstruction.neg_I_mul_re_eq_im]
    exact (mem_tubeDomain_flatPositiveTimeDiffReal_iff (k := 2) (d := d) u).mp hu ⟨1, by omega⟩
  have hcont_spatial :=
    continuousOn_twoPointSpatialWitness
      (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact
  have hcomp :
      ContinuousOn
        (fun u =>
          twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact (Φ u).1 (Φ u).2)
        (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d)) :=
    hcont_spatial.comp hΦcont.continuousOn hΦmaps
  have hEq :
      (fun u =>
        twoPointSpatialWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact (Φ u).1 (Φ u).2) =
      twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact := by
    funext u
    simp [Φ, twoPointCorrectedWitness_eq_twoPointSpatialWitness]
  simpa [hEq] using hcomp

/-- Once continuity is supplied, the corrected `k = 2` witness satisfies the
full time-parametric witness surface required at the first continuation step. -/
theorem isTimeHolomorphicFlatPositiveTimeDiffWitness_twoPointCorrectedWitness_of_continuousOn
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hcont : ContinuousOn
      (twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact)
      (SCV.TubeDomain (FlatPositiveTimeDiffReal 2 d))) :
    IsTimeHolomorphicFlatPositiveTimeDiffWitness
      (twoPointCorrectedWitness OS lgc χ₀ g hχ₀_pos hg_pos hg_compact) := by
  refine ⟨hcont, ?_⟩
  intro u hu i
  have hu' : ∀ j : Fin 2, 0 < (u (finProdFinEquiv (j, (0 : Fin (d + 1))))).im := by
    exact (mem_tubeDomain_flatPositiveTimeDiffReal_iff (k := 2) (d := d) u).mp hu
  exact twoPointCorrectedWitness_timeSliceDifferentiableOn
    (d := d) OS lgc χ₀ g hχ₀_pos hg_pos hg_compact u hu' i

/-- Root-facing fixed-time shell equality for a `k = 2` flat witness.
At positive real time, once `G` is already known to reproduce `OS.S 2` on all
zero-diagonal two-point tests, the corresponding fixed-time kernel CLM should
reproduce the Schwinger functional on the admissible positive-time difference
shell. This is the honest step-C theorem surface needed before the later
reduced/dense extension route can be applied. -/
theorem twoPointFixedTimeKernelCLM_eq_schwinger_on_differenceShell_of_positiveSupport
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hK_meas : MeasureTheory.AEStronglyMeasurable
      (OSReconstruction.twoPointFixedTimeKernel (d := d) G (t : ℂ)) MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂MeasureTheory.volume,
      ‖OSReconstruction.twoPointFixedTimeKernel (d := d) G (t : ℂ) x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (χ h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    OSReconstruction.twoPointFlatKernelCLM
        (OSReconstruction.twoPointFixedTimeKernel (d := d) G (t : ℂ))
        hK_meas C_bd N hC hK_bound
        (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ h)))) =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ
            (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
  sorry

/-- Fixed-admissible-shell version of the `k = 2` time-parametric witness
assembly. For a normalized center cutoff `χ₀` and a positive compact difference
test `g`, the corrected witness gives a single-shell time-parametric witness
whose fixed-time kernels reproduce the translated Schwinger family generated by
`g`. This isolates the local semigroup-side assembly before the later global
flattened-witness packaging step. -/
theorem exists_twoPoint_timeParametric_singleWitness_on_differenceShell
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ g : SchwartzSpacetime d)
    (hχ₀_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ₀ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (t : ℝ) (ht : 0 < t) (χ : SchwartzSpacetime d)
          (hK_meas : MeasureTheory.AEStronglyMeasurable
            (OSReconstruction.twoPointFixedTimeKernel (d := d) G (t : ℂ))
              MeasureTheory.volume)
          (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
          (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂MeasureTheory.volume,
            ‖OSReconstruction.twoPointFixedTimeKernel (d := d) G (t : ℂ) x‖ ≤
              C_bd * (1 + ‖x‖) ^ N),
        OSReconstruction.twoPointFlatKernelCLM
            (OSReconstruction.twoPointFixedTimeKernel (d := d) G (t : ℂ))
            hK_meas C_bd N hC hK_bound
            (OSReconstruction.reindexSchwartzFin (by ring)
              (OSReconstruction.flattenSchwartzNPoint (d := d)
                (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ g)))) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) g)))) := by
  sorry

/-- Root-facing step-D wrapper: once a flattened CLM agrees with a fixed-time
kernel on the admissible two-point difference shell, the `DenseCLM` uniqueness
route upgrades that shell agreement to the expected product-shell and
difference-shell formulas. -/
theorem map_productLift_and_differenceLift_of_eq_on_twoPointDifferenceShell_fixedTime
    {d : ℕ} [NeZero d]
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable
      (OSReconstruction.twoPointFixedTimeKernel (d := d) G t) MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂MeasureTheory.volume,
      ‖OSReconstruction.twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hEq : ∀ χ h : SchwartzSpacetime d,
      T (OSReconstruction.reindexSchwartzFin (by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeKernel (d := d) G t z *
            (χ (z 0) * h (z 1)))
    (χ g h : SchwartzSpacetime d) :
    T (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointProductLift χ g)))) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeKernel (d := d) G t z *
            (χ (z 0) * g (z 0 + z 1)) ∧
      T (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2,
          OSReconstruction.twoPointFixedTimeKernel (d := d) G t z *
            (χ (z 0) * h (z 1)) := by
  let TK : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    OSReconstruction.twoPointFlatKernelCLM
      (OSReconstruction.twoPointFixedTimeKernel (d := d) G t)
      hK_meas C_bd N hC hK_bound
  have hShell :
      ∀ χ h : SchwartzSpacetime d,
        T (OSReconstruction.reindexSchwartzFin (by ring)
              (OSReconstruction.flattenSchwartzNPoint (d := d)
                (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ h)))) =
          TK (OSReconstruction.reindexSchwartzFin (by ring)
              (OSReconstruction.flattenSchwartzNPoint (d := d)
                (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ h)))) := by
    intro χ h
    rw [hEq χ h]
    simpa [TK] using
      (OSReconstruction.twoPointFixedTimeKernelCLM_apply_differenceLift
        (d := d) G t hK_meas C_bd N hC hK_bound χ h).symm
  have hT_eq : T = TK :=
    flattened_clm_eq_of_eq_on_twoPointDifferenceShell (d := d) T TK hShell
  constructor
  · calc
      T (OSReconstruction.reindexSchwartzFin (by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift χ g)))) =
          TK (OSReconstruction.reindexSchwartzFin (by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift χ g)))) := by
              simpa [TK] using congrArg
                (fun L : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ =>
                  L (OSReconstruction.reindexSchwartzFin (by ring)
                    (OSReconstruction.flattenSchwartzNPoint (d := d)
                      (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                        (twoPointProductLift χ g)))))
                hT_eq
      _ = ∫ z : NPointDomain d 2,
            OSReconstruction.twoPointFixedTimeKernel (d := d) G t z *
              (χ (z 0) * g (z 0 + z 1)) := by
            simpa [TK] using
              OSReconstruction.twoPointFixedTimeKernelCLM_apply_productLift
                (d := d) G t hK_meas C_bd N hC hK_bound χ g
  · exact hEq χ h

/-- **Corrected universalization** for `k = 2` (ZeroDiag-native).

The Schwinger functional `OS.S 2` lives on `ZeroDiagonalSchwartz d 2` — it
cannot be extended to the full Schwartz space because the Schwinger kernel has
diagonal singularities. Two CLMs on `ZeroDiagonalSchwartz` that agree on a
dense set of difference shells are equal. -/
theorem twoPointWitnessKernelCLM_eq_schwinger_of_shell_agreement
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (L : ZeroDiagonalSchwartz d 2 →L[ℂ] ℂ)
    (hShell : ∀ χ h : SchwartzSpacetime d,
      tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} →
      HasCompactSupport (h : SpacetimeDim d → ℂ) →
        L (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)))
    (hDense : Dense {f : ZeroDiagonalSchwartz d 2 |
      ∃ (χ h : SchwartzSpacetime d),
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} ∧
        HasCompactSupport (h : SpacetimeDim d → ℂ) ∧
        f = ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)}) :
    L = OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2 :=
  ContinuousLinearMap.eq_of_eq_on_dense L
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 2) hDense
    (fun f ⟨χ, h, hh_pos, hh_compact, hf_eq⟩ => by
      rw [hf_eq]; exact hShell χ h hh_pos hh_compact)

/-- **Two-point Schwinger kernel regularity.**

The two-point Schwinger function S₂ is a regular distribution on
`ZeroDiagonalSchwartz d 2`: there exists a measurable kernel K such that
`S₂(f) = ∫ K * f` for all zero-diagonal test functions f.

K may have inverse-power singularity at coincidence (the diagonal x₁ = x₂).
The zero-diagonal condition on f kills this singularity, making K * f
integrable. The integrability is stated explicitly rather than via a
global bound.

Ref: Reed-Simon IV §XIII.12; Glimm-Jaffe "Quantum Physics" §19.1. -/
theorem schwinger_twoPoint_kernel_regularity {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (K : NPointDomain d 2 → ℂ),
      -- K is measurable
      MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume ∧
      -- K * f is integrable for all zero-diagonal f
      (∀ (f : ZeroDiagonalSchwartz d 2),
        MeasureTheory.Integrable (fun x => K x * (f.1 x)) MeasureTheory.volume) ∧
      -- S₂(f) = ∫ K * f for all zero-diagonal f
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2, K x * (f.1 x)) := by
  sorry

/-- `k = 2` special case of the time-parametric base-step theorem.

**Architecture (2026-03-17):** The proof has two separate obligations:

1. `schwinger_twoPoint_kernel_regularity` provides a real measurable kernel K
   with the Euclidean integral formula S₂(f) = ∫ K * f.
2. The witness G on the complex tube requires extending K holomorphically in
   time. This extension is a separate obligation (from the semigroup spectral
   representation), NOT automatically provided by kernel regularity. -/
theorem schwinger_continuation_base_step_timeParametric_twoPoint {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (G : (Fin (2 * (d + 1)) → ℂ) → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun j => wickRotatePoint (x j))) * (f.1 x)) := by
  -- Step 1: Get the Schwinger kernel K from regularity
  obtain ⟨K, hK_meas, hK_int, hK_euclid⟩ :=
    schwinger_twoPoint_kernel_regularity (d := d) OS lgc
  -- Step 2: Define G on the flattened tube as K composed with inverse Wick rotation
  -- G(u) = K(wickRotateInverse(fromDiffFlat(u))) — the kernel in flat tube coordinates
  -- For now, use K directly on the Euclidean domain
  -- The time holomorphicity and tube extension come from the semigroup
  sorry

/-- OS-II-faithful first-stage base-step theorem: construct a witness on the
flattened positive-time-difference tube that is holomorphic in the time-difference
variables and continuous in the remaining variables, together with the Euclidean
reproduction identity.

This matches the corrected reading of OS II more closely than the older single-step
formulation asking immediately for full holomorphicity on all complex coordinates. -/
theorem schwinger_continuation_base_step_timeParametric {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (G : (Fin (k * (d + 1)) → ℂ) → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) := by
  sorry

/-- Second subproblem for the base step: upgrade the OS-II time-parametric witness to
the legacy fully holomorphic surface currently consumed by the downstream
restriction chain.

This theorem isolates the statement-design issue at the root blocker. If that
full-holomorphic surface is not the right OS-II endpoint, then this is exactly the
place where the continuation chain should be refactored instead of smuggled. -/
private theorem schwinger_continuation_spatial_upgrade_of_timeWitness {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ)
    (G : (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hG_time : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d k),
      OS.S k f = ∫ x : NPointDomain d k,
        G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  sorry

/-- Public OS-II-faithful base-step theorem: produce a witness on the flattened
positive-time-difference tube that is holomorphic in the time-difference variables
and continuous in the remaining variables, together with the Euclidean
reproduction identity. -/
theorem schwinger_continuation_base_step {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (G : (Fin (k * (d + 1)) → ℂ) → ℂ),
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) := by
  exact schwinger_continuation_base_step_timeParametric (d := d) OS lgc k

/-- Legacy full-holomorphic `ACR(1)` version of the base step.

This is the theorem currently consumed by the downstream restriction chain.
Mathematically, it should now be read as "time-parametric base step + a separate
spatial-upgrade step", not as the primary OS-II base-step statement. -/
private theorem schwinger_continuation_base_step_full {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  obtain ⟨G, hG_time, hG_euclid⟩ :=
    schwinger_continuation_base_step_timeParametric (d := d) OS lgc k
  exact
    schwinger_continuation_spatial_upgrade_of_timeWitness
      (d := d) OS k G hG_time hG_euclid

/-- Two-point payoff from any explicit Euclidean witness. Once a center cutoff
`χ₀` with integral `1` is fixed, the admissible Schwinger two-point family
`χ ↦ S₂(twoPointDifferenceLift χ h)` is recovered by scaling the single witness
integral at `χ₀` by `∫ χ`. This is the first concrete `k = 2` consequence on the
path to `schwinger_continuation_base_step`. -/
theorem schwinger_twoPointDifferenceLift_eq_centerWitnessIntegral
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      (∫ x : NPointDomain d 2,
          Ψ (fun i => wickRotatePoint (x i)) * (twoPointDifferenceLift χ₀ h) x) *
        ∫ y : SpacetimeDim d, χ y := by
  have hcenter :=
    OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue
      (d := d) OS h h0 χ₀ hχ₀ χ
  have hχ₀_vanish :
      VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ₀ h) :=
    twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ₀ h h0
  have hχ₀_eval :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) =
        ∫ x : NPointDomain d 2,
          Ψ (fun i => wickRotatePoint (x i)) * (twoPointDifferenceLift χ₀ h) x := by
    calc
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h))
          = ∫ x : NPointDomain d 2,
              Ψ (fun i => wickRotatePoint (x i)) *
                ((ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)).1 x) := by
            exact hΨ_euclid (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h))
      _ = ∫ x : NPointDomain d 2,
            Ψ (fun i => wickRotatePoint (x i)) * (twoPointDifferenceLift χ₀ h) x := by
            simp [hχ₀_vanish]
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))
        = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) *
            ∫ y : SpacetimeDim d, χ y := hcenter
    _ = (∫ x : NPointDomain d 2,
          Ψ (fun i => wickRotatePoint (x i)) * (twoPointDifferenceLift χ₀ h) x) *
            ∫ y : SpacetimeDim d, χ y := by
          rw [hχ₀_eval]

/-- The same two-point witness identity rewritten in center/difference
coordinates `(u, ξ) ↦ (u, u + ξ)`. This is the first production theorem that
puts the `k = 2` witness directly into the coordinates natural for the
difference-variable continuation problem. -/
theorem schwinger_twoPointDifferenceLift_eq_centerDiffWitnessIntegral
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      (∫ z : NPointDomain d 2,
          Ψ (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)) *
            (χ₀ (z 0) * h (z 1))) *
        ∫ y : SpacetimeDim d, χ y := by
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))
        = (∫ x : NPointDomain d 2,
            Ψ (fun i => wickRotatePoint (x i)) * (twoPointDifferenceLift χ₀ h) x) *
          ∫ y : SpacetimeDim d, χ y := by
            exact schwinger_twoPointDifferenceLift_eq_centerWitnessIntegral
              (d := d) OS Ψ hΨ_euclid h h0 χ₀ hχ₀ χ
    _ = (∫ z : NPointDomain d 2,
          Ψ (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)) *
            (χ₀ (z 0) * h (z 1))) *
          ∫ y : SpacetimeDim d, χ y := by
          congr 1
          simpa using
            (integral_mul_twoPointDifferenceLift_eq_centerDiff (d := d)
              (Ψ := fun x => Ψ (fun i => wickRotatePoint (x i))) (χ := χ₀) (h := h))

/-- The normalized two-point center/difference witness value is independent of
the choice of center cutoff `χ₀` with integral `1`. This is the first honest
cutoff-independence statement for the `k = 2` witness on the `E -> R` path. -/
theorem schwinger_twoPoint_centerDiffWitness_eq_of_centerIntegral_one
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ χ₁ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (hχ₁ : ∫ x : SpacetimeDim d, χ₁ x = 1) :
    (∫ z : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)) *
          (χ₀ (z 0) * h (z 1))) =
      ∫ z : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)) *
          (χ₁ (z 0) * h (z 1)) := by
  have h₀ :=
    schwinger_twoPointDifferenceLift_eq_centerDiffWitnessIntegral
      (d := d) OS Ψ hΨ_euclid h h0 χ₀ hχ₀ χ₀
  have h₁ :=
    schwinger_twoPointDifferenceLift_eq_centerDiffWitnessIntegral
      (d := d) OS Ψ hΨ_euclid h h0 χ₁ hχ₁ χ₀
  simpa [hχ₀] using h₀.symm.trans h₁

private theorem twoPointCenterDiff_toDiffFlat_wickRotate
    (z : NPointDomain d 2) :
    BHW.toDiffFlat 2 d (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)) =
      BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)) := by
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  fin_cases i
  · simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
      twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint]
  · by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint]
      ring_nf
    · simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint, hμ]

/-- Direct two-point Euclidean recovery in center/difference coordinates. For
an admissible difference-variable test `h`, the flat witness for `OS.S 2`
already evaluates the lifted test `χ(u) h(ξ)` with the same center cutoff `χ`,
not just through a normalized center family. -/
theorem schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral_sameCenter
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ : SchwartzSpacetime d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ (z 0) * h (z 1)) := by
  have hχ_vanish :
      VanishesToInfiniteOrderOnCoincidence (twoPointDifferenceLift χ h) :=
    twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ h h0
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))
        = ∫ x : NPointDomain d 2,
            G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) *
              (twoPointDifferenceLift χ h) x := by
            rw [hG_euclid (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))]
            simp [hχ_vanish]
    _ = ∫ z : NPointDomain d 2,
          (fun x => G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))))
            ((twoPointCenterDiffCLE d) z) * (χ (z 0) * h (z 1)) := by
          simpa using
            (integral_mul_twoPointDifferenceLift_eq_centerDiff (d := d)
              (Ψ := fun x => G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))))
              (χ := χ) (h := h))
    _ = ∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
            (χ (z 0) * h (z 1)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with z
          rw [twoPointCenterDiff_toDiffFlat_wickRotate]

/-- Witness-side center-value formula for the two-point flat center/difference
integral. Once a normalized center cutoff `χ₀` is fixed, every admissible
center cutoff `χ` is recovered by multiplying the normalized witness value by
`∫ χ`. -/
theorem schwinger_twoPoint_flatCenterDiffWitness_eq_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d) :
    ∫ z : NPointDomain d 2,
      G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
        (χ (z 0) * h (z 1)) =
      (∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ₀ (z 0) * h (z 1))) *
        ∫ y : SpacetimeDim d, χ y := by
  calc
    ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ (z 0) * h (z 1))
      = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
          symm
          exact schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral_sameCenter
            (d := d) OS G hG_euclid h h0 χ
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) *
          ∫ y : SpacetimeDim d, χ y := by
          exact OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue
            (d := d) (OS := OS) h h0 χ₀ hχ₀ χ
    _ = (∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
            (χ₀ (z 0) * h (z 1))) *
          ∫ y : SpacetimeDim d, χ y := by
          rw [schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral_sameCenter
            (d := d) OS G hG_euclid h h0 χ₀]

/-- If the center cutoff has integral `0`, then the two-point flat
center/difference witness integral vanishes. This is the exact witness-side
form of center-slot collapse for zero-mean test functions. -/
theorem schwinger_twoPoint_flatCenterDiffWitness_eq_zero_of_centerIntegral_zero
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d)
    (hχ : ∫ x : SpacetimeDim d, χ x = 0) :
    ∫ z : NPointDomain d 2,
      G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
        (χ (z 0) * h (z 1)) = 0 := by
  rw [schwinger_twoPoint_flatCenterDiffWitness_eq_centerValue
    (d := d) OS G hG_euclid h h0 χ₀ hχ₀ χ, hχ, mul_zero]

/-- The two-point flat center/difference witness integral is translation
invariant in the center cutoff. This is the witness-side center reduction
statement with no normalization hypothesis on `χ`. -/
theorem schwinger_twoPoint_flatCenterDiffWitness_translation_invariant
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d)
    (a : SpacetimeDim d) :
    ∫ z : NPointDomain d 2,
      G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
        (SCV.translateSchwartz a χ (z 0) * h (z 1)) =
      ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ (z 0) * h (z 1)) := by
  have htrans :
      ∫ x : SpacetimeDim d, SCV.translateSchwartz a χ x =
        ∫ x : SpacetimeDim d, χ x := by
    simpa [SCV.translateSchwartz_apply] using
      (MeasureTheory.integral_add_right_eq_self
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
        (fun x : SpacetimeDim d => χ x) a)
  rw [schwinger_twoPoint_flatCenterDiffWitness_eq_centerValue
        (d := d) OS G hG_euclid h h0 χ₀ hχ₀ (SCV.translateSchwartz a χ),
      schwinger_twoPoint_flatCenterDiffWitness_eq_centerValue
        (d := d) OS G hG_euclid h h0 χ₀ hχ₀ χ,
      htrans]

/-- The two-point flat center/difference witness depends on the center cutoff
only through its integral. This is the actual one-difference-variable `k = 2`
consequence at the witness level: for admissible `h`, the center slot has
collapsed to a single scalar factor. -/
theorem schwinger_twoPoint_flatCenterDiffWitness_exists_const
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    ∃ c : ℂ, ∀ χ : SchwartzSpacetime d,
      ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ (z 0) * h (z 1)) =
        c * ∫ y : SpacetimeDim d, χ y := by
  obtain ⟨c, hc⟩ :=
    OsterwalderSchraderAxioms.exists_const_twoPointDifferenceLift_eq_integral
      (d := d) (OS := OS) (h := h) h0
  refine ⟨c, ?_⟩
  intro χ
  calc
    ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ (z 0) * h (z 1))
      = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
          symm
          exact schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral_sameCenter
            (d := d) OS G hG_euclid h h0 χ
    _ = c * ∫ y : SpacetimeDim d, χ y := hc χ

/-- Equivalent center cutoffs, i.e. center cutoffs with the same integral, give
the same two-point flat center/difference witness integral. This is the clean
“depends only on `∫ χ`” form of center-slot collapse. -/
theorem schwinger_twoPoint_flatCenterDiffWitness_eq_of_centerIntegral_eq
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ χ₁ : SchwartzSpacetime d)
    (hint : ∫ x : SpacetimeDim d, χ₀ x = ∫ x : SpacetimeDim d, χ₁ x) :
    (∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ₀ (z 0) * h (z 1))) =
      ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ₁ (z 0) * h (z 1)) := by
  obtain ⟨c, hc⟩ :=
    schwinger_twoPoint_flatCenterDiffWitness_exists_const
      (d := d) OS G hG_euclid h h0
  calc
    ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ₀ (z 0) * h (z 1))
      = c * ∫ x : SpacetimeDim d, χ₀ x := hc χ₀
    _ = c * ∫ x : SpacetimeDim d, χ₁ x := by rw [hint]
    _ = ∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
            (χ₁ (z 0) * h (z 1)) := by
          symm
          exact hc χ₁

/-- Two-point payoff in the actual flattened-difference witness coordinates used
by `schwinger_continuation_base_step`. If `G` is a flat witness for `OS.S 2`,
then on center/difference test functions the witness depends on `(u, ξ)` only
through the flattened wick-rotated pair `(wick(u), wick(ξ))`. -/
theorem schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (χ : SchwartzSpacetime d) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      (∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
            (χ₀ (z 0) * h (z 1))) *
        ∫ y : SpacetimeDim d, χ y := by
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))
        = (∫ z : NPointDomain d 2,
            (fun x => G (BHW.toDiffFlat 2 d x))
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)) *
              (χ₀ (z 0) * h (z 1))) *
          ∫ y : SpacetimeDim d, χ y := by
            exact schwinger_twoPointDifferenceLift_eq_centerDiffWitnessIntegral
              (d := d) OS
              (Ψ := fun x => G (BHW.toDiffFlat 2 d x))
              (hΨ_euclid := hG_euclid) h h0 χ₀ hχ₀ χ
    _ = (∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
            (χ₀ (z 0) * h (z 1))) *
          ∫ y : SpacetimeDim d, χ y := by
          congr 1
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with z
          rw [twoPointCenterDiff_toDiffFlat_wickRotate]

/-- Flat-witness cutoff independence for the two-point center/difference
formula. This is the `k = 2` version of saying the normalized center slot has
already descended to a genuine witness in the difference variable. -/
theorem schwinger_twoPoint_flatCenterDiffWitness_eq_of_centerIntegral_one
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ₀ χ₁ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (hχ₁ : ∫ x : SpacetimeDim d, χ₁ x = 1) :
    (∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ₀ (z 0) * h (z 1))) =
      ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ₁ (z 0) * h (z 1)) := by
  have h₀ :=
    schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral
      (d := d) OS G hG_euclid h h0 χ₀ hχ₀ χ₀
  have h₁ :=
    schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral
      (d := d) OS G hG_euclid h h0 χ₁ hχ₁ χ₀
  simpa [hχ₀] using h₀.symm.trans h₁

/-- For any normalized center cutoff `χ` with `∫ χ = 1`, the two-point
Schwinger value is exactly the corresponding flat center/difference witness
integral with the same cutoff inserted in the center slot. -/
theorem schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral_of_centerIntegral_one
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ : SchwartzSpacetime d)
    (hχ : ∫ x : SpacetimeDim d, χ x = 1) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ (z 0) * h (z 1)) := by
  simpa [hχ] using
    (schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral
      (d := d) OS G hG_euclid h h0 χ hχ χ)

/-- The normalized flat center/difference witness value is translation-invariant
in the center slot. This is the witness-side form of the two-point Schwinger
translation reduction after collapsing to the flat BHW coordinates. -/
theorem schwinger_twoPoint_flatCenterDiffWitness_translation_invariant_of_centerIntegral_one
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ))
    (χ : SchwartzSpacetime d)
    (hχ : ∫ x : SpacetimeDim d, χ x = 1)
    (a : SpacetimeDim d) :
    ∫ z : NPointDomain d 2,
      G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
        (SCV.translateSchwartz a χ (z 0) * h (z 1)) =
      ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (χ (z 0) * h (z 1)) := by
  have htrans : ∫ x : SpacetimeDim d, SCV.translateSchwartz a χ x = 1 := by
    rw [show ∫ x : SpacetimeDim d, SCV.translateSchwartz a χ x =
        ∫ x : SpacetimeDim d, χ x by
          simpa [SCV.translateSchwartz_apply] using
            (MeasureTheory.integral_add_right_eq_self
              (μ := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
              (fun x : SpacetimeDim d => χ x) a)]
    exact hχ
  calc
    ∫ z : NPointDomain d 2,
        G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
          (SCV.translateSchwartz a χ (z 0) * h (z 1))
      = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift (SCV.translateSchwartz a χ) h)) := by
            symm
            exact schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral_of_centerIntegral_one
              (d := d) OS G hG_euclid h h0 (SCV.translateSchwartz a χ) htrans
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
          exact (OsterwalderSchraderAxioms.schwinger_twoPointDifferenceLift_translation_invariant
            (d := d) (OS := OS) (a := a) (χ := χ) (h := h) h0).symm
    _ = ∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
            (χ (z 0) * h (z 1)) := by
          exact schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral_of_centerIntegral_one
            (d := d) OS G hG_euclid h h0 χ hχ

/-- **ξ-shift: the correct one-variable perturbation in the cumulative-sum structure.**

    In the cumulative-sum parametrization, the j-th new variable at level r is
      ξ[j] = z[j][r] - (if j = 0 then 0 else z[j-1][r])
    These k variables ξ[0], ..., ξ[k-1] are INDEPENDENT:
      C_k^(r+1) = C_k^(r) × UHP^k  (in the (z_base, ξ) parametrization).

    Moving ξ[j] by t (holding ξ[i] fixed for i ≠ j) requires shifting ALL z[i][r]
    for i ≥ j by +t simultaneously, since z[i][r] = ξ[0] + ... + ξ[i] (cumulative sum).

    WARNING: Updating only z[j][r] while keeping z[j+1][r],...,z[k-1][r] fixed changes
    BOTH ξ[j] (by +t) AND ξ[j+1] (by -t), which is NOT a single-variable extension.
    The test case in `test/acr_next_steps_test.lean` (d=1, k=2, r=1) confirms that a
    single-coordinate update can FAIL to land in ACR(r+1). -/
def xiShift {k d : ℕ} (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (t : ℂ) : Fin k → Fin (d + 1) → ℂ :=
  fun i μ => if j.val ≤ i.val ∧ μ = r then z i μ + t else z i μ

/-- Shifting a cumulative-difference slice by zero does nothing. -/
private theorem xiShift_zero {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) :
    xiShift j r z 0 = z := by
  ext i μ
  by_cases h : j ≤ i ∧ μ = r
  · simp [xiShift, h]
  · simp [xiShift, h]

/-- Successive ξ-shifts in the same cumulative-difference coordinate add. -/
private theorem xiShift_add_same {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (s t : ℂ) :
    xiShift j r (xiShift j r z s) t = xiShift j r z (s + t) := by
  ext i μ
  by_cases h : j ≤ i ∧ μ = r
  · simp [xiShift, h, add_assoc]
  · simp [xiShift, h]

/-- In flattened difference coordinates, `xiShift` changes exactly one coordinate:
the `(j,r)` difference variable is translated by `t`, and all other difference
coordinates stay fixed. This is the concrete bookkeeping fact behind the
one-variable slice picture used in analytic continuation. -/
private theorem toDiffFlat_xiShift_eq_update {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (t : ℂ) :
    BHW.toDiffFlat k d (xiShift j r z t) =
      Function.update (BHW.toDiffFlat k d z) (finProdFinEquiv (j, r))
        (BHW.toDiffFlat k d z (finProdFinEquiv (j, r)) + t) := by
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  simp only [BHW.toDiffFlat, BHW.flattenCfg]
  simp only [finProdFinEquiv.symm_apply_apply]
  have hflat :
      BHW.flattenCfg k d (BHW.diffCoordEquiv k d z) (finProdFinEquiv (i, μ)) =
        BHW.diffCoordEquiv k d z i μ := by
    simp [BHW.flattenCfg]
  by_cases hμ : μ = r
  · subst hμ
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i.val = 0
      · simp [Function.update, BHW.diffCoordEquiv_apply, xiShift, hi0]
      · have hpred_not : ¬ i.val ≤ i.val - 1 := by omega
        simp [Function.update, BHW.diffCoordEquiv_apply, xiShift, hi0, hpred_not]
        ring
    · by_cases hij_lt : i.val < j.val
      · have hneq : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (j, μ) := by
          intro h
          apply hij
          exact congrArg Prod.fst (finProdFinEquiv.injective h)
        have hj_not_le : ¬ j.val ≤ i.val := not_le.mpr hij_lt
        by_cases hi0 : i.val = 0
        · have hj0 : j.val ≠ 0 := by omega
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj0]
        · have hpred_not : ¬ j.val ≤ i.val - 1 := by omega
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj_not_le, hpred_not]
      · have hj_le : j.val ≤ i.val := le_of_not_gt hij_lt
        by_cases hi0 : i.val = 0
        · have : False := by
            apply hij
            exact Fin.ext (by omega)
          exact False.elim this
        · have hneq : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (j, μ) := by
            intro h
            apply hij
            exact congrArg Prod.fst (finProdFinEquiv.injective h)
          have hpred : j.val ≤ i.val - 1 := by omega
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj_le, hpred]
  · have hneq : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (j, r) := by
      intro h
      apply hμ
      exact congrArg Prod.snd (finProdFinEquiv.injective h)
    by_cases hi0 : i.val = 0
    · simp [Function.update, hneq]
      rw [hflat]
      simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hμ]
    · by_cases hj_le : j.val ≤ i.val
      · by_cases hpred : j.val ≤ i.val - 1
        · simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hμ, hj_le, hpred]
        · have hji : j = i := by
            apply Fin.ext
            omega
          subst hji
          simp [Function.update, hneq]
          rw [hflat]
          simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hμ]
      · simp [Function.update, hneq]
        rw [hflat]
        simp [BHW.diffCoordEquiv_apply, xiShift, hi0, hj_le, hμ]

/-- Inverse-chart form of `toDiffFlat_xiShift_eq_update`: updating exactly the
flattened difference coordinate `(j,r)` by `+ t` reconstructs the configuration
obtained from `xiShift j r` by the same increment. -/
private theorem fromDiffFlat_update_eq_xiShift {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (u : Fin (k * (d + 1)) → ℂ) (t : ℂ) :
    BHW.fromDiffFlat k d
        (Function.update u (finProdFinEquiv (j, r))
          (u (finProdFinEquiv (j, r)) + t)) =
      xiShift j r (BHW.fromDiffFlat k d u) t := by
  have hinj : Function.Injective (BHW.toDiffFlat k d) := by
    intro z₁ z₂ h
    simpa [BHW.fromDiffFlat_toDiffFlat (n := k) (d := d) z₁,
      BHW.fromDiffFlat_toDiffFlat (n := k) (d := d) z₂] using
      congrArg (BHW.fromDiffFlat k d) h
  apply hinj
  rw [BHW.toDiffFlat_fromDiffFlat]
  rw [toDiffFlat_xiShift_eq_update]
  simp [BHW.toDiffFlat_fromDiffFlat]

/-- Affine version of `fromDiffFlat_update_eq_xiShift`: replacing the flattened
coordinate `(j,r)` by an arbitrary value `w` corresponds to `xiShift` by the
increment `w - u(j,r)`. This is the form used by one-variable slice maps
written with `Function.update`. -/
theorem fromDiffFlat_update_eq_xiShift_sub {k d : ℕ}
    (j : Fin k) (r : Fin (d + 1))
    (u : Fin (k * (d + 1)) → ℂ) (w : ℂ) :
    BHW.fromDiffFlat k d
        (Function.update u (finProdFinEquiv (j, r)) w) =
      xiShift j r (BHW.fromDiffFlat k d u)
        (w - u (finProdFinEquiv (j, r))) := by
  rw [← fromDiffFlat_update_eq_xiShift (j := j) (r := r) (u := u)
    (t := w - u (finProdFinEquiv (j, r)))]
  congr 1
  ext q
  by_cases hq : q = finProdFinEquiv (j, r)
  · subst hq
    simp [Function.update]
  · simp [Function.update, hq]

/-- Tail Euclidean time shift starting at index `j`: points with index `i ≥ j`
are shifted by the real time vector `timeShiftVec d t`, earlier points are fixed. -/
private def tailTimeShiftConfig {d k : ℕ} (j : Fin k) (t : ℝ)
    (x : NPointDomain d k) : NPointDomain d k :=
  fun i => if j.val ≤ i.val then x i + timeShiftVec d t else x i

/-- Sign-correct inverse form of `osConjTensorProduct_timeShift_eq_tailShift`.
A positive tail shift of the right block corresponds to a negative time shift on
the right Schwartz factor. This fixes the sign convention needed when a flat
coordinate update by `+ t * I` is converted back to the OS semigroup picture. -/
private theorem osConjTensorProduct_tailTimeShift_eq_timeShift {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (hm : 0 < m) (t : ℝ)
    (x : NPointDomain d (n + m)) :
    (f.osConjTensorProduct g)
        (tailTimeShiftConfig (d := d) ⟨n, by omega⟩ t x) =
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (-t) g)) x := by
  have htail :=
    osConjTensorProduct_timeShift_eq_tailShift (d := d) f g (-t) x
  have hneg_shift : -timeShiftVec d (-t) = timeShiftVec d t := by
    ext μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeShiftVec]
    · simp [timeShiftVec, hμ]
  have hcfg :
      (fun i => if h : n ≤ i.val then x i - timeShiftVec d (-t) else x i) =
        tailTimeShiftConfig (d := d) ⟨n, by omega⟩ t x := by
    funext i
    by_cases hi : n ≤ i.val
    · simp [tailTimeShiftConfig, hi, sub_eq_add_neg, hneg_shift]
    · simp [tailTimeShiftConfig, hi]
  rw [hcfg] at htail
  exact htail.symm

/-- Forward form of `osConjTensorProduct_tailTimeShift_eq_timeShift`: a positive
time shift on the right Schwartz factor is evaluation of the unshifted tensor
product on the configuration with the right block shifted by `- timeShiftVec d t`.
Written with `tailTimeShiftConfig`, this is the form that matches a flat update
by `- t * I`. -/
private theorem osConjTensorProduct_timeShift_eq_tailTimeShift {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (hm : 0 < m) (t : ℝ)
    (x : NPointDomain d (n + m)) :
    (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      (f.osConjTensorProduct g)
        (tailTimeShiftConfig (d := d) ⟨n, by omega⟩ (-t) x) := by
  simpa using
    (osConjTensorProduct_tailTimeShift_eq_timeShift
      (d := d) (f := f) (g := g) (hm := hm) (t := -t) (x := x)).symm

/-- Tail translation of the right block preserves Lebesgue measure on configuration
space. This is the change-of-variables ingredient for converting the sign-correct
flat-update slice picture back to the Euclidean integral. -/
private theorem rightBlockTailShift_measurePreserving {n m : ℕ}
    (hm : 0 < m) (t : ℝ) :
    MeasureTheory.MeasurePreserving
      (tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t)
      MeasureTheory.volume MeasureTheory.volume := by
  classical
  rw [show tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t =
      (fun (x : NPointDomain d (n + m)) (i : Fin (n + m)) =>
        (if h : n ≤ i.val then fun y : SpacetimeDim d => y + timeShiftVec d t else id) (x i)) by
      funext x i
      by_cases h : n ≤ i.val <;> simp [tailTimeShiftConfig, h]]
  exact MeasureTheory.volume_preserving_pi
    (fun i : Fin (n + m) => by
      by_cases h : n ≤ i.val
      · simpa [h] using
          (MeasureTheory.measurePreserving_add_right
            (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))
            (timeShiftVec d t))
      · simpa [h] using
          (MeasureTheory.MeasurePreserving.id
            (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))))

/-- The right-block tail shift is a measurable equivalence, with inverse given by
shifting the same tail by `-t`. This packages the change of variables needed in
the Euclidean integral form of the slice identity. -/
private def rightBlockTailShiftMeasurableEquiv {n m : ℕ}
    (hm : 0 < m) (t : ℝ) :
    NPointDomain d (n + m) ≃ᵐ NPointDomain d (n + m) where
  toEquiv :=
    { toFun := tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t
      invFun := tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ (-t)
      left_inv := by
        intro x
        ext i μ
        by_cases hi : n ≤ i.val
        · by_cases hμ : μ = 0
          · subst hμ
            simp [tailTimeShiftConfig, hi, timeShiftVec]
          · simp [tailTimeShiftConfig, hi, timeShiftVec, hμ]
        · simp [tailTimeShiftConfig, hi]
      right_inv := by
        intro x
        ext i μ
        by_cases hi : n ≤ i.val
        · by_cases hμ : μ = 0
          · subst hμ
            simp [tailTimeShiftConfig, hi, timeShiftVec]
          · simp [tailTimeShiftConfig, hi, timeShiftVec, hμ]
        · simp [tailTimeShiftConfig, hi] }
  measurable_toFun := by
    unfold tailTimeShiftConfig
    exact measurable_pi_lambda _ (fun i => by
      by_cases h : n ≤ i.val
      · simp [h]
        exact (measurable_pi_apply i).add measurable_const
      · simpa [h] using (measurable_pi_apply i))
  measurable_invFun := by
    unfold tailTimeShiftConfig
    exact measurable_pi_lambda _ (fun i => by
      by_cases h : n ≤ i.val
      · simp [h]
        exact (measurable_pi_apply i).add measurable_const
      · simpa [h] using (measurable_pi_apply i))

/-- Change of variables under the right-block tail shift. Combined with the
sign-correct pointwise bridge lemmas above, this is the generic integral shell
needed for the remaining `schwinger_continuation_base_step` slice theorem. -/
private theorem integral_comp_rightBlockTailShift {n m : ℕ}
    (hm : 0 < m) (t : ℝ)
    {e : NPointDomain d (n + m) → ℂ} :
    ∫ x, e (tailTimeShiftConfig (d := d) ⟨n, Nat.lt_add_of_pos_right hm⟩ t x) =
      ∫ x, e x := by
  let Ψ := rightBlockTailShiftMeasurableEquiv (d := d) (n := n) (m := m) hm t
  have hmp : MeasureTheory.MeasurePreserving
      (Ψ : NPointDomain d (n + m) → NPointDomain d (n + m))
      MeasureTheory.volume MeasureTheory.volume := by
    simpa [Ψ] using rightBlockTailShift_measurePreserving (d := d) (n := n) (m := m) hm t
  exact hmp.integral_comp' (f := Ψ) e

/-- On Wick-rotated Euclidean configurations, the complex ξ-shift in the time
difference coordinate `(j,0)` is exactly the Wick rotation of a real tail time
shift on the underlying Euclidean configuration. -/
private theorem xiShift_wickRotate_eq_tailTimeShift {d k : ℕ}
    (j : Fin k) (x : NPointDomain d k) (t : ℝ) :
    xiShift j 0 (fun i => wickRotatePoint (x i)) ((t : ℂ) * Complex.I) =
      fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j t x i) := by
  ext i μ
  by_cases hji : j.val ≤ i.val
  · by_cases hμ : μ = 0
    · subst hμ
      simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint, timeShiftVec]
      ring
    · simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint, timeShiftVec, hμ]
  · by_cases hμ : μ = 0
    · subst hμ
      simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint]
    · simp [xiShift, tailTimeShiftConfig, hji, wickRotatePoint, hμ]

/-- Flattened-difference form of `xiShift_wickRotate_eq_tailTimeShift`: a flat
update by `+ t I` in the `(j,0)` coordinate is exactly the Wick-rotated tail
time shift on Euclidean configurations. This is the coordinate bridge from flat
slice updates back to the OS semigroup picture. -/
private theorem toDiffFlat_wickRotate_tailTimeShift_eq_update {d k : ℕ}
    (j : Fin k) (x : NPointDomain d k) (t : ℝ) :
    BHW.toDiffFlat k d (fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j t x i)) =
      Function.update
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i)))
        (finProdFinEquiv (j, 0))
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i))
          (finProdFinEquiv (j, 0)) + (t : ℂ) * Complex.I) := by
  rw [← xiShift_wickRotate_eq_tailTimeShift (d := d) (j := j) (x := x) (t := t)]
  simpa using
    toDiffFlat_xiShift_eq_update (j := j) (r := (0 : Fin (d + 1)))
      (z := fun i => wickRotatePoint (x i)) (t := (t : ℂ) * Complex.I)

/-- Sign-correct specialization of `toDiffFlat_wickRotate_tailTimeShift_eq_update`:
shifting the Euclidean tail by `-t` corresponds to updating the flattened time
difference coordinate by `- t * I`. This is the form aligned with the positive
OS semigroup parameter in `timeShiftSchwartzNPoint t`. -/
private theorem toDiffFlat_wickRotate_tailTimeShift_eq_update_sub {d k : ℕ}
    (j : Fin k) (x : NPointDomain d k) (t : ℝ) :
    BHW.toDiffFlat k d (fun i => wickRotatePoint (tailTimeShiftConfig (d := d) j (-t) x i)) =
      Function.update
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i)))
        (finProdFinEquiv (j, 0))
        (BHW.toDiffFlat k d (fun i => wickRotatePoint (x i))
          (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    toDiffFlat_wickRotate_tailTimeShift_eq_update (d := d) (j := j) (x := x) (-t)

/-- Generic simple-tensor slice identity under the Euclidean integral. A positive
time shift on the right Schwartz factor is converted into a flat update by
`- t * I` in the split time-difference coordinate, with the intervening tail
translation absorbed by `integral_comp_rightBlockTailShift`. This is the core
integral shell for the remaining `schwinger_continuation_base_step` assembly. -/
private theorem simpleTensor_flatUpdate_integral_eq {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Φ : (Fin ((n + m) * (d + 1)) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
        Φ (Function.update
          (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
          (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0))
          (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
            (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0)) - (t : ℂ) * Complex.I)) =
      ∫ y : NPointDomain d (n + m),
        (f.osConjTensorProduct g) y *
          Φ (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (y i))) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let e : NPointDomain d (n + m) → ℂ := fun y =>
    (f.osConjTensorProduct g) y *
      Φ (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (y i)))
  have hshell :
      ∀ x : NPointDomain d (n + m),
        e (tailTimeShiftConfig (d := d) j (-t) x) =
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
            Φ (Function.update
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
              (finProdFinEquiv (j, 0))
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
                (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I)) := by
    intro x
    unfold e
    rw [toDiffFlat_wickRotate_tailTimeShift_eq_update_sub (d := d) (j := j) (x := x) (t := t)]
    rw [osConjTensorProduct_timeShift_eq_tailTimeShift
      (d := d) (f := f) (g := g) (hm := hm) (t := t) (x := x)]
  calc
    ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Φ (Function.update
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
            (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0))
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
              (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0)) - (t : ℂ) * Complex.I)) =
      ∫ x : NPointDomain d (n + m), e (tailTimeShiftConfig (d := d) j (-t) x) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        simpa [j] using (hshell x).symm
    _ = ∫ x : NPointDomain d (n + m), e x := by
        simpa [j] using
          (integral_comp_rightBlockTailShift (d := d) (n := n) (m := m) (hm := hm)
            (t := -t) (e := e))
    _ = ∫ y : NPointDomain d (n + m),
          (f.osConjTensorProduct g) y *
            Φ (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (y i))) := by
        rfl

/-- Configuration-space form of `simpleTensor_flatUpdate_integral_eq`: composing
the flat update with `fromDiffFlat` yields the same Euclidean slice identity. -/
private theorem simpleTensor_fromDiffFlatUpdate_integral_eq {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
        Ψ (BHW.fromDiffFlat (n + m) d
          (Function.update
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
            (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0))
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
              (finProdFinEquiv (⟨n, Nat.lt_add_of_pos_right hm⟩, 0)) - (t : ℂ) * Complex.I))) =
      ∫ y : NPointDomain d (n + m),
        (f.osConjTensorProduct g) y * Ψ (fun i => wickRotatePoint (y i)) := by
  simpa [Function.comp_apply, BHW.fromDiffFlat_toDiffFlat] using
    (simpleTensor_flatUpdate_integral_eq (d := d) (n := n) (m := m)
      (hm := hm) (f := f) (g := g) (t := t)
      (Φ := Ψ ∘ BHW.fromDiffFlat (n + m) d))

/-- Integrated ξ-shift form of the simple-tensor slice identity. A flat update by
`- t * I` in the split time-difference coordinate is exactly the same Euclidean
integral as the positive right-factor time shift. -/
private theorem simpleTensor_xiShift_integral_eq {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (x i)) (-(t : ℂ) * Complex.I)) =
      ∫ y : NPointDomain d (n + m),
        (f.osConjTensorProduct g) y * Ψ (fun i => wickRotatePoint (y i)) := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  have hslice :
      ∀ x : NPointDomain d (n + m),
        BHW.fromDiffFlat (n + m) d
          (Function.update
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
            (finProdFinEquiv (j, 0))
            (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
              (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I)) =
          xiShift j 0 (fun i => wickRotatePoint (x i)) (-(t : ℂ) * Complex.I) := by
    intro x
    let u : Fin ((n + m) * (d + 1)) → ℂ :=
      BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
    simpa [u, sub_eq_add_neg, BHW.fromDiffFlat_toDiffFlat] using
      (fromDiffFlat_update_eq_xiShift (j := j) (r := (0 : Fin (d + 1)))
        (u := u) (t := -(t : ℂ) * Complex.I))
  calc
    ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (x i)) (-(t : ℂ) * Complex.I)) =
      ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Ψ (BHW.fromDiffFlat (n + m) d
            (Function.update
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i)))
              (finProdFinEquiv (j, 0))
              (BHW.toDiffFlat (n + m) d (fun i => wickRotatePoint (x i))
                (finProdFinEquiv (j, 0)) - (t : ℂ) * Complex.I))) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        rw [hslice x]
    _ = ∫ y : NPointDomain d (n + m),
          (f.osConjTensorProduct g) y * Ψ (fun i => wickRotatePoint (y i)) := by
        simpa [j] using
          (simpleTensor_fromDiffFlatUpdate_integral_eq (d := d) (n := n) (m := m)
            (hm := hm) (f := f) (g := g) (t := t) (Ψ := Ψ))

/-- Witness-side version of `simpleTensor_xiShift_integral_eq`: moving the positive
right-factor time shift from the Schwartz tensor term to the Euclidean witness
changes the witness by `+ t * I` in the split time-difference coordinate. -/
theorem simpleTensor_timeShift_integral_eq_xiShift {n m : ℕ}
    (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (t : ℝ)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ) :
    ∫ x : NPointDomain d (n + m),
      Ψ (fun i => wickRotatePoint (x i)) *
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      ∫ y : NPointDomain d (n + m),
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  have hcancel : (-(t : ℂ) * Complex.I) + (t : ℂ) * Complex.I = 0 := by
    ring
  calc
    ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) *
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x =
      ∫ x : NPointDomain d (n + m),
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x *
          Ψ (fun i => wickRotatePoint (x i)) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        simp [mul_comm]
    _ = ∫ y : NPointDomain d (n + m),
          (f.osConjTensorProduct g) y *
            Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) := by
        simpa [j, xiShift_add_same, xiShift_zero, hcancel] using
          (simpleTensor_xiShift_integral_eq (d := d) (n := n) (m := m)
            (hm := hm) (f := f) (g := g) (t := t)
            (Ψ := fun z =>
              Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z
                ((t : ℂ) * Complex.I))))
    _ = ∫ y : NPointDomain d (n + m),
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with y
        simp [mul_comm]

/-- If a Euclidean witness `Ψ` recovers `OS.S (n+m)` on zero-diagonal tests, then
the positive right-factor time shift of a simple tensor is recovered by the same
witness evaluated on the `+ t * I` ξ-shifted Euclidean configuration. This is the
direct `OS.S`-level slice identity needed before the finite-sum `ExpandBoth`
assembly in `schwinger_continuation_base_step`. -/
theorem schwinger_simpleTensor_timeShift_eq_xiShift {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (hm : 0 < m)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d (n + m)),
      OS.S (n + m) h = ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (t : ℝ) (ht : 0 < t) :
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) =
      ∫ y : NPointDomain d (n + m),
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
  have hg_shift_ord :
      tsupport ((timeShiftSchwartzNPoint (d := d) t g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m := by
    exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
      (d := d) t ht g hg_ord
  have hvanish_shift :
      VanishesToInfiniteOrderOnCoincidence
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (f := f) (g := timeShiftSchwartzNPoint (d := d) t g) hf_ord hg_shift_ord
  calc
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) =
      ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) *
          ((ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))).1 x) := by
        exact hΨ_euclid (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
    _ = ∫ x : NPointDomain d (n + m),
          Ψ (fun i => wickRotatePoint (x i)) *
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x := by
        simp [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes, hvanish_shift]
    _ = ∫ y : NPointDomain d (n + m),
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y := by
        exact simpleTensor_timeShift_integral_eq_xiShift
          (d := d) (n := n) (m := m) (hm := hm) (f := f) (g := g) (t := t) (Ψ := Ψ)

/-- Concentrated-right-factor finite-sum Euclidean recovery. For a fixed split point
`m > 0`, the positive-real restriction of the one-variable OS holomorphic matrix
element against a concentrated right factor is the finite sum of the corresponding
`ξ`-shifted Euclidean witnesses over the left Borchers components. This is the first
genuine finite-sum upgrade of `schwinger_simpleTensor_timeShift_eq_xiShift`. -/
theorem OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single_xiShift_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (N : ℕ) → (Fin N → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (N : ℕ) (h : ZeroDiagonalSchwartz d N),
      OS.S N h = ∫ x : NPointDomain d N,
        Ψ N (fun i => wickRotatePoint (x i)) * (h.1 x))
    (F : PositiveTimeBorchersSequence d)
    {m : ℕ} (hm : 0 < m)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
      ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        ∫ y : NPointDomain d (n + m),
          Ψ (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (((F : BorchersSequence d).funcs n).osConjTensorProduct g) y := by
  rw [OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single
    (d := d) (OS := OS) (lgc := lgc) (F := F)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact) (t := t) ht]
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact schwinger_simpleTensor_timeShift_eq_xiShift
    (d := d) (OS := OS) (hm := hm) (Ψ := Ψ (n + m))
    (hΨ_euclid := hΨ_euclid (n + m))
    (f := ((F : BorchersSequence d).funcs n))
    (hf_ord := F.ordered_tsupport n)
    (g := g) (hg_ord := hg_ord) (t := t) ht

/-- Single-split Euclidean recovery before the `ξ`-shift rewrite. On positive real
points, the concentrated `ExpandBoth` term agrees with the direct Euclidean integral
against the time-shifted simple tensor. This branch is needed in the `m = 0` case,
where there is no split time-difference variable to shift. -/
private theorem OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_euclid
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d (n + m)),
      OS.S (n + m) h = ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
      ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) *
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x := by
  have hreal :
      OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
    rw [OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
      (d := d) (OS := OS) (lgc := lgc)
      (F := PositiveTimeBorchersSequence.single n f hf_ord)
      (G := PositiveTimeBorchersSequence.single m g hg_ord)
      (hG_compact := by
        intro k
        by_cases hk : k = m
        · subst hk
          simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
        · have hzero :
            ((((PositiveTimeBorchersSequence.single m g hg_ord : PositiveTimeBorchersSequence d) :
                BorchersSequence d).funcs k : SchwartzNPoint d k) :
              NPointDomain d k → ℂ) = 0 := by
            simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
              BorchersSequence.single, hk]
          rw [hzero]
          simpa using (HasCompactSupport.zero :
            HasCompactSupport (0 : NPointDomain d k → ℂ)))
      (t := t) ht]
    simp only [PositiveTimeBorchersSequence.single_toBorchersSequence]
    have hshift_single :
        ∀ k,
          (timeShiftBorchers (d := d) t (BorchersSequence.single m g)).funcs k =
            (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)).funcs k := by
      intro k
      by_cases hk : k = m
      · subst hk
        simp [BorchersSequence.single]
      · simp [BorchersSequence.single, hk]
    calc
      OSInnerProduct d OS.S (BorchersSequence.single n f)
          (timeShiftBorchers (d := d) t (BorchersSequence.single m g)) =
        OSInnerProduct d OS.S (BorchersSequence.single n f)
          (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)) := by
            exact OSInnerProduct_congr_right d OS.S OS.E0_linear
              (BorchersSequence.single n f)
              (timeShiftBorchers (d := d) t (BorchersSequence.single m g))
              (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g))
              hshift_single
      _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
            simpa using
              (OSInnerProduct_single_single d OS.S OS.E0_linear n m f
                (timeShiftSchwartzNPoint (d := d) t g))
  have hg_shift_ord :
      tsupport ((timeShiftSchwartzNPoint (d := d) t g : SchwartzNPoint d m) :
        NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m := by
    exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
      (d := d) t ht g hg_ord
  have hvanish_shift :
      VanishesToInfiniteOrderOnCoincidence
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := by
    exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (f := f) (g := timeShiftSchwartzNPoint (d := d) t g) hf_ord hg_shift_ord
  calc
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := hreal
    _ = ∫ x : NPointDomain d (n + m),
          Ψ (fun i => wickRotatePoint (x i)) *
            ((ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))).1 x) := by
        exact hΨ_euclid (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
    _ = ∫ x : NPointDomain d (n + m),
          Ψ (fun i => wickRotatePoint (x i)) *
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) x := by
        simp [hvanish_shift]

/-- Single-split bridge from the semigroup-side holomorphic term to the Euclidean
ξ-shift witness. On positive real points, the public `ExpandBoth` value for
concentrated left/right Borchers sequences matches the corresponding shifted
simple-tensor Schwinger term, which is then rewritten by
`schwinger_simpleTensor_timeShift_eq_xiShift`. This is the first production theorem
that directly connects the one-variable OS holomorphic family to the Euclidean
slice witness used in `schwinger_continuation_base_step`. -/
theorem OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d (n + m)),
      OS.S (n + m) h = ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
      ∫ y : NPointDomain d (n + m),
        Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
  have hreal :
      OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
    rw [OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
      (d := d) (OS := OS) (lgc := lgc)
      (F := PositiveTimeBorchersSequence.single n f hf_ord)
      (G := PositiveTimeBorchersSequence.single m g hg_ord)
      (hG_compact := by
        intro k
        by_cases hk : k = m
        · subst hk
          simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
        · have hzero :
            ((((PositiveTimeBorchersSequence.single m g hg_ord : PositiveTimeBorchersSequence d) :
                BorchersSequence d).funcs k : SchwartzNPoint d k) :
              NPointDomain d k → ℂ) = 0 := by
            simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
              BorchersSequence.single, hk]
          rw [hzero]
          simpa using (HasCompactSupport.zero :
            HasCompactSupport (0 : NPointDomain d k → ℂ)))
      (t := t) ht]
    simp only [PositiveTimeBorchersSequence.single_toBorchersSequence]
    have hshift_single :
        ∀ k,
          (timeShiftBorchers (d := d) t (BorchersSequence.single m g)).funcs k =
            (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)).funcs k := by
      intro k
      by_cases hk : k = m
      · subst hk
        simp [BorchersSequence.single]
      · simp [BorchersSequence.single, hk]
    calc
      OSInnerProduct d OS.S (BorchersSequence.single n f)
          (timeShiftBorchers (d := d) t (BorchersSequence.single m g)) =
        OSInnerProduct d OS.S (BorchersSequence.single n f)
          (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g)) := by
            exact OSInnerProduct_congr_right d OS.S OS.E0_linear
              (BorchersSequence.single n f)
              (timeShiftBorchers (d := d) t (BorchersSequence.single m g))
              (BorchersSequence.single m (timeShiftSchwartzNPoint (d := d) t g))
              hshift_single
      _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
            simpa using
              (OSInnerProduct_single_single d OS.S OS.E0_linear n m f
                (timeShiftSchwartzNPoint (d := d) t g))
  exact hreal.trans <|
    schwinger_simpleTensor_timeShift_eq_xiShift (d := d) (OS := OS)
      (hm := hm) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) (t := t) ht

/-- Finite double-sum Euclidean recovery for `ExpandBoth` on positive real points.
Each summand is rewritten honestly according to whether the right block contributes
a genuine time-difference variable (`m > 0`) or is the vacuum branch (`m = 0`). -/
theorem OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_piecewise_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (N : ℕ) → (Fin N → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (N : ℕ) (h : ZeroDiagonalSchwartz d N),
      OS.S N h = ∫ x : NPointDomain d N,
        Ψ N (fun i => wickRotatePoint (x i)) * (h.1 x))
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((
        G : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G (t : ℂ) =
      ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
          if hm : 0 < m then
            ∫ y : NPointDomain d (n + m),
              Ψ (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (((F : BorchersSequence d).funcs n).osConjTensorProduct
                  ((G : BorchersSequence d).funcs m)) y
          else
            ∫ y : NPointDomain d (n + m),
              Ψ (n + m) (fun i => wickRotatePoint (y i)) *
                (((F : BorchersSequence d).funcs n).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))) y := by
  unfold OSInnerProductTimeShiftHolomorphicValueExpandBoth
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro m hm_range
  by_cases hm : 0 < m
  · simp [hm]
    calc
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m)) (t : ℂ) =
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          ((((F : BorchersSequence d).funcs n).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs m))))) := by
            exact OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
              (d := d) (OS := OS) (lgc := lgc)
              (f := ((F : BorchersSequence d).funcs n))
              (hf_ord := F.ordered_tsupport n)
              (g := ((G : BorchersSequence d).funcs m))
              (hg_ord := G.ordered_tsupport m)
              (hg_compact := hG_compact m)
              (t := t) ht
      _ = ∫ y : NPointDomain d (n + m),
            Ψ (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (((F : BorchersSequence d).funcs n).osConjTensorProduct
                ((G : BorchersSequence d).funcs m)) y := by
            exact schwinger_simpleTensor_timeShift_eq_xiShift
              (d := d) (OS := OS) (hm := hm) (Ψ := Ψ (n + m))
              (hΨ_euclid := hΨ_euclid (n + m))
              (f := ((F : BorchersSequence d).funcs n))
              (hf_ord := F.ordered_tsupport n)
              (g := ((G : BorchersSequence d).funcs m))
              (hg_ord := G.ordered_tsupport m)
              (t := t) ht
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst hm0
    simp
    have hg_shift_ord :
        tsupport
            ((timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0) :
                SchwartzNPoint d 0) : NPointDomain d 0 → ℂ) ⊆
          OrderedPositiveTimeRegion d 0 := by
      exact timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
        (d := d) t ht ((G : BorchersSequence d).funcs 0) (G.ordered_tsupport 0)
    have hvanish_shift :
        VanishesToInfiniteOrderOnCoincidence
          (((F : BorchersSequence d).funcs n).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0))) := by
      exact
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
          (f := ((F : BorchersSequence d).funcs n))
          (g := timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0))
          (F.ordered_tsupport n) hg_shift_ord
    calc
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single 0 (((G : BorchersSequence d).funcs 0))
            (G.ordered_tsupport 0)) (t : ℂ) =
        OS.S n (ZeroDiagonalSchwartz.ofClassical
          ((((F : BorchersSequence d).funcs n).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0))))) := by
            simpa using OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
              (d := d) (OS := OS) (lgc := lgc)
              (f := ((F : BorchersSequence d).funcs n))
              (hf_ord := F.ordered_tsupport n)
              (g := ((G : BorchersSequence d).funcs 0))
              (hg_ord := G.ordered_tsupport 0)
              (hg_compact := hG_compact 0)
              (t := t) ht
      _ = ∫ y : NPointDomain d n,
            Ψ n (fun i => wickRotatePoint (y i)) *
              ((ZeroDiagonalSchwartz.ofClassical
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0))))).1 y) := by
            exact hΨ_euclid n
              (ZeroDiagonalSchwartz.ofClassical
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0)))))
      _ = ∫ y : NPointDomain d n,
            Ψ n (fun i => wickRotatePoint (y i)) *
              ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t ((G : BorchersSequence d).funcs 0))) y) := by
            simp [hvanish_shift]

theorem hasCompactSupport_onePointToFin1
    (h : SchwartzSpacetime d)
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    HasCompactSupport (((onePointToFin1CLM d h : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) := by
  simpa [onePointToFin1CLM] using
    hh_compact.comp_homeomorph
      ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)).toHomeomorph)

theorem onePoint_osConjTensorProduct_apply
    (χ h : SchwartzSpacetime d)
    (y : NPointDomain d 2) :
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (onePointToFin1CLM d h : SchwartzNPoint d 1)) y) =
      χ (y 0) * h (y 1) := by
  have hosconj :
      SchwartzNPoint.osConj (d := d) (n := 1)
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)) =
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
    ext x
    simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
      timeReflectionN, timeReflection_timeReflection]
  calc
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (onePointToFin1CLM d h : SchwartzNPoint d 1)) y)
      = (((onePointToFin1CLM d χ : SchwartzNPoint d 1).tensorProduct
          (onePointToFin1CLM d h : SchwartzNPoint d 1)) y) := by
            simp [SchwartzNPoint.osConjTensorProduct, hosconj]
    _ = χ (y 0) * h (y 1) := by
          rw [SchwartzMap.tensorProduct_apply]
          simp [onePointToFin1CLM_apply, splitFirst, splitLast]

theorem onePoint_osConjTensorProduct_timeShift_apply
    (χ h : SchwartzSpacetime d) (t : ℝ)
    (y : NPointDomain d 2) :
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) t (onePointToFin1CLM d h))) y) =
      χ (y 0) * (SCV.translateSchwartz (- timeShiftVec d t) h) (y 1) := by
  have hosconj :
      SchwartzNPoint.osConj (d := d) (n := 1)
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1)) =
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
    ext x
    simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
      timeReflectionN, timeReflection_timeReflection]
  calc
    (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) t (onePointToFin1CLM d h))) y)
      = (((onePointToFin1CLM d χ : SchwartzNPoint d 1).tensorProduct
          (timeShiftSchwartzNPoint (d := d) t (onePointToFin1CLM d h))) y) := by
            simp [SchwartzNPoint.osConjTensorProduct, hosconj]
    _ = χ (y 0) * h (y 1 - timeShiftVec d t) := by
          rw [SchwartzMap.tensorProduct_apply]
          simp [onePointToFin1CLM_apply, splitFirst, splitLast,
            timeShiftSchwartzNPoint_apply]
    _ = χ (y 0) * (SCV.translateSchwartz (- timeShiftVec d t) h) (y 1) := by
          simp [SCV.translateSchwartz_apply, sub_eq_add_neg]

theorem twoPoint_flattenCfg_xiShift_secondTime_eq_update
    (z : Fin 2 → Fin (d + 1) → ℂ) (t : ℂ) :
    BHW.flattenCfg 2 d (xiShift ⟨1, by omega⟩ 0 z t) =
      Function.update
        (BHW.flattenCfg 2 d z)
        (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
        (BHW.flattenCfg 2 d z (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + t) := by
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  fin_cases i
  · simp [BHW.flattenCfg, xiShift, Function.update]
  · by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.flattenCfg, xiShift, Function.update]
    · simp [BHW.flattenCfg, xiShift, Function.update, hμ]

omit [NeZero d] in
theorem zero_not_mem_tsupport_translate_of_notMem
    (h : SchwartzSpacetime d) (a : SpacetimeDim d)
    (ha : a ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    (0 : SpacetimeDim d) ∉
      tsupport (((SCV.translateSchwartz a h : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ)) := by
  rw [notMem_tsupport_iff_eventuallyEq] at ha ⊢
  have hcont :
      Filter.Tendsto (fun x : SpacetimeDim d => x + a)
        (nhds (0 : SpacetimeDim d)) (nhds a) := by
    simpa using ((continuous_id.add continuous_const).continuousAt.tendsto
      (x := (0 : SpacetimeDim d)))
  simpa [SCV.translateSchwartz_apply] using ha.comp_tendsto hcont

omit [NeZero d] in
theorem neg_timeShiftVec_not_mem_positive_tsupport
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    (- timeShiftVec d t : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
  intro hx
  have hpos := hh_pos hx
  have hpos0 : 0 < (- timeShiftVec d t : SpacetimeDim d) 0 := hpos
  have htime : (- timeShiftVec d t : SpacetimeDim d) 0 = -t := by
    simp [timeShiftVec]
  linarith [hpos0, ht]

private theorem onePointToFin1_tsupport_subset_orderedPositiveTimeRegion_of_tsupport_positive
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport (((onePointToFin1CLM d h : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro x hx
  have hx0 : x 0 ∈ tsupport (h : SpacetimeDim d → ℂ) := by
    by_contra hx0
    have hzero :
        (x : NPointDomain d 1) ∉ tsupport (((onePointToFin1CLM d h : SchwartzNPoint d 1) :
          NPointDomain d 1 → ℂ)) := by
      rw [notMem_tsupport_iff_eventuallyEq] at hx0 ⊢
      simpa [onePointToFin1CLM_apply] using
        hx0.comp_tendsto ((continuous_apply 0).continuousAt.tendsto : Filter.Tendsto
          (fun y : NPointDomain d 1 => y 0) (nhds x) (nhds (x 0)))
    exact hzero hx
  have hpos0 : 0 < (x 0) 0 := hh_pos hx0
  simpa [OrderedPositiveTimeRegion] using hpos0

/-- A first honest `k = 2` continuation statement from the one-variable OS
holomorphic bridge. Choosing the left one-point factor as an OS-conjugated
center cutoff and the right one-point factor as a compactly supported
difference-variable test produces a holomorphic function on the right
half-plane whose positive-real restriction is the explicit `ξ`-shifted
Euclidean two-point integral. -/
theorem exists_singleSplit_xiShift_holomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d (n + m)),
      OS.S (n + m) h = ∫ x : NPointDomain d (n + m),
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d (n + m),
            Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.osConjTensorProduct g) y := by
  let F : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n f hf_ord
  let G : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single m g hg_ord
  refine ⟨OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G, ?_, ?_⟩
  · simpa [F, G] using
      differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G
  · intro t ht
    simpa [F, G, PositiveTimeBorchersSequence.single_toBorchersSequence] using
      (OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
        (f := f) (hf_ord := hf_ord)
        (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
        (t := t) ht)

/-- A first honest `k = 2` continuation statement from the one-variable OS
holomorphic bridge. Choosing the left one-point factor as an OS-conjugated
center cutoff and the right one-point factor as a compactly supported
difference-variable test produces a holomorphic function on the right
half-plane whose positive-real restriction is the explicit `ξ`-shifted
Euclidean two-point integral. -/
theorem exists_twoPoint_xiShift_holomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d 2),
      OS.S 2 h = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hh_pos : tsupport (((onePointToFin1CLM d h : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (χ (y 0) * h (y 1)) := by
  let F : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)) hχ_pos
  let G : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d h : SchwartzNPoint d 1) hh_pos
  refine ⟨OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G, ?_, ?_⟩
  · simpa [F, G] using
      differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G
  · intro t ht
    have hh1_compact :
        HasCompactSupport (((((G : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs 1 :
          SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) := by
      simpa [G, PositiveTimeBorchersSequence.single_toBorchersSequence] using
        hasCompactSupport_onePointToFin1 (d := d) h hh_compact
    calc
      OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G (t : ℂ)
          = ∫ y : NPointDomain d (1 + 1),
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (((SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
                  (onePointToFin1CLM d h : SchwartzNPoint d 1)) y) := by
            simpa [F, G, PositiveTimeBorchersSequence.single_toBorchersSequence] using
              (OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift
                (d := d) (OS := OS) (lgc := lgc) (hm := by omega)
                (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
                (f := (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1)))
                (hf_ord := hχ_pos)
                (g := (onePointToFin1CLM d h : SchwartzNPoint d 1))
                (hg_ord := hh_pos)
                (hg_compact := hh1_compact)
                (t := t) ht)
      _ = ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (χ (y 0) * h (y 1)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with y
            rw [onePoint_osConjTensorProduct_apply (d := d) χ h y]

/-- On positive real times, the explicit off-diagonal spectral Laplace function
of the OS time-shift semigroup for the simple pair `(χ, g)` is exactly the
product-shell `ξ`-shift witness integral. This is the concrete semigroup-side
real-axis formula behind the later normalized-center matching criteria. -/
theorem selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d 2),
      OS.S 2 h = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t) :
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                hχ_pos⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (onePointToFin1CLM d g : SchwartzNPoint d 1)
                hg_pos⟧)) : OSHilbertSpace OS))
        (t : ℂ) =
      ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (χ (y 0) * g (y 1)) := by
  let F : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1)) hχ_pos
  let G : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single 1
      (onePointToFin1CLM d g : SchwartzNPoint d 1) hg_pos
  have hg1_compact :
      HasCompactSupport (((((G : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs 1 :
        SchwartzNPoint d 1) : NPointDomain d 1 → ℂ)) := by
    simpa [G, PositiveTimeBorchersSequence.single_toBorchersSequence] using
      hasCompactSupport_onePointToFin1 (d := d) g hg_compact
  calc
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
        (t : ℂ)
      = OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc F G (t : ℂ) := by
          symm
          exact OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
            (d := d) OS lgc F G (t : ℂ) ht
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (((SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t
              (onePointToFin1CLM d g : SchwartzNPoint d 1))))) := by
          simpa [F, G, PositiveTimeBorchersSequence.single_toBorchersSequence] using
            (OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
              (d := d) (OS := OS) (lgc := lgc)
              (f := (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1)))
              (hf_ord := hχ_pos)
              (g := (onePointToFin1CLM d g : SchwartzNPoint d 1))
              (hg_ord := hg_pos)
              (hg_compact := hg1_compact)
              (t := t) ht)
    _ = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (((SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
              (onePointToFin1CLM d g : SchwartzNPoint d 1)) y) := by
          symm
          exact (schwinger_simpleTensor_timeShift_eq_xiShift
            (d := d) (OS := OS) (n := 1) (m := 1) (hm := by omega)
            (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            (f := (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1)))
            (hf_ord := hχ_pos)
            (g := (onePointToFin1CLM d g : SchwartzNPoint d 1))
            (hg_ord := hg_pos)
            (t := t) ht).symm
    _ = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (χ (y 0) * g (y 1)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          rw [onePoint_osConjTensorProduct_apply (d := d) χ g y]

/-- For r ≥ 1, the ξ-shift stays in C_k^(r). The shift only modifies column r,
    and C_k^(r) only constrains columns with μ.val ≤ r-1. -/
private theorem xiShift_stays_in_acr {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r)
    (z₀ : Fin k → Fin (d + 1) → ℂ)
    (hz₀ : z₀ ∈ AnalyticContinuationRegion d k r)
    (j : Fin k) (t : ℝ) :
    xiShift j ⟨r, hr⟩ z₀ (t : ℂ) ∈ AnalyticContinuationRegion d k r := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  simp only [AnalyticContinuationRegion, Set.mem_setOf_eq] at hz₀ ⊢
  intro i μ hμ
  have hμ_ne : μ ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) := by
    intro heq; have := congr_arg Fin.val heq; simp at this; omega
  -- xiShift is identity at μ ≠ ⟨r'+1, _⟩
  have h_eq : ∀ i' : Fin k, xiShift j ⟨r' + 1, by omega⟩ z₀ ↑t i' μ = z₀ i' μ := by
    intro i'
    unfold xiShift
    split_ifs with h
    · exact absurd h.2 hμ_ne
    · rfl
  rw [h_eq i]
  have h_prev : (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
                 else xiShift j ⟨r' + 1, by omega⟩ z₀ ↑t ⟨i.val - 1, by omega⟩) μ =
                (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
                 else z₀ ⟨i.val - 1, by omega⟩) μ := by
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · simp only [hi0, ↓reduceDIte]; exact h_eq ⟨i.val - 1, by omega⟩
  rw [h_prev]
  exact hz₀ i μ hμ

/-- For r ≥ 1, ACR(r+1) is a subset of ACR(r): adding more imaginary-positivity
    constraints gives a smaller domain. -/
private theorem acr_succ_subset {d k r : ℕ} [NeZero d] (hr : 0 < r) :
    AnalyticContinuationRegion d k (r + 1) ⊆ AnalyticContinuationRegion d k r := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, rfl⟩
  intro z hz
  simpa [AnalyticContinuationRegion] using
    (fun i μ hμ => hz i μ (Nat.le_trans hμ (Nat.le_succ _)))

/-- **Mixed one-slice continuation domain** for the r → r+1 inductive step.

    `OneSliceContinuationDomain d k r hr i₀` is the "intermediate" domain where:
    - all ACR(r) positivity constraints hold (Im-differences > 0 for μ < r), AND
    - the new cumulative-difference coordinate for particle `i₀` at level r also
      has positive imaginary part: Im(z[i₀][r] - prev[i₀][r]) > 0,
    - but the other new r-th differences (for i ≠ i₀) remain unconstrained.

    **Why this domain matters**: ACR(r+1) = ⋂_{i₀} OneSliceContinuationDomain i₀
    (proved by `iInter_oneSliceContinuationDomain_eq_acr_succ`). The full Paley-Wiener
    continuation argument extends S_prev to ONE slice at a time: for each i₀, extend
    in the ξ[i₀][r] direction using 1D Paley-Wiener to get a holomorphic function on
    `OneSliceContinuationDomain i₀`. Then assemble all k slice extensions via Osgood's
    theorem to get holomorphicity on ACR(r+1).

    Ref: OS II, Theorem 4.1; Vladimirov §26 -/
def OneSliceContinuationDomain (d k r : ℕ) [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) : Set (Fin k → Fin (d + 1) → ℂ) :=
  { z |
      (∀ i : Fin k, ∀ μ : Fin (d + 1), μ.val < r →
        let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
        (z i μ - prev μ).im > 0) ∧
      let prev₀ := if h : i₀.val = 0 then 0 else z ⟨i₀.val - 1, by omega⟩
      (z i₀ ⟨r, hr⟩ - prev₀ ⟨r, hr⟩).im > 0 }

/-- Individual coordinate positivity condition is open (helper). -/
private theorem diffImPos_isOpen' {d k : ℕ} [NeZero d]
    (i : Fin k) (μ : Fin (d + 1)) :
    IsOpen { z : Fin k → Fin (d + 1) → ℂ |
      let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
      (z i μ - prev μ).im > 0 } := by
  by_cases hi : i.val = 0
  · simpa [hi] using isOpen_lt continuous_const
      (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i)))
  · let j : Fin k := ⟨i.val - 1, by omega⟩
    have hj' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z j μ).im :=
      Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply j))
    have hi' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z i μ).im :=
      Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i))
    simpa [hi, j, Complex.sub_im, sub_pos] using isOpen_lt hj' hi'

/-- `OneSliceContinuationDomain` is open. -/
theorem isOpen_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) :
    IsOpen (OneSliceContinuationDomain d k r hr i₀) := by
  have : OneSliceContinuationDomain d k r hr i₀ =
      (⋂ i : Fin k, ⋂ μ : Fin (d + 1),
        { z : Fin k → Fin (d + 1) → ℂ |
          μ.val < r →
            let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
            (z i μ - prev μ).im > 0 }) ∩
      { z : Fin k → Fin (d + 1) → ℂ |
        let prev₀ := if h : i₀.val = 0 then 0 else z ⟨i₀.val - 1, by omega⟩
        (z i₀ ⟨r, hr⟩ - prev₀ ⟨r, hr⟩).im > 0 } := by
    ext z; simp [OneSliceContinuationDomain]
  rw [this]
  apply (isOpen_iInter_of_finite fun i : Fin k =>
    isOpen_iInter_of_finite fun μ : Fin (d + 1) => ?_).inter (diffImPos_isOpen' i₀ ⟨r, hr⟩)
  by_cases hμ : μ.val < r
  · simpa [hμ] using diffImPos_isOpen' (d := d) (k := k) i μ
  · simp [hμ]

/-- ACR(r+1) ⊆ OneSliceContinuationDomain for each i₀. -/
theorem acr_succ_subset_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) :
    AnalyticContinuationRegion d k (r + 1) ⊆ OneSliceContinuationDomain d k r hr i₀ := by
  intro z hz
  simp only [AnalyticContinuationRegion, OneSliceContinuationDomain, Set.mem_setOf_eq] at hz ⊢
  exact ⟨fun i μ hμ => hz i μ (Nat.le_of_lt hμ), hz i₀ ⟨r, hr⟩ (Nat.le_refl r)⟩

/-- OneSliceContinuationDomain ⊆ ACR(r) for r ≥ 1. -/
theorem oneSliceContinuationDomain_subset_acr {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r) (i₀ : Fin k) :
    OneSliceContinuationDomain d k r hr i₀ ⊆ AnalyticContinuationRegion d k r := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  intro z hz
  simp only [OneSliceContinuationDomain, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz ⊢
  intro i μ hμ
  exact hz.1 i μ (by omega)

/-- ACR(r+1) = ⋂_{i₀} OneSliceContinuationDomain d k r hr i₀. -/
theorem iInter_oneSliceContinuationDomain_eq_acr_succ {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) :
    (⋂ i₀ : Fin k, OneSliceContinuationDomain d k r hr i₀) =
      AnalyticContinuationRegion d k (r + 1) := by
  ext z
  simp only [Set.mem_iInter, OneSliceContinuationDomain, AnalyticContinuationRegion,
    Set.mem_setOf_eq]
  constructor
  · intro h i μ hμ
    rcases Nat.lt_or_eq_of_le hμ with hlt | rfl
    · exact (h i).1 i μ hlt
    · exact (h i).2
  · intro hz i₀
    exact ⟨fun i μ hμ => hz i μ (Nat.le_of_lt hμ), hz i₀ ⟨r, hr⟩ (Nat.le_refl r)⟩

/-- Updating the i₀-th row's r-th entry to `prev₀ ⟨r,hr⟩ + w` (with Im(w) > 0)
    lands in `OneSliceContinuationDomain d k r hr i₀`. -/
theorem sliceUpdate_mem_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r)
    (z₀ : Fin k → Fin (d + 1) → ℂ)
    (hz₀ : z₀ ∈ AnalyticContinuationRegion d k r)
    (i₀ : Fin k) {w : ℂ} (hw : 0 < w.im) :
    let prev₀ : Fin (d + 1) → ℂ :=
      if _ : i₀.val = 0 then 0 else z₀ ⟨i₀.val - 1, by omega⟩
    Function.update z₀ i₀
        (Function.update (z₀ i₀) ⟨r, hr⟩ (prev₀ ⟨r, hr⟩ + w))
      ∈ OneSliceContinuationDomain d k r hr i₀ := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  simp only [OneSliceContinuationDomain, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz₀ ⊢
  have hμ_ne : (⟨r' + 1, by omega⟩ : Fin (d + 1)) ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) →
      False := fun h => h rfl
  refine ⟨fun i μ hμ => ?_, ?_⟩
  · have hμ_ne : μ ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) :=
        fun heq => by simp [heq] at hμ
    have h_eq : ∀ j : Fin k, Function.update z₀ i₀
        (Function.update (z₀ i₀) (⟨r' + 1, by omega⟩ : Fin (d + 1))
          ((if h : i₀.val = 0 then (0 : Fin (d + 1) → ℂ)
            else z₀ ⟨i₀.val - 1, by omega⟩) ⟨r' + 1, by omega⟩ + w)) j μ = z₀ j μ := by
      intro j
      by_cases hj : j = i₀
      · subst hj; simp [hμ_ne]
      · simp [hj]
    rw [h_eq i]
    have h_prev_eq :
        (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
          else Function.update z₀ i₀
            (Function.update (z₀ i₀) (⟨r' + 1, by omega⟩ : Fin (d + 1))
              ((if h : i₀.val = 0 then (0 : Fin (d + 1) → ℂ)
                else z₀ ⟨i₀.val - 1, by omega⟩) ⟨r' + 1, by omega⟩ + w))
            ⟨i.val - 1, by omega⟩) μ =
        (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ) else z₀ ⟨i.val - 1, by omega⟩) μ := by
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceDIte]; exact h_eq ⟨i.val - 1, by omega⟩
    rw [h_prev_eq]
    exact hz₀ i μ (by omega)
  · by_cases hi0 : i₀.val = 0
    · simpa [sub_eq_add_neg, Function.update, hi0] using hw
    · have hprev_ne : (⟨i₀.val - 1, by omega⟩ : Fin k) ≠ i₀ :=
        fun heq => absurd (congrArg Fin.val heq)
          (Nat.ne_of_lt (Nat.sub_lt (Nat.pos_of_ne_zero hi0) one_pos))
      simpa [sub_eq_add_neg, Function.update, hi0, hprev_ne, add_assoc, add_left_comm, add_comm]
        using hw


/-- **Domain restriction lemma: ACR(r+1) ⊆ ACR(r) (r ≥ 1).**

    This is a RESTRICTION lemma, not the OS II continuation step. Because
    ACR(r+1) ⊆ ACR(r) for r ≥ 1, any function holomorphic on ACR(r) is also
    holomorphic on ACR(r+1) by restriction (S_ext := S_prev).

    **This is NOT the full OS II argument.** The true OS II inductive step for r ≥ 1
    would extend holomorphicity to `OneSliceContinuationDomain`, which lies strictly
    between ACR(r+1) and ACR(r): `ACR(r+1) ⊆ OneSlice ⊆ ACR(r)`. Since OneSlice ⊆ ACR(r),
    a restriction argument suffices for holomorphicity on OneSlice, but not for the
    Paley-Wiener boundary value behavior needed to assemble the full OS continuation.
    The genuinely non-trivial OS II step is the base case r=0→1 (handled by
    `schwinger_continuation_base_step`), where ACR(0) (Im=0) and ACR(1) (Im>0)
    are disjoint and a Laplace/Paley-Wiener argument is indispensable.

    Ref: OS II, Theorem 4.1 (the domain inclusions) -/
theorem restrict_holomorphic_to_acr_succ {d : ℕ} [NeZero d]
    (k : ℕ) (r : ℕ) (_ : r < d + 1) (hr_pos : 0 < r)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k r, S_ext z = S_prev z :=
  ⟨S_prev, hS_prev.mono (acr_succ_subset hr_pos), fun _ _ => rfl⟩


/-- **Inductive continuation for `r ≥ 1` (OS II, Theorem 4.1).**

    Once the base-step has produced a holomorphic witness on `C_k^(1)`, every further
    stage `C_k^(r+1) ⊆ C_k^(r)` is obtained by restriction. The genuinely non-trivial
    analytic continuation is therefore concentrated in `schwinger_continuation_base_step`;
    this theorem is only the monotonicity step for the nested domains.

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 -/
theorem inductive_analytic_continuation {d : ℕ} [NeZero d]
    (k : ℕ) (r : ℕ) (hr : r < d + 1) (hr_pos : 0 < r)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k r, S_ext z = S_prev z := by
  exact restrict_holomorphic_to_acr_succ k r hr hr_pos S_prev hS_prev

/-! ### Full analytic continuation from Euclidean to forward tube

After the base step, the active reconstruction chain already produces a holomorphic
witness on `C_k^(1)`, and `ForwardTube d k ⊆ C_k^(1)`. So the forward-tube existence
statement used below no longer depends on the separate Bochner route from
`C_k^(d+1)`.

The older Bochner approach from `C_k^(d+1)` remains mathematically interesting, but
it is not part of the active OS→Wightman pipeline here. The naive
"common SO(d+1)-orbit of the positive orthant, then convex hull" story is false, so
that side development needs a different geometric input before it can be reinstated.

Ref: OS II, Sections IV-V; Vladimirov Section 20.2 -/

/-- The forward tube already lies inside the first-step continuation region `C_k^(1)`,
    since each forward-cone difference has positive time component. -/
private theorem forwardTube_subset_acr_one {d k : ℕ} [NeZero d] :
    ForwardTube d k ⊆ AnalyticContinuationRegion d k 1 := by
  intro z hz
  rw [forwardTube_eq_imPreimage] at hz
  simp only [ForwardConeAbs, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz ⊢
  intro i μ hμ
  have hμ0 : μ = 0 := Fin.ext (Nat.eq_zero_of_le_zero hμ)
  have htime :
      0 <
        ((z i 0).im -
          ((if h : i.val = 0 then (0 : Fin (d + 1) → ℝ)
            else fun ν => (z ⟨i.val - 1, by omega⟩ ν).im) 0)) := (hz i).1
  subst hμ0
  have htime' :
      ((if h : i.val = 0 then (0 : Fin (d + 1) → ℂ) else z ⟨i.val - 1, by omega⟩) 0).im <
        (z i 0).im := by
    by_cases hi : i.val = 0
    · simpa [hi, sub_pos] using htime
    · simpa [hi, sub_pos] using htime
  simpa [Complex.sub_im, sub_pos] using htime'

/-- Iterate analytic continuation from the base-step witness on `C_k^(1)` to `C_k^(d+1)`.

    The real analytic continuation starts at `r = 1`, not `r = 0`: the base-step
    theorem `schwinger_continuation_base_step_full` produces the first holomorphic witness
    on `ACR(1)` directly from the Schwinger functional. For `r ≥ 1`, all further steps
    are restrictions along the inclusions `ACR(r+1) ⊆ ACR(r)`.

    This avoids treating `ACR(0)` as an open complex holomorphic domain and removes
    the need for a separate pointwise "base-region kernel" theorem.

    Ref: OS II, Theorem 4.1 -/
theorem iterated_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (d + 1)) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  obtain ⟨S₁, hS₁_hol, hS₁_rep⟩ := schwinger_continuation_base_step_full OS lgc k
  -- Invariant for r ≥ 1: holomorphicity on ACR(r) and preservation of the
  -- Euclidean pairing identity with OS.S.
  let P : ℕ → Prop := fun s =>
    ∃ (S_r : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_r (AnalyticContinuationRegion d k (s + 1)) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_r (fun j => wickRotatePoint (x j)) * (f.1 x))
  have hP0 : P 0 := ⟨S₁, hS₁_hol, hS₁_rep⟩
  have hstep : ∀ s, s + 1 < d + 1 → P s → P (s + 1) := by
    intro s hs hPs
    have hs_pos : 0 < s + 1 := Nat.succ_pos s
    rcases hPs with ⟨S_r, hS_r_hol, hS_r_rep⟩
    exact ⟨S_r, hS_r_hol.mono (acr_succ_subset hs_pos), hS_r_rep⟩
  have hP_all : ∀ s, s + 1 ≤ d + 1 → P s := by
    intro s hsle
    induction s with
    | zero =>
        exact hP0
    | succ s ih =>
        have hslt : s + 1 < d + 1 := by omega
        have hsle' : s + 1 ≤ d + 1 := by omega
        exact hstep (s := s) hslt (ih hsle')
  rcases hP_all d (by simp) with ⟨S_ext, hS_ext_hol, hS_ext_rep⟩
  exact ⟨S_ext, hS_ext_hol, hS_ext_rep⟩

theorem full_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  obtain ⟨S₁, hS₁_hol, hS₁_euclid⟩ := schwinger_continuation_base_step_full OS lgc k
  refine ⟨S₁, hS₁_hol.mono (forwardTube_subset_acr_one (d := d) (k := k)), hS₁_euclid⟩

/-! ### Downstream Boundary Values

Phase 4 boundary values, Phase 5 transfer theorems, and the final bridge
theorems now live in `OSToWightmanBoundaryValues.lean`. This file keeps the
semigroup and analytic-continuation core, including the live
`schwinger_continuation_base_step` blocker. -/

end
