/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup

/-!
# OS to Wightman Analytic Continuation Core

This file contains Phase 3 of the `E'→R'` reconstruction chain:

- the base-step analytic continuation on the first tube domain
- the slice geometry and interleaved bookkeeping around `schwinger_continuation_base_step`
- the inductive restriction from `ACR(1)` to the forward tube

The semigroup, Hilbert-space, and one-variable holomorphic bridge infrastructure
now lives in `OSToWightmanSemigroup.lean`. The downstream boundary-value and
transfer package lives in `OSToWightmanBoundaryValues.lean`.
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

/-- Transport holomorphicity on `C_k^(1)` to the positive-time-difference tube in
    flattened difference coordinates. -/
private theorem differentiableOn_toDiffFlat_of_acrone_holo {d k : ℕ} [NeZero d]
    (F : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (AnalyticContinuationRegion d k 1)) :
    DifferentiableOn ℂ (fun u : Fin (k * (d + 1)) → ℂ => F (BHW.fromDiffFlat k d u))
      (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) := by
  intro u hu
  have hz : BHW.fromDiffFlat k d u ∈ AnalyticContinuationRegion d k 1 := by
    have hu' : BHW.toDiffFlat k d (BHW.fromDiffFlat k d u) ∈
        SCV.TubeDomain (FlatPositiveTimeDiffReal k d) := by
      simpa [BHW.toDiffFlat_fromDiffFlat (n := k) (d := d) u] using hu
    exact (acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff
      (d := d) (k := k) (BHW.fromDiffFlat k d u)).mpr hu'
  have hF_at : DifferentiableAt ℂ F (BHW.fromDiffFlat k d u) :=
    (hF_holo _ hz).differentiableAt
      ((isOpen_analyticContinuationRegion_succ (d := d) (k := k) (r := 0)).mem_nhds hz)
  exact (hF_at.comp u (by
    simpa [BHW.fromDiffFlat] using differentiable_fromDiffFlat_local k d u)).differentiableWithinAt

/-- Transport holomorphicity from the positive-time-difference tube in flattened
    difference coordinates back to `C_k^(1)`. -/
private theorem differentiableOn_of_toDiffFlat_acrone_holo {d k : ℕ} [NeZero d]
    (G : (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hG_holo : DifferentiableOn ℂ G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d))) :
    DifferentiableOn ℂ (fun z : Fin k → Fin (d + 1) → ℂ => G (BHW.toDiffFlat k d z))
      (AnalyticContinuationRegion d k 1) := by
  intro z hz
  have hu : BHW.toDiffFlat k d z ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d) :=
    (acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff (d := d) (k := k) z).mp hz
  have hG_at : DifferentiableAt ℂ G (BHW.toDiffFlat k d z) :=
    (hG_holo _ hu).differentiableAt
      ((SCV.tubeDomain_isOpen (isOpen_flatPositiveTimeDiffReal k d)).mem_nhds hu)
  exact (hG_at.comp z (differentiable_toDiffFlat_local k d z)).differentiableWithinAt

/-- **Base step of analytic continuation (r = 0 → r = 1).**

    Produces the first genuinely holomorphic witness on `C_k^(1)` directly from the
    Schwinger functional `OS.S k`. This avoids introducing a separate "base-region
    kernel" on `C_k^(0)`, which would be a stronger and less natural object than the
    reconstruction chain actually needs.

    In the current file, `C_k^(1)` has already been identified as a tube domain over
    the positive time-difference cone in flattened difference coordinates via
    `acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff`. So the remaining
    content is not target-domain geometry.

    The one-variable spectral/Laplace representation gap has now been closed on
    the compact-support positive-time OS core, both diagonally and off-diagonally:
    for arbitrary `x` and compact-support core `y = [F]`, the matrix element
      `t ↦ ⟪x, T_t y⟫`
    is represented honestly by a polarized Laplace expression built from finite
    measures on `[0, ∞)`.

    So the live gap is now genuinely multivariable/interleaved. To finish the
    base step, those one-variable matrix-element witnesses must still be assembled
    into the flattened holomorphic witness `G` required here for the full
    positive-time-difference tube. The unresolved theorem-level choice is:

    1. assemble `G` from separate holomorphicity in each time-difference variable
       plus continuity/Osgood bookkeeping for the interleaved operator product, or
    2. build the deeper joint spectral / product-measure package for the interleaved
       semigroup insertions directly.

    So the blocker is no longer existence of a one-variable positive-energy measure
    on the compact-support core, but the passage from those one-variable witnesses
    to the full OS II flat continuation statement.

    Ref: OS II, Section IV (base case of induction); Reed-Simon II, Section X.7;
    Streater-Wightman, §3.2-§3.3. -/
private theorem schwinger_continuation_base_step_of_flatWitness {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ)
    (G : (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hG_holo : DifferentiableOn ℂ G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)))
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d k),
      OS.S k f = ∫ x : NPointDomain d k,
        G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  let S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ := fun z => G (BHW.toDiffFlat k d z)
  refine ⟨S_ext, ?_, ?_⟩
  · simpa [S_ext] using
      differentiableOn_of_toDiffFlat_acrone_holo (d := d) (k := k) G hG_holo
  · intro f
    simpa [S_ext] using hG_euclid f

theorem schwinger_continuation_base_step {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  -- The SCV side now has both the 1D and product-half-plane Laplace theorems:
  -- `SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport` and
  -- `SCV.multivariateLaplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport`.
  -- So the genuine remaining gap is not half-plane holomorphicity or Osgood assembly.
  -- The compact-support diagonal Laplace witness is now available. What remains is to
  -- convert it into the flattened continuation witness `G` required here, either by a
  -- direct compact-support/time-difference argument or by an honest polarized upgrade.
  obtain ⟨G, hG_holo, hG_euclid⟩ :
      ∃ (G : (Fin (k * (d + 1)) → ℂ) → ℂ),
        DifferentiableOn ℂ G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) ∧
        (∀ (f : ZeroDiagonalSchwartz d k),
          OS.S k f = ∫ x : NPointDomain d k,
            G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) := by
    sorry
  exact schwinger_continuation_base_step_of_flatWitness OS k G hG_holo hG_euclid

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
private theorem fromDiffFlat_update_eq_xiShift_sub {k d : ℕ}
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

/-- Translation in Euclidean spacetime preserves Lebesgue measure. -/
private theorem translate_spacetime_measurePreserving (a : SpacetimeDim d) :
    MeasureTheory.MeasurePreserving
      (fun x : SpacetimeDim d => x - a) MeasureTheory.volume MeasureTheory.volume := by
  simpa [sub_eq_add_neg] using
    (MeasureTheory.measurePreserving_add_right
      (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)) (-a))

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
    theorem `schwinger_continuation_base_step` produces the first holomorphic witness
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
  obtain ⟨S₁, hS₁_hol, hS₁_rep⟩ := schwinger_continuation_base_step OS lgc k
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
  obtain ⟨S₁, hS₁_hol, hS₁_euclid⟩ := schwinger_continuation_base_step OS lgc k
  refine ⟨S₁, hS₁_hol.mono (forwardTube_subset_acr_one (d := d) (k := k)), hS₁_euclid⟩

/-! ### Downstream Boundary Values

Phase 4 boundary values, Phase 5 transfer theorems, and the final bridge
theorems now live in `OSToWightmanBoundaryValues.lean`. This file keeps the
semigroup and analytic-continuation core, including the live
`schwinger_continuation_base_step` blocker. -/

end
