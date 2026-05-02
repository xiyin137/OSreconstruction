/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.BEGTrigonometric
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslationCore
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReducedExtension
import OSReconstruction.ComplexLieGroups.DifferenceCoordinates
import OSReconstruction.ComplexLieGroups.Connectedness.Permutation
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SeedSlices
import OSReconstruction.Wightman.Reconstruction.PoincareRep
import OSReconstruction.SCV.PaleyWiener

/-!
# BHW Translation Invariance

Translation invariance of the BHW extension. Also defines the Schwinger function
construction and proves distributional boundary value correspondence.

The main theorem `bhw_translation_invariant` is proved via Route 1 (reduced
difference coordinates): a second holomorphic extension G is constructed as a
pullback from reduced coordinates, making it algebraically translation-invariant.
BHW uniqueness then identifies G = F_ext on PET.
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]
/-! #### BHW extension helper lemmas and translation invariance

The proof is decomposed into:
1. `permutedExtendedTube_translation_closed` — trivial closure cases (c=0 or n=0)
2. `W_analytic_translation_on_forwardTube` — in BHWTranslationCore
3. `bhw_translation_invariant_of_common_perm` — common-permutation witness case
4. `bhw_translation_local` — local translation invariance via a BHW witness chain
5. `baseFiber*` infrastructure — decomposition into convex slices (open problem)
6. `bhw_translation_invariant` — proved via Route 1 (reduced difference coordinates),
   bypassing the base-fiber preconnectedness problem entirely -/

/-- Trivial translation-closure cases for the permuted extended tube.

    This records the only currently formalized regimes where closure under
    `z ↦ z + c` is immediate in our absolute-coordinate PET:
    - `c = 0` (identity shift),
    - `n = 0` (empty configuration index).

    The nontrivial geometric closure claim (`n > 0`, `c ≠ 0`) is deferred and
    must be treated separately. -/
theorem permutedExtendedTube_translation_closed {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hc : c = 0 ∨ n = 0) :
    (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n := by
  rcases hc with hc | hn
  · simpa [hc] using hz
  · subst hn
    have hshift : (fun k μ => z k μ + c μ) = z := by
      ext k
      exact Fin.elim0 k
    simpa [hshift] using hz


-- `W_analytic_translation_on_forwardTube`, `permutedExtendedTube_isConnected`,
-- and `forwardTube_inter_translate_nonempty` are now provided by BHWTranslationCore.

/-- **BHW extension is translation-invariant when a common permutation witness exists.**

    If z∘π ∈ FT and (z+c)∘π ∈ FT for the SAME permutation π, then F_ext(z+c) = F_ext(z).

    The proof uses the chain:
      F_ext(z+c) = F_ext((z+c)∘π)   [perm inv, since (z+c) ∈ PET from hzc_ft]
               = W_analytic((z+c)∘π) [BHW prop 2, (z+c)∘π ∈ FT]
               = W_analytic(z∘π)     [trans inv on FT: z∘π ∈ FT, (z∘π)+c ∈ FT]
               = F_ext(z∘π)          [BHW prop 2, z∘π ∈ FT]
               = F_ext(z)            [perm inv, since z ∈ PET from hz_ft]

    This avoids needing D = PET ∩ (PET-c) to be connected, and applies directly
    to the Euclidean case where the same ordering permutation works for both z and z+c.

    Used in `F_ext_translation_invariant` for the Euclidean application. -/
theorem bhw_translation_invariant_of_common_perm {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin n))
    (hz_ft : (fun k => z (π k)) ∈ ForwardTube d n)
    (hzc_ft : (fun k μ => z (π k) μ + c μ) ∈ ForwardTube d n) :
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c μ) =
    (W_analytic_BHW Wfn n).val z := by
  set F_ext := (W_analytic_BHW Wfn n).val with hF_ext_def
  set W_analytic := (Wfn.spectrum_condition n).choose
  -- hF_eq : F_ext z = W_analytic z for z ∈ FT
  have hF_eq := (W_analytic_BHW Wfn n).property.2.1
  -- hF_perm : F_ext (z ∘ π) = F_ext z for z ∈ PET
  have hF_perm := (W_analytic_BHW Wfn n).property.2.2.2
  -- Establish PET membership for z and z+c via PermutedForwardTube π ⊆ PET
  -- Strategy: work in BHW namespace and use complexLorentzAction_one
  have hz_pet : z ∈ PermutedExtendedTube d n := by
    rw [← BHW_permutedExtendedTube_eq]
    -- Show z ∈ BHW.PermutedExtendedTube: take π, Λ = 1, w = z
    refine Set.mem_iUnion.mpr ⟨π, 1, z, ?_, (BHW.complexLorentzAction_one z).symm⟩
    -- z ∈ BHW.PermutedForwardTube π: (fun k => z (π k)) ∈ BHW.ForwardTube
    simp only [BHW.PermutedForwardTube, Set.mem_setOf_eq]
    rwa [BHW_forwardTube_eq]
  have hzc_pet : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n := by
    rw [← BHW_permutedExtendedTube_eq]
    -- Show (z+c) ∈ BHW.PermutedExtendedTube: take π, Λ = 1, w = (z+c)
    refine Set.mem_iUnion.mpr ⟨π, 1, fun k μ => z k μ + c μ,
      ?_, (BHW.complexLorentzAction_one _).symm⟩
    -- (z+c) ∈ BHW.PermutedForwardTube π: (fun k => (z+c) (π k)) ∈ BHW.ForwardTube
    simp only [BHW.PermutedForwardTube, Set.mem_setOf_eq]
    rwa [BHW_forwardTube_eq]
  -- Step 1: F_ext(z+c) = F_ext((z+c)∘π) by perm invariance
  -- hF_perm π (z+c) hzc_pet : F_ext (fun k => (z+c) (π k)) = F_ext (z+c)
  -- Note: (fun k => (fun k' μ => z k' μ + c μ) (π k)) = (fun k μ => z (π k) μ + c μ) by rfl
  have h1 : F_ext (fun k μ => z k μ + c μ) = F_ext (fun k μ => z (π k) μ + c μ) :=
    (hF_perm π (fun k μ => z k μ + c μ) hzc_pet).symm
  -- Step 2: F_ext((z+c)∘π) = W_analytic((z+c)∘π) since (z+c)∘π ∈ FT
  -- hF_eq gives F_ext w = W_analytic w for w ∈ FT
  have h2 : F_ext (fun k μ => z (π k) μ + c μ) = W_analytic (fun k μ => z (π k) μ + c μ) :=
    hF_eq (fun k μ => z (π k) μ + c μ) hzc_ft
  -- Step 3: W_analytic((z+c)∘π) = W_analytic(z∘π) by translation invariance on FT
  have h3 : W_analytic (fun k μ => z (π k) μ + c μ) = W_analytic (fun k => z (π k)) :=
    W_analytic_translation_on_forwardTube Wfn c (fun k => z (π k)) hz_ft hzc_ft
  -- Step 4: W_analytic(z∘π) = F_ext(z∘π) since z∘π ∈ FT
  have h4 : W_analytic (fun k => z (π k)) = F_ext (fun k => z (π k)) :=
    (hF_eq _ hz_ft).symm
  -- Step 5: F_ext(z∘π) = F_ext(z) by perm invariance
  have h5 : F_ext (fun k => z (π k)) = F_ext z :=
    hF_perm π z hz_pet
  calc F_ext (fun k μ => z k μ + c μ)
      = F_ext (fun k μ => z (π k) μ + c μ) := h1
    _ = W_analytic (fun k μ => z (π k) μ + c μ) := h2
    _ = W_analytic (fun k => z (π k)) := h3
    _ = F_ext (fun k => z (π k)) := h4
    _ = F_ext z := h5

/-- **Local translation invariance of the BHW extension.**

    For any z ∈ PET and shift direction c, there exists ε > 0 such that
    for all |t| < ε, `z + tc ∈ PET` and `F_ext(z + tc) = F_ext(z)`.

    **Proof.** Extract the PET witness (π, Λ, w) with `w ∈ PFT(π)` and
    `z = Λ · w`. Form `w' = w + t · Λ⁻¹c`. Successive imaginary-part differences
    are unchanged by the uniform shift `Λ⁻¹c`, so `w' ∈ PFT(π)` for small `t`
    (only the k = 0 condition shifts, and FT is open). Then chain BHW properties:
      `F_ext(z + tc) = F_ext(Λ · w') = F_ext(w') = F_ext(w) = F_ext(Λ · w) = F_ext(z)`
    using Lorentz invariance, the common-permutation lemma (which invokes
    permutation invariance + FT agreement + translation invariance on FT).

    This captures the "BHW witness chain" argument and shows F_ext is locally
    constant under uniform translations at every point of PET.

    Ref: Streater-Wightman §2.5; Jost, "General Theory of Quantized Fields" §III.1 -/
theorem bhw_translation_local {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n) :
    ∃ ε > 0, ∀ (t : ℂ), ‖t‖ < ε →
      (fun k μ => z k μ + t * c μ) ∈ PermutedExtendedTube d n ∧
      (W_analytic_BHW Wfn n).val (fun k μ => z k μ + t * c μ) =
      (W_analytic_BHW Wfn n).val z := by
  -- Trivial case: n = 0
  by_cases hn : n = 0
  · subst hn
    refine ⟨1, one_pos, fun t _ => ?_⟩
    have htriv : (fun k μ => z k μ + t * c μ) = z := by ext k; exact Fin.elim0 k
    rw [htriv]; exact ⟨hz, rfl⟩
  -- PET is open → z + tc ∈ PET for small t
  have hPET_open : IsOpen (PermutedExtendedTube d n) :=
    BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube
  have hshift_cont : Continuous (fun t : ℂ => fun k μ => z k μ + t * c μ) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    exact continuous_const.add (continuous_id.mul continuous_const)
  obtain ⟨ε₁, hε₁_pos, hε₁_ball⟩ := Metric.isOpen_iff.mp
    (hPET_open.preimage hshift_cont) 0
    (show (fun k μ => z k μ + (0 : ℂ) * c μ) ∈ PermutedExtendedTube d n by simp [hz])
  -- Extract PET witness: z = Λ₀ · w₀ with w₀ ∈ PFT(π₀)
  rw [← BHW_permutedExtendedTube_eq] at hz
  obtain ⟨π₀, Λ₀, w₀, hw₀_pft, hz_eq⟩ := Set.mem_iUnion.mp hz
  -- w₀ ∘ π₀ ∈ FT
  have hw₀π₀_ft : (fun k => w₀ (π₀ k)) ∈ ForwardTube d n := by
    rw [← BHW_forwardTube_eq]; exact hw₀_pft
  -- Define inverse-rotated shift: c' = Λ₀⁻¹ · c (single-point Lorentz action)
  let c' : Fin (d + 1) → ℂ := fun μ => ∑ ν, (Λ₀⁻¹).val μ ν * c ν
  -- FT is open → perturbed w₀∘π₀ stays in FT for small t
  have hFT_open : IsOpen (ForwardTube d n) :=
    BHW_forwardTube_eq (d := d) (n := n) ▸ BHW.isOpen_forwardTube
  have hshift_cont' : Continuous (fun t : ℂ => fun k μ => w₀ (π₀ k) μ + t * c' μ) := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    exact continuous_const.add (continuous_id.mul continuous_const)
  obtain ⟨ε₂, hε₂_pos, hε₂_ball⟩ := Metric.isOpen_iff.mp
    (hFT_open.preimage hshift_cont') 0
    (show (fun k μ => w₀ (π₀ k) μ + (0 : ℂ) * c' μ) ∈ ForwardTube d n by simp [hw₀π₀_ft])
  -- Take ε = min(ε₁, ε₂)
  refine ⟨min ε₁ ε₂, lt_min hε₁_pos hε₂_pos, fun t ht => ?_⟩
  have ht₁ : ‖t‖ < ε₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : ‖t‖ < ε₂ := lt_of_lt_of_le ht (min_le_right _ _)
  constructor
  -- Part 1: z + tc ∈ PET (from PET openness)
  · exact hε₁_ball (Metric.mem_ball.mpr (show dist t 0 < ε₁ by rwa [dist_comm, dist_zero_left]))
  -- Part 2: F_ext(z + tc) = F_ext(z)
  · -- Abbreviations
    set F_ext := (W_analytic_BHW Wfn n).val with hF_ext_def
    have hF_lorentz := (W_analytic_BHW Wfn n).property.2.2.1
    -- Perturbed FT membership: (w₀∘π₀) + t*c' ∈ FT
    have hw't_ft : (fun k μ => w₀ (π₀ k) μ + t * c' μ) ∈ ForwardTube d n :=
      hε₂_ball (Metric.mem_ball.mpr (show dist t 0 < ε₂ by rwa [dist_comm, dist_zero_left]))
    -- Common permutation lemma: F_ext(w₀ + tc') = F_ext(w₀)
    have hF_w : F_ext (fun k μ => w₀ k μ + t * c' μ) = F_ext w₀ :=
      bhw_translation_invariant_of_common_perm Wfn (fun μ => t * c' μ) w₀ π₀ hw₀π₀_ft hw't_ft
    -- w₀ ∈ PET (PFT(π₀) ⊆ PET via Λ = 1)
    have hw₀_pet : w₀ ∈ PermutedExtendedTube d n := by
      rw [← BHW_permutedExtendedTube_eq]
      exact Set.mem_iUnion.mpr ⟨π₀, 1, w₀, hw₀_pft, (BHW.complexLorentzAction_one w₀).symm⟩
    -- w' ∈ PET (PFT(π₀) ⊆ PET via Λ = 1)
    have hw'_pet : (fun k μ => w₀ k μ + t * c' μ) ∈ PermutedExtendedTube d n := by
      rw [← BHW_permutedExtendedTube_eq]
      refine Set.mem_iUnion.mpr ⟨π₀, 1, fun k μ => w₀ k μ + t * c' μ, ?_,
        (BHW.complexLorentzAction_one _).symm⟩
      show (fun k μ => w₀ (π₀ k) μ + t * c' μ) ∈ BHW.ForwardTube d n
      rwa [BHW_forwardTube_eq]
    -- Algebraic identity: z + tc = Λ₀ · (w₀ + tc')
    -- Key: Λ₀ · (Λ₀⁻¹ · c_broadcast) = c_broadcast (matrix cancellation)
    have hΛΛinv_cancel : ∀ μ : Fin (d + 1),
        ∑ ν, Λ₀.val μ ν * (∑ ρ, (Λ₀⁻¹).val ν ρ * c ρ) = c μ := by
      intro μ
      have h := congr_fun (congr_fun
        (show BHW.complexLorentzAction Λ₀
          (BHW.complexLorentzAction Λ₀⁻¹ (fun (_k : Fin n) => c)) = fun _k => c
        from by rw [← BHW.complexLorentzAction_mul, mul_inv_cancel,
                     BHW.complexLorentzAction_one])
        ⟨0, Nat.pos_of_ne_zero hn⟩) μ
      simpa [BHW.complexLorentzAction] using h
    have hshift_eq : (fun k μ => z k μ + t * c μ) =
        (fun k μ => ∑ ν, Λ₀.val μ ν * (w₀ k ν + t * c' ν)) := by
      ext k μ
      have hz_k : z k μ = ∑ ν, Λ₀.val μ ν * w₀ k ν := congr_fun (congr_fun hz_eq k) μ
      rw [hz_k]
      simp only [mul_add, Finset.sum_add_distrib, c']
      congr 1
      -- ∑ ν, Λ₀.val μ ν * (t * (∑ ρ, (Λ₀⁻¹).val ν ρ * c ρ)) = t * c μ
      simp_rw [← mul_assoc, mul_comm (Λ₀.val μ _) t, mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      exact (hΛΛinv_cancel μ).symm
    -- Chain: F_ext(z+tc) = F_ext(Λ₀·w') = F_ext(w') = F_ext(w₀) = F_ext(z)
    have hF_z_eq_w₀ : F_ext z = F_ext w₀ := by
      conv_lhs => rw [hz_eq]
      exact hF_lorentz Λ₀ w₀ hw₀_pet
    calc F_ext (fun k μ => z k μ + t * c μ)
        = F_ext (fun k μ => ∑ ν, Λ₀.val μ ν * (w₀ k ν + t * c' ν)) := by rw [hshift_eq]
      _ = F_ext (fun k μ => w₀ k μ + t * c' μ) :=
          hF_lorentz Λ₀ (fun k μ => w₀ k μ + t * c' μ) hw'_pet
      _ = F_ext w₀ := hF_w
      _ = F_ext z := hF_z_eq_w₀.symm

/-- Reconstruct a cumulative-sum configuration from a fixed tail of difference
variables and a varying base difference variable `ζ₀`. This is the natural
coordinate chart for translation invariance: simultaneous translation changes
only `ζ₀`, leaving the tail differences fixed. -/
def baseFiberConfig (m d : ℕ)
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    (Fin (d + 1) → ℂ) → (Fin (m + 1) → Fin (d + 1) → ℂ) :=
  fun ζ₀ => BHW.partialSumFun (m + 1) d (Fin.cons ζ₀ ζtail)

/-- The base fiber over a fixed tail `ζ₁, ..., ζₘ`: those base variables `ζ₀`
whose reconstructed cumulative configuration lies in the permuted extended
tube. -/
def baseFiber (m d : ℕ) [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ) : Set (Fin (d + 1) → ℂ) :=
  {ζ₀ | baseFiberConfig m d ζtail ζ₀ ∈ PermutedExtendedTube d (m + 1)}

@[simp] theorem baseFiberConfig_zero_apply {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (ζ₀ : Fin (d + 1) → ℂ) (μ : Fin (d + 1)) :
    baseFiberConfig m d ζtail ζ₀ 0 μ = ζ₀ μ := by
  simp [baseFiberConfig, BHW.partialSumFun]

@[simp] theorem baseFiberConfig_succ_apply {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (ζ₀ : Fin (d + 1) → ℂ) (k : Fin m) (μ : Fin (d + 1)) :
    baseFiberConfig m d ζtail ζ₀ k.succ μ =
      ζ₀ μ + ∑ j : Fin (k.val + 1), ζtail ⟨j.val, by omega⟩ μ := by
  rw [baseFiberConfig, BHW.partialSumFun, Fin.sum_univ_succ]
  refine congrArg (fun z : ℂ => ζ₀ μ + z) ?_
  refine Finset.sum_congr rfl ?_
  intro x hx
  rfl

/-- Shifting the base difference variable by `c` translates every cumulative
coordinate by the same `c`. -/
theorem baseFiberConfig_add {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (ζ₀ c : Fin (d + 1) → ℂ) :
    baseFiberConfig m d ζtail (ζ₀ + c) =
      fun k μ => baseFiberConfig m d ζtail ζ₀ k μ + c μ := by
  ext k μ
  refine Fin.cases ?_ ?_ k
  · simp [baseFiberConfig_zero_apply]
  · intro i
    simp [baseFiberConfig_succ_apply, add_assoc, add_left_comm, add_comm]

/-- Reconstructing from the base variable and the tail of the difference
coordinates recovers the original cumulative configuration. -/
theorem baseFiberConfig_diffCoord_tail {m d : ℕ}
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) :
    baseFiberConfig m d (Fin.tail (BHW.diffCoordFun (m + 1) d z))
      (BHW.diffCoordFun (m + 1) d z 0) = z := by
  have hcons :
      Fin.cons (BHW.diffCoordFun (m + 1) d z 0)
        (Fin.tail (BHW.diffCoordFun (m + 1) d z))
        = BHW.diffCoordFun (m + 1) d z := by
    ext k μ
    refine Fin.cases ?_ ?_ k
    · rfl
    · intro i
      rfl
  simp [baseFiberConfig, hcons, BHW.partialSum_diffCoord]

/-- Translating a cumulative configuration by `c` changes only the base
difference variable. -/
theorem diffCoord_translate_head_tail {m d : ℕ}
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ) :
    BHW.diffCoordFun (m + 1) d (fun k μ => z k μ + c μ) =
      Fin.cons (BHW.diffCoordFun (m + 1) d z 0 + c)
        (Fin.tail (BHW.diffCoordFun (m + 1) d z)) := by
  ext k μ
  refine Fin.cases ?_ ?_ k
  · simp [BHW.diffCoordFun]
  · intro i
    simp [BHW.diffCoordFun, Fin.tail, sub_eq_add_neg]

/-- Difference coordinates commute with the coordinatewise complex Lorentz
action. This is the algebraic bridge from absolute-coordinate sector witnesses
to the fixed-tail difference-coordinate geometry. -/
private theorem diffCoordFun_complexLorentzAction {m d : ℕ}
    (Λ : ComplexLorentzGroup d)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) :
    BHW.diffCoordFun (m + 1) d (BHW.complexLorentzAction Λ z) =
      BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d z) := by
  ext k μ
  by_cases hk : k.val = 0
  · simp [BHW.diffCoordFun, BHW.complexLorentzAction, hk]
  · simp [BHW.diffCoordFun, BHW.complexLorentzAction, hk]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]

/-- Partial sums commute with the coordinatewise complex Lorentz action. -/
private theorem partialSumFun_complexLorentzAction {m d : ℕ}
    (Λ : ComplexLorentzGroup d)
    (ξ : Fin (m + 1) → Fin (d + 1) → ℂ) :
    BHW.partialSumFun (m + 1) d (BHW.complexLorentzAction Λ ξ) =
      BHW.complexLorentzAction Λ (BHW.partialSumFun (m + 1) d ξ) := by
  ext k μ
  simp [BHW.partialSumFun, BHW.complexLorentzAction, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Evaluate the BHW extension on a fixed-tail base fiber. -/
def baseFiberValue {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (m : ℕ)
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    (Fin (d + 1) → ℂ) → ℂ :=
  fun ζ₀ => (W_analytic_BHW Wfn (m + 1)).val (baseFiberConfig m d ζtail ζ₀)

private theorem differentiable_baseFiberConfig {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    Differentiable ℂ (baseFiberConfig m d ζtail) := by
  intro ζ₀
  rw [differentiableAt_pi]
  intro k
  rw [differentiableAt_pi]
  intro μ
  refine Fin.cases ?_ ?_ k
  · simpa using
      (differentiableAt_apply (𝕜 := ℂ) μ ζ₀ : DifferentiableAt ℂ
        (fun ζ : Fin (d + 1) → ℂ => ζ μ) ζ₀)
  · intro i
    simpa [baseFiberConfig_succ_apply, add_comm, add_left_comm, add_assoc] using
      ((differentiableAt_apply (𝕜 := ℂ) μ ζ₀ : DifferentiableAt ℂ
          (fun ζ : Fin (d + 1) → ℂ => ζ μ) ζ₀).add
        (differentiableAt_const
          (c := ∑ j : Fin (i.val + 1), ζtail ⟨j.val, by omega⟩ μ)))

private theorem continuous_baseFiberConfig {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    Continuous (baseFiberConfig m d ζtail) :=
  (differentiable_baseFiberConfig ζtail).continuous

theorem isOpen_baseFiber {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    IsOpen (baseFiber m d ζtail) := by
  have hPET_open : IsOpen (PermutedExtendedTube d (m + 1)) :=
    BHW_permutedExtendedTube_eq (d := d) (n := m + 1) ▸ BHW.isOpen_permutedExtendedTube
  simpa [baseFiber] using hPET_open.preimage (continuous_baseFiberConfig ζtail)

private theorem differentiableOn_baseFiberValue {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (m : ℕ)
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    DifferentiableOn ℂ (baseFiberValue Wfn m ζtail) (baseFiber m d ζtail) := by
  intro ζ₀ hζ₀
  have hF_holo := (W_analytic_BHW Wfn (m + 1)).property.1
  exact (hF_holo _ hζ₀).comp ζ₀
    ((differentiable_baseFiberConfig ζtail) ζ₀).differentiableWithinAt
    (fun y hy => hy)

private theorem fderiv_baseFiberValue_eq_zero {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (m : ℕ)
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    (baseFiber m d ζtail).EqOn (fderiv ℂ (baseFiberValue Wfn m ζtail)) 0 := by
  intro ζ₀ hζ₀
  have hPET_open : IsOpen (PermutedExtendedTube d (m + 1)) :=
    BHW_permutedExtendedTube_eq (d := d) (n := m + 1) ▸ BHW.isOpen_permutedExtendedTube
  have hF_holo := (W_analytic_BHW Wfn (m + 1)).property.1
  have hval_diff :
      DifferentiableAt ℂ (baseFiberValue Wfn m ζtail) ζ₀ := by
    have hF_at :
        DifferentiableAt ℂ (W_analytic_BHW Wfn (m + 1)).val
          (baseFiberConfig m d ζtail ζ₀) :=
      (hF_holo _ hζ₀).differentiableAt (hPET_open.mem_nhds hζ₀)
    exact hF_at.comp ζ₀ ((differentiable_baseFiberConfig ζtail) ζ₀)
  ext c
  let φ : ℂ → ℂ := fun t => baseFiberValue Wfn m ζtail (ζ₀ + t • c)
  have hφ_deriv :
      HasDerivAt φ ((fderiv ℂ (baseFiberValue Wfn m ζtail) ζ₀) c) 0 := by
    have hline : HasDerivAt (fun t : ℂ => ζ₀ + t • c) c 0 := by
      simpa [one_smul] using (((hasDerivAt_id' (0 : ℂ)).smul_const c).const_add ζ₀)
    simpa [one_smul, φ] using
      hval_diff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  obtain ⟨ε, hε_pos, hlocal⟩ :=
    bhw_translation_local Wfn c (baseFiberConfig m d ζtail ζ₀) hζ₀
  have hφ_const :
      φ =ᶠ[nhds 0] fun _ : ℂ => baseFiberValue Wfn m ζtail ζ₀ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε_pos] with t ht
    have ht' : ‖t‖ < ε := by
      simpa [Metric.mem_ball, dist_comm] using ht
    rcases hlocal t ht' with ⟨_htPET, hEq⟩
    simpa [φ, baseFiberValue, baseFiberConfig_add, smul_eq_mul,
      add_comm, add_left_comm, add_assoc] using hEq
  have hφ_zero : HasDerivAt φ 0 0 := by
    exact (hasDerivAt_const (0 : ℂ) (baseFiberValue Wfn m ζtail ζ₀)).congr_of_eventuallyEq hφ_const
  exact hφ_deriv.unique hφ_zero

/-- On a preconnected base fiber, the BHW extension is constant as a function of
the base difference variable `ζ₀`. This packages the local translation
invariance from `bhw_translation_local` into the exact global fiber statement
needed for translation invariance. -/
theorem exists_isConst_baseFiberValue_of_isPreconnected {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (m : ℕ)
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (hconn : IsPreconnected (baseFiber m d ζtail)) :
    ∃ a : ℂ, ∀ ζ₀ ∈ baseFiber m d ζtail, baseFiberValue Wfn m ζtail ζ₀ = a := by
  exact (isOpen_baseFiber (m := m) (d := d) ζtail).exists_is_const_of_fderiv_eq_zero
    hconn
    (differentiableOn_baseFiberValue Wfn m ζtail)
    (fderiv_baseFiberValue_eq_zero Wfn m ζtail)

/-- Conditional translation invariance from base-fiber preconnectedness.
This is the cleaner replacement surface for the old overlap-domain blocker:
once the fixed-tail base fiber is known to be preconnected, simultaneous
translation invariance follows immediately. -/
theorem bhw_translation_invariant_of_baseFiber_isPreconnected {d m : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d (m + 1))
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d (m + 1))
    (hconn : IsPreconnected
      (baseFiber m d (Fin.tail (BHW.diffCoordFun (m + 1) d z)))) :
    (W_analytic_BHW Wfn (m + 1)).val (fun k μ => z k μ + c μ) =
    (W_analytic_BHW Wfn (m + 1)).val z := by
  let ζtail : Fin m → Fin (d + 1) → ℂ := Fin.tail (BHW.diffCoordFun (m + 1) d z)
  let ζ₀ : Fin (d + 1) → ℂ := BHW.diffCoordFun (m + 1) d z 0
  have hz_cfg : baseFiberConfig m d ζtail ζ₀ = z := by
    simpa [ζtail, ζ₀] using baseFiberConfig_diffCoord_tail (m := m) (d := d) z
  have hzc_cfg :
      baseFiberConfig m d ζtail (ζ₀ + c) = (fun k μ => z k μ + c μ) := by
    calc
      baseFiberConfig m d ζtail (ζ₀ + c)
          = (fun k μ => baseFiberConfig m d ζtail ζ₀ k μ + c μ) :=
              baseFiberConfig_add (m := m) (d := d) ζtail ζ₀ c
      _ = (fun k μ => z k μ + c μ) := by
            simp [hz_cfg]
  have hζ₀ : ζ₀ ∈ baseFiber m d ζtail := by
    simpa [baseFiber, hz_cfg]
      using hz
  have hζ₀c : ζ₀ + c ∈ baseFiber m d ζtail := by
    simpa [baseFiber, hzc_cfg]
      using hzc
  obtain ⟨a, ha⟩ :=
    exists_isConst_baseFiberValue_of_isPreconnected (Wfn := Wfn) (m := m)
      (ζtail := ζtail) hconn
  calc
    (W_analytic_BHW Wfn (m + 1)).val (fun k μ => z k μ + c μ)
        = baseFiberValue Wfn m ζtail (ζ₀ + c) := by
            simp [baseFiberValue, hzc_cfg]
    _ = a := ha _ hζ₀c
    _ = baseFiberValue Wfn m ζtail ζ₀ := (ha _ hζ₀).symm
    _ = (W_analytic_BHW Wfn (m + 1)).val z := by
          simp [baseFiberValue, hz_cfg]

/-- The permutation-sector slice of a fixed-tail base fiber. The full fiber is
the union of these slices, so proving fiber preconnectedness reduces to proving
sector-slice preconnectedness and adjacent overlaps. -/
def baseFiberSector (m d : ℕ) [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1))) :
    Set (Fin (d + 1) → ℂ) :=
  {ζ₀ | ∃ (Λ : ComplexLorentzGroup d) (w : Fin (m + 1) → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d (m + 1) π ∧
      baseFiberConfig m d ζtail ζ₀ = BHW.complexLorentzAction Λ w}

/-- The fixed-tail base fiber is the union of its permutation-sector slices. -/
theorem baseFiber_eq_iUnion_baseFiberSector {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    baseFiber m d ζtail = ⋃ π : Equiv.Perm (Fin (m + 1)), baseFiberSector m d ζtail π := by
  ext ζ₀
  constructor
  · intro hζ₀
    simp only [baseFiber, Set.mem_setOf_eq, PermutedExtendedTube, Set.mem_iUnion] at hζ₀
    rcases hζ₀ with ⟨π, Λ, w, hw, hz⟩
    refine Set.mem_iUnion.mpr ⟨π, ?_⟩
    exact ⟨Λ, w, hw, by simpa [BHW.complexLorentzAction] using hz⟩
  · intro hζ₀
    simp only [Set.mem_iUnion, baseFiberSector, Set.mem_setOf_eq] at hζ₀
    rcases hζ₀ with ⟨π, Λ, w, hw, hz⟩
    simp only [baseFiber, Set.mem_setOf_eq, PermutedExtendedTube, Set.mem_iUnion]
    exact ⟨π, Λ, w, hw, by simpa [BHW.complexLorentzAction] using hz⟩

/-- Sector membership on a fixed-tail base fiber can be rewritten directly in
difference coordinates: the fixed-tail configuration `Fin.cons ζ₀ ζtail` is the
Lorentz transform of the witness difference coordinates. -/
theorem mem_baseFiberSector_iff_diffCoordWitness {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (ζ₀ : Fin (d + 1) → ℂ) :
    ζ₀ ∈ baseFiberSector m d ζtail π ↔
      ∃ (Λ : ComplexLorentzGroup d) (w : Fin (m + 1) → Fin (d + 1) → ℂ),
        w ∈ PermutedForwardTube d (m + 1) π ∧
        Fin.cons ζ₀ ζtail =
          BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w) := by
  constructor
  · rintro ⟨Λ, w, hw, hz⟩
    refine ⟨Λ, w, hw, ?_⟩
    have hcfg :
        BHW.diffCoordFun (m + 1) d (baseFiberConfig m d ζtail ζ₀) =
          Fin.cons ζ₀ ζtail := by
      simpa [BHW.diffCoordEquiv_apply] using
        BHW.diffCoord_partialSum (m + 1) d (Fin.cons ζ₀ ζtail)
    calc
      Fin.cons ζ₀ ζtail
          = BHW.diffCoordFun (m + 1) d (baseFiberConfig m d ζtail ζ₀) := hcfg.symm
      _ = BHW.diffCoordFun (m + 1) d (BHW.complexLorentzAction Λ w) := by
            simp [hz]
      _ = BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w) :=
            diffCoordFun_complexLorentzAction Λ w
  · rintro ⟨Λ, w, hw, hξ⟩
    refine ⟨Λ, w, hw, ?_⟩
    calc
      baseFiberConfig m d ζtail ζ₀
          = BHW.partialSumFun (m + 1) d (Fin.cons ζ₀ ζtail) := rfl
      _ = BHW.partialSumFun (m + 1) d
            (BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w)) := by
              rw [hξ]
      _ = BHW.complexLorentzAction Λ
            (BHW.partialSumFun (m + 1) d (BHW.diffCoordFun (m + 1) d w)) := by
              exact partialSumFun_complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w)
      _ = BHW.complexLorentzAction Λ w := by
            simp [BHW.partialSum_diffCoord]

/-- The permutation-sector geometry in difference coordinates. -/
def diffPermSector (m d : ℕ) [NeZero d]
    (π : Equiv.Perm (Fin (m + 1))) :
    Set (Fin (m + 1) → Fin (d + 1) → ℂ) :=
  {ξ | ∃ (Λ : ComplexLorentzGroup d) (w : Fin (m + 1) → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d (m + 1) π ∧
      ξ = BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w)}

/-- A fixed-tail base-fiber sector is exactly the pullback of the corresponding
difference-coordinate sector along `Fin.cons`. -/
theorem baseFiberSector_eq_preimage_diffPermSector {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1))) :
    baseFiberSector m d ζtail π =
      (fun ζ₀ => Fin.cons ζ₀ ζtail) ⁻¹' diffPermSector m d π := by
  ext ζ₀
  constructor
  · intro hζ₀
    rw [Set.mem_preimage]
    rcases (mem_baseFiberSector_iff_diffCoordWitness (m := m) (d := d) ζtail π ζ₀).mp hζ₀
      with ⟨Λ, w, hw, hξ⟩
    exact ⟨Λ, w, hw, hξ⟩
  · intro hζ₀
    rw [Set.mem_preimage] at hζ₀
    rcases hζ₀ with ⟨Λ, w, hw, hξ⟩
    exact (mem_baseFiberSector_iff_diffCoordWitness (m := m) (d := d) ζtail π ζ₀).mpr
      ⟨Λ, w, hw, hξ⟩

private theorem tail_complexLorentzAction {m d : ℕ}
    (Λ : ComplexLorentzGroup d)
    (ξ : Fin (m + 1) → Fin (d + 1) → ℂ) :
    Fin.tail (BHW.complexLorentzAction Λ ξ) =
      BHW.complexLorentzAction Λ (Fin.tail ξ) := by
  ext i μ
  simp [BHW.complexLorentzAction, Fin.tail]

/-- Tail-difference sector attached to a permutation: the possible fixed tails
arising from permuted forward-tube configurations in difference coordinates. -/
def tailDiffPermSector (m d : ℕ) [NeZero d]
    (π : Equiv.Perm (Fin (m + 1))) :
    Set (Fin m → Fin (d + 1) → ℂ) :=
  {ηtail | ∃ w : Fin (m + 1) → Fin (d + 1) → ℂ,
      w ∈ PermutedForwardTube d (m + 1) π ∧
      Fin.tail (BHW.diffCoordFun (m + 1) d w) = ηtail}

/-- Fixed-`Λ` slice of a base-fiber sector. -/
def baseFiberSectorSlice (m d : ℕ) [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (Λ : ComplexLorentzGroup d) :
    Set (Fin (d + 1) → ℂ) :=
  {ζ₀ | ∃ w : Fin (m + 1) → Fin (d + 1) → ℂ,
      w ∈ PermutedForwardTube d (m + 1) π ∧
      baseFiberConfig m d ζtail ζ₀ = BHW.complexLorentzAction Λ w}

/-- A base-fiber sector is the union of its fixed-`Λ` slices. -/
theorem baseFiberSector_eq_iUnion_slice {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1))) :
    baseFiberSector m d ζtail π = ⋃ Λ : ComplexLorentzGroup d, baseFiberSectorSlice m d ζtail π Λ := by
  ext ζ₀
  simp [baseFiberSector, baseFiberSectorSlice]

/-- Convex-combination formula for `baseFiberConfig` at fixed tail. -/
private theorem baseFiberConfig_convexCombo {m d : ℕ}
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (ζ₁ ζ₂ : Fin (d + 1) → ℂ)
    (a b : ℝ) (hab : a + b = 1) :
    a • baseFiberConfig m d ζtail ζ₁ + b • baseFiberConfig m d ζtail ζ₂ =
      baseFiberConfig m d ζtail (a • ζ₁ + b • ζ₂) := by
  ext k μ
  refine Fin.cases ?_ ?_ k
  · simp [baseFiberConfig_zero_apply, Pi.smul_apply]
  · intro i
    simp [baseFiberConfig_succ_apply, Pi.smul_apply, smul_add, add_assoc, add_left_comm]
    rw [← add_mul]
    have habC : (a : ℂ) + (b : ℂ) = 1 := by
      exact_mod_cast hab
    simp [habC]

/-- Real convex combinations commute with the coordinatewise complex Lorentz action. -/
private theorem complexLorentzAction_convexCombo {m d : ℕ}
    (Λ : ComplexLorentzGroup d)
    (w₁ w₂ : Fin (m + 1) → Fin (d + 1) → ℂ)
    (a b : ℝ) :
    a • BHW.complexLorentzAction Λ w₁ + b • BHW.complexLorentzAction Λ w₂ =
      BHW.complexLorentzAction Λ (a • w₁ + b • w₂) := by
  ext k μ
  simp [BHW.complexLorentzAction, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private theorem permutedForwardTube_convex_local {m d : ℕ} [NeZero d]
    (π : Equiv.Perm (Fin (m + 1))) :
    Convex ℝ (PermutedForwardTube d (m + 1) π) := by
  simpa [BHW_permutedForwardTube_eq (d := d) (n := m + 1) π] using
    (BHW.permutedForwardTube_convex (d := d) (n := m + 1) π)

/-- Each fixed-`Λ` base-fiber sector slice is convex, hence preconnected. -/
theorem baseFiberSectorSlice_convex {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (Λ : ComplexLorentzGroup d) :
    Convex ℝ (baseFiberSectorSlice m d ζtail π Λ) := by
  intro ζ₁ hζ₁ ζ₂ hζ₂ a b ha hb hab
  rcases hζ₁ with ⟨w₁, hw₁, hz₁⟩
  rcases hζ₂ with ⟨w₂, hw₂, hz₂⟩
  refine ⟨a • w₁ + b • w₂, ?_, ?_⟩
  · exact permutedForwardTube_convex_local π hw₁ hw₂ ha hb hab
  · calc
      baseFiberConfig m d ζtail (a • ζ₁ + b • ζ₂)
          = a • baseFiberConfig m d ζtail ζ₁ + b • baseFiberConfig m d ζtail ζ₂ := by
              symm
              exact baseFiberConfig_convexCombo ζtail ζ₁ ζ₂ a b hab
      _ = a • BHW.complexLorentzAction Λ w₁ + b • BHW.complexLorentzAction Λ w₂ := by
            rw [hz₁, hz₂]
      _ = BHW.complexLorentzAction Λ (a • w₁ + b • w₂) :=
            complexLorentzAction_convexCombo Λ w₁ w₂ a b

theorem baseFiberSectorSlice_isPreconnected {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (Λ : ComplexLorentzGroup d) :
    IsPreconnected (baseFiberSectorSlice m d ζtail π Λ) :=
  (baseFiberSectorSlice_convex ζtail π Λ).isPreconnected

/-- Fixed-`Λ` base-fiber slices can be characterized directly by pulling the
configuration back through `Λ⁻¹` and requiring it to lie in the permuted forward
tube. This removes the existential witness from the slice membership test. -/
theorem mem_baseFiberSectorSlice_iff_inv_mem_permutedForwardTube {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (Λ : ComplexLorentzGroup d)
    (ζ₀ : Fin (d + 1) → ℂ) :
    ζ₀ ∈ baseFiberSectorSlice m d ζtail π Λ ↔
      BHW.complexLorentzAction Λ⁻¹ (baseFiberConfig m d ζtail ζ₀) ∈
        PermutedForwardTube d (m + 1) π := by
  constructor
  · rintro ⟨w, hw, hz⟩
    rw [hz]
    simpa [BHW.complexLorentzAction_inv]
  · intro hζ₀
    refine ⟨BHW.complexLorentzAction Λ⁻¹ (baseFiberConfig m d ζtail ζ₀), hζ₀, ?_⟩
    symm
    simpa using
      (BHW.complexLorentzAction_inv (d := d) (n := m + 1) (Λ := Λ⁻¹)
        (z := baseFiberConfig m d ζtail ζ₀))

/-- Lorentz-group index set of nonempty fixed-`Λ` slices for a base-fiber sector. -/
def baseFiberSectorIndexSet (m d : ℕ) [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1))) : Set (ComplexLorentzGroup d) :=
  {Λ : ComplexLorentzGroup d | (baseFiberSectorSlice m d ζtail π Λ).Nonempty}

/-- Structural form of the base-fiber sector index set: a Lorentz parameter
belongs to the index set exactly when the transformed fixed tail lands in the
corresponding tail-difference sector. This removes the existential base
coordinate from the index-set geometry. -/
theorem mem_baseFiberSectorIndexSet_iff_inv_tail_mem_tailDiffPermSector
    {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (Λ : ComplexLorentzGroup d) :
    Λ ∈ baseFiberSectorIndexSet m d ζtail π ↔
      BHW.complexLorentzAction Λ⁻¹ ζtail ∈ tailDiffPermSector m d π := by
  constructor
  · rintro ⟨ζ₀, ⟨w, hw, hz⟩⟩
    refine ⟨w, hw, ?_⟩
    have hcfg :
        Fin.cons ζ₀ ζtail =
          BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w) := by
      calc
        Fin.cons ζ₀ ζtail
            = BHW.diffCoordFun (m + 1) d (baseFiberConfig m d ζtail ζ₀) := by
                simpa [BHW.diffCoordEquiv_apply] using
                  (BHW.diffCoord_partialSum (m + 1) d (Fin.cons ζ₀ ζtail)).symm
        _ = BHW.diffCoordFun (m + 1) d (BHW.complexLorentzAction Λ w) := by
              simp [hz]
        _ = BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w) :=
              diffCoordFun_complexLorentzAction Λ w
    have hinv :
        BHW.complexLorentzAction Λ⁻¹ (Fin.cons ζ₀ ζtail) =
          BHW.diffCoordFun (m + 1) d w := by
      rw [hcfg]
      exact BHW.complexLorentzAction_inv (d := d) (n := m + 1) Λ
        (BHW.diffCoordFun (m + 1) d w)
    have htail := congrArg Fin.tail hinv
    simpa [tail_complexLorentzAction, Fin.cons_self_tail] using htail.symm
  · rintro ⟨w, hw, htail⟩
    let ξ : Fin (m + 1) → Fin (d + 1) → ℂ :=
      BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w)
    let ζ₀ : Fin (d + 1) → ℂ := ξ 0
    refine ⟨ζ₀, ⟨w, hw, ?_⟩⟩
    have htailξ : Fin.tail ξ = ζtail := by
      calc
        Fin.tail ξ
            = BHW.complexLorentzAction Λ
                (Fin.tail (BHW.diffCoordFun (m + 1) d w)) := by
                    simp [ξ, tail_complexLorentzAction]
        _ = BHW.complexLorentzAction Λ (BHW.complexLorentzAction Λ⁻¹ ζtail) := by
              rw [htail]
        _ = ζtail := by
              simpa using
                (BHW.complexLorentzAction_inv (d := d) (n := m) (Λ := Λ⁻¹)
                  (z := ζtail))
    have hcons : Fin.cons ζ₀ ζtail = ξ := by
      ext k μ
      refine Fin.cases ?_ ?_ k
      · rfl
      · intro i
        have hi := congrFun htailξ i
        have hiμ := congrFun hi μ
        simpa [ζ₀, ξ, Fin.tail] using hiμ.symm
    calc
      baseFiberConfig m d ζtail ζ₀
          = BHW.partialSumFun (m + 1) d (Fin.cons ζ₀ ζtail) := rfl
      _ = BHW.partialSumFun (m + 1) d ξ := by rw [hcons]
      _ = BHW.partialSumFun (m + 1) d
            (BHW.complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w)) := by
              rfl
      _ = BHW.complexLorentzAction Λ
            (BHW.partialSumFun (m + 1) d (BHW.diffCoordFun (m + 1) d w)) := by
              exact partialSumFun_complexLorentzAction Λ (BHW.diffCoordFun (m + 1) d w)
      _ = BHW.complexLorentzAction Λ w := by
            simp [BHW.partialSum_diffCoord]

/-- A witness in a fixed base-fiber sector slice persists for nearby Lorentz
parameters, because `PermutedForwardTube` is open and the pulled-back
configuration depends continuously on `Λ`. -/
private theorem baseFiberSectorSlice_nonempty_nhds {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    {Λ : ComplexLorentzGroup d}
    {ζ₀ : Fin (d + 1) → ℂ}
    (hζ₀ : ζ₀ ∈ baseFiberSectorSlice m d ζtail π Λ) :
    ∃ V : Set (ComplexLorentzGroup d), IsOpen V ∧ Λ ∈ V ∧
      ∀ Λ' ∈ V, ζ₀ ∈ baseFiberSectorSlice m d ζtail π Λ' := by
  rw [mem_baseFiberSectorSlice_iff_inv_mem_permutedForwardTube (m := m) (d := d) ζtail π Λ ζ₀] at hζ₀
  refine ⟨{Λ' : ComplexLorentzGroup d |
      BHW.complexLorentzAction Λ'⁻¹ (baseFiberConfig m d ζtail ζ₀) ∈
        PermutedForwardTube d (m + 1) π}, ?_, hζ₀, ?_⟩
  · have hcont : Continuous (fun Λ' : ComplexLorentzGroup d =>
        BHW.complexLorentzAction Λ'⁻¹ (baseFiberConfig m d ζtail ζ₀)) := by
      simpa using
        (BHW.continuous_complexLorentzAction_fst (baseFiberConfig m d ζtail ζ₀)).comp
          (show Continuous fun Λ' : ComplexLorentzGroup d => Λ'⁻¹ from continuous_inv)
    have hopen : IsOpen (PermutedForwardTube d (m + 1) π) := by
      simpa [PermutedForwardTube] using
        ((BHW_forwardTube_eq (d := d) (n := m + 1)) ▸
          BHW.isOpen_forwardTube (d := d) (n := m + 1)).preimage
          (continuous_pi fun k =>
            continuous_pi fun μ =>
              (continuous_apply μ).comp (continuous_apply (π k)))
    exact hopen.preimage hcont
  · intro Λ' hΛ'
    exact (mem_baseFiberSectorSlice_iff_inv_mem_permutedForwardTube
      (m := m) (d := d) ζtail π Λ' ζ₀).2 hΛ'

theorem isOpen_baseFiberSectorIndexSet {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1))) :
    IsOpen (baseFiberSectorIndexSet m d ζtail π) := by
  rw [isOpen_iff_mem_nhds]
  intro Λ hΛ
  rcases hΛ with ⟨ζ₀, hζ₀⟩
  rcases baseFiberSectorSlice_nonempty_nhds (m := m) (d := d) ζtail π hζ₀ with
    ⟨V, hV_open, hΛV, hV_sub⟩
  refine Filter.mem_of_superset (hV_open.mem_nhds hΛV) ?_
  intro Λ' hΛ'V
  exact ⟨ζ₀, hV_sub Λ' hΛ'V⟩

theorem nonempty_baseFiberSectorIndexSet_of_sectorNonempty {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (hnonempty : (baseFiberSector m d ζtail π).Nonempty) :
    (baseFiberSectorIndexSet m d ζtail π).Nonempty := by
  rcases hnonempty with ⟨ζ₀, hζ₀⟩
  rw [baseFiberSector_eq_iUnion_slice (m := m) (d := d) ζtail π] at hζ₀
  rcases Set.mem_iUnion.mp hζ₀ with ⟨Λ, hΛ⟩
  exact ⟨Λ, ⟨ζ₀, hΛ⟩⟩

theorem nonempty_baseFiberSectorIndexSet_iff_sectorNonempty {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1))) :
    (baseFiberSectorIndexSet m d ζtail π).Nonempty ↔
      (baseFiberSector m d ζtail π).Nonempty := by
  constructor
  · rintro ⟨Λ, ζ₀, hζ₀⟩
    rw [baseFiberSector_eq_iUnion_slice (m := m) (d := d) ζtail π]
    exact ⟨ζ₀, Set.mem_iUnion.mpr ⟨Λ, hζ₀⟩⟩
  · exact nonempty_baseFiberSectorIndexSet_of_sectorNonempty (m := m) (d := d) ζtail π

/-- Connected-index reduction for base-fiber sector slices. If the set of Lorentz
parameters with nonempty slices is connected, then the full base-fiber sector is
preconnected. -/
theorem isPreconnected_baseFiberSector_of_indexConnected {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (π : Equiv.Perm (Fin (m + 1)))
    (hidx_conn : IsConnected (baseFiberSectorIndexSet m d ζtail π))
    (hnonempty : (baseFiberSector m d ζtail π).Nonempty) :
    IsPreconnected (baseFiberSector m d ζtail π) := by
  let t : Set (ComplexLorentzGroup d) := baseFiberSectorIndexSet m d ζtail π

  have hpre_union_subtype :
      IsPreconnected
        (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
          baseFiberSectorSlice m d ζtail π x.1) := by
    apply IsPreconnected.iUnion_of_reflTransGen
    · intro x
      exact baseFiberSectorSlice_isPreconnected ζtail π x.1
    · intro x y
      let R :
          {Λ : ComplexLorentzGroup d | t Λ} →
          {Λ : ComplexLorentzGroup d | t Λ} → Prop :=
        fun a b =>
          ((baseFiberSectorSlice m d ζtail π a.1) ∩
            (baseFiberSectorSlice m d ζtail π b.1)).Nonempty
      let U : Set {Λ : ComplexLorentzGroup d | t Λ} :=
        {a | Relation.ReflTransGen R x a}

      have hU_open : IsOpen U := by
        rw [isOpen_iff_mem_nhds]
        intro a haU
        rcases a.2 with ⟨ζ₀, hζ₀a⟩
        rcases baseFiberSectorSlice_nonempty_nhds (m := m) (d := d) ζtail π hζ₀a with
          ⟨V, hV_open, haV, hV_sub⟩
        let W : Set {Λ : ComplexLorentzGroup d | t Λ} := Subtype.val ⁻¹' V
        have hW_open : IsOpen W := hV_open.preimage continuous_subtype_val
        have haW : a ∈ W := by simpa [W] using haV
        refine Filter.mem_of_superset (hW_open.mem_nhds haW) ?_
        intro b hbW
        have hbV : b.1 ∈ V := by simpa [W] using hbW
        have hζ₀b : ζ₀ ∈ baseFiberSectorSlice m d ζtail π b.1 := hV_sub b.1 hbV
        have hab : R a b := ⟨ζ₀, hζ₀a, hζ₀b⟩
        exact Relation.ReflTransGen.tail haU hab

      have hU_closed : IsClosed U := by
        rw [← isOpen_compl_iff]
        rw [isOpen_iff_mem_nhds]
        intro a haU
        rcases a.2 with ⟨ζ₀, hζ₀a⟩
        rcases baseFiberSectorSlice_nonempty_nhds (m := m) (d := d) ζtail π hζ₀a with
          ⟨V, hV_open, haV, hV_sub⟩
        let W : Set {Λ : ComplexLorentzGroup d | t Λ} := Subtype.val ⁻¹' V
        have hW_open : IsOpen W := hV_open.preimage continuous_subtype_val
        have haW : a ∈ W := by simpa [W] using haV
        refine Filter.mem_of_superset (hW_open.mem_nhds haW) ?_
        intro b hbW hbU
        have hbV : b.1 ∈ V := by simpa [W] using hbW
        have hζ₀b : ζ₀ ∈ baseFiberSectorSlice m d ζtail π b.1 := hV_sub b.1 hbV
        have hba : R b a := ⟨ζ₀, hζ₀b, hζ₀a⟩
        have ha_inU : a ∈ U := Relation.ReflTransGen.tail hbU hba
        exact haU ha_inU

      have hU_nonempty : U.Nonempty := ⟨x, Relation.ReflTransGen.refl⟩

      haveI : ConnectedSpace {Λ : ComplexLorentzGroup d | t Λ} :=
        Subtype.connectedSpace hidx_conn

      have hU_eq : U = Set.univ := IsClopen.eq_univ ⟨hU_closed, hU_open⟩ hU_nonempty
      have : y ∈ U := by rw [hU_eq]; exact Set.mem_univ _
      exact this

  have h_union_eq_all :
      (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
        baseFiberSectorSlice m d ζtail π x.1)
        = ⋃ Λ : ComplexLorentzGroup d,
            baseFiberSectorSlice m d ζtail π Λ := by
    ext ζ₀
    constructor
    · intro hζ₀
      rcases Set.mem_iUnion.mp hζ₀ with ⟨x, hx⟩
      exact Set.mem_iUnion.mpr ⟨x.1, hx⟩
    · intro hζ₀
      rcases Set.mem_iUnion.mp hζ₀ with ⟨Λ, hΛ⟩
      have hΛt : t Λ := ⟨ζ₀, hΛ⟩
      exact Set.mem_iUnion.mpr ⟨⟨Λ, hΛt⟩, hΛ⟩

  have hset_eq :
      baseFiberSector m d ζtail π =
        (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
          baseFiberSectorSlice m d ζtail π x.1) := by
    calc
      baseFiberSector m d ζtail π
          = ⋃ Λ : ComplexLorentzGroup d,
              baseFiberSectorSlice m d ζtail π Λ :=
            baseFiberSector_eq_iUnion_slice (m := m) (d := d) ζtail π
      _ = (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
            baseFiberSectorSlice m d ζtail π x.1) :=
          h_union_eq_all.symm

  rcases hnonempty with ⟨ζ₀, hζ₀⟩
  have h_union_nonempty :
      (⋃ x : {Λ : ComplexLorentzGroup d | t Λ},
        baseFiberSectorSlice m d ζtail π x.1).Nonempty := by
    rw [← hset_eq]
    exact ⟨ζ₀, hζ₀⟩
  simpa [hset_eq] using hpre_union_subtype

/-- Sector-decomposition reduction for base-fiber preconnectedness. This is the
exact analogue of `permutedExtendedTube_isPreconnected`, but on the fixed-tail
base fiber. Once sector slices are known to be preconnected and adjacent slices
overlap, the full base fiber is preconnected. -/
theorem baseFiber_isPreconnected_of_sector_geometry {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (hsector : ∀ π : Equiv.Perm (Fin (m + 1)),
      IsPreconnected (baseFiberSector m d ζtail π))
    (hoverlap : ∀ (π : Equiv.Perm (Fin (m + 1))) (i : Fin (m + 1))
      (hi : i.val + 1 < m + 1),
      (baseFiberSector m d ζtail π ∩
        baseFiberSector m d ζtail (π * Equiv.swap i ⟨i.val + 1, hi⟩)).Nonempty) :
    IsPreconnected (baseFiber m d ζtail) := by
  rw [baseFiber_eq_iUnion_baseFiberSector]
  apply IsPreconnected.iUnion_of_reflTransGen
  · exact hsector
  · intro π₁ π₂
    set τ := π₁⁻¹ * π₂
    suffices h :
        ∀ σ : Equiv.Perm (Fin (m + 1)),
          Relation.ReflTransGen
            (fun i j =>
              (baseFiberSector m d ζtail i ∩ baseFiberSector m d ζtail j).Nonempty)
            π₁ (π₁ * σ) by
      have : π₂ = π₁ * τ := by simp [τ]
      rw [this]
      exact h τ
    intro σ
    induction σ using BHW.Fin.Perm.adjSwap_induction_right with
    | one =>
        simpa using Relation.ReflTransGen.refl
    | mul_adj σ₀ i₀ hi₀ ih =>
        apply Relation.ReflTransGen.tail ih
        simpa [baseFiberSector, mul_assoc] using hoverlap (π₁ * σ₀) i₀ hi₀

/-- Cleaner sector-gluing reduction for the base fiber: only the nonempty
permutation sectors matter. If every sector is preconnected and the graph of
nonempty sectors is connected under nonempty overlaps, then the full base fiber
is preconnected. This is the right theorem surface for the live blocker, since
empty sectors should not force artificial overlap obligations. -/
theorem baseFiber_isPreconnected_of_active_sector_geometry {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (hsector : ∀ π : Equiv.Perm (Fin (m + 1)),
      IsPreconnected (baseFiberSector m d ζtail π))
    (hactive :
      ∀ x y : {π : Equiv.Perm (Fin (m + 1)) // (baseFiberSector m d ζtail π).Nonempty},
        Relation.ReflTransGen
          (fun a b :
            {π : Equiv.Perm (Fin (m + 1)) // (baseFiberSector m d ζtail π).Nonempty} =>
              (baseFiberSector m d ζtail a.1 ∩ baseFiberSector m d ζtail b.1).Nonempty)
          x y) :
    IsPreconnected (baseFiber m d ζtail) := by
  have h_union_eq :
      (⋃ x : {π : Equiv.Perm (Fin (m + 1)) // (baseFiberSector m d ζtail π).Nonempty},
        baseFiberSector m d ζtail x.1)
        = ⋃ π : Equiv.Perm (Fin (m + 1)), baseFiberSector m d ζtail π := by
    ext ζ₀
    constructor
    · intro hζ₀
      rcases Set.mem_iUnion.mp hζ₀ with ⟨x, hx⟩
      exact Set.mem_iUnion.mpr ⟨x.1, hx⟩
    · intro hζ₀
      rcases Set.mem_iUnion.mp hζ₀ with ⟨π, hπ⟩
      have hπ_nonempty : (baseFiberSector m d ζtail π).Nonempty := ⟨ζ₀, hπ⟩
      exact Set.mem_iUnion.mpr ⟨⟨π, hπ_nonempty⟩, hπ⟩
  rw [baseFiber_eq_iUnion_baseFiberSector]
  rw [← h_union_eq]
  apply IsPreconnected.iUnion_of_reflTransGen
  · intro x
    exact hsector x.1
  · intro x y
    exact hactive x y

/-- Combined reduction for the fixed-tail base fiber. To prove
`isPreconnected_baseFiber`, it is enough to show:
1. each nonempty sector has connected Lorentz index set of nonempty fixed-`Λ`
   slices;
2. the graph of nonempty sectors is connected under nonempty overlaps.

This packages the current production strategy into the exact two geometric
subproblems that remain after the slice-level convexity work. -/
theorem baseFiber_isPreconnected_of_index_and_active_geometry {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ)
    (hidx_conn :
      ∀ x : {π : Equiv.Perm (Fin (m + 1)) // (baseFiberSector m d ζtail π).Nonempty},
        IsConnected (baseFiberSectorIndexSet m d ζtail x.1))
    (hactive :
      ∀ x y : {π : Equiv.Perm (Fin (m + 1)) // (baseFiberSector m d ζtail π).Nonempty},
        Relation.ReflTransGen
          (fun a b :
            {π : Equiv.Perm (Fin (m + 1)) // (baseFiberSector m d ζtail π).Nonempty} =>
              (baseFiberSector m d ζtail a.1 ∩ baseFiberSector m d ζtail b.1).Nonempty)
          x y) :
    IsPreconnected (baseFiber m d ζtail) := by
  apply baseFiber_isPreconnected_of_active_sector_geometry (m := m) (d := d) ζtail
  · intro π
    by_cases hπ : (baseFiberSector m d ζtail π).Nonempty
    · exact isPreconnected_baseFiberSector_of_indexConnected
        (m := m) (d := d) ζtail π
        (hidx_conn ⟨π, hπ⟩) hπ
    · have hempty : baseFiberSector m d ζtail π = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun ζ₀ hζ₀ => hπ ⟨ζ₀, hζ₀⟩
      simpa [hempty] using (isPreconnected_empty : IsPreconnected (∅ : Set (Fin (d + 1) → ℂ)))
  · exact hactive

/-- **Preconnectedness of the fixed-tail base fiber.**

    For fixed tail difference coordinates `ζtail`, the set of base values `ζ₀`
    for which `baseFiberConfig m d ζtail ζ₀` lies in the permuted extended tube
    is preconnected.

    This is the cleaner remaining geometric blocker for BHW translation
    invariance. Once this theorem is available, the already-proved local
    translation invariance in `bhw_translation_local` upgrades to global
    constancy on the base fiber via
    `bhw_translation_invariant_of_baseFiber_isPreconnected`.

    Compared to the older overlap-domain theorem on
    `PET ∩ {z | z + c ∈ PET}`, this fiber statement matches the actual
    difference-variable geometry of translation invariance and avoids the
    false-looking 1-dimensional line-fiber route that was removed.

    The live production reduction is now
    `baseFiber_isPreconnected_of_index_and_active_geometry`, so the remaining
    work is exactly:
    1. connectedness of the Lorentz index set for each nonempty fiber sector;
    2. connectedness of the active sector graph under nonempty overlaps.

    **Numerical status (2026-03-14).** In the tested `d = 1`, `n = 2` regime,
    sampled base fibers remained connected even for the same shifts that split
    the one-complex-dimensional line fiber `Ω = {t | z + t c ∈ PET}`.

    Ref: Streater-Wightman §2.5; Jost, "General Theory of Quantized Fields" §III.1 -/
theorem isPreconnected_baseFiber {m d : ℕ} [NeZero d]
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    IsPreconnected (baseFiber m d ζtail) := by
  sorry

/-! #### Route 1: Translation invariance via reduced difference coordinates

Instead of proving the base fiber is preconnected, Route 1 constructs a
**second** holomorphic extension G that is algebraically translation-invariant
(as a pullback from reduced difference coordinates), then uses BHW uniqueness
to show G = F_ext on PET. -/

/-- A normalized basepoint cutoff (Schwartz function with integral 1),
constructed from a smooth compactly supported bump function. -/
noncomputable def exists_normalized_cutoff (d : ℕ) [NeZero d] :
    BHW.NormalizedBasepointCutoff d :=
  BHW.normalizedCutoffOfBump d

namespace BHW

omit [NeZero d] in
/-- The reduced difference map sends forward-tube points to the reduced forward tube.

For z ∈ ForwardTube, the successive differences z_{j+1} - z_j have imaginary
parts in V₊ by definition, which is exactly the reduced forward-tube condition. -/
private theorem reducedDiffMap_mem_reducedForwardTubeN [NeZero d]
    (m : ℕ) {z : Fin (m + 1) → Fin (d + 1) → ℂ}
    (hz : z ∈ ForwardTube d (m + 1)) :
    reducedDiffMap (m + 1) d z ∈ ReducedForwardTubeN d m := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  have hz_pft : z ∈ PermutedForwardTube d (m + 1) 1 := by
    simpa [PermutedForwardTube] using hz
  have hpft := reducedDiffMap_mem_reducedPermutedForwardTube_of_mem_permutedForwardTube
    (1 : Equiv.Perm (Fin (m + 1))) hz_pft
  rwa [mem_reducedPermutedForwardTube, permOnReducedDiff_one] at hpft

omit [NeZero d] in
/-- Route 1 extension agrees with the spectrum-condition witness on the forward tube.

This is the key bridge: `route1AbsoluteBHWExtensionCanonical` is a pullback from
reduced coordinates, so it agrees with the input function on the forward tube
(where the input was descended from the spectrum condition). -/
theorem route1_agrees_with_old_on_forwardTube [NeZero d]
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (m : ℕ) (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d (m + 1)) :
    route1AbsoluteBHWExtensionCanonical Wfn χ m z =
      (Wfn.spectrum_condition (m + 1)).choose z := by
  -- Unfold to reduced BHW extension applied to reducedDiffMap z
  set hInput := route1ReducedAnalyticInputExists (d := d) Wfn χ m
  set ext := route1ReducedBHWExtension (d := d) Wfn χ hInput
  -- route1AbsoluteBHWExtensionCanonical z = ext.toFun (reducedDiffMap z)
  show ext.toFun (reducedDiffMap (m + 1) d z) = (Wfn.spectrum_condition (m + 1)).choose z
  -- reducedDiffMap z ∈ ReducedForwardTubeN, so ext agrees with the input there
  have hred : reducedDiffMap (m + 1) d z ∈ ReducedForwardTubeN d m :=
    reducedDiffMap_mem_reducedForwardTubeN m hz
  calc ext.toFun (reducedDiffMap (m + 1) d z)
      = hInput.toFun (reducedDiffMap (m + 1) d z) :=
          ext.agrees_on_reducedForwardTube _ hred
    _ = (route1ReducedPreInputFromSpectrumCondition (d := d) Wfn m).toFun
          (reducedDiffMap (m + 1) d z) := rfl
    _ = (Wfn.spectrum_condition (m + 1)).choose z :=
          route1ReducedPreInputFromSpectrumCondition_factorization (d := d) Wfn m z hz

omit [NeZero d] in
/-- Route 1 extension is holomorphic on the permuted extended tube.

The Route 1 extension is a composition of the reduced BHW extension
(holomorphic on reduced PET) with the reduced difference map (a CLM,
hence holomorphic everywhere). Since reduced PET = reducedDiffMap '' PET,
the composition is holomorphic on PET. -/
theorem route1_holomorphicOn_PET [NeZero d]
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) (m : ℕ) :
    DifferentiableOn ℂ (route1AbsoluteBHWExtensionCanonical Wfn χ m)
      (PermutedExtendedTube d (m + 1)) := by
  set hInput := route1ReducedAnalyticInputExists (d := d) Wfn χ m
  set ext := route1ReducedBHWExtension (d := d) Wfn χ hInput
  -- route1AbsoluteBHWExtensionCanonical = ext.toFun ∘ reducedDiffMap
  show DifferentiableOn ℂ (fun z => ext.toFun (reducedDiffMap (m + 1) d z))
    (PermutedExtendedTube d (m + 1))
  apply DifferentiableOn.comp ext.holomorphic
    (reducedDiffMap (m + 1) d).differentiable.differentiableOn
  -- For z ∈ PET, reducedDiffMap z ∈ reducedPermutedExtendedTube (which = reducedDiffMap '' PET)
  intro z hz
  exact Set.mem_image_of_mem _ hz

end BHW

/-- **BHW extension is translation invariant on the permuted extended tube.**

    The n-point Wightman function W_n(z₁, ..., zₙ) depends only on the differences
    z_k - z_{k-1}, hence is invariant under simultaneous translation z_k ↦ z_k + c
    for any constant c ∈ ℂ^{d+1}. The BHW extension inherits this property.

    **Proof.** By Route 1 (reduced difference coordinates): the Route 1 extension
    `G = route1AbsoluteBHWExtensionCanonical` is a pullback from reduced coordinates,
    hence algebraically translation-invariant. By BHW uniqueness (`W_analytic_BHW_unique`),
    `G = F_ext` on PET, so:

      F_ext(z+c) = G(z+c)  [BHW uniqueness]
               = G(z)      [algebraic: G is a pullback from reduced coords]
               = F_ext(z)  [BHW uniqueness]

    Ref: Streater-Wightman §2.5 (translation invariance);
    Jost, "The General Theory of Quantized Fields" §III.1 -/
theorem bhw_translation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c μ) =
    (W_analytic_BHW Wfn n).val z := by
  -- Trivial cases
  by_cases hc : c = 0
  · simp [hc]
  by_cases hn : n = 0
  · subst hn
    have hshift : (fun k μ => z k μ + c μ) = z := by
      ext k
      exact Fin.elim0 k
    simp [hshift]
  -- Cast n to m + 1 form
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  -- Route 1 construction
  let χ := exists_normalized_cutoff d
  set G := BHW.route1AbsoluteBHWExtensionCanonical Wfn χ m
  -- G is holomorphic on PET (in the BHW namespace sense, then bridge)
  have hG_holo : DifferentiableOn ℂ G (PermutedExtendedTube d (m + 1)) := by
    rw [← BHW_permutedExtendedTube_eq]
    exact BHW.route1_holomorphicOn_PET Wfn χ m
  -- G agrees with W_analytic on FT
  have hG_ft : ∀ w ∈ ForwardTube d (m + 1),
      G w = (Wfn.spectrum_condition (m + 1)).choose w := by
    intro w hw
    exact BHW.route1_agrees_with_old_on_forwardTube Wfn χ m w
      (BHW_forwardTube_eq (d := d) (n := m + 1) ▸ hw)
  -- By BHW uniqueness: G = F_ext on PET
  have hG_eq : ∀ w ∈ PermutedExtendedTube d (m + 1),
      G w = (W_analytic_BHW Wfn (m + 1)).val w :=
    W_analytic_BHW_unique Wfn (m + 1) G hG_holo hG_ft
  -- 3-step calc via Route 1 translation invariance
  calc (W_analytic_BHW Wfn (m + 1)).val (fun k μ => z k μ + c μ)
      = G (fun k μ => z k μ + c μ) := (hG_eq _ hzc).symm
    _ = G z := BHW.route1AbsoluteBHWExtensionCanonical_translate Wfn χ m z c
    _ = (W_analytic_BHW Wfn (m + 1)).val z := hG_eq z hz

/-! #### TranslatedPET kernel extension

    The BHW extension `F_ext = (W_analytic_BHW Wfn n).val` is defined by
    `Classical.choice` as a total function on `Fin n → Fin (d + 1) → ℂ`, but only
    behaves meaningfully on `PermutedExtendedTube` (PET). For n ≥ d+2, Wick-rotated
    Euclidean configurations generically lie in `TranslatedPET \ PET`, a set of
    positive measure (see W11Counterexample.lean).

    The definitions below give a well-defined, translation-invariant kernel on
    `TranslatedPET` by choosing any PET witness. This is the correct upstream
    surface for Wick-rotated pairings. -/

/-- **F_ext has a well-defined value on TranslatedPET.**

    If z+c₁ and z+c₂ are both in PET, then F_ext(z+c₁) = F_ext(z+c₂).
    Proof: Apply `bhw_translation_invariant` with translation (c₂ - c₁). -/
theorem F_ext_value_on_translatedPET {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (c₁ c₂ : Fin (d + 1) → ℂ)
    (h₁ : (fun k μ => z k μ + c₁ μ) ∈ PermutedExtendedTube d n)
    (h₂ : (fun k μ => z k μ + c₂ μ) ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c₁ μ) =
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c₂ μ) := by
  have key := bhw_translation_invariant Wfn (fun μ => c₂ μ - c₁ μ)
    (fun k μ => z k μ + c₁ μ) h₁
    (by convert h₂ using 1; ext k μ; ring)
  simpa [sub_eq_add_neg, add_assoc] using key.symm

/-- The BHW extension evaluated via a TranslatedPET witness.

    For z ∈ TranslatedPET, this evaluates F_ext at z + c for some c with z+c ∈ PET.
    By `F_ext_value_on_translatedPET`, the result is independent of the witness c. -/
noncomputable def F_ext_on_translatedPET {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n) : ℂ :=
  (W_analytic_BHW Wfn n).val (fun k μ => z k μ + hz.choose μ)

/-- `F_ext_on_translatedPET` agrees with `F_ext` on PET. -/
theorem F_ext_on_translatedPET_eq_on_PET {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz_pet : z ∈ PermutedExtendedTube d n)
    (hz_tpet : z ∈ TranslatedPET d n) :
    F_ext_on_translatedPET Wfn z hz_tpet =
    (W_analytic_BHW Wfn n).val z := by
  unfold F_ext_on_translatedPET
  have := F_ext_value_on_translatedPET Wfn z hz_tpet.choose 0
    hz_tpet.choose_spec
    (show (fun k μ => z k μ + (0 : Fin (d + 1) → ℂ) μ) ∈ PermutedExtendedTube d n by
      simp_rw [Pi.zero_apply, add_zero]; exact hz_pet)
  simp_rw [Pi.zero_apply, add_zero] at this
  exact this

/-- `F_ext_on_translatedPET` is translation-invariant on TranslatedPET. -/
theorem F_ext_on_translatedPET_translation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ TranslatedPET d n) :
    F_ext_on_translatedPET Wfn z hz =
    F_ext_on_translatedPET Wfn (fun k μ => z k μ + c μ) hzc := by
  simp only [F_ext_on_translatedPET]
  show (W_analytic_BHW Wfn n).val (fun k μ => z k μ + hz.choose μ) =
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c μ + hzc.choose μ)
  have := F_ext_value_on_translatedPET Wfn z hz.choose (fun μ => c μ + hzc.choose μ)
    hz.choose_spec
    (show (fun k μ => z k μ + (fun μ => c μ + hzc.choose μ) μ) ∈ PermutedExtendedTube d n by
      convert hzc.choose_spec using 1; ext k μ; ring)
  convert this using 2
  ext k μ; ring

/-- Total-function version of `F_ext_on_translatedPET`: returns the TranslatedPET
    value when z ∈ TranslatedPET, else 0. This gives a well-defined integrand
    everywhere, with the "correct" BHW-extended value on the only set that matters
    (the complement is null for Wick-rotated Euclidean configurations, by
    `ae_euclidean_points_in_translatedPET`). -/
noncomputable def F_ext_on_translatedPET_total {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ) : ℂ :=
  if hz : z ∈ TranslatedPET d n then
    F_ext_on_translatedPET Wfn z hz
  else 0

/-- On PET, `F_ext_on_translatedPET_total` unfolds to the raw BHW extension. -/
theorem F_ext_on_translatedPET_total_eq_on_PET {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz_pet : z ∈ PermutedExtendedTube d n) :
    F_ext_on_translatedPET_total Wfn z =
    (W_analytic_BHW Wfn n).val z := by
  have hz_tpet : z ∈ TranslatedPET d n :=
    PermutedExtendedTube_subset_TranslatedPET hz_pet
  simp only [F_ext_on_translatedPET_total, dif_pos hz_tpet]
  exact F_ext_on_translatedPET_eq_on_PET Wfn z hz_pet hz_tpet

/-- `F_ext_on_translatedPET_total` is translation-invariant on TranslatedPET. -/
theorem F_ext_on_translatedPET_total_translation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n) :
    F_ext_on_translatedPET_total Wfn z =
    F_ext_on_translatedPET_total Wfn (fun k μ => z k μ + c μ) := by
  have hzc : (fun k μ => z k μ + c μ) ∈ TranslatedPET d n :=
    translatedPET_translate hz c
  simp only [F_ext_on_translatedPET_total, dif_pos hz, dif_pos hzc]
  exact F_ext_on_translatedPET_translation_invariant Wfn z c hz hzc

/-- `F_ext_on_translatedPET_total` is permutation-invariant on `TranslatedPET`. -/
theorem F_ext_on_translatedPET_total_perm_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n) :
    F_ext_on_translatedPET_total Wfn z =
    F_ext_on_translatedPET_total Wfn (fun k => z (σ k)) := by
  let zσ : Fin n → Fin (d + 1) → ℂ := fun k => z (σ k)
  have hzc : (fun k μ => z k μ + hz.choose μ) ∈ PermutedExtendedTube d n :=
    hz.choose_spec
  have hzσc : (fun k μ => zσ k μ + hz.choose μ) ∈ PermutedExtendedTube d n := by
    simpa [zσ] using permutedExtendedTube_perm (d := d) (n := n) σ hzc
  have hzσ : zσ ∈ TranslatedPET d n := ⟨hz.choose, hzσc⟩
  have hperm :
      (W_analytic_BHW Wfn n).val (fun k μ => z k μ + hz.choose μ) =
        (W_analytic_BHW Wfn n).val (fun k μ => zσ k μ + hz.choose μ) := by
    simpa [zσ] using
      (((W_analytic_BHW Wfn n).property.2.2.2 σ
        (fun k μ => z k μ + hz.choose μ) hzc)).symm
  have hbridge :
      (W_analytic_BHW Wfn n).val (fun k μ => zσ k μ + hz.choose μ) =
        (W_analytic_BHW Wfn n).val (fun k μ => zσ k μ + hzσ.choose μ) :=
    F_ext_value_on_translatedPET Wfn zσ hz.choose hzσ.choose hzσc hzσ.choose_spec
  rw [F_ext_on_translatedPET_total, dif_pos hz, F_ext_on_translatedPET,
    F_ext_on_translatedPET_total, dif_pos hzσ, F_ext_on_translatedPET]
  exact hperm.trans hbridge

/-- Euclidean rotations preserve the total TranslatedPET extension. -/
theorem F_ext_on_translatedPET_total_rotation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hz : (fun k => wickRotatePoint (x k)) ∈ TranslatedPET d n) :
    F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (x k)) =
    F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (R.mulVec (x k))) := by
  let Λ := ComplexLorentzGroup.ofEuclidean R hR_det hR_orth
  let z : Fin n → Fin (d + 1) → ℂ := fun k => wickRotatePoint (x k)
  let zR : Fin n → Fin (d + 1) → ℂ := fun k => wickRotatePoint (R.mulVec (x k))
  let cR : Fin (d + 1) → ℂ := fun μ => ∑ ν, Λ.val μ ν * hz.choose ν
  have hzc : (fun k μ => z k μ + hz.choose μ) ∈ PermutedExtendedTube d n :=
    hz.choose_spec
  have hzR_add :
      (fun k μ => zR k μ + cR μ) =
        BHW.complexLorentzAction Λ (fun k μ => z k μ + hz.choose μ) := by
    ext k μ
    rw [show zR k μ = ∑ ν, Λ.val μ ν * wickRotatePoint (x k) ν by
      simpa [zR, z, BHW.complexLorentzAction] using
        wickRotatePoint_ofEuclidean R hR_det hR_orth (x k) μ]
    simp [cR, BHW.complexLorentzAction, z]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ν hν
    ring
  have hzR_pet : (fun k μ => zR k μ + cR μ) ∈ PermutedExtendedTube d n := by
    have hzcBHW :
        (fun k μ => z k μ + hz.choose μ) ∈ BHW.PermutedExtendedTube d n := by
      simpa [BHW_permutedExtendedTube_eq (d := d) (n := n)] using hzc
    have hzR_petBHW :
        BHW.complexLorentzAction Λ (fun k μ => z k μ + hz.choose μ) ∈
          BHW.PermutedExtendedTube d n :=
      BHW.complexLorentzAction_mem_permutedExtendedTube hzcBHW Λ
    simpa [BHW_permutedExtendedTube_eq (d := d) (n := n), hzR_add] using hzR_petBHW
  have hzR : zR ∈ TranslatedPET d n := ⟨cR, hzR_pet⟩
  have hlor :
      (W_analytic_BHW Wfn n).val (fun k μ => zR k μ + cR μ) =
        (W_analytic_BHW Wfn n).val (fun k μ => z k μ + hz.choose μ) := by
    have h :=
      (W_analytic_BHW Wfn n).property.2.2.1 Λ (fun k μ => z k μ + hz.choose μ) hzc
    simpa [hzR_add, BHW.complexLorentzAction] using h
  have hbridge :
      (W_analytic_BHW Wfn n).val (fun k μ => zR k μ + cR μ) =
        (W_analytic_BHW Wfn n).val (fun k μ => zR k μ + hzR.choose μ) :=
    F_ext_value_on_translatedPET Wfn zR cR hzR.choose hzR_pet hzR.choose_spec
  simp only [F_ext_on_translatedPET_total, dif_pos hz, dif_pos hzR, F_ext_on_translatedPET,
    z, zR]
  exact hlor.symm.trans hbridge

/-- The smeared BHW extension equals the smeared W_analytic for approach directions
    within the forward tube cone.

    When the approach direction η has successive differences in V₊ (not just
    per-component V₊), the point x + iεη lies in the forward tube for all ε > 0.
    Since F_ext = W_analytic on the forward tube (BHW property 2), the integrals
    agree pointwise in ε, so the limits (distributional boundary values) also agree.

    This captures the forward-tube membership calculation: for z_k = x_k + iεη_k,
    the successive difference of imaginary parts is ε(η_k - η_{k-1}), which lies in
    V₊ when η has successive differences in V₊ and ε > 0 (V₊ is a cone).

    Ref: Streater-Wightman, Theorem 2-11; BHW property 2 -/
theorem bhw_smeared_eq_W_analytic_forwardTube_direction {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη_ft : ∀ k : Fin n,
      let prev := if _h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩
      InOpenForwardCone d (fun μ => η k μ - prev μ))
    (ε : ℝ) (hε : ε > 0) :
    (∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n).val
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
    (∫ x : NPointDomain d n,
      (Wfn.spectrum_condition n).choose
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
  congr 1; ext x; congr 1
  -- F_ext and W_analytic agree at x + iεη because x + iεη ∈ ForwardTube
  apply (W_analytic_BHW Wfn n).property.2.1
  -- x + iεη ∈ ForwardTube: successive differences of Im parts are ε·(η_k - η_{k-1}) ∈ V₊
  intro k
  show InOpenForwardCone d _
  -- The imaginary part of the successive difference is ε·(η_k - η_{k-1})
  have him : (fun μ => ((↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) -
      (if h : k.val = 0 then 0 else
        fun μ => ↑(x ⟨k.val - 1, by omega⟩ μ) + ↑ε * ↑(η ⟨k.val - 1, by omega⟩ μ) * Complex.I) μ).im) =
      ε • (fun μ => η k μ - (if h : k.val = 0 then 0 else η ⟨k.val - 1, by omega⟩) μ) := by
    ext μ
    by_cases hk : (k : ℕ) = 0
    · simp [hk, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
            Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
    · simp [hk, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
            Complex.ofReal_re, Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
      ring
  rw [him]
  exact inOpenForwardCone_smul d ε hε _ (hη_ft k)

/-- The BHW extension has the same distributional boundary values as W_n.

    The BHW extension F_ext agrees with W_analytic on the forward tube, and
    W_analytic has distributional boundary values recovering W_n by `spectrum_condition`.
    Therefore F_ext also has these boundary values: for η with each η_k ∈ V+,
    lim_{ε→0+} ∫ F_ext(x + iεη) f(x) dx = W_n(f).

    For `η : InForwardCone d n η`, the point `x + iεη` is in `ForwardTube d n` for
    every `ε > 0`. Hence `F_ext = W_analytic` pointwise on the whole integration path,
    and the claimed limit follows directly from `spectrum_condition`.

    Ref: Streater-Wightman Theorem 2-11 -/
theorem bhw_distributional_boundary_values {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (W_analytic_BHW Wfn n).val
            (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)) := by
  intro f η hη
  have h_sc := (Wfn.spectrum_condition n).choose_spec.2.2 f η hη
  refine Filter.Tendsto.congr' ?_ h_sc
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨Set.Ioi 0, self_mem_nhdsWithin, fun ε hε =>
    (bhw_smeared_eq_W_analytic_forwardTube_direction Wfn f η hη ε hε).symm⟩

/-! #### Schwinger function construction -/

/-- Define Schwinger functions from Wightman functions via Wick rotation.

    The construction uses the **TranslatedPET-extended** BHW kernel
    `F_ext_on_translatedPET_total` composed with the Wick rotation map
    (τ,x⃗) ↦ (iτ,x⃗):

      S_n(f) = ∫_x F_ext_on_translatedPET_total(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ) f(x₁,...,xₙ) dx

    `F_ext_on_translatedPET_total` agrees with `F_ext` on PET and extends to
    `TranslatedPET` via translation invariance (`bhw_translation_invariant`),
    returning 0 on the null set where wick(x) ∉ TranslatedPET. This is crucial
    for `n ≥ d+2`, where Wick-rotated Euclidean configurations generically lie
    in `TranslatedPET \ PET` (see `W11Counterexample.lean`). On this set, the
    raw `F_ext` value would be arbitrary `Classical.choice` garbage, but the
    TranslatedPET-extended value is the unique translation-invariant extension.

    Important: this full-Schwartz pairing belongs to the Wightman side of the
    story. Wightman functions are tempered distributions on all of
    `SchwartzNPoint`, so there is no problem with a raw full-Schwartz pairing
    appearing here.

    What the corrected OS-I axiom surface forbids is interpreting this raw
    Euclidean Wick-rotated formula as the honest Schwinger object. The honest
    Euclidean Schwinger family of the project lives on `ZeroDiagonalSchwartz`.
    So the present definition should be read as the raw Wightman-side
    Wick-rotated boundary pairing, while `constructSchwingerFunctions` below is
    the actual zero-diagonal Euclidean Schwinger family.

    Ref: OS I (1973), Section 5; Streater-Wightman, Chapter 3 -/
def wickRotatedBoundaryPairing (Wfn : WightmanFunctions d) :
    (n : ℕ) → SchwartzNPoint d n → ℂ :=
  fun n f =>
    ∫ x : NPointDomain d n,
      F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (x k)) * (f x)

/-- The honest OS-I Euclidean family extracted from Wightman functions: the raw
    Wick-rotated pairing restricted to `ZeroDiagonalSchwartz`.

    This is the Euclidean Schwinger family that should appear in the OS axioms
    and in the `R -> E` direction. -/
def constructSchwingerFunctions (Wfn : WightmanFunctions d) :
    SchwingerFunctions d :=
  fun n f => wickRotatedBoundaryPairing Wfn n f.1

/-- Auxiliary alias for the honest zero-diagonal Schwinger family. -/
abbrev constructZeroDiagonalSchwingerFunctions (Wfn : WightmanFunctions d) :
    ZeroDiagonalSchwingerFunctions d :=
  constructSchwingerFunctions Wfn

end
