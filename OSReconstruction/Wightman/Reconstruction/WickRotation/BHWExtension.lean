/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.ForwardTubeLorentz
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# BHW Extension

The Bargmann-Hall-Wightman extension of the analytic Wightman function
from the forward tube to the permuted extended tube, with Lorentz
invariance and permutation symmetry properties.
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]
/-! #### BHW extension (needed before constructing Schwinger functions) -/

private theorem continuous_minkowskiNormSq (d : ℕ) :
    Continuous (fun η : Fin (d + 1) → ℝ => MinkowskiSpace.minkowskiNormSq d η) := by
  simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner]
  apply continuous_finset_sum
  intro i _
  exact ((continuous_const.mul (continuous_apply i)).mul (continuous_apply i))

private theorem integral_swap_eq_self {d n : ℕ} [NeZero d]
    (i j : Fin n) (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun k => x (Equiv.swap i j k)) =
    ∫ x : NPointDomain d n, h x := by
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  let e : NPointDomain d n ≃ᵐ NPointDomain d n :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Fin (d + 1) → ℝ) σ
  have hmp : MeasureTheory.MeasurePreserving (⇑e) MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin n => Fin (d + 1) → ℝ) σ
  have hEq : ∫ x : NPointDomain d n, h (e x) = ∫ x : NPointDomain d n, h x := hmp.integral_comp' h
  rw [MeasurableEquiv.coe_piCongrLeft] at hEq
  calc
    ∫ x : NPointDomain d n, h (fun k => x (Equiv.swap i j k))
        = ∫ x : NPointDomain d n,
            h ((Equiv.piCongrLeft (fun _ : Fin n => Fin (d + 1) → ℝ) σ) x) := by
            congr 1
            ext x
            congr 1
            ext k μ
            simpa [σ] using (congrArg (fun u => u μ)
              (Equiv.piCongrLeft_apply
                (P := fun _ : Fin n => Fin (d + 1) → ℝ)
                (e := σ) x k)).symm
    _ = ∫ x : NPointDomain d n, h x := hEq

private theorem one_add_norm_clm_le_mul_one_add_norm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (x : E) :
    1 + ‖L x‖ ≤ (‖L‖ + 1) * (1 + ‖x‖) := by
  have hLx : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
  have hLn : 0 ≤ ‖L‖ := norm_nonneg L
  have hxn : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith

private theorem one_add_norm_pow_mono
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) {m n : ℕ} (hmn : m ≤ n) :
    (1 + ‖x‖) ^ m ≤ (1 + ‖x‖) ^ n := by
  rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
  have hx : 1 ≤ 1 + ‖x‖ := by
    nlinarith [norm_nonneg x]
  have hpow : 1 ≤ (1 + ‖x‖) ^ k := one_le_pow₀ hx
  have hnonneg : 0 ≤ (1 + ‖x‖) ^ m := by
    have hx0 : 0 ≤ 1 + ‖x‖ := by nlinarith [norm_nonneg x]
    exact pow_nonneg hx0 m
  calc
    (1 + ‖x‖) ^ m ≤ (1 + ‖x‖) ^ m * (1 + ‖x‖) ^ k := by
      nlinarith
    _ = (1 + ‖x‖) ^ (m + k) := by rw [← pow_add]

/-- W_analytic inherits real Lorentz invariance from the Wightman distribution.

    Both z ↦ W_analytic(z) and z ↦ W_analytic(Λz) are holomorphic on the forward tube
    with the same distributional boundary values (by Lorentz invariance of W_n).
    The proof now runs through the explicit flattened regular Fourier-Laplace package and
    `distributional_uniqueness_forwardTube_of_flatRegular_from_bvZero`.

    Ref: Streater-Wightman, §2.4 -/
theorem W_analytic_lorentz_on_tube (Wfn : WightmanFunctions d) (n : ℕ)
    (hRegular_W : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm)) :
    ∀ (Λ : LorentzGroup.Restricted (d := d))
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      (Wfn.spectrum_condition n).choose
        (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
      (Wfn.spectrum_condition n).choose z := by
  intro Λ z hz
  let W_analytic := (Wfn.spectrum_condition n).choose
  let F₁ : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z => W_analytic (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν)
  have hF₁_holo : DifferentiableOn ℂ F₁ (ForwardTube d n) :=
    W_analytic_lorentz_holomorphic Wfn n Λ
  have hW_holo : DifferentiableOn ℂ W_analytic (ForwardTube d n) :=
    (Wfn.spectrum_condition n).choose_spec.1
  have hW_bv := (Wfn.spectrum_condition n).choose_spec.2
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let lorentzAbsR : NPointDomain d n →L[ℝ] NPointDomain d n :=
    ContinuousLinearMap.pi fun k : Fin n =>
      ((Matrix.mulVecLin Λ.val.val).toContinuousLinearMap).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin (d + 1) → ℝ) k)
  let lorentzAbsC : (Fin n → Fin (d + 1) → ℂ) →L[ℂ] (Fin n → Fin (d + 1) → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin n =>
      ((Matrix.mulVecLin (fun μ ν => (Λ.val.val μ ν : ℂ))).toContinuousLinearMap).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin (d + 1) → ℂ) k)
  let LR : (Fin (n * (d + 1)) → ℝ) →L[ℝ] (Fin (n * (d + 1)) → ℝ) :=
    eR.toContinuousLinearMap.comp (lorentzAbsR.comp eR.symm.toContinuousLinearMap)
  let LC : (Fin (n * (d + 1)) → ℂ) →L[ℂ] (Fin (n * (d + 1)) → ℂ) :=
    e.toContinuousLinearMap.comp (lorentzAbsC.comp e.symm.toContinuousLinearMap)
  let G0 : (Fin (n * (d + 1)) → ℂ) → ℂ := W_analytic ∘ e.symm
  let G₁ : (Fin (n * (d + 1)) → ℂ) → ℂ := F₁ ∘ e.symm
  have hG₁_eq : G₁ = fun w => G0 (LC w) := by
    funext w
    change
      W_analytic (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * (e.symm w) k ν) =
        W_analytic (e.symm (LC w))
    congr 1
    ext k μ
    change
      ∑ ν, (Λ.val.val μ ν : ℂ) * w (finProdFinEquiv (k, ν)) =
        (e.symm (LC w)) k μ
    simp [e, LC, lorentzAbsC, Matrix.mulVec, dotProduct, flattenCLEquiv_symm_apply]
  have hLR_maps_coneAbs :
      Set.MapsTo lorentzAbsR (ForwardConeAbs d n) (ForwardConeAbs d n) := by
    intro y hy k
    let prev : Fin (d + 1) → ℝ := if h : k.val = 0 then 0 else y ⟨k.val - 1, by omega⟩
    let diff_y : Fin (d + 1) → ℝ := fun μ => y k μ - prev μ
    have hdiff : InOpenForwardCone d diff_y := by
      simpa [diff_y, prev] using hy k
    convert restricted_preserves_forward_cone Λ diff_y hdiff using 1
    ext μ
    split_ifs with h0
    · simp [lorentzAbsR, diff_y, prev, h0, Matrix.mulVec, dotProduct]
    · simp [lorentzAbsR, diff_y, prev, h0, Matrix.mulVec, dotProduct,
        Finset.sum_sub_distrib, mul_sub]
  have hLR_maps_cone :
      Set.MapsTo LR (ForwardConeFlat d n) (ForwardConeFlat d n) := by
    intro y hy
    rcases hy with ⟨yAbs, hyAbs, rfl⟩
    refine ⟨lorentzAbsR yAbs, hLR_maps_coneAbs hyAbs, ?_⟩
    simp [LR, eR]
  have hLC_maps_tube :
      Set.MapsTo LC (SCV.TubeDomain (ForwardConeFlat d n))
        (SCV.TubeDomain (ForwardConeFlat d n)) := by
    intro w hw
    rw [← forwardTube_flatten_eq_tubeDomain] at hw ⊢
    rcases hw with ⟨z, hz, rfl⟩
    refine ⟨fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν, restricted_preserves_forward_tube Λ z hz, ?_⟩
    ext i
    rcases finProdFinEquiv.symm i with ⟨k, μ⟩
    simp [e, LC, lorentzAbsC, Matrix.mulVec, dotProduct, flattenCLEquiv_apply]
  have hLC_split :
      ∀ x y : Fin (n * (d + 1)) → ℝ,
        LC (fun i => ↑(x i) + ↑(y i) * Complex.I) =
          fun i => ↑((LR x) i) + ↑((LR y) i) * Complex.I := by
    intro x y
    ext i
    rcases finProdFinEquiv.symm i with ⟨k, μ⟩
    simp [LC, LR, e, eR, lorentzAbsC, lorentzAbsR, Matrix.mulVec, dotProduct,
      flattenCLEquiv_apply, flattenCLEquivReal_apply, mul_add, Finset.sum_add_distrib,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hRegular_W' : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n) G0 := by
    simpa [G0, Function.comp] using hRegular_W
  have hRegular_F₁ :
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n) G₁ := by
    refine
      { toHasFourierLaplaceRepr := ?_
        poly_growth := ?_
        uniform_bound := ?_
        boundary_continuous := ?_
        tube_continuousWithinAt := ?_ }
    · refine schwartz_bv_to_flat_repr hF₁_holo ?_
      refine ⟨Wfn.W n, Wfn.tempered n, ?_⟩
      intro f η hη
      exact lorentz_covariant_distributional_bv (d := d) (n := n)
        Wfn W_analytic hW_holo hW_bv Λ f η hη
    · intro K hK hK_sub
      let K' := LR '' K
      have hK' : IsCompact K' := hK.image LR.continuous
      have hK'_sub : K' ⊆ ForwardConeFlat d n := by
        intro y hy
        rcases hy with ⟨y0, hy0, rfl⟩
        exact hLR_maps_cone (hK_sub hy0)
      obtain ⟨C₁, N₁, hC₁_pos, hbound₁⟩ := hRegular_W'.poly_growth K' hK' hK'_sub
      refine ⟨C₁ * (‖LR‖ + 1) ^ N₁, N₁, by positivity, ?_⟩
      intro x y hy
      have hy' : LR y ∈ K' := ⟨y, hy, rfl⟩
      have hLR_norm :
          (1 + ‖LR x‖) ^ N₁ ≤ (‖LR‖ + 1) ^ N₁ * (1 + ‖x‖) ^ N₁ := by
        have hbase := one_add_norm_clm_le_mul_one_add_norm LR x
        have hpow := pow_le_pow_left₀ (by positivity) hbase N₁
        simpa [mul_pow] using hpow
      have hG₁_val :
          G₁ (fun i => ↑(x i) + ↑(y i) * Complex.I) =
            G0 (fun i => ↑((LR x) i) + ↑((LR y) i) * Complex.I) := by
        rw [hG₁_eq]
        exact congrArg G0 (hLC_split x y)
      calc
        ‖G₁ (fun i => ↑(x i) + ↑(y i) * Complex.I)‖
            = ‖G0 (fun i => ↑((LR x) i) + ↑((LR y) i) * Complex.I)‖ := by rw [hG₁_val]
        _ ≤ C₁ * (1 + ‖LR x‖) ^ N₁ := hbound₁ (LR x) (LR y) hy'
        _ ≤ C₁ * ((‖LR‖ + 1) ^ N₁ * (1 + ‖x‖) ^ N₁) := by
              gcongr
        _ = (C₁ * (‖LR‖ + 1) ^ N₁) * (1 + ‖x‖) ^ N₁ := by ring
    · intro η hη
      have hLRη : LR η ∈ ForwardConeFlat d n := hLR_maps_cone hη
      obtain ⟨C₁, N₁, δ₁, hC₁_pos, hδ₁_pos, hbound₁⟩ :=
        hRegular_W'.uniform_bound (LR η) hLRη
      refine ⟨C₁ * (‖LR‖ + 1) ^ N₁, N₁, δ₁, by positivity, hδ₁_pos, ?_⟩
      intro x ε hε_pos hεδ₁
      have hLR_norm :
          (1 + ‖LR x‖) ^ N₁ ≤ (‖LR‖ + 1) ^ N₁ * (1 + ‖x‖) ^ N₁ := by
        have hbase := one_add_norm_clm_le_mul_one_add_norm LR x
        have hpow := pow_le_pow_left₀ (by positivity) hbase N₁
        simpa [mul_pow] using hpow
      have hG₁_val :
          G₁ (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) =
            G0 (fun i => ↑((LR x) i) + ↑ε * ↑((LR η) i) * Complex.I) := by
        rw [hG₁_eq]
        have hsplit := hLC_split x (ε • η)
        exact congrArg G0 (by simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using hsplit)
      calc
        ‖G₁ (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I)‖
            = ‖G0 (fun i => ↑((LR x) i) + ↑ε * ↑((LR η) i) * Complex.I)‖ := by rw [hG₁_val]
        _ ≤ C₁ * (1 + ‖LR x‖) ^ N₁ := hbound₁ (LR x) ε hε_pos hεδ₁
        _ ≤ C₁ * ((‖LR‖ + 1) ^ N₁ * (1 + ‖x‖) ^ N₁) := by
              gcongr
        _ = (C₁ * (‖LR‖ + 1) ^ N₁) * (1 + ‖x‖) ^ N₁ := by ring
    ·
      have hEq :
          (fun x : Fin (n * (d + 1)) → ℝ => G₁ (SCV.realEmbed x)) =
          (fun x : Fin (n * (d + 1)) → ℝ => G0 (SCV.realEmbed (LR x))) := by
        funext x
        have hpt : LC (SCV.realEmbed x) = SCV.realEmbed (LR x) := by
          simpa [SCV.realEmbed] using hLC_split x 0
        rw [hG₁_eq]
        exact congrArg G0 hpt
      rw [hEq]
      exact hRegular_W'.boundary_continuous.comp LR.continuous
    · intro x
      have hbase :
          ContinuousWithinAt G0 (SCV.TubeDomain (ForwardConeFlat d n))
            (LC (SCV.realEmbed x)) := by
        have hpt : LC (SCV.realEmbed x) = SCV.realEmbed (LR x) := by
          simpa [SCV.realEmbed] using hLC_split x 0
        simpa [hpt] using hRegular_W'.tube_continuousWithinAt (LR x)
      have hcomp :
          ContinuousWithinAt (fun z => G0 (LC z))
            (SCV.TubeDomain (ForwardConeFlat d n)) (SCV.realEmbed x) :=
        hbase.comp (f := LC) LC.continuous.continuousWithinAt hLC_maps_tube
      simpa [hG₁_eq] using hcomp
  have h_agree :
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            ((F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) -
             (W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := by
    intro f η hη
    have h_term2 : Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)) := hW_bv f η hη
    have h_term1 : Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)) :=
      lorentz_covariant_distributional_bv (d := d) (n := n)
        Wfn W_analytic hW_holo hW_bv Λ f η hη
    have hdiff := Filter.Tendsto.sub h_term1 h_term2
    simp only [sub_self] at hdiff
    refine hdiff.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← MeasureTheory.integral_sub]
    · congr 1
      ext x
      ring
    · exact forward_tube_bv_integrable_of_flatRegular
        F₁ hF₁_holo hRegular_F₁ f η hη ε (Set.mem_Ioi.mp hε)
    · exact forward_tube_bv_integrable_of_flatRegular
        W_analytic hW_holo hRegular_W f η hη ε (Set.mem_Ioi.mp hε)
  have hdiff_holo : DifferentiableOn ℂ (fun z => F₁ z - W_analytic z) (ForwardTube d n) :=
    hF₁_holo.sub hW_holo
  let h_zero_bv_ex :
      ∃ (T : SchwartzNPoint d n → ℂ), Continuous T ∧
        ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
          InForwardCone d n η →
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d n,
              ((F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) -
               (W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))) * (f x))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (T f)) := ⟨0, continuous_const, h_agree⟩
  have hRegular_diff :
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n) (fun w => G₁ w - G0 w) := by
    refine
      { toHasFourierLaplaceRepr := schwartz_bv_to_flat_repr hdiff_holo h_zero_bv_ex
        poly_growth := ?_
        uniform_bound := ?_
        boundary_continuous := ?_
        tube_continuousWithinAt := ?_ }
    · intro K hK hK_sub
      let K' := LR '' K
      have hK' : IsCompact K' := hK.image LR.continuous
      have hK'_sub : K' ⊆ ForwardConeFlat d n := by
        intro y hy
        rcases hy with ⟨y0, hy0, rfl⟩
        exact hLR_maps_cone (hK_sub hy0)
      obtain ⟨C₁, N₁, hC₁_pos, hbound₁⟩ := hRegular_W'.poly_growth K' hK' hK'_sub
      obtain ⟨C₂, N₂, hC₂_pos, hbound₂⟩ := hRegular_W'.poly_growth K hK hK_sub
      let N := max N₁ N₂
      refine
        ⟨C₁ * (‖LR‖ + 1) ^ N₁ + C₂, N, by positivity, ?_⟩
      intro x y hy
      have hy' : LR y ∈ K' := ⟨y, hy, rfl⟩
      have hLR_norm :
          (1 + ‖LR x‖) ^ N₁ ≤ (‖LR‖ + 1) ^ N₁ * (1 + ‖x‖) ^ N₁ := by
        have hbase := one_add_norm_clm_le_mul_one_add_norm LR x
        have hpow := pow_le_pow_left₀ (by positivity) hbase N₁
        simpa [mul_pow] using hpow
      have hmono₁ : (1 + ‖x‖) ^ N₁ ≤ (1 + ‖x‖) ^ N := one_add_norm_pow_mono x (Nat.le_max_left _ _)
      have hmono₂ : (1 + ‖x‖) ^ N₂ ≤ (1 + ‖x‖) ^ N := one_add_norm_pow_mono x (Nat.le_max_right _ _)
      have hG₁_val :
          G₁ (fun i => ↑(x i) + ↑(y i) * Complex.I) =
            G0 (fun i => ↑((LR x) i) + ↑((LR y) i) * Complex.I) := by
        rw [hG₁_eq]
        exact congrArg G0 (hLC_split x y)
      calc
        ‖(fun w => G₁ w - G0 w) (fun i => ↑(x i) + ↑(y i) * Complex.I)‖
            = ‖G₁ (fun i => ↑(x i) + ↑(y i) * Complex.I) -
                G0 (fun i => ↑(x i) + ↑(y i) * Complex.I)‖ := by rfl
        _ ≤ ‖G₁ (fun i => ↑(x i) + ↑(y i) * Complex.I)‖ +
              ‖G0 (fun i => ↑(x i) + ↑(y i) * Complex.I)‖ := norm_sub_le _ _
        _ = ‖G0 (fun i => ↑((LR x) i) + ↑((LR y) i) * Complex.I)‖ +
              ‖G0 (fun i => ↑(x i) + ↑(y i) * Complex.I)‖ := by rw [hG₁_val]
        _ ≤ C₁ * (1 + ‖LR x‖) ^ N₁ + C₂ * (1 + ‖x‖) ^ N₂ := by
              gcongr
              · exact hbound₁ (LR x) (LR y) hy'
              · exact hbound₂ x y hy
        _ ≤ C₁ * ((‖LR‖ + 1) ^ N₁ * (1 + ‖x‖) ^ N₁) + C₂ * (1 + ‖x‖) ^ N₂ := by
              gcongr
        _ ≤ C₁ * ((‖LR‖ + 1) ^ N₁ * (1 + ‖x‖) ^ N) + C₂ * (1 + ‖x‖) ^ N := by
              gcongr
        _ = (C₁ * (‖LR‖ + 1) ^ N₁ + C₂) * (1 + ‖x‖) ^ N := by ring
    · intro η hη
      have hLRη : LR η ∈ ForwardConeFlat d n := hLR_maps_cone hη
      obtain ⟨C₁, N₁, δ₁, hC₁_pos, hδ₁_pos, hbound₁⟩ :=
        hRegular_W'.uniform_bound (LR η) hLRη
      obtain ⟨C₂, N₂, δ₂, hC₂_pos, hδ₂_pos, hbound₂⟩ :=
        hRegular_W'.uniform_bound η hη
      let N := max N₁ N₂
      let δ := min δ₁ δ₂
      refine ⟨C₁ * (‖LR‖ + 1) ^ N₁ + C₂, N, δ, by positivity, by positivity, ?_⟩
      intro x ε hε_pos hεδ
      have hLR_norm :
          (1 + ‖LR x‖) ^ N₁ ≤ (‖LR‖ + 1) ^ N₁ * (1 + ‖x‖) ^ N₁ := by
        have hbase := one_add_norm_clm_le_mul_one_add_norm LR x
        have hpow := pow_le_pow_left₀ (by positivity) hbase N₁
        simpa [mul_pow] using hpow
      have hmono₁ : (1 + ‖x‖) ^ N₁ ≤ (1 + ‖x‖) ^ N := one_add_norm_pow_mono x (Nat.le_max_left _ _)
      have hmono₂ : (1 + ‖x‖) ^ N₂ ≤ (1 + ‖x‖) ^ N := one_add_norm_pow_mono x (Nat.le_max_right _ _)
      have hεδ₁ : ε < δ₁ := lt_of_lt_of_le hεδ (min_le_left _ _)
      have hεδ₂ : ε < δ₂ := lt_of_lt_of_le hεδ (min_le_right _ _)
      have hG₁_val :
          G₁ (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) =
            G0 (fun i => ↑((LR x) i) + ↑ε * ↑((LR η) i) * Complex.I) := by
        rw [hG₁_eq]
        have hsplit := hLC_split x (ε • η)
        exact congrArg G0 (by simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using hsplit)
      calc
        ‖(fun w => G₁ w - G0 w) (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I)‖
            = ‖G₁ (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) -
                G0 (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I)‖ := by rfl
        _ ≤ ‖G₁ (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I)‖ +
              ‖G0 (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I)‖ := norm_sub_le _ _
        _ = ‖G0 (fun i => ↑((LR x) i) + ↑ε * ↑((LR η) i) * Complex.I)‖ +
              ‖G0 (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I)‖ := by rw [hG₁_val]
        _ ≤ C₁ * (1 + ‖LR x‖) ^ N₁ + C₂ * (1 + ‖x‖) ^ N₂ := by
              gcongr
              · exact hbound₁ (LR x) ε hε_pos hεδ₁
              · exact hbound₂ x ε hε_pos hεδ₂
        _ ≤ C₁ * ((‖LR‖ + 1) ^ N₁ * (1 + ‖x‖) ^ N₁) + C₂ * (1 + ‖x‖) ^ N₂ := by
              gcongr
        _ ≤ C₁ * ((‖LR‖ + 1) ^ N₁ * (1 + ‖x‖) ^ N) + C₂ * (1 + ‖x‖) ^ N := by
              gcongr
        _ = (C₁ * (‖LR‖ + 1) ^ N₁ + C₂) * (1 + ‖x‖) ^ N := by ring
    ·
      have hcont₁ : Continuous (fun x : Fin (n * (d + 1)) → ℝ => G₁ (SCV.realEmbed x)) := by
        have hEq :
            (fun x : Fin (n * (d + 1)) → ℝ => G₁ (SCV.realEmbed x)) =
            (fun x : Fin (n * (d + 1)) → ℝ => G0 (SCV.realEmbed (LR x))) := by
          funext x
          have hpt : LC (SCV.realEmbed x) = SCV.realEmbed (LR x) := by
            simpa [SCV.realEmbed] using hLC_split x 0
          rw [hG₁_eq]
          exact congrArg G0 hpt
        rw [hEq]
        exact hRegular_W'.boundary_continuous.comp LR.continuous
      exact hcont₁.sub hRegular_W'.boundary_continuous
    · intro x
      have hcont₁ :
          ContinuousWithinAt G₁ (SCV.TubeDomain (ForwardConeFlat d n)) (SCV.realEmbed x) := by
        have hbase :
            ContinuousWithinAt G0 (SCV.TubeDomain (ForwardConeFlat d n))
              (LC (SCV.realEmbed x)) := by
          have hpt : LC (SCV.realEmbed x) = SCV.realEmbed (LR x) := by
            simpa [SCV.realEmbed] using hLC_split x 0
          simpa [hpt] using hRegular_W'.tube_continuousWithinAt (LR x)
        have hcomp :
            ContinuousWithinAt (fun z => G0 (LC z))
              (SCV.TubeDomain (ForwardConeFlat d n)) (SCV.realEmbed x) :=
          hbase.comp (f := LC) LC.continuous.continuousWithinAt hLC_maps_tube
        simpa [hG₁_eq] using hcomp
      exact hcont₁.sub (hRegular_W'.tube_continuousWithinAt x)
  have huniq :=
    distributional_uniqueness_forwardTube_of_flatRegular_from_bvZero
      hF₁_holo hW_holo hRegular_diff h_agree
  exact huniq z hz

/-- W_analytic extends continuously to the real boundary of the forward tube.

    This is now routed through the proved explicit-regularity theorem on the
    flattened forward tube.

    Ref: Streater-Wightman, Theorem 2-9 -/
theorem W_analytic_continuous_boundary (Wfn : WightmanFunctions d) (n : ℕ)
    (hRegular_W : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm)) :
    ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt (Wfn.spectrum_condition n).choose
        (ForwardTube d n) (fun k μ => (x k μ : ℂ)) := by
  intro x
  exact continuous_boundary_forwardTube_of_flatRegular
    (d := d) (n := n) hRegular_W x

/-- Distributional swap-agreement on boundary values in test-function form.

    Fix adjacent indices `i, i+1`. If `g` is obtained from `f` by swapping those
    coordinates and `f` is supported on configurations where the swapped pair is
    spacelike separated, then local commutativity gives `W n g = W n f`.

    Combining this with the boundary-value convergence for `f` and `g` along the
    same forward direction `η`, the smeared boundary-value difference converges to 0:
    `∫ W_analytic(x+iεη) * (g-f) → 0`. -/
theorem W_analytic_swap_distributional_agree {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (W_analytic ∘ (flattenCLEquiv n (d + 1)).symm))
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
    (_hW_cont : Continuous (W n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hLC : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ x : NPointDomain d n, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x - f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  intro f g η hsep hswap hη
  have h_g : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W n g)) := hBV g η hη
  have h_f : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W n f)) := hBV f η hη
  have h_diff : Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) -
        (∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W n g - W n f)) := Filter.Tendsto.sub h_g h_f
  have hW_eq : W n g = W n f := (hLC n i ⟨i.val + 1, hi⟩ f g hsep hswap).symm
  have h_diff_zero : Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) -
        (∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    simpa [hW_eq] using h_diff
  refine h_diff_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← MeasureTheory.integral_sub]
  · congr 1
    ext x
    ring
  · exact forward_tube_bv_integrable_of_flatRegular
      W_analytic hW_hol hRegular g η hη ε (Set.mem_Ioi.mp hε)
  · exact forward_tube_bv_integrable_of_flatRegular
      W_analytic hW_hol hRegular f η hη ε (Set.mem_Ioi.mp hε)

/-- Boundary-pairing form of local commutativity for adjacent swaps.

    For test functions `f, g` related by adjacent swap on a spacelike support
    region, the real-boundary pairings of `W_analytic` coincide:
    `∫ W_analytic(x) g(x) dx = ∫ W_analytic(x) f(x) dx`.

    This now uses the explicit flattened regular Fourier-Laplace package
    rather than the old weak forward-tube recovery placeholder. -/
theorem W_analytic_swap_boundary_pairing_eq {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (W_analytic ∘ (flattenCLEquiv n (d + 1)).symm))
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
    (hW_cont : Continuous (W n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hLC : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      (∫ x : NPointDomain d n,
        W_analytic (fun k μ => (x k μ : ℂ)) * (g x)) =
      (∫ x : NPointDomain d n,
        W_analytic (fun k μ => (x k μ : ℂ)) * (f x)) := by
  intro f g hsep hswap
  have hW_eq : W n g = W n f := (hLC n i ⟨i.val + 1, hi⟩ f g hsep hswap).symm
  have hg_pair :
      W n g =
        ∫ x : NPointDomain d n, W_analytic (fun k μ => (x k μ : ℂ)) * (g x) :=
    boundary_value_recovery_forwardTube_of_flatRegular_from_bv
      (d := d) (n := n) hW_hol hRegular hW_cont hBV g
  have hf_pair :
      W n f =
        ∫ x : NPointDomain d n, W_analytic (fun k μ => (x k μ : ℂ)) * (f x) :=
    boundary_value_recovery_forwardTube_of_flatRegular_from_bv
      (d := d) (n := n) hW_hol hRegular hW_cont hBV f
  calc
    (∫ x : NPointDomain d n, W_analytic (fun k μ => (x k μ : ℂ)) * (g x))
        = W n g := hg_pair.symm
    _ = W n f := hW_eq
    _ = (∫ x : NPointDomain d n, W_analytic (fun k μ => (x k μ : ℂ)) * (f x)) := hf_pair

/-- Pointwise local commutativity of the analytic continuation at spacelike boundary.

    g(z) = W_analytic(swap(z)) - W_analytic(z) is holomorphic where defined.
    By `W_analytic_swap_distributional_agree`, g has zero distributional boundary
    values at real spacelike points. By the edge-of-the-wedge theorem (sorry-free
    in `EdgeOfWedge.lean`), g extends holomorphically across the boundary.
    Since g = 0 distributionally on an open real set, the identity theorem gives g = 0.

    Blocked by: multi-tube EOW application (expressing the forward and swapped tubes
    as tube domains) and the distributional-to-pointwise bridge (from vanishing
    distributional boundary values on spacelike test supports to pointwise boundary
    equality at a fixed spacelike configuration). The distributional swap-agreement
    itself is now provided by `W_analytic_swap_distributional_agree`, while the
    boundary continuity input is routed through explicit flattened regularity.

    Ref: Streater-Wightman Thm 3-5; Jost §IV.3 -/
theorem analytic_boundary_local_commutativity {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (W_analytic ∘ (flattenCLEquiv n (d + 1)).symm))
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
    (hW_cont : Continuous (W n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hLC : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hx : MinkowskiSpace.minkowskiNormSq d
      (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0) :
    W_analytic (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
    W_analytic (fun k μ => (x k μ : ℂ)) := by
  let j : Fin n := ⟨i.val + 1, hi⟩
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  have _hSwapDist := W_analytic_swap_distributional_agree
    (d := d) (n := n) W_analytic hW_hol hRegular W hW_cont hBV hLC i hi
  have hSwapBdry := W_analytic_swap_boundary_pairing_eq
    (d := d) (n := n) W_analytic hW_hol hRegular W hW_cont hBV hLC i hi
  let B : NPointDomain d n → ℂ := fun y => W_analytic (fun k μ => (y k μ : ℂ))
  have hB_cont : Continuous B :=
    boundary_function_continuous_forwardTube_of_flatRegular
      (d := d) (n := n) hW_hol hRegular
  have hBσ_cont : Continuous (fun y : NPointDomain d n => B (fun k => y (σ k))) :=
    hB_cont.comp (continuous_pi fun k => continuous_apply (σ k))
  let U : Set (NPointDomain d n) := {y : NPointDomain d n |
      MinkowskiSpace.minkowskiNormSq d (fun μ => y j μ - y i μ) > 0}
  have hU_nhds : U ∈ nhds x := by
    have hcontU : Continuous (fun y : NPointDomain d n =>
        MinkowskiSpace.minkowskiNormSq d (fun μ => y j μ - y i μ)) := by
      exact (continuous_minkowskiNormSq d).comp
        (continuous_pi fun μ =>
          ((continuous_apply μ).comp (continuous_apply j)).sub
            ((continuous_apply μ).comp (continuous_apply i)))
    have hU_open : IsOpen U := isOpen_lt continuous_const hcontU
    have hxU : x ∈ U := by simpa [U, j] using hx
    exact hU_open.mem_nhds hxU
  obtain ⟨χ, hχ_tsupport, hχ_compact, hχ_smooth, _, hχx⟩ :=
    exists_contDiff_tsupport_subset (s := U) (x := x) (n := (⊤ : ℕ∞)) hU_nhds
  let χC : NPointDomain d n → ℂ := fun y => (χ y : ℂ)
  have hχC_compact : HasCompactSupport χC := hχ_compact.comp_left Complex.ofReal_zero
  have hχC_smooth : ContDiff ℝ (⊤ : ℕ∞) χC :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp hχ_smooth
  have hχC_temp : χC.HasTemperateGrowth := hχC_compact.hasTemperateGrowth hχC_smooth
  have hχC_cont : Continuous χC := (Complex.continuous_ofReal.comp hχ_smooth.continuous)
  have hloc :
      ∀ φ : SchwartzNPoint d n,
        ∫ y : NPointDomain d n,
          (B (fun k => y (σ k)) - B y) * (χC y * φ y) = 0 := by
    intro φ
    let f : SchwartzNPoint d n := SchwartzMap.smulLeftCLM ℂ χC φ
    let eSwap : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      ContinuousLinearEquiv.piCongrLeft ℝ
        (fun _ : Fin n => Fin (d + 1) → ℝ) σ
    let g : SchwartzNPoint d n := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eSwap f
    have hsep : ∀ y : NPointDomain d n, f.toFun y ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (y i) (y j) := by
      intro y hy
      have hf_eval : f.toFun y = χC y * φ y := by
        simpa [f, smul_eq_mul] using
          (SchwartzMap.smulLeftCLM_apply_apply hχC_temp φ y)
      have hχC_ne : χC y ≠ 0 := by
        intro hzero
        apply hy
        rw [hf_eval, hzero]
        simp
      have hχ_ne : χ y ≠ 0 := by
        intro hzero
        exact hχC_ne (by simp [χC, hzero])
      have hy_support : y ∈ Function.support χ := by
        simpa [Function.mem_support] using hχ_ne
      have hy_tsupport : y ∈ tsupport χ := subset_closure hy_support
      have hyU : y ∈ U := hχ_tsupport hy_tsupport
      have hy_spacelike :
          MinkowskiSpace.minkowskiNormSq d (fun μ => y i μ - y j μ) > 0 := by
        have hsymm :
            MinkowskiSpace.minkowskiNormSq d (fun μ => y i μ - y j μ) =
            MinkowskiSpace.minkowskiNormSq d (fun μ => y j μ - y i μ) := by
          unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
          refine Finset.sum_congr rfl ?_
          intro μ _
          ring
        exact hsymm ▸ (by simpa [U] using hyU)
      simpa [MinkowskiSpace.AreSpacelikeSeparated, MinkowskiSpace.IsSpacelike]
        using hy_spacelike
    have hswap : ∀ y : NPointDomain d n,
        g.toFun y = f.toFun (fun k => y (σ k)) := by
      intro y
      simpa [g, eSwap] using
        (show (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (ContinuousLinearEquiv.piCongrLeft ℝ
            (fun _ : Fin n => Fin (d + 1) → ℝ) σ) f) y
            = f (fun k => y (σ k)) from by
              change f ((Equiv.piCongrLeft (fun _ : Fin n => Fin (d + 1) → ℝ) σ) y) =
                f (fun k => y (σ k))
              congr 1
              ext k μ
              simpa [σ] using (congrArg (fun u => u μ)
                (Equiv.piCongrLeft_apply
                  (P := fun _ : Fin n => Fin (d + 1) → ℝ)
                  (e := σ) y k)))
    have hpair :
        (∫ y : NPointDomain d n, B y * g y) =
        (∫ y : NPointDomain d n, B y * f y) := by
      exact hSwapBdry f g hsep hswap
    have hpair' :
        (∫ y : NPointDomain d n, B y * f (fun k => y (σ k))) =
        (∫ y : NPointDomain d n, B y * f y) := by
      have hfg_eq :
          (fun y : NPointDomain d n => B y * f (fun k => y (σ k))) =
          (fun y : NPointDomain d n => B y * g y) := by
        funext y
        change B y * f.toFun (fun k => y (σ k)) = B y * g.toFun y
        rw [hswap y]
      calc
        (∫ y : NPointDomain d n, B y * f (fun k => y (σ k)))
            = (∫ y : NPointDomain d n, B y * g y) := by
                simp [hfg_eq]
        _ = (∫ y : NPointDomain d n, B y * f y) := hpair
    have hswap_int :
        (∫ y : NPointDomain d n, B y * f (fun k => y (σ k))) =
        (∫ y : NPointDomain d n, B (fun k => y (σ k)) * f y) := by
      have htmp := integral_swap_eq_self (d := d) (n := n) i j
        (h := fun t : NPointDomain d n => B (fun k => t (σ k)) * f t)
      simpa [σ] using htmp
    have hB_eq :
        (∫ y : NPointDomain d n, B (fun k => y (σ k)) * f y) =
        (∫ y : NPointDomain d n, B y * f y) := hswap_int.symm.trans hpair'
    have hf_eval : ∀ y : NPointDomain d n, f y = χC y * φ y := by
      intro y
      simp [f, SchwartzMap.smulLeftCLM_apply_apply hχC_temp, smul_eq_mul]
    have hf_compact : HasCompactSupport (fun y : NPointDomain d n => f y) := by
      have hf_eq : (fun y : NPointDomain d n => f y) = (fun y => χC y * φ y) := by
        funext y
        rw [hf_eval y]
      rw [hf_eq]
      exact hχC_compact.mul_right
    have hInt₁_cont : Continuous (fun y : NPointDomain d n => B (fun k => y (σ k)) * f y) :=
      hBσ_cont.mul f.continuous
    have hInt₂_cont : Continuous (fun y : NPointDomain d n => B y * f y) :=
      hB_cont.mul f.continuous
    have hInt₁_compact : HasCompactSupport (fun y : NPointDomain d n => B (fun k => y (σ k)) * f y) :=
      HasCompactSupport.mul_left hf_compact
    have hInt₂_compact : HasCompactSupport (fun y : NPointDomain d n => B y * f y) :=
      HasCompactSupport.mul_left hf_compact
    have hInt₁_integrable : MeasureTheory.Integrable (fun y : NPointDomain d n => B (fun k => y (σ k)) * f y) :=
      hInt₁_cont.integrable_of_hasCompactSupport hInt₁_compact
    have hInt₂_integrable : MeasureTheory.Integrable (fun y : NPointDomain d n => B y * f y) :=
      hInt₂_cont.integrable_of_hasCompactSupport hInt₂_compact
    have hdiff_zero :
        ∫ y : NPointDomain d n, (B (fun k => y (σ k)) - B y) * f y = 0 := by
      have hIntegrand :
          (fun y : NPointDomain d n => (B (fun k => y (σ k)) - B y) * f y) =
          (fun y : NPointDomain d n => B (fun k => y (σ k)) * f y - B y * f y) := by
        funext y
        ring
      calc
        ∫ y : NPointDomain d n, (B (fun k => y (σ k)) - B y) * f y
            = (∫ y : NPointDomain d n, B (fun k => y (σ k)) * f y) -
              (∫ y : NPointDomain d n, B y * f y) := by
                rw [hIntegrand, MeasureTheory.integral_sub hInt₁_integrable hInt₂_integrable]
        _ = 0 := sub_eq_zero.mpr hB_eq
    calc
      ∫ y : NPointDomain d n, (B (fun k => y (σ k)) - B y) * (χC y * φ y)
          = ∫ y : NPointDomain d n, (B (fun k => y (σ k)) - B y) * f y := by
              congr 1
              ext y
              rw [hf_eval y]
      _ = 0 := hdiff_zero
  let G : NPointDomain d n → ℂ := fun y =>
    (B (fun k => y (σ k)) - B y) * χC y
  have hG_cont : Continuous G := (hBσ_cont.sub hB_cont).mul hχC_cont
  let eR : NPointDomain d n ≃L[ℝ] (Fin (n * (d + 1)) → ℝ) := flattenCLEquivReal n (d + 1)
  let Gflat : (Fin (n * (d + 1)) → ℝ) → ℂ := fun z => G (eR.symm z)
  have hGflat_cont : Continuous Gflat := hG_cont.comp eR.symm.continuous
  have hG_zero_pairing : ∀ φ : SchwartzNPoint d n,
      ∫ y : NPointDomain d n, G y * φ y = 0 := by
    intro φ
    simpa [G, mul_assoc, mul_comm, mul_left_comm] using hloc φ
  have hGflat_zero_pairing : ∀ ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ,
      ∫ z : Fin (n * (d + 1)) → ℝ, Gflat z * ψ z = 0 := by
    intro ψ
    let pullback : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR
    have hprod : ∫ y : NPointDomain d n, G y * (pullback ψ) y = 0 :=
      hG_zero_pairing (pullback ψ)
    have hchange :
        ∫ z : Fin (n * (d + 1)) → ℝ, Gflat z * ψ z =
        ∫ y : NPointDomain d n, G y * (pullback ψ) y := by
      rw [integral_flatten_change_of_variables]
      congr 1
      ext y
      simp [Gflat, pullback, eR]
    exact hchange.trans hprod
  have hGflat_zero : ∀ z : Fin (n * (d + 1)) → ℝ, Gflat z = 0 :=
    SCV.eq_zero_of_schwartz_integral_zero hGflat_cont hGflat_zero_pairing
  have hχxC : χC x = 1 := by
    simp [χC, hχx]
  have hBx_diff : B (fun k => x (σ k)) - B x = 0 := by
    have hx0 : G x = 0 := by
      simpa [Gflat, eR] using hGflat_zero (eR x)
    change (B (fun k => x (σ k)) - B x) * χC x = 0 at hx0
    simpa [hχxC] using hx0
  have hBx_eq : B (fun k => x (σ k)) = B x := sub_eq_zero.mp hBx_diff
  simpa [B, σ, j] using hBx_eq

/-- Local commutativity of W_analytic at spacelike-separated boundary points.

    At real points where consecutive arguments are spacelike separated
    (Minkowski norm > 0), swapping those arguments doesn't change the boundary
    value. This follows from `analytic_boundary_local_commutativity` applied to
    the analytic continuation from `spectrum_condition`.

    Ref: Streater-Wightman, §3.3; Jost, §IV.3 -/
theorem W_analytic_local_commutativity (Wfn : WightmanFunctions d) (n : ℕ)
    (hRegular_W : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm)) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        MinkowskiSpace.minkowskiNormSq d
          (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0 →
        (Wfn.spectrum_condition n).choose
          (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        (Wfn.spectrum_condition n).choose (fun k μ => (x k μ : ℂ)) := by
  intro i hi x hx
  exact analytic_boundary_local_commutativity (d := d) (n := n)
    (Wfn.spectrum_condition n).choose
    (Wfn.spectrum_condition n).choose_spec.1
    hRegular_W
    Wfn.W
    (Wfn.tempered n)
    (Wfn.spectrum_condition n).choose_spec.2
    Wfn.locally_commutative
    i hi x hx

/-- The BHW extension of W_analytic from the forward tube to the permuted extended tube.

    Proved by applying the `bargmann_hall_wightman` axiom (AnalyticContinuation.lean) to
    the holomorphic extension `W_analytic` from `spectrum_condition`, with:
    - Lorentz invariance from `W_analytic_lorentz_on_tube`
    - Continuous boundary values from `W_analytic_continuous_boundary`
    - Local commutativity from `W_analytic_local_commutativity`

    Ref: Streater-Wightman, Theorem 2-11; Jost, Ch. IV -/
noncomputable def W_analytic_BHW (Wfn : WightmanFunctions d) (n : ℕ)
    (hRegular_W : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      ((Wfn.spectrum_condition n).choose ∘ (flattenCLEquiv n (d + 1)).symm))
    (hSeedConn_hd2 :
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 → 2 ≤ d →
        IsConnected (BHW.permSeedSet (d := d) n σ))
    (hExtPerm_d1 :
      d = 1 →
      ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 → ¬ n ≤ 1 →
        ∀ (z : Fin n → Fin (d + 1) → ℂ),
          z ∈ BHW.ExtendedTube d n →
          (fun k => z (σ k)) ∈ BHW.ExtendedTube d n →
          BHW.extendF ((Wfn.spectrum_condition n).choose) (fun k => z (σ k)) =
            BHW.extendF ((Wfn.spectrum_condition n).choose) z) :
    { F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ //
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n,
        F_ext z = (Wfn.spectrum_condition n).choose z) ∧
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k μ => ∑ ν, Λ.val μ ν * z k ν) = F_ext z) ∧
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) } := by
  let h := bargmann_hall_wightman n
      (Wfn.spectrum_condition n).choose
      (Wfn.spectrum_condition n).choose_spec.1
      (W_analytic_lorentz_on_tube Wfn n hRegular_W)
      (W_analytic_continuous_boundary Wfn n hRegular_W)
      (W_analytic_local_commutativity Wfn n hRegular_W)
      hSeedConn_hd2 hExtPerm_d1
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1,
    h.choose_spec.2.2.2.1⟩


end
