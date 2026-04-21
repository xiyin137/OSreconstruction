import OSReconstruction.ComplexLieGroups.JostPoints
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace MeasureTheory
open scoped Matrix.Norms.Operator

namespace BHW

variable {d : ℕ} [NeZero d]

open BHWCore

/-- Local light-cone bridge. Keeping this file free of `AxiomBridge` avoids an
import cycle when threading the distributional theorem into the core BHW spine. -/
private theorem bhw_inOpenForwardCone_iff_wightman
    (η : Fin (d + 1) → ℝ) :
    BHW.InOpenForwardCone d η ↔ _root_.InOpenForwardCone d η := by
  unfold BHW.InOpenForwardCone _root_.InOpenForwardCone
  unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩
  · convert h.2 using 1
    apply Finset.sum_congr rfl
    intro i _
    simp [MinkowskiSpace.metricSignature, LorentzLieGroup.minkowskiSignature]
    ring
  · convert h.2 using 1
    apply Finset.sum_congr rfl
    intro i _
    simp [MinkowskiSpace.metricSignature, LorentzLieGroup.minkowskiSignature]
    ring

/-- Local spacelike-condition bridge. -/
private theorem bhw_spacelike_condition_iff
    (v : Fin (d + 1) → ℝ) :
    (∑ μ, LorentzLieGroup.minkowskiSignature d μ * v μ ^ 2 > 0) ↔
      MinkowskiSpace.minkowskiNormSq d v > 0 := by
  unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  constructor <;> intro h <;> convert h using 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [MinkowskiSpace.metricSignature, LorentzLieGroup.minkowskiSignature]
    ring
  · apply Finset.sum_congr rfl
    intro i _
    simp [MinkowskiSpace.metricSignature, LorentzLieGroup.minkowskiSignature]
    ring

omit [NeZero d] in
/-- Permutations preserve the ambient product volume on `NPointDomain d n`. -/
private theorem integral_perm_eq_self {n : ℕ} (σ : Equiv.Perm (Fin n))
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun k => x (σ k)) =
    ∫ x : NPointDomain d n, h x :=
  (MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp' h

/-- Distributional adjacent-swap locality on compactly supported tests.

This is the pairing-level replacement for the pointwise real-boundary theorem
`extendF_adjSwap_eq_on_realOpen`: instead of evaluating `extendF F` at boundary points,
it only compares pairings against compactly supported Schwartz tests whose real support
lies in the extended tube. The proof uses:

1. the weak boundary-value convergence hypothesis `hF_bv_dist`,
2. weak local commutativity of the boundary functional `W`,
3. the already-proved boundary-pairing theorem
   `tendsto_extendF_boundary_integral_of_hasCompactSupport_ET`.

This is the natural theorem surface for tempered Wightman applications. -/
theorem extendF_adjSwap_pairing_eq_of_distributional_local_commutativity
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_bv_dist : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W n f)))
    (hF_local_dist : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n)
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g : NPointDomain d n → ℂ))
    (hsep : ∀ x : NPointDomain d n, f x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩))
    (hswap : ∀ x : NPointDomain d n,
      g x = f (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)))
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η)
    (hf_ET : ∀ x ∈ tsupport (f : NPointDomain d n → ℂ), realEmbed x ∈ ExtendedTube d n)
    (hg_ET : ∀ x ∈ tsupport (g : NPointDomain d n → ℂ), realEmbed x ∈ ExtendedTube d n) :
    (∫ x : NPointDomain d n, extendF F (realEmbed x) * g x) =
      (∫ x : NPointDomain d n, extendF F (realEmbed x) * f x) := by
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  have hη_FT :
      ∀ (x : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) ∈ ForwardTube d n := by
    intro x ε hε k
    show InOpenForwardCone d _
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
    exact (bhw_inOpenForwardCone_iff_wightman _).2
      (inOpenForwardCone_smul d ε hε _ (hη k))
  have h_tendsto_g :=
    tendsto_extendF_boundary_integral_of_hasCompactSupport_ET n F hF_holo hF_cinv
      g hg_compact η hη_FT hg_ET
  have h_tendsto_f :=
    tendsto_extendF_boundary_integral_of_hasCompactSupport_ET n F hF_holo hF_cinv
      f hf_compact η hη_FT hf_ET
  have h_bv_g := hF_bv_dist g η hη
  have h_bv_f := hF_bv_dist f η hη
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := by infer_instance
  have h_pairing_g : (∫ x : NPointDomain d n, extendF F (realEmbed x) * g x) = W n g :=
    tendsto_nhds_unique h_tendsto_g h_bv_g
  have h_pairing_f : (∫ x : NPointDomain d n, extendF F (realEmbed x) * f x) = W n f :=
    tendsto_nhds_unique h_tendsto_f h_bv_f
  have hW_eq : W n g = W n f :=
    (hF_local_dist n i hi f g hsep hswap).symm
  calc
    ∫ x : NPointDomain d n, extendF F (realEmbed x) * g x = W n g := h_pairing_g
    _ = W n f := hW_eq
    _ = ∫ x : NPointDomain d n, extendF F (realEmbed x) * f x := h_pairing_f.symm

/-- Pointwise adjacent-swap equality on a real open edge from distributional
local commutativity and distributional boundary values. -/
theorem extendF_adjSwap_eq_on_realOpen_of_distributional_local_commutativity
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_bv_dist : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W n f)))
    (hF_local_dist : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (Fin n → Fin (d + 1) → ℝ))
    (hV_open : IsOpen V)
    (hV_sp : ∀ x ∈ V, ∑ μ, minkowskiSignature d μ *
      (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0)
    (hV_ET : ∀ x ∈ V, realEmbed x ∈ ExtendedTube d n)
    (hV_swapET : ∀ x ∈ V,
      realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n) :
    ∀ x ∈ V,
      extendF F (fun k => (realEmbed x) (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
      extendF F (realEmbed x) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hF_cinv : ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
    intro Λ z hz hΛz
    exact complex_lorentz_invariance n F hF_holo hF_real_inv Λ z hz hΛz
  have hExtend_cont : ContinuousOn (extendF F) (ExtendedTube d n) :=
    (extendF_holomorphicOn n F hF_holo hF_cinv).continuousOn
  have hrealEmbed_cont :
      Continuous (realEmbed : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply k))
  have hswapReal_cont :
      Continuous (fun x : NPointDomain d n => fun k => (realEmbed x) (τ k)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply (τ k)))
  let gV : NPointDomain d n → ℂ :=
    fun x => extendF F (fun k => (realEmbed x) (τ k))
  let hVf : NPointDomain d n → ℂ := fun x => extendF F (realEmbed x)
  have hgV_cont : ContinuousOn gV V := by
    refine hExtend_cont.comp hswapReal_cont.continuousOn ?_
    intro x hx
    exact hV_swapET x hx
  have hhVf_cont : ContinuousOn hVf V := by
    refine hExtend_cont.comp hrealEmbed_cont.continuousOn ?_
    intro x hx
    exact hV_ET x hx
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η := (inForwardCone_iff_mem_forwardConeAbs η).2 hη_abs
  have hEqOn : Set.EqOn gV hVf V := by
    refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      hV_open hgV_cont hhVf_cont ?_
    intro φ hφ_compact hφ_tsupport
    let eτ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
      (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv
    let φτ : SchwartzNPoint d n :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eτ φ
    have hφτ_apply : ∀ x : NPointDomain d n, φτ x = φ (fun k => x (τ k)) := by
      intro x
      rfl
    have hφτ_compact : HasCompactSupport (φτ : NPointDomain d n → ℂ) := by
      simpa [φτ, eτ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
        hφ_compact.comp_homeomorph eτ.toHomeomorph
    have hφ_sp :
        ∀ x : NPointDomain d n, φ x ≠ 0 →
          MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩) := by
      intro x hxφ
      have hx_support : x ∈ Function.support (φ : NPointDomain d n → ℂ) := by
        simpa [Function.mem_support] using hxφ
      have hx_tsupport : x ∈ tsupport (φ : NPointDomain d n → ℂ) :=
        subset_tsupport _ hx_support
      have hxV : x ∈ V := hφ_tsupport hx_tsupport
      have hx_sp :
          MinkowskiSpace.minkowskiNormSq d
              (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0 :=
        (bhw_spacelike_condition_iff (d := d)
          (v := fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ)).1 (hV_sp x hxV)
      unfold MinkowskiSpace.AreSpacelikeSeparated MinkowskiSpace.IsSpacelike
      have hnorm_eq :
          MinkowskiSpace.minkowskiNormSq d (fun μ => x i μ - x ⟨i.val + 1, hi⟩ μ) =
            MinkowskiSpace.minkowskiNormSq d
              (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) := by
        unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
        apply Finset.sum_congr rfl
        intro μ _
        ring
      change MinkowskiSpace.minkowskiNormSq d
          (fun μ => x i μ - x ⟨i.val + 1, hi⟩ μ) > 0
      rw [hnorm_eq]
      exact hx_sp
    have hφ_ET :
        ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ), realEmbed x ∈ ExtendedTube d n := by
      intro x hx
      exact hV_ET x (hφ_tsupport hx)
    have hφτ_tsupport :
        tsupport (φτ : NPointDomain d n → ℂ) =
          eτ.toHomeomorph ⁻¹' tsupport (φ : NPointDomain d n → ℂ) := by
      simpa [φτ, eτ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
        (tsupport_comp_eq_preimage (g := (φ : NPointDomain d n → ℂ)) eτ.toHomeomorph)
    have hφτ_ET :
        ∀ x ∈ tsupport (φτ : NPointDomain d n → ℂ), realEmbed x ∈ ExtendedTube d n := by
      intro x hx
      have hxτ : (fun k => x (τ k)) ∈ tsupport (φ : NPointDomain d n → ℂ) := by
        simpa [hφτ_tsupport, eτ] using hx
      have hxV : (fun k => x (τ k)) ∈ V := hφ_tsupport hxτ
      have hswapET := hV_swapET (fun k => x (τ k)) hxV
      simpa [realEmbed, τ] using hswapET
    have hpair :
        (∫ x : NPointDomain d n, hVf x * φτ x) =
          ∫ x : NPointDomain d n, hVf x * φ x := by
      simpa [hVf] using
        extendF_adjSwap_pairing_eq_of_distributional_local_commutativity
          F hF_holo hF_real_inv W hF_bv_dist hF_local_dist
          i hi φ φτ hφ_compact hφτ_compact hφ_sp
          (fun x => hφτ_apply x) η hη hφ_ET hφτ_ET
    have hperm :
        (∫ x : NPointDomain d n, gV x * φ x) =
          ∫ x : NPointDomain d n, hVf x * φτ x := by
      simpa [gV, hVf, τ, hφτ_apply, realEmbed] using
        (integral_perm_eq_self (d := d) (n := n) τ
          (fun x : NPointDomain d n => hVf x * φτ x))
    calc
      ∫ x : NPointDomain d n, gV x * φ x =
        ∫ x : NPointDomain d n, hVf x * φτ x := hperm
      _ = ∫ x : NPointDomain d n, hVf x * φ x := hpair
  intro x hx
  exact hEqOn hx

/-- Connected-overlap propagation of the distributional adjacent-swap equality.

This upgrades the real-open edge equality obtained from distributional local
commutativity to holomorphic equality on the full connected ET overlap. -/
theorem extendF_adjSwap_eq_of_connected_overlap_of_distributional_local_commutativity
    {n : ℕ}
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_bv_dist : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W n f)))
    (hF_local_dist : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n)
    (hD_conn : IsConnected
      {z : Fin n → Fin (d + 1) → ℂ |
        z ∈ ExtendedTube d n ∧
        (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n})
    (x0 : Fin n → Fin (d + 1) → ℝ)
    (hx0_sp : ∑ μ, minkowskiSignature d μ *
      (x0 ⟨i.val + 1, hi⟩ μ - x0 i μ) ^ 2 > 0)
    (hx0_ET : realEmbed x0 ∈ ExtendedTube d n)
    (hx0_swapET :
      realEmbed (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n) :
    ∀ (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ExtendedTube d n →
      (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n →
      extendF F (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) = extendF F z := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  let D : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | z ∈ ExtendedTube d n ∧ (fun k => z (τ k)) ∈ ExtendedTube d n}
  have hD_open : IsOpen D := by
    have hperm_cont : Continuous
        (fun z : Fin n → Fin (d + 1) → ℂ => fun k => z (τ k)) :=
      continuous_pi (fun k => continuous_pi (fun μ =>
        (continuous_apply μ).comp (continuous_apply (τ k))))
    exact isOpen_extendedTube.inter (isOpen_extendedTube.preimage hperm_cont)
  have hD_conn' : IsConnected D := by
    simpa [D, τ] using hD_conn
  have hD_sub_ET : D ⊆ ExtendedTube d n := by
    intro z hz
    exact hz.1
  have hD_sub_permET : D ⊆ {z | (fun k => z (τ k)) ∈ ExtendedTube d n} := by
    intro z hz
    exact hz.2
  obtain ⟨V, hV_open, hx0V, hV_sp, hV_ET, hV_swapET⟩ :=
    exists_real_open_nhds_adjSwap n i hi x0 hx0_sp hx0_ET hx0_swapET
  have hV_ne : V.Nonempty := ⟨x0, hx0V⟩
  have hV_sub_D : ∀ x ∈ V, realEmbed x ∈ D := by
    intro x hxV
    exact ⟨hV_ET x hxV, by simpa [D, τ, realEmbed] using hV_swapET x hxV⟩
  have hV_eq :
      ∀ x ∈ V, extendF F (fun k => (realEmbed x) (τ k)) = extendF F (realEmbed x) := by
    intro x hxV
    exact extendF_adjSwap_eq_on_realOpen_of_distributional_local_commutativity
      F hF_holo hF_real_inv W hF_bv_dist hF_local_dist
      i hi V hV_open hV_sp hV_ET hV_swapET x hxV
  intro z hzET hτzET
  have hzD : z ∈ D := ⟨hzET, by simpa [τ] using hτzET⟩
  have hmain := extendF_perm_eq_on_connectedDomain_of_realOpen n F hF_holo
    hF_real_inv τ D hD_open hD_conn' hD_sub_ET hD_sub_permET V hV_open hV_ne
    hV_sub_D hV_eq z hzD
  simpa [τ] using hmain

end BHW
