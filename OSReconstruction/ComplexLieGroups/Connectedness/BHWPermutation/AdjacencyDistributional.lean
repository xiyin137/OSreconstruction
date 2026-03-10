import OSReconstruction.Bridge.AxiomBridge
import OSReconstruction.ComplexLieGroups.JostPoints
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace MeasureTheory
open scoped Matrix.Norms.Operator

namespace BHW

variable {d : ℕ} [NeZero d]

open BHWCore

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
    exact (inOpenForwardCone_iff _).2 (inOpenForwardCone_smul d ε hε _ (hη k))
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
    (hF_local_dist n i ⟨i.val + 1, hi⟩ f g hsep hswap).symm
  calc
    ∫ x : NPointDomain d n, extendF F (realEmbed x) * g x = W n g := h_pairing_g
    _ = W n f := hW_eq
    _ = ∫ x : NPointDomain d n, extendF F (realEmbed x) * f x := h_pairing_f.symm

end BHW
