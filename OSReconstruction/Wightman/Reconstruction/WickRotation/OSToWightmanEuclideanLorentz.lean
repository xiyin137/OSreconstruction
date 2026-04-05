/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanEuclideanNearIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend

/-!
# Euclidean Distributional Lorentz Invariance

Final support stage of the strict OS-II route from Euclidean Wick-section
distributional equalities to real and complex Lorentz invariance on the forward
tube.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW
namespace Task5Bridge

open Task4Bridge

theorem complex_lorentz_invariance_from_euclidean_distributional (n : ℕ) [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_dist :
      ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (hR : R.det = 1) (horth : R.transpose * R = 1)
        (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n |
            (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n ∧
              BHW.complexLorentzAction
                (ComplexLorentzGroup.ofEuclidean R hR horth)
                (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            F (BHW.complexLorentzAction
              (ComplexLorentzGroup.ofEuclidean R hR horth)
              (fun k => wickRotatePoint (x k))) * φ x =
          ∫ x : NPointDomain d n,
            F (fun k => wickRotatePoint (x k)) * φ x) :
    ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
  have hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z := by
    intro Λ z hz
    let S : Set (RestrictedLorentzGroup d) :=
      {R | F (complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = F z}
    have h1S : (1 : RestrictedLorentzGroup d) ∈ S := by
      simp [S, ofReal_one_eq, complexLorentzAction_one]
    have hS_closed : IsClosed S := by
      have hcont_action : Continuous (fun R : RestrictedLorentzGroup d =>
          complexLorentzAction (ComplexLorentzGroup.ofReal R) z) :=
        (continuous_complexLorentzAction_fst z).comp continuous_ofReal
      have hcont_F_on : ContinuousOn (fun R : RestrictedLorentzGroup d =>
          F (complexLorentzAction (ComplexLorentzGroup.ofReal R) z)) Set.univ :=
        hF_holo.continuousOn.comp hcont_action.continuousOn
          (fun R _ => ofReal_preserves_forwardTube R z hz)
      have hcont_F : Continuous (fun R : RestrictedLorentzGroup d =>
          F (complexLorentzAction (ComplexLorentzGroup.ofReal R) z)) := by
        simpa using hcont_F_on
      simpa [S] using isClosed_singleton.preimage hcont_F
    have hS_open : IsOpen S := by
      rw [isOpen_iff_forall_mem_open]
      intro Λ₀ hΛ₀
      let z₀ := complexLorentzAction (ComplexLorentzGroup.ofReal Λ₀) z
      have hz₀ : z₀ ∈ ForwardTube d n := ofReal_preserves_forwardTube Λ₀ z hz
      have h_near_z₀ :=
        near_identity_invariance_euclidean_distributional
          (d := d) n F hF_holo hF_dist z₀ hz₀
      have hright_cont : Continuous (fun R : RestrictedLorentzGroup d =>
          ComplexLorentzGroup.ofReal (R * Λ₀⁻¹)) :=
        continuous_ofReal.comp (continuous_id.mul continuous_const)
      have h_tend : Tendsto (fun R : RestrictedLorentzGroup d =>
          ComplexLorentzGroup.ofReal (R * Λ₀⁻¹)) (𝓝 Λ₀) (𝓝 (1 : ComplexLorentzGroup d)) := by
        have h_tend' :
            Tendsto (fun R : RestrictedLorentzGroup d =>
              ComplexLorentzGroup.ofReal (R * Λ₀⁻¹)) (𝓝 Λ₀)
              (𝓝 (ComplexLorentzGroup.ofReal (Λ₀ * Λ₀⁻¹))) :=
          (hright_cont.continuousAt : ContinuousAt
            (fun R : RestrictedLorentzGroup d => ComplexLorentzGroup.ofReal (R * Λ₀⁻¹)) Λ₀).tendsto
        simpa [mul_inv_cancel, ofReal_one_eq] using h_tend'
      have h_near_pull : ∀ᶠ R in 𝓝 Λ₀,
          F (complexLorentzAction (ComplexLorentzGroup.ofReal (R * Λ₀⁻¹)) z₀) = F z₀ := by
        filter_upwards [h_tend.eventually h_near_z₀] with R hR
        exact hR (ofReal_preserves_forwardTube (R * Λ₀⁻¹) z₀ hz₀)
      have h_eventually : ∀ᶠ R in 𝓝 Λ₀, R ∈ S := by
        filter_upwards [h_near_pull] with R hR
        have hmul :
            complexLorentzAction (ComplexLorentzGroup.ofReal (R * Λ₀⁻¹)) z₀ =
              complexLorentzAction (ComplexLorentzGroup.ofReal R) z := by
          unfold z₀
          calc
            complexLorentzAction (ComplexLorentzGroup.ofReal (R * Λ₀⁻¹))
                (complexLorentzAction (ComplexLorentzGroup.ofReal Λ₀) z)
                =
              complexLorentzAction
                (ComplexLorentzGroup.ofReal (R * Λ₀⁻¹) * ComplexLorentzGroup.ofReal Λ₀) z := by
                  symm
                  exact complexLorentzAction_mul _ _ z
            _ = complexLorentzAction
                (ComplexLorentzGroup.ofReal ((R * Λ₀⁻¹) * Λ₀)) z := by
                  rw [← ofReal_mul_eq]
            _ = complexLorentzAction (ComplexLorentzGroup.ofReal R) z := by
                  rw [mul_assoc, inv_mul_cancel, mul_one]
        have hR_eq : F (complexLorentzAction (ComplexLorentzGroup.ofReal R) z) =
            F (complexLorentzAction (ComplexLorentzGroup.ofReal Λ₀) z) := by
          simpa [hmul] using hR
        have hΛ₀_eq : F (complexLorentzAction (ComplexLorentzGroup.ofReal Λ₀) z) = F z := hΛ₀
        exact hR_eq.trans hΛ₀_eq
      obtain ⟨W, hW_nhd, hW_sub⟩ := Filter.Eventually.exists_mem h_eventually
      obtain ⟨V, hV_sub, hV_open, hΛ₀V⟩ := mem_nhds_iff.mp hW_nhd
      exact ⟨V, fun R hR => hW_sub R (hV_sub hR), hV_open, hΛ₀V⟩
    haveI : PathConnectedSpace (RestrictedLorentzGroup d) :=
      pathConnectedSpace_iff_univ.mpr (RestrictedLorentzGroup.isPathConnected (d := d))
    have hS_univ : S = Set.univ := IsClopen.eq_univ ⟨hS_closed, hS_open⟩ ⟨1, h1S⟩
    have hΛS : Λ ∈ S := by simp [hS_univ]
    simpa [S, complexLorentzAction, ComplexLorentzGroup.ofReal] using hΛS
  exact complex_lorentz_invariance n F hF_holo hF_real_inv

theorem real_lorentz_invariance_from_euclidean_distributional (n : ℕ) [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_dist :
      ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (hR : R.det = 1) (horth : R.transpose * R = 1)
        (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n |
            (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n ∧
              BHW.complexLorentzAction
                (ComplexLorentzGroup.ofEuclidean R hR horth)
                (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            F (BHW.complexLorentzAction
              (ComplexLorentzGroup.ofEuclidean R hR horth)
              (fun k => wickRotatePoint (x k))) * φ x =
          ∫ x : NPointDomain d n,
            F (fun k => wickRotatePoint (x k)) * φ x)
    (Λ : RestrictedLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z := by
  simpa [complexLorentzAction, ComplexLorentzGroup.ofReal] using
    complex_lorentz_invariance_from_euclidean_distributional
      (d := d) n F hF_holo hF_dist
      (ComplexLorentzGroup.ofReal Λ) z hz (ofReal_preserves_forwardTube Λ z hz)

end Task5Bridge
end BHW
