/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanEuclideanDistributionalBridge

/-!
# Euclidean Near-Identity Bridge

Near-identity complex Lorentz propagation for the strict OS-II route, starting
from Euclidean Wick-section distributional equalities.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW
namespace Task4Bridge

open Task3Bridge

/-- Exponential neighborhood lemma for the distributional Euclidean bridge. -/
private theorem exp_nhd_of_one_euclidean (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      ∃ (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ),
        ComplexLorentzGroup.IsInLieAlgebra X ∧ Λ.val = NormedSpace.exp X ∧ ‖X‖ < ε := by
  set E := Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  let mexp : E → E := NormedSpace.exp
  have hexp_strict : HasStrictFDerivAt mexp
      ((ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E)) (0 : E) := by
    show HasStrictFDerivAt NormedSpace.exp _ _
    convert hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := E) using 1
  set Φ := hexp_strict.toOpenPartialHomeomorph mexp
  have h0_mem : (0 : E) ∈ Φ.source := hexp_strict.mem_toOpenPartialHomeomorph_source
  have hS_nhds : Φ.source ∈ 𝓝 (0 : E) := Φ.open_source.mem_nhds h0_mem
  have hinj : Set.InjOn mexp Φ.source := Φ.injOn
  set η := ComplexLorentzGroup.ηℂ (d := d)
  have hneg_nhds : ∀ᶠ X in 𝓝 (0 : E), -X ∈ Φ.source :=
    continuous_neg.continuousAt.preimage_mem_nhds (by rw [neg_zero]; exact hS_nhds)
  have hconj_cont : Continuous (fun X : E => η * X.transpose * η) :=
    (continuous_const.mul (Continuous.matrix_transpose continuous_id)).mul continuous_const
  have hconj_nhds : ∀ᶠ X in 𝓝 (0 : E), η * X.transpose * η ∈ Φ.source :=
    hconj_cont.continuousAt.preimage_mem_nhds
      (by simp only [Matrix.transpose_zero, mul_zero, zero_mul]; exact hS_nhds)
  have hball : ∀ᶠ X in 𝓝 (0 : E), ‖X‖ < ε :=
    Metric.eventually_nhds_iff.mpr ⟨ε, hε, fun _ hx => by rwa [dist_zero_right] at hx⟩
  have hS_ev : ∀ᶠ X in 𝓝 (0 : E), X ∈ Φ.source := hS_nhds
  have h_good : ∀ᶠ X in 𝓝 (0 : E),
      X ∈ Φ.source ∧ -X ∈ Φ.source ∧ η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε :=
    hS_ev.and (hneg_nhds.and (hconj_nhds.and hball))
  have hmap : map mexp (𝓝 0) = 𝓝 (1 : E) := by
    have hsurj : (ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E).range = ⊤ := by
      ext x
      exact ⟨fun _ => trivial, fun _ => ⟨x, by simp⟩⟩
    have := hexp_strict.map_nhds_eq_of_surj hsurj
    rwa [show mexp 0 = (1 : E) from NormedSpace.exp_zero] at this
  have h_mat : ∀ᶠ M in 𝓝 (1 : E),
      ∃ X : E, mexp X = M ∧ X ∈ Φ.source ∧ -X ∈ Φ.source ∧
        η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε := by
    rw [← hmap, Filter.eventually_map]
    exact h_good.mono fun X ⟨hXS, hnXS, hcXS, hXε⟩ =>
      ⟨X, rfl, hXS, hnXS, hcXS, hXε⟩
  have h_grp : ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      ∃ X : E, mexp X = Λ.val ∧ X ∈ Φ.source ∧ -X ∈ Φ.source ∧
        η * X.transpose * η ∈ Φ.source ∧ ‖X‖ < ε := by
    have hca : ContinuousAt (fun Λ : ComplexLorentzGroup d => Λ.val) 1 :=
      ComplexLorentzGroup.continuous_val.continuousAt
    rw [ContinuousAt, ComplexLorentzGroup.one_val'] at hca
    exact hca.eventually h_mat
  apply h_grp.mono
  intro Λ ⟨X, hexpX, hXS, hnXS, hcXS, hXε⟩
  refine ⟨X, ?_, hexpX.symm, hXε⟩
  have h1 : mexp (η * X.transpose * η) = η * mexp X.transpose * η := by
    simpa [η, ComplexLorentzGroup.ηℂ_unit] using
      (Matrix.exp_units_conj' (ComplexLorentzGroup.ηℂ_unit (d := d)) X.transpose)
  have h2 : mexp X.transpose = (mexp X).transpose :=
    show NormedSpace.exp X.transpose = (NormedSpace.exp X).transpose from
      Matrix.exp_transpose X
  have h3 : (Λ⁻¹).val = η * Λ.val.transpose * η := rfl
  have h5 : mexp (η * X.transpose * η) = (Λ⁻¹).val := by
    rw [h1, h2, h3, hexpX]
  have h6 : (Λ⁻¹).val = mexp (-X) := by
    have hinvmul : (Λ⁻¹).val * Λ.val = 1 := by
      have : (Λ⁻¹ * Λ).val = 1 := by rw [inv_mul_cancel]; rfl
      rwa [ComplexLorentzGroup.mul_val] at this
    have hexp_rinv : mexp X * mexp (-X) = 1 := by
      show NormedSpace.exp X * NormedSpace.exp (-X) = 1
      rw [← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl X))]
      simp [NormedSpace.exp_zero]
    calc
      (Λ⁻¹).val = (Λ⁻¹).val * (mexp X * mexp (-X)) := by rw [hexp_rinv, mul_one]
      _ = (Λ⁻¹).val * mexp X * mexp (-X) := by rw [mul_assoc]
      _ = (Λ⁻¹).val * Λ.val * mexp (-X) := by rw [hexpX]
      _ = mexp (-X) := by rw [hinvmul, one_mul]
  have h7 : mexp (η * X.transpose * η) = mexp (-X) := by rw [h5, h6]
  have h8 : η * X.transpose * η = -X := hinj hcXS hnXS h7
  show ComplexLorentzGroup.IsInLieAlgebra X
  unfold ComplexLorentzGroup.IsInLieAlgebra
  have h9 : X.transpose * η = -(η * X) := by
    calc
      X.transpose * η = 1 * X.transpose * η := by rw [Matrix.one_mul]
      _ = (η * η) * X.transpose * η := by rw [ComplexLorentzGroup.ηℂ_sq (d := d)]
      _ = η * (η * X.transpose * η) := by simp only [Matrix.mul_assoc]
      _ = η * (-X) := by rw [h8]
      _ = -(η * X) := Matrix.mul_neg η X
  rw [h9]
  exact neg_add_cancel _

/-- Distributional-input analogue of the Euclidean near-identity invariance step. -/
theorem near_identity_invariance_euclidean_distributional
    (n : ℕ) [NeZero d]
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
    (z : Fin n → Fin (d + 1) → ℂ) (hz : z ∈ ForwardTube d n) :
    ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
      complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z := by
  have hexp_action_cont : Continuous (fun A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    apply continuous_finset_sum
    intro ν _
    refine Continuous.mul ?_ continuous_const
    exact (continuous_apply ν).comp ((continuous_apply μ).comp NormedSpace.exp_continuous)
  have h0_in_FT : (fun k (μ : Fin (d + 1)) =>
      ∑ ν, (exp (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : Matrix _ _ ℂ) μ ν * z k ν) ∈
        ForwardTube d n := by
    convert hz using 2
    ext k
    simp [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_forwardTube.preimage hexp_action_cont) 0 h0_in_FT
  have hA_in_FT : ∀ A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖A‖ < δ →
      (fun k (μ : Fin (d + 1)) => ∑ ν, (exp A : Matrix _ _ ℂ) μ ν * z k ν) ∈
        ForwardTube d n :=
    fun A hA => hδ_sub (by rwa [Metric.mem_ball, dist_zero_right])
  apply (exp_nhd_of_one_euclidean (δ / 7) (by positivity)).mono
  intro Λ ⟨X, hX_lie, hΛ_eq, hX_small⟩ hΛz
  have haction_eq : complexLorentzAction Λ z =
      fun k μ => ∑ ν, (exp X : Matrix _ _ ℂ) μ ν * z k ν := by
    ext k μ
    simp only [complexLorentzAction]
    congr 1
    ext ν
    rw [← hΛ_eq]
  rw [haction_eq]
  exact near_identity_core_euclidean_distributional
    (d := d) n F hF_holo hF_dist hz hδ_pos hA_in_FT hX_lie hX_small

end Task4Bridge
end BHW
