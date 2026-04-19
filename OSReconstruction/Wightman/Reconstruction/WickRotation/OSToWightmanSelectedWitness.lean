import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues

/-!
# Selected OS witness support

This file exposes small theorem-surface facts about the selected OS analytic
witness `bvt_F OS lgc`.  The facts here are already implicit in the boundary
value construction, but later OS-route PET/edge arguments need them as named
inputs.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

variable {d : ℕ} [NeZero d]

/-- The selected OS analytic witness is invariant under restricted real Lorentz
transformations on the forward tube. -/
theorem bvt_F_restrictedLorentzInvariant_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      bvt_F OS lgc n
        (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
      bvt_F OS lgc n z := by
  intro Λ z hz
  have hF_holo_BHW :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_dist_BHW :
      ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (hdet : R.det = 1) (horth : R.transpose * R = 1)
        (ψ : SchwartzNPoint d n),
          HasCompactSupport (ψ : NPointDomain d n → ℂ) →
          tsupport (ψ : NPointDomain d n → ℂ) ⊆
            {x : NPointDomain d n |
              (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n ∧
                BHW.complexLorentzAction
                  (ComplexLorentzGroup.ofEuclidean R hdet horth)
                  (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n} →
          ∫ x : NPointDomain d n,
              bvt_F OS lgc n
                (BHW.complexLorentzAction
                  (ComplexLorentzGroup.ofEuclidean R hdet horth)
                  (fun k => wickRotatePoint (x k))) * ψ x
            =
          ∫ x : NPointDomain d n,
              bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * ψ x := by
    intro R hdet horth ψ hψ_compact hψ_tsupport
    refine bvt_F_ofEuclidean_wick_pairing
      (d := d) OS lgc n R hdet horth ψ hψ_compact ?_
    intro x hx
    rcases hψ_tsupport hx with ⟨hx0, hx1⟩
    constructor
    · simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx0
    · simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx1
  have hz_BHW : z ∈ BHW.ForwardTube d n := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hz
  exact
    BHW.Task5Bridge.real_lorentz_invariance_from_euclidean_distributional
      (d := d) n (bvt_F OS lgc n) hF_holo_BHW hF_dist_BHW Λ z hz_BHW

/-- Restricted real Lorentz invariance analytically continues to complex
Lorentz invariance on the forward-tube overlap. -/
theorem bvt_F_complexLorentzInvariant_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n →
      BHW.complexLorentzAction Λ z ∈ ForwardTube d n →
      bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
        bvt_F OS lgc n z := by
  intro Λ z hz hΛz
  have hF_hol_BHW :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hreal_BHW :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  exact
    BHW.complex_lorentz_invariance
      (d := d) n (bvt_F OS lgc n)
      hF_hol_BHW
      hreal_BHW
      Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
