import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSelectedWitness

noncomputable section

open Topology

namespace BHW

variable {d : ℕ} [NeZero d]

/-- The adjacent real-edge branch difference on the explicit ET/swap-ET overlap.
This is the real-side analytic object that later common-boundary / EOW steps
must compare to zero on a selected real-open edge slice. -/
def adjacentOS45RealEdgeDifference
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  fun z =>
    BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) τ z) -
      BHW.extendF (bvt_F OS lgc n) z

/-- The adjacent real-edge branch difference is holomorphic on the explicit
ET/swap-ET overlap. -/
theorem adjacentOS45RealEdgeDifference_holomorphicOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    DifferentiableOn ℂ
      (adjacentOS45RealEdgeDifference (d := d) OS lgc n i hi)
      (adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ForwardTube d n →
        BHW.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n (BHW.complexLorentzAction Λ z) = bvt_F OS lgc n z := by
    intro Λ z hz hΛz
    exact bvt_F_complexLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
  have hExtend_holo :
      DifferentiableOn ℂ (BHW.extendF (bvt_F OS lgc n)) (BHW.ExtendedTube d n) :=
    BHW.extendF_holomorphicOn n (bvt_F OS lgc n) hF_holo hF_cinv
  have hperm_cont :
      Continuous
        (fun z : Fin n → Fin (d + 1) → ℂ => BHW.permAct (d := d) τ z) := by
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact (continuous_apply μ).comp (continuous_apply (τ k))
  have hperm_diff :
      Differentiable ℂ
        (fun z : Fin n → Fin (d + 1) → ℂ => BHW.permAct (d := d) τ z) := by
    rw [differentiable_pi]
    intro k
    simpa [BHW.permAct] using
      (differentiable_apply (τ k) :
        Differentiable ℂ
          (fun z : Fin n → Fin (d + 1) → ℂ => z (τ k)))
  have hperm_maps :
      Set.MapsTo
        (fun z : Fin n → Fin (d + 1) → ℂ => BHW.permAct (d := d) τ z)
        (adjacentOS45RealEdgeDomain (d := d) (n := n) i hi)
        (BHW.ExtendedTube d n) := by
    intro z hz
    exact hz.2
  have hDiff_perm :
      DifferentiableOn ℂ
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) τ z))
        (adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) := by
    intro z hz
    exact (hExtend_holo _ (hperm_maps hz)).comp z
      ((hperm_diff z).differentiableWithinAt) hperm_maps
  have hDiff_id :
      DifferentiableOn ℂ (BHW.extendF (bvt_F OS lgc n))
        (adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) :=
    hExtend_holo.mono (by
      intro z hz
      exact hz.1)
  simpa [adjacentOS45RealEdgeDifference, τ] using hDiff_perm.sub hDiff_id

/-- Continuous version of `adjacentOS45RealEdgeDifference_holomorphicOn`. -/
theorem adjacentOS45RealEdgeDifference_continuousOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ContinuousOn
      (adjacentOS45RealEdgeDifference (d := d) OS lgc n i hi)
      (adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) := by
  intro z hz
  exact (adjacentOS45RealEdgeDifference_holomorphicOn
    (d := d) OS lgc n i hi z hz).continuousWithinAt

/-- On any real-open edge slice whose real embeddings lie in the explicit
adjacent ET/swap-ET overlap, the adjacent real-edge branch difference is
continuous. -/
theorem adjacentOS45RealEdgeDifference_realEmbed_continuousOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_real :
      ∀ x ∈ V,
        BHW.realEmbed x ∈ adjacentOS45RealEdgeDomain (d := d) (n := n) i hi) :
    ContinuousOn
      (fun x : NPointDomain d n =>
        adjacentOS45RealEdgeDifference (d := d) OS lgc n i hi (BHW.realEmbed x))
      V := by
  have hrealEmbed_cont :
      Continuous (BHW.realEmbed : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ)) := by
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply k))
  refine
    (adjacentOS45RealEdgeDifference_continuousOn (d := d) OS lgc n i hi).comp
      hrealEmbed_cont.continuousOn ?_
  intro x hx
  exact hV_real x hx

end BHW
