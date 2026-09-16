/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.ForwardTubeLorentz
import Init
import OSReconstruction.ComplexLieGroups.JostPoints
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions









open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]


/-- W_analytic inherits real Lorentz invariance from the Wightman distribution.

    Both z ↦ W_analytic(z) and z ↦ W_analytic(Λz) are holomorphic on the forward tube
    with the same distributional boundary values (by Lorentz invariance of W_n).
    By `distributional_uniqueness_forwardTube`, they agree on the forward tube.

    Ref: Streater-Wightman, §2.4 -/
theorem W_analytic_lorentz_on_tube_of_restrictedCovariance {d n : ℕ} [NeZero d]
    (W_n : SchwartzNPoint d n → ℂ)
    (hW_linear : IsLinearMap ℂ W_n)
    (hW_cont : Continuous W_n)
    (hW_lorentz :
      ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        W_n f = W_n g)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_growth : ∀ (K : Set (Fin n → Fin (d + 1) → ℝ)), IsCompact K →
      K ⊆ ForwardConeAbs d n →
      ∃ (C : ℝ) (N : ℕ), 0 < C ∧
        ∀ (x y : Fin n → Fin (d + 1) → ℝ), y ∈ K →
          ‖F (fun k μ => (x k μ : ℂ) + (y k μ : ℂ) * Complex.I)‖ ≤
            C * (1 + ‖x‖) ^ N)
    (hF_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f))) :
    ∀ (Λ : LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν) = F z := by
  intro Λ z hz
  have hF_lor_hol :
      DifferentiableOn ℂ
        (fun z => F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν))
        (ForwardTube d n) := by
    apply DifferentiableOn.comp hF_hol
    · intro z _hz
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_pi.mpr
      intro k
      apply differentiableAt_pi.mpr
      intro μ
      have hcoord : ∀ (k : Fin n) (ν : Fin (d + 1)),
          DifferentiableAt ℂ (fun x : Fin n → Fin (d + 1) → ℂ => x k ν) z :=
        fun k' ν' => differentiableAt_pi.mp (differentiableAt_pi.mp differentiableAt_id k') ν'
      suffices h :
          ∀ (s : Finset (Fin (d + 1))),
            DifferentiableAt ℂ
              (fun x : Fin n → Fin (d + 1) → ℂ =>
                ∑ ν ∈ s, (↑(Λ.val μ ν) : ℂ) * x k ν) z by
        exact h Finset.univ
      intro s
      induction s using Finset.induction with
      | empty =>
          simp [differentiableAt_const]
      | @insert ν s hν ih =>
          simp only [Finset.sum_insert hν]
          exact ((differentiableAt_const _).mul (hcoord k ν)).add ih
    · intro z hz
      exact restricted_preserves_forward_tube Λ z hz
  have huniq := distributional_uniqueness_forwardTube
    hF_lor_hol
    hF_hol
    (fun f η ε hε hη => by
      have hInt₁ : MeasureTheory.Integrable
          (fun x : NPointDomain d n =>
            F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
              (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * f x) := by
        exact forward_tube_bv_integrable_of_compact
          (fun z => F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν))
          hF_lor_hol
          (forward_tube_lorentz_compact_growth Λ F hF_growth)
          f η hη ε hε
      have hInt₂ : MeasureTheory.Integrable
          (fun x : NPointDomain d n =>
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x) := by
        exact forward_tube_bv_integrable_of_compact F hF_hol
          hF_growth
          f η hη ε hε
      have hInt_sub :
          @MeasureTheory.Integrable ℂ _ _ (NPointDomain d n) MeasurableSpace.pi
            ((fun x : NPointDomain d n =>
                F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
                  (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * f x) -
              (fun x : NPointDomain d n =>
                F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x))
            MeasureTheory.volume := by
        exact cast (by rfl) (hInt₁.sub hInt₂)
      refine hInt_sub.congr (Filter.Eventually.of_forall fun x => ?_)
      simp [sub_mul])
    (W_analytic_lorentz_bv_agree_of_restrictedCovariance
      (d := d) (n := n)
      W_n hW_linear hW_cont hW_lorentz
      F hF_hol hF_growth hF_bv
      Λ)
  exact huniq z hz

/-- W_analytic inherits real Lorentz invariance from the Wightman distribution.

    Both z ↦ W_analytic(z) and z ↦ W_analytic(Λz) are holomorphic on the forward tube
    with the same distributional boundary values (by Lorentz invariance of W_n).
    By `distributional_uniqueness_forwardTube`, they agree on the forward tube.

    Ref: Streater-Wightman, §2.4 -/
theorem W_analytic_lorentz_on_tube (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ (Λ : LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      (Wfn.spectrum_condition n).choose
        (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν) =
      (Wfn.spectrum_condition n).choose z := by
  exact W_analytic_lorentz_on_tube_of_restrictedCovariance
    (d := d) (n := n)
    (Wfn.W n) (Wfn.linear n) (Wfn.tempered n)
    (fun Λ f g hfg => Wfn.lorentz_covariant n Λ f g hfg)
    (Wfn.spectrum_condition n).choose
    (Wfn.spectrum_condition n).choose_spec.1
    (Wfn.spectrum_condition n).choose_spec.2.1
    (Wfn.spectrum_condition n).choose_spec.2.2

/-- The BHW extension of W_analytic from the forward tube to the permuted extended tube.

    Proved by applying the repaired `bargmann_hall_wightman` theorem
    (AnalyticContinuation.lean) directly to the spectrum-condition witness,
    using its honest distributional boundary values and weak local commutativity.

    Ref: Streater-Wightman, Theorem 2-11; Jost, Ch. IV -/
noncomputable def W_analytic_BHW (Wfn : WightmanFunctions d) (n : ℕ) :
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
      (W_analytic_lorentz_on_tube Wfn n)
      Wfn.W
      (Wfn.spectrum_condition n).choose_spec.2.2
      Wfn.locally_commutative
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1,
    h.choose_spec.2.2.2.1⟩

/-- Uniqueness of the BHW extension chosen in `W_analytic_BHW`.

    This restates the uniqueness clause of `bargmann_hall_wightman` for the
    specific extension packaged by `W_analytic_BHW`. It is the concrete
    uniqueness fact needed when comparing `W_analytic_BHW` to other holomorphic
    functions on the permuted extended tube with the same forward-tube boundary
    data. -/
theorem W_analytic_BHW_unique (Wfn : WightmanFunctions d) (n : ℕ)
    (G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hG_holo : DifferentiableOn ℂ G (PermutedExtendedTube d n))
    (hG_eq : ∀ z ∈ ForwardTube d n, G z = (Wfn.spectrum_condition n).choose z) :
    ∀ z ∈ PermutedExtendedTube d n, G z = (W_analytic_BHW Wfn n).val z := by
  let h := bargmann_hall_wightman n
      (Wfn.spectrum_condition n).choose
      (Wfn.spectrum_condition n).choose_spec.1
      (W_analytic_lorentz_on_tube Wfn n)
      Wfn.W
      (Wfn.spectrum_condition n).choose_spec.2.2
      Wfn.locally_commutative
  have hchosen : (W_analytic_BHW Wfn n).val = h.choose := by
    rfl
  intro z hz
  rw [hchosen]
  exact h.choose_spec.2.2.2.2 G hG_holo hG_eq z hz

end
