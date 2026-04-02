/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.ForwardTubeLorentz
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.AdjacencyDistributional

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
        exact forward_tube_bv_integrable
          (fun z => F (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) * z k ν))
          hF_lor_hol
          ⟨{ toLinearMap := ⟨⟨W_n, hW_linear.map_add⟩, hW_linear.map_smul⟩,
             cont := hW_cont }, fun f' η' hη' =>
            lorentz_covariant_distributional_bv_of_restrictedCovariance
              (d := d) (n := n)
              W_n hW_linear hW_cont hW_lorentz
              F hF_hol hF_bv
              Λ f' η' hη'⟩
          f η hη ε hε
      have hInt₂ : MeasureTheory.Integrable
          (fun x : NPointDomain d n =>
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x) := by
        exact forward_tube_bv_integrable F hF_hol
          ⟨{ toLinearMap := ⟨⟨W_n, hW_linear.map_add⟩, hW_linear.map_smul⟩,
             cont := hW_cont }, hF_bv⟩
          f η hη ε hε
      simpa [sub_mul] using hInt₁.sub hInt₂)
    (W_analytic_lorentz_bv_agree_of_restrictedCovariance
      (d := d) (n := n)
      W_n hW_linear hW_cont hW_lorentz
      F hF_hol hF_bv
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
    (Wfn.spectrum_condition n).choose_spec.2

/-- Connected Lorentz covariance of the boundary distribution already pays the
compact-support Wick-section pairing identity for the transformed forward-tube
witness. This is the Wick-section pairing form of
`W_analytic_lorentz_on_tube_of_restrictedCovariance`, and it is the exact shape
used by downstream BHW/Schwinger comparisons. -/
theorem W_analytic_lorentz_wick_pairing_eq_of_restrictedCovariance {d n : ℕ} [NeZero d]
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
    (hF_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (Λ : LorentzGroup d)
    (φ : SchwartzNPoint d n)
    (_hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ))
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆
      {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n}) :
        ∫ x : NPointDomain d n,
        F (fun k μ =>
          ∑ ν, (↑((Λ⁻¹).val μ ν) : ℂ) * wickRotatePoint (x k) ν) * (φ x)
      =
    ∫ x : NPointDomain d n,
        F (fun k => wickRotatePoint (x k)) * (φ x) := by
  refine MeasureTheory.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun x => by
    by_cases hxφ : φ x = 0
    · simp [hxφ]
    · have hx_support : x ∈ Function.support (φ : NPointDomain d n → ℂ) := by
        simpa [Function.mem_support] using hxφ
      have hx_tsupport : x ∈ tsupport (φ : NPointDomain d n → ℂ) :=
        subset_closure hx_support
      have hx_ft : (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n :=
        hφ_tsupport hx_tsupport
      have hcov :
          F (fun k μ =>
            ∑ ν, (↑((Λ⁻¹).val μ ν) : ℂ) * wickRotatePoint (x k) ν)
          =
          F (fun k => wickRotatePoint (x k)) := by
        exact W_analytic_lorentz_on_tube_of_restrictedCovariance
          (d := d) (n := n)
          W_n hW_linear hW_cont hW_lorentz
          F hF_hol hF_bv
          Λ⁻¹ (fun k => wickRotatePoint (x k)) hx_ft
      change
        F (fun k μ =>
            ∑ ν, (↑((Λ⁻¹).val μ ν) : ℂ) * wickRotatePoint (x k) ν) * φ x
          =
        F (fun k => wickRotatePoint (x k)) * φ x
      rw [hcov]

/-- Distributional adjacent-swap equality on compactly supported ET-supported tests.

    This is the honest boundary-pairing theorem for the analytic Wightman function:
    it does not evaluate `W_analytic` at arbitrary real boundary points. Instead it
    compares the pairings of `extendF W_analytic` against compactly supported test
    functions whose real support already lies in the extended tube. The proof is the
    direct specialization of the distributional adjacent-swap theorem proved upstream
    in `AdjacencyDistributional.lean`. -/
theorem W_analytic_swap_boundary_pairing_eq {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (hW_real_inv : ∀ (Λ : LorentzLieGroup.LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      W_analytic (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = W_analytic z)
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hLC : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x : NPointDomain d n, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      (∀ x ∈ tsupport (f : NPointDomain d n → ℂ), BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) →
      (∀ x ∈ tsupport (g : NPointDomain d n → ℂ), BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) →
      (∫ x : NPointDomain d n,
        BHW.extendF W_analytic (BHW.realEmbed x) * (g x)) =
      (∫ x : NPointDomain d n,
        BHW.extendF W_analytic (BHW.realEmbed x) * (f x)) := by
  intro f g hf_compact hg_compact hsep hswap hf_ET hg_ET
  have hft_eq : BHW.ForwardTube d n = ForwardTube d n := by
    ext z
    simp only [BHW.ForwardTube, ForwardTube, Set.mem_setOf_eq]
    exact forall_congr' fun k => inOpenForwardCone_iff _
  have hW_hol' : DifferentiableOn ℂ W_analytic (BHW.ForwardTube d n) := by
    simpa [hft_eq] using hW_hol
  have hW_real_inv' : ∀ (Λ : LorentzLieGroup.LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
      W_analytic (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = W_analytic z := by
    intro Λ z hz
    exact hW_real_inv Λ z (hft_eq ▸ hz)
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η := (inForwardCone_iff_mem_forwardConeAbs η).2 hη_abs
  exact BHW.extendF_adjSwap_pairing_eq_of_distributional_local_commutativity
    W_analytic hW_hol' hW_real_inv' W hBV hLC i hi f g hf_compact hg_compact
    hsep hswap η hη hf_ET hg_ET

/-- Pointwise adjacent-swap equality for the analytic extension at a real
    spacelike ET-overlap point.

    This is the honest pointwise theorem delivered by the distributional EOW
    infrastructure: if the real configuration `x` and its adjacent swap already
    lie in the extended tube, then the extended analytic continuation is
    invariant under that swap at `x`. No boundary continuity of `W_analytic`
    itself is used here. -/
theorem analytic_extended_local_commutativity {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (hW_real_inv : ∀ (Λ : LorentzLieGroup.LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      W_analytic (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = W_analytic z)
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (hLC : IsLocallyCommutativeWeak d W)
    (i : Fin n) (hi : i.val + 1 < n)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hx_sp : MinkowskiSpace.minkowskiNormSq d
      (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0)
    (hx_ET : BHW.realEmbed x ∈ BHWCore.ExtendedTube d n)
    (hx_swapET :
      BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        BHWCore.ExtendedTube d n) :
    BHW.extendF W_analytic (fun k => (BHW.realEmbed x) (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
      BHW.extendF W_analytic (BHW.realEmbed x) := by
  have hft_eq : BHW.ForwardTube d n = ForwardTube d n := by
    ext z
    simp only [BHW.ForwardTube, ForwardTube, Set.mem_setOf_eq]
    exact forall_congr' fun k => inOpenForwardCone_iff _
  have hW_hol' : DifferentiableOn ℂ W_analytic (BHW.ForwardTube d n) := by
    simpa [hft_eq] using hW_hol
  have hW_real_inv' : ∀ (Λ : LorentzLieGroup.LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
      W_analytic (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = W_analytic z := by
    intro Λ z hz
    exact hW_real_inv Λ z (hft_eq ▸ hz)
  have hx_sp' : ∑ μ, LorentzLieGroup.minkowskiSignature d μ *
      (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 := by
    simpa [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
      minkowskiSignature_eq_metricSignature, pow_two, mul_assoc] using hx_sp
  obtain ⟨V, hV_open, hxV, hV_sp, hV_ET, hV_swapET⟩ :=
    BHW.exists_real_open_nhds_adjSwap n i hi x hx_sp' hx_ET hx_swapET
  exact BHW.extendF_adjSwap_eq_on_realOpen_of_distributional_local_commutativity
    W_analytic hW_hol' hW_real_inv' W hBV hLC i hi V hV_open hV_sp hV_ET hV_swapET x hxV

/-- Pointwise adjacent-swap equality for the raw boundary representative, under
    the exact local boundary-identification hypotheses needed to compare it with
    the ET holomorphic extension.

    This theorem isolates the remaining gap behind the old raw-boundary local
    commutativity surface: distributional EOW already gives the equality for
    `BHW.extendF W_analytic`; to descend to the raw `W_analytic(realEmbed x)`
    values, one additionally needs boundary continuity of `W_analytic` from
    the forward tube at the two relevant real ET points. -/
theorem analytic_boundary_local_commutativity_of_boundary_continuous {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (hW_real_inv : ∀ (Λ : LorentzLieGroup.LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      W_analytic (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = W_analytic z)
    (W : (n' : ℕ) → SchwartzNPoint d n' → ℂ)
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
      (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0)
    (hx_ET : BHW.realEmbed x ∈ BHWCore.ExtendedTube d n)
    (hx_swapET :
      BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        BHWCore.ExtendedTube d n)
    (hx_bv : ContinuousWithinAt W_analytic (ForwardTube d n)
      (fun k μ => (x k μ : ℂ)))
    (hx_swap_bv : ContinuousWithinAt W_analytic (ForwardTube d n)
      (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ))) :
    W_analytic (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
      W_analytic (fun k μ => (x k μ : ℂ)) := by
  have hft_eq : BHW.ForwardTube d n = ForwardTube d n := by
    ext z
    simp only [BHW.ForwardTube, ForwardTube, Set.mem_setOf_eq]
    exact forall_congr' fun k => inOpenForwardCone_iff _
  have hW_hol' : DifferentiableOn ℂ W_analytic (BHW.ForwardTube d n) := by
    simpa [hft_eq] using hW_hol
  have hW_real_inv' : ∀ (Λ : LorentzLieGroup.LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
      W_analytic (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = W_analytic z := by
    intro Λ z hz
    exact hW_real_inv Λ z (hft_eq ▸ hz)
  have hx_bv' : ContinuousWithinAt W_analytic (BHW.ForwardTube d n) (BHW.realEmbed x) := by
    simpa [hft_eq, BHW.realEmbed] using hx_bv
  have hx_swap_bv' : ContinuousWithinAt W_analytic (BHW.ForwardTube d n)
      (BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) := by
    simpa [hft_eq, BHW.realEmbed] using hx_swap_bv
  have hW_cinv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ BHW.ForwardTube d n → BHWCore.complexLorentzAction Λ z ∈ BHW.ForwardTube d n →
      W_analytic (BHWCore.complexLorentzAction Λ z) = W_analytic z := by
    intro Λ z hz hΛz
    exact BHW.complex_lorentz_invariance n W_analytic hW_hol' hW_real_inv' Λ z hz hΛz
  have hExt :
      BHW.extendF W_analytic (fun k => (BHW.realEmbed x) (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
        BHW.extendF W_analytic (BHW.realEmbed x) :=
    analytic_extended_local_commutativity W_analytic hW_hol hW_real_inv W hBV hLC
      i hi x hx hx_ET hx_swapET
  have hbd_x :
      BHW.extendF W_analytic (BHW.realEmbed x) = W_analytic (fun k μ => (x k μ : ℂ)) := by
    exact BHW.extendF_eq_boundary_value_ET_of_continuousWithinAt
      n W_analytic hW_hol' hW_cinv x hx_ET hx_bv'
  have hbd_swap :
      BHW.extendF W_analytic (fun k => (BHW.realEmbed x) (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
        W_analytic (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) := by
    simpa [BHW.realEmbed] using
      (BHW.extendF_eq_boundary_value_ET_of_continuousWithinAt
        n W_analytic hW_hol' hW_cinv
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) hx_swapET hx_swap_bv')
  calc
    W_analytic (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ))
        = BHW.extendF W_analytic (fun k => (BHW.realEmbed x) (Equiv.swap i ⟨i.val + 1, hi⟩ k)) := by
            exact hbd_swap.symm
    _ = BHW.extendF W_analytic (BHW.realEmbed x) := hExt
    _ = W_analytic (fun k μ => (x k μ : ℂ)) := hbd_x

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
      (Wfn.spectrum_condition n).choose_spec.2
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
      (Wfn.spectrum_condition n).choose_spec.2
      Wfn.locally_commutative
  have hchosen : (W_analytic_BHW Wfn n).val = h.choose := by
    rfl
  intro z hz
  rw [hchosen]
  exact h.choose_spec.2.2.2.2 G hG_holo hG_eq z hz


end
