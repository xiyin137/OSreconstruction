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

/-- W_analytic inherits real Lorentz invariance from the Wightman distribution.

    Both z ↦ W_analytic(z) and z ↦ W_analytic(Λz) are holomorphic on the forward tube
    with the same distributional boundary values (by Lorentz invariance of W_n).
    By `distributional_uniqueness_forwardTube`, they agree on the forward tube.

    Ref: Streater-Wightman, §2.4 -/
theorem W_analytic_lorentz_on_tube (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ (Λ : LorentzGroup.Restricted (d := d))
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      (Wfn.spectrum_condition n).choose
        (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
      (Wfn.spectrum_condition n).choose z := by
  intro Λ z hz
  -- Apply distributional uniqueness: two holomorphic functions on the forward tube
  -- with the same distributional boundary values must agree.
  have huniq := distributional_uniqueness_forwardTube
    (W_analytic_lorentz_holomorphic Wfn n Λ)
    (Wfn.spectrum_condition n).choose_spec.1
    (W_analytic_lorentz_bv_agree Wfn n Λ)
  exact huniq z hz

/-- W_analytic extends continuously to the real boundary of the forward tube.

    Proved using `continuous_boundary_forwardTube`: the distributional boundary value
    condition from `spectrum_condition` provides the hypothesis.

    Ref: Streater-Wightman, Theorem 2-9 -/
theorem W_analytic_continuous_boundary (Wfn : WightmanFunctions d) (n : ℕ) :
    ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt (Wfn.spectrum_condition n).choose
        (ForwardTube d n) (fun k μ => (x k μ : ℂ)) := by
  intro x
  exact continuous_boundary_forwardTube (d := d) (n := n)
    (Wfn.spectrum_condition n).choose_spec.1
    ⟨Wfn.W n, Wfn.tempered n, (Wfn.spectrum_condition n).choose_spec.2⟩ x

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
  · exact forward_tube_bv_integrable
      W_analytic hW_hol ⟨W n, hW_cont, hBV⟩ g η hη ε (Set.mem_Ioi.mp hε)
  · exact forward_tube_bv_integrable
      W_analytic hW_hol ⟨W n, hW_cont, hBV⟩ f η hη ε (Set.mem_Ioi.mp hε)

/-- Boundary-pairing form of local commutativity for adjacent swaps.

    For test functions `f, g` related by adjacent swap on a spacelike support
    region, the real-boundary pairings of `W_analytic` coincide:
    `∫ W_analytic(x) g(x) dx = ∫ W_analytic(x) f(x) dx`. -/
theorem W_analytic_swap_boundary_pairing_eq {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
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
    boundary_value_recovery_forwardTube
      (d := d) (n := n) hW_hol hW_cont hBV g
  have hf_pair :
      W n f =
        ∫ x : NPointDomain d n, W_analytic (fun k μ => (x k μ : ℂ)) * (f x) :=
    boundary_value_recovery_forwardTube
      (d := d) (n := n) hW_hol hW_cont hBV f
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
    itself is now provided by `W_analytic_swap_distributional_agree`.

    Ref: Streater-Wightman Thm 3-5; Jost §IV.3 -/
theorem analytic_boundary_local_commutativity {d n : ℕ} [NeZero d]
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
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
    (d := d) (n := n) W_analytic hW_hol W hW_cont hBV hLC i hi
  have hSwapBdry := W_analytic_swap_boundary_pairing_eq
    (d := d) (n := n) W_analytic hW_hol W hW_cont hBV hLC i hi
  let B : NPointDomain d n → ℂ := fun y => W_analytic (fun k μ => (y k μ : ℂ))
  have hB_cont : Continuous B :=
    boundary_function_continuous_forwardTube (d := d) (n := n) hW_hol hW_cont hBV
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
theorem W_analytic_local_commutativity (Wfn : WightmanFunctions d) (n : ℕ) :
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
      (W_analytic_continuous_boundary Wfn n)
      (W_analytic_local_commutativity Wfn n)
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1,
    h.choose_spec.2.2.2.1⟩


end
