/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.IdentityTheorem
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions

/-!
# Identity Theorem for Totally Real Submanifolds

If a holomorphic function on an open connected domain D ⊆ ℂ^m vanishes on an
open subset of the totally real subspace ℝ^m ⊂ ℂ^m, then it vanishes on all of D.

## Main results

* `analyticAt_eq_zero_of_vanish_on_reals` — analytic function vanishing on open
  real set vanishes in a complex neighborhood
* `identity_theorem_totally_real` — propagation to the full connected domain

## Proof strategy

For the local step, we use "1D slicing": for z near z₀ ∈ ℝ^m, decompose
z - z₀ = a + ib (a,b ∈ ℝ^m). The 1D function t ↦ f(z₀ + a + tb) is analytic
and vanishes for real t (argument is then real). By isolated zeros, it vanishes
for all t; evaluating at t = i gives f(z) = 0.

## References

* Rudin, *Function Theory in the Unit Ball*, Chapter 11
* Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.3
-/

noncomputable section

open Complex Topology Filter Set

variable {m : ℕ}

namespace SCV

/-! ### Embedding of ℝ^m into ℂ^m -/

/-- Embedding of ℝ^m into ℂ^m. -/
def realToComplex (x : Fin m → ℝ) : Fin m → ℂ := fun i => (x i : ℂ)

@[simp]
theorem realToComplex_apply (x : Fin m → ℝ) (i : Fin m) :
    realToComplex x i = (x i : ℂ) := rfl

/-! ### 1D base case -/

/-- A 1D analytic function vanishing on a real interval vanishes in a complex disc. -/
theorem analyticAt_eq_zero_of_vanish_on_reals_1d
    {f : ℂ → ℂ} {x₀ : ℝ}
    (hf : AnalyticAt ℂ f (x₀ : ℂ))
    {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ t : ℝ, |t - x₀| < ε → f t = 0) :
    f =ᶠ[nhds (x₀ : ℂ)] 0 := by
  obtain ⟨r, hr, hball⟩ := hf.exists_ball_analyticOnNhd
  set D := Metric.ball (x₀ : ℂ) (min r ε)
  have hD_conn : IsPreconnected D := (convex_ball _ _).isPreconnected
  have hx₀_mem : (x₀ : ℂ) ∈ D := by simp [D, lt_min hr hε]
  have hf_anal : AnalyticOnNhd ℂ f D := fun z hz =>
    hball z (Metric.ball_subset_ball (min_le_left r ε) hz)
  -- Real zeros accumulate at x₀
  have hfreq : ∃ᶠ z in nhdsWithin (↑x₀) {(↑x₀)}ᶜ, f z = 0 := by
    rw [Filter.Frequently]
    intro h_ev
    rw [Filter.Eventually, mem_nhdsWithin] at h_ev
    obtain ⟨U, hU_open, hx₀_U, hU_sub⟩ := h_ev
    obtain ⟨δ, hδ, hball_U⟩ := Metric.isOpen_iff.mp hU_open (↑x₀) hx₀_U
    set t₀ := x₀ + min (δ / 2) (ε / 2)
    have ht₀_pos : 0 < min (δ / 2) (ε / 2) := by positivity
    have ht₀_in_U : (↑t₀ : ℂ) ∈ U := by
      apply hball_U
      rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      simp only [t₀, add_sub_cancel_left, abs_of_pos ht₀_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht₀_ne : (↑t₀ : ℂ) ∈ ({(↑x₀ : ℂ)} : Set ℂ)ᶜ := by
      simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj, t₀]
      linarith
    have ht₀_zero : f ↑t₀ = 0 := by
      apply hzero
      simp only [t₀, add_sub_cancel_left, abs_of_pos ht₀_pos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    exact absurd ht₀_zero (hU_sub ⟨ht₀_in_U, ht₀_ne⟩)
  have h_eq : EqOn f 0 D :=
    hf_anal.eqOn_zero_of_preconnected_of_frequently_eq_zero hD_conn hx₀_mem hfreq
  exact Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨D, Metric.isOpen_ball.mem_nhds hx₀_mem, h_eq⟩

/-! ### Multi-dimensional case by 1D slicing -/

/-- **Local vanishing**: an analytic function on ℂ^m vanishing on an open subset
    of ℝ^m vanishes in a complex neighborhood. -/
theorem analyticAt_eq_zero_of_vanish_on_reals
    {f : (Fin m → ℂ) → ℂ} {z₀ : Fin m → ℂ}
    (hf : AnalyticAt ℂ f z₀)
    (hreal : z₀ = realToComplex (fun i => (z₀ i).re))
    {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ x : Fin m → ℝ, (∀ i, |x i - (z₀ i).re| < ε) →
      f (realToComplex x) = 0) :
    f =ᶠ[nhds z₀] 0 := by
  -- Get ball of analyticity
  obtain ⟨r, hr, hball⟩ := hf.exists_ball_analyticOnNhd
  -- Work in a small ball (use r/4 to get strict inequality 3δ < r)
  set δ := min (r / 4) (ε / 4) with hδ_def
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ_r : 3 * δ < r := by
    calc 3 * δ ≤ 3 * (r / 4) := by gcongr; exact min_le_left _ _
      _ < r := by linarith
  have hδ_ε : 2 * δ < ε := by
    calc 2 * δ ≤ 2 * (ε / 4) := by gcongr; exact min_le_right _ _
      _ < ε := by linarith
  -- Show f = 0 on B(z₀, δ)
  suffices h : ∀ z ∈ Metric.ball z₀ δ, f z = 0 from
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Metric.ball z₀ δ, Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ_pos),
       fun z hz => h z hz⟩
  intro z hz
  set x₀ : Fin m → ℝ := fun i => (z₀ i).re
  -- Real and imaginary parts of z - z₀
  set a : Fin m → ℝ := fun i => (z i - z₀ i).re
  set b : Fin m → ℝ := fun i => (z i - z₀ i).im
  -- z₀ i + ↑(a i) + ↑(b i) * I = z i (componentwise complex decomposition)
  have hz_eq : ∀ i, z i = z₀ i + ↑(a i) + ↑(b i) * I := by
    intro i; simp only [a, b]
    rw [show z₀ i + ↑(z i - z₀ i).re + ↑(z i - z₀ i).im * I =
        z₀ i + (↑(z i - z₀ i).re + ↑(z i - z₀ i).im * I) from by ring,
        Complex.re_add_im, add_sub_cancel]
  -- Component bounds
  have h_norm : ‖z - z₀‖ < δ := by rwa [← dist_eq_norm]
  have ha_bound : ∀ i, |a i| < δ := fun i =>
    calc |a i| ≤ ‖z i - z₀ i‖ := Complex.abs_re_le_norm _
      _ ≤ ‖z - z₀‖ := norm_le_pi_norm (z - z₀) i
      _ < δ := h_norm
  have hb_bound : ∀ i, |b i| < δ := fun i =>
    calc |b i| ≤ ‖z i - z₀ i‖ := Complex.abs_im_le_norm _
      _ ≤ ‖z - z₀‖ := norm_le_pi_norm (z - z₀) i
      _ < δ := h_norm
  -- 1D slice: L(t) = z₀ + realToComplex(a) + t * realToComplex(b)
  set L : ℂ → (Fin m → ℂ) := fun t => fun i => z₀ i + ↑(a i) + t * ↑(b i)
  -- L(I) = z
  have hL_I : L I = z := by
    ext i; simp only [L]
    rw [mul_comm]; exact (hz_eq i).symm
  -- z₀ i is real (so we can rewrite in hL_real)
  have hreal_i : ∀ i, z₀ i = ↑((z₀ i).re) := by
    intro i; have := congr_fun hreal i; simpa [realToComplex] using this
  -- L(t) for real t is a real point
  have hL_real : ∀ t : ℝ, L (↑t) = realToComplex (fun i => x₀ i + a i + t * b i) := by
    intro t; ext i; simp only [L, realToComplex]
    rw [hreal_i i]; push_cast; ring
  -- For |t| ≤ 1, L(↑t) is in the ε-ball (so f vanishes there)
  have hL_vanish : ∀ t : ℝ, |t| ≤ 1 → f (L (↑t)) = 0 := by
    intro t ht
    rw [hL_real]
    apply hzero
    intro i
    simp only [x₀]
    have h1 : |(z₀ i).re + a i + t * b i - (z₀ i).re| = |a i + t * b i| := by ring_nf
    rw [h1]
    calc |a i + t * b i| ≤ |a i| + |t * b i| := abs_add_le _ _
      _ = |a i| + |t| * |b i| := by rw [abs_mul]
      _ ≤ 2 * δ := by
          have h1 : |a i| ≤ δ := le_of_lt (ha_bound i)
          have h2 : |t| * |b i| ≤ 1 * δ :=
            mul_le_mul ht (le_of_lt (hb_bound i)) (abs_nonneg _) (by norm_num)
          linarith
      _ < ε := hδ_ε
  -- L(t) in ball of analyticity for ‖t‖ ≤ 2
  have hL_in_ball : ∀ t : ℂ, ‖t‖ ≤ 2 → L t ∈ Metric.ball z₀ r := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff (by linarith : (0 : ℝ) < r)]
    intro i
    simp only [L, Pi.sub_apply]
    calc ‖(z₀ i + ↑(a i) + t * ↑(b i)) - z₀ i‖
        = ‖(↑(a i) : ℂ) + t * ↑(b i)‖ := by congr 1; ring
      _ ≤ ‖(↑(a i) : ℂ)‖ + ‖t * ↑(b i)‖ := norm_add_le _ _
      _ = ‖(↑(a i) : ℂ)‖ + ‖t‖ * ‖(↑(b i) : ℂ)‖ := by rw [norm_mul]
      _ = |a i| + ‖t‖ * |b i| := by
          rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 3 * δ := by
          have h1 : |a i| ≤ δ := le_of_lt (ha_bound i)
          have h2 : ‖t‖ * |b i| ≤ 2 * δ :=
            mul_le_mul ht (le_of_lt (hb_bound i)) (abs_nonneg _) (by norm_num)
          linarith
      _ < r := hδ_r
  -- g(t) = f(L(t)) is analytic on the disc D(0, 2)
  set Disc := Metric.ball (0 : ℂ) 2
  have hDisc_conn : IsPreconnected Disc := (convex_ball _ _).isPreconnected
  have h0_mem : (0 : ℂ) ∈ Disc := Metric.mem_ball_self (by norm_num : (0:ℝ) < 2)
  have hI_mem : I ∈ Disc := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]; norm_num
  have hg_anal : AnalyticOnNhd ℂ (fun t => f (L t)) Disc := by
    intro t ht
    have ht_norm : ‖t‖ < 2 := by rwa [Metric.mem_ball, dist_zero_right] at ht
    have hL_anal : AnalyticAt ℂ L t := by
      show AnalyticAt ℂ (fun s => (fun i => z₀ i + ↑(a i) + s * ↑(b i))) t
      rw [show (fun s => (fun i => z₀ i + ↑(a i) + s * ↑(b i))) =
          (fun x i => (fun j s => z₀ j + ↑(a j) + s * ↑(b j)) i x) from rfl]
      rw [analyticAt_pi_iff]
      intro i
      exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
    exact (hball (L t) (hL_in_ball t (le_of_lt ht_norm))).comp hL_anal
  -- g vanishes frequently near 0 (real zeros accumulate)
  have hg_freq : ∃ᶠ t in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
      f (L t) = 0 := by
    rw [Filter.Frequently]
    intro h_ev
    rw [Filter.Eventually, mem_nhdsWithin] at h_ev
    obtain ⟨U, hU_open, h0_U, hU_sub⟩ := h_ev
    obtain ⟨η, hη, hball_U⟩ := Metric.isOpen_iff.mp hU_open 0 h0_U
    set t₀ : ℝ := min (η / 2) (1 / 2)
    have ht₀_pos : 0 < t₀ := by positivity
    have ht₀_in_U : (↑t₀ : ℂ) ∈ U := by
      apply hball_U
      rw [Metric.mem_ball, dist_eq_norm, sub_zero,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht₀_ne : (↑t₀ : ℂ) ∈ ({(0 : ℂ)} : Set ℂ)ᶜ := by
      simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
      exact ne_of_gt ht₀_pos
    have ht₀_zero : f (L ↑t₀) = 0 :=
      hL_vanish t₀ (by
        rw [abs_of_pos ht₀_pos]; exact le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by norm_num)))
    exact absurd ht₀_zero (hU_sub ⟨ht₀_in_U, ht₀_ne⟩)
  -- By isolated zeros: f ∘ L = 0 on Disc
  have h_eq : EqOn (fun t => f (L t)) 0 Disc :=
    hg_anal.eqOn_zero_of_preconnected_of_frequently_eq_zero hDisc_conn h0_mem hg_freq
  -- f(z) = f(L(I)) = 0
  have h := h_eq hI_mem
  -- h : (fun t => f (L t)) I = 0 I, which is definitionally f (L I) = 0
  show f z = 0
  have : f (L I) = 0 := h
  rwa [hL_I] at this

/-! ### Propagation to connected domains -/

/-- **Identity theorem for totally real submanifolds** (Fin m → ℂ version).
    If f is holomorphic on an open connected D ⊆ ℂ^m and f = 0 on an open
    subset V of D ∩ ℝ^m, then f = 0 on all of D. -/
theorem identity_theorem_totally_real
    {D : Set (Fin m → ℂ)} (hD_open : IsOpen D) (hD_conn : IsConnected D)
    {f : (Fin m → ℂ) → ℂ} (hf : DifferentiableOn ℂ f D)
    {V : Set (Fin m → ℝ)} (hV_open : IsOpen V) (hV_ne : V.Nonempty)
    (hV_sub : ∀ x ∈ V, realToComplex x ∈ D)
    (hf_zero : ∀ x ∈ V, f (realToComplex x) = 0) :
    ∀ z ∈ D, f z = 0 := by
  obtain ⟨x₀, hx₀⟩ := hV_ne
  set z₀ := realToComplex x₀
  have hz₀ : z₀ ∈ D := hV_sub x₀ hx₀
  have hf_anal : AnalyticAt ℂ f z₀ :=
    SCV.differentiableOn_analyticAt hD_open hf hz₀
  obtain ⟨ε, hε, hball_V⟩ := Metric.isOpen_iff.mp hV_open x₀ hx₀
  have hzero : ∀ x : Fin m → ℝ, (∀ i, |x i - x₀ i| < ε) →
      f (realToComplex x) = 0 := by
    intro x hx
    apply hf_zero
    apply hball_V
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
    intro i; rw [Real.norm_eq_abs]; exact hx i
  have hreal : z₀ = realToComplex (fun i => (z₀ i).re) := by
    ext i; simp only [z₀, realToComplex_apply, Complex.ofReal_re]
  have hlocal : f =ᶠ[nhds z₀] 0 :=
    analyticAt_eq_zero_of_vanish_on_reals hf_anal hreal hε hzero
  intro z hz
  exact identity_theorem_SCV hD_open hD_conn hf (differentiableOn_const 0) hz₀ hlocal hz

/-! ### Product type version -/

/-- Embedding of product real space into product complex space. -/
def realToComplexProduct {n p : ℕ} (x : Fin n → Fin p → ℝ) :
    Fin n → Fin p → ℂ := fun i j => (x i j : ℂ)

/-! #### CLE coordinate lemmas -/

private lemma flattenCLE_symm_apply {n p : ℕ}
    (w : Fin (n * p) → ℂ) (i : Fin n) (j : Fin p) :
    (SCV.flattenCLE n p).symm w i j = w (finProdFinEquiv (i, j)) := by
  simp only [SCV.flattenCLE, LinearEquiv.coe_toContinuousLinearEquiv_symm',
    LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.piCurry_apply]
  unfold LinearEquiv.piCongrLeft Sigma.curry; simp

private lemma flattenCLE_apply {n p : ℕ}
    (z : Fin n → Fin p → ℂ) (k : Fin (n * p)) :
    (SCV.flattenCLE n p) z k =
      z (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  have h := flattenCLE_symm_apply ((SCV.flattenCLE n p) z)
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  simp only [Prod.mk.eta, Equiv.apply_symm_apply] at h; exact h.symm

/-- **Identity theorem for totally real submanifolds** (product type version).
    Transfer to flat `Fin (n*p) → ℂ` via `flattenCLE`, apply the flat version,
    then transfer back. -/
theorem identity_theorem_totally_real_product
    {n p : ℕ}
    {D : Set (Fin n → Fin p → ℂ)} (hD_open : IsOpen D) (hD_conn : IsConnected D)
    {f : (Fin n → Fin p → ℂ) → ℂ} (hf : DifferentiableOn ℂ f D)
    {V : Set (Fin n → Fin p → ℝ)} (hV_open : IsOpen V) (hV_ne : V.Nonempty)
    (hV_sub : ∀ x ∈ V, realToComplexProduct x ∈ D)
    (hf_zero : ∀ x ∈ V, f (realToComplexProduct x) = 0) :
    ∀ z ∈ D, f z = 0 := by
  obtain ⟨x₀, hx₀⟩ := hV_ne
  set z₀ := realToComplexProduct x₀
  have hz₀ : z₀ ∈ D := hV_sub x₀ hx₀
  -- Set up CLE transfer
  set φ := SCV.flattenCLE n p
  set f' : (Fin (n * p) → ℂ) → ℂ := f ∘ ⇑φ.symm
  -- f is analytic at z₀
  have hf_anal : AnalyticAt ℂ f z₀ := analyticAt_of_differentiableOn_product hD_open hf hz₀
  -- f' is analytic at φ z₀
  have hf'_anal : AnalyticAt ℂ f' (φ z₀) := by
    have h1 : AnalyticAt ℂ (⇑φ.symm) (φ z₀) := φ.symm.analyticAt _
    have h2 : AnalyticAt ℂ f (φ.symm (φ z₀)) := by rwa [ContinuousLinearEquiv.symm_apply_apply]
    exact h2.comp h1
  -- φ z₀ is a real point
  have hφz₀_real : φ z₀ = realToComplex (fun k => (φ z₀ k).re) := by
    ext k; simp only [realToComplex_apply]
    show (SCV.flattenCLE n p) z₀ k = _
    rw [flattenCLE_apply]
    simp [z₀, realToComplexProduct, Complex.ofReal_re]
  -- Get ε for the real neighborhood
  obtain ⟨ε, hε, hball_V⟩ := Metric.isOpen_iff.mp hV_open x₀ hx₀
  -- f' vanishes on reals near φ z₀
  have hf'_zero : ∀ y : Fin (n * p) → ℝ,
      (∀ k, |y k - (φ z₀ k).re| < ε) → f' (realToComplex y) = 0 := by
    intro y hy
    show f (φ.symm (realToComplex y)) = 0
    have h_unflatten : φ.symm (realToComplex y) =
        realToComplexProduct (fun i j => y (finProdFinEquiv (i, j))) := by
      ext i j
      show (SCV.flattenCLE n p).symm (realToComplex y) i j = _
      rw [flattenCLE_symm_apply, realToComplex_apply]; rfl
    rw [h_unflatten]
    apply hf_zero
    apply hball_V
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
    intro i; rw [pi_norm_lt_iff hε]
    intro j; simp only [Pi.sub_apply, Real.norm_eq_abs]
    have h_re : (φ z₀ (finProdFinEquiv (i, j))).re = x₀ i j := by
      show ((SCV.flattenCLE n p) z₀ (finProdFinEquiv (i, j))).re = x₀ i j
      rw [flattenCLE_apply]
      simp [z₀, realToComplexProduct, Equiv.symm_apply_apply, Complex.ofReal_re]
    rw [← h_re]; exact hy (finProdFinEquiv (i, j))
  -- Apply local vanishing
  have hlocal' : f' =ᶠ[nhds (φ z₀)] 0 :=
    analyticAt_eq_zero_of_vanish_on_reals hf'_anal hφz₀_real hε hf'_zero
  -- Transfer back: f = f' ∘ φ, so f =ᶠ 0
  have hlocal : f =ᶠ[nhds z₀] 0 := by
    have hf_eq : f = f' ∘ φ := by
      ext z; simp [f', Function.comp, ContinuousLinearEquiv.symm_apply_apply]
    rw [hf_eq]; exact hlocal'.comp_tendsto φ.continuous.continuousAt
  -- Propagate via identity theorem for product types
  intro z hz
  exact identity_theorem_product hD_open hD_conn hf (differentiableOn_const 0) hz₀ hlocal hz

end SCV

end
