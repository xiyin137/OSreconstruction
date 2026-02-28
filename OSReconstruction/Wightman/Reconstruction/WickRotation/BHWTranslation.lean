/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWExtension
import OSReconstruction.SCV.PaleyWiener

/-!
# BHW Translation Invariance

Translation invariance of the BHW extension, proved via the identity theorem
on the connected permuted extended tube. Also defines the Schwinger function
construction and proves distributional boundary value correspondence.
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]
/-! #### BHW extension helper lemmas and translation invariance

The BHW extension inherits translation invariance from the Wightman functions.
The proof uses BHW uniqueness (property 5 of `bargmann_hall_wightman`) and the
identity theorem for holomorphic functions on connected domains.

The proof is decomposed into three helpers:
1. `permutedExtendedTube_translation_closed` — PET is closed under z ↦ z + c
2. `W_analytic_translation_on_forwardTube` — W_analytic is translation-invariant on FT
3. `permutedExtendedTube_isConnected` — PET is connected

Each helper captures a specific gap in the current formalization infrastructure. -/

/-- The open forward light cone absorbs arbitrary perturbations when scaled large enough.
    For any η ∈ V₊ and any δ : Fin (d+1) → ℝ, there exists t > 0 such that t • η + δ ∈ V₊.

    This follows from V₊ being an open cone: t • η ∈ V₊ for all t > 0, and for large t
    the perturbation δ becomes negligible relative to t • η.

    Blocked by: detailed bound on MinkowskiSpace.minkowskiNormSq of a sum in terms of
    the individual norms and cross terms. The key estimate is that the quadratic form
    grows like t² while the perturbation is O(t). -/
theorem inOpenForwardCone_absorb_perturbation {d : ℕ} [NeZero d]
    (η : Fin (d + 1) → ℝ) (hη : InOpenForwardCone d η)
    (δ : Fin (d + 1) → ℝ) :
    ∃ t : ℝ, t > 0 ∧ InOpenForwardCone d (fun μ => t * η μ + δ μ) := by
  obtain ⟨hη0, hηneg⟩ := hη
  -- The Minkowski norm of (tη + δ) is a downward-opening quadratic in t:
  --   Q(t) = minkowskiNormSq(η) · t² + 2·minkowskiInner(η,δ) · t + minkowskiNormSq(δ)
  -- with leading coefficient minkowskiNormSq(η) < 0. So Q(t) < 0 for large t.
  -- The time component t·η₀ + δ₀ > 0 for large t since η₀ > 0.
  -- Choose t = max(1, t₁, t₂) where t₁ handles positivity and t₂ handles the norm.
  set a := MinkowskiSpace.minkowskiNormSq d η with ha_def
  set b := MinkowskiSpace.minkowskiInner d η δ
  set c_norm := MinkowskiSpace.minkowskiNormSq d δ
  -- t₁: ensures time component positive
  set t₁ := 1 + |δ 0| / η 0 with ht₁_def
  have ht₁_pos : t₁ > 0 := by positivity
  have ht₁_time : t₁ * η 0 + δ 0 > 0 := by
    have := neg_abs_le (δ 0)
    have : |δ 0| / η 0 * η 0 = |δ 0| := by field_simp
    nlinarith
  -- t₂: ensures norm condition. Since a < 0, Q(t) < 0 for t > (-2|b| - |c_norm|) / a.
  -- We pick t₂ large enough.
  set t₂ := 1 + (|2 * b| + |c_norm| + 1) / |a| with ht₂_def
  have ha_neg : a < 0 := hηneg
  have ha_ne : a ≠ 0 := ne_of_lt ha_neg
  have ha_abs_pos : |a| > 0 := abs_pos.mpr ha_ne
  -- Use t = max(t₁, t₂)
  set t := max t₁ t₂
  refine ⟨t, lt_of_lt_of_le ht₁_pos (le_max_left _ _), ?_, ?_⟩
  · -- Time component positive: t * η 0 + δ 0 > 0
    calc t * η 0 + δ 0 ≥ t₁ * η 0 + δ 0 := by
          have : t ≥ t₁ := le_max_left _ _
          nlinarith
      _ > 0 := ht₁_time
  · -- Minkowski norm negative: Q(t) = a·t² + 2bt + c_norm < 0
    -- Since a < 0 and t is large enough, a·t² dominates.
    -- Q(t) = a·t² + 2bt + c_norm
    -- ≤ a·t₂² + |2b|·t₂ + |c_norm|  (since a < 0, t ≥ t₂ gives a·t² ≤ a·t₂²)
    -- Actually let's use the direct estimate.
    -- Q(t) := minkowskiNormSq(tη + δ) = t²·a + 2t·b + c_norm
    -- We show (fun μ => t * η μ + δ μ) = t • η + δ in the Pi-function sense
    have hfun : (fun μ => t * η μ + δ μ) = t • η + δ := by
      ext μ; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    -- Use bilinearity: ‖tη + δ‖² = t²‖η‖² + 2t⟨η,δ⟩ + ‖δ‖²
    have hexpand : MinkowskiSpace.minkowskiNormSq d (fun μ => t * η μ + δ μ) =
        t ^ 2 * a + 2 * t * b + c_norm := by
      simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner, a, b, c_norm]
      conv_lhs => rw [show (∑ i, MinkowskiSpace.metricSignature d i * (t * η i + δ i) *
        (t * η i + δ i)) =
        t ^ 2 * (∑ i, MinkowskiSpace.metricSignature d i * η i * η i) +
        2 * t * (∑ i, MinkowskiSpace.metricSignature d i * η i * δ i) +
        (∑ i, MinkowskiSpace.metricSignature d i * δ i * δ i) from by
          trans (∑ i, (t ^ 2 * (MinkowskiSpace.metricSignature d i * η i * η i) +
            2 * t * (MinkowskiSpace.metricSignature d i * η i * δ i) +
            MinkowskiSpace.metricSignature d i * δ i * δ i))
          · congr 1; ext i; ring
          · simp only [Finset.sum_add_distrib, ← Finset.mul_sum]]
    rw [hexpand]
    have ht_ge_t₂ : t ≥ t₂ := le_max_right _ _
    have ht_pos : t > 0 := lt_of_lt_of_le ht₁_pos (le_max_left _ _)
    have ht₂_ge_one : t₂ ≥ 1 := le_add_of_nonneg_right (div_nonneg (by positivity) (le_of_lt ha_abs_pos))
    have ht_ge_one : t ≥ 1 := le_trans ht₂_ge_one ht_ge_t₂
    -- Key estimate: a * t ≤ -(|2*b| + |c_norm| + 1)
    have hkey : a * t ≤ -(|2 * b| + |c_norm| + 1) := by
      have h1 : t ≥ (|2 * b| + |c_norm| + 1) / |a| :=
        le_trans (le_add_of_nonneg_left (by linarith : (0 : ℝ) ≤ 1)) ht_ge_t₂
      rw [abs_of_neg ha_neg] at h1
      -- h1 : t ≥ (|2*b| + |c_norm| + 1) / (-a), and a < 0
      -- Since t ≥ X/(-a) and a < 0, we get a*t ≤ a*(X/(-a)) = -X
      have hna_pos : -a > 0 := by linarith
      -- h1 : (|2*b| + |c_norm| + 1) / (-a) ≤ t
      -- Multiply both sides by (-a) > 0: |2*b| + |c_norm| + 1 ≤ (-a) * t
      have h2 : (|2 * b| + |c_norm| + 1) / (-a) ≤ t := h1
      rw [div_le_iff₀ hna_pos] at h2
      linarith
    -- From hkey: a*t ≤ -(|2b| + |c_norm| + 1)
    -- t²*a + 2t*b + c_norm = t*(a*t) + 2t*b + c_norm
    --   ≤ t*(-(|2b| + |c_norm| + 1)) + 2t*b + c_norm
    --   = -t*|2b| - t*|c_norm| - t + 2t*b + c_norm
    --   ≤ -t*|2b| - t*|c_norm| - t + t*|2b| + |c_norm|   [since 2t*b ≤ t*|2b| and c_norm ≤ |c_norm|]
    --   = -t*|c_norm| - t + |c_norm|
    --   = (1 - t)*|c_norm| - t
    --   ≤ -t  [since t ≥ 1]
    --   < 0
    -- t²*a + 2tb + c_norm = t*(a*t) + 2tb + c_norm
    --   ≤ t*(-(|2b|+|c_norm|+1)) + 2tb + c_norm  [hkey]
    --   = -t*|2b| - t*|c_norm| - t + 2tb + c_norm
    --   ≤ -t*|c_norm| - t + |c_norm|  [since 2b ≤ |2b|, hence 2tb ≤ t|2b| for t>0]
    --   = |c_norm|*(1-t) - t ≤ -t < 0
    have h2b_le : 2 * t * b ≤ t * |2 * b| := by
      have : 2 * b ≤ |2 * b| := le_abs_self _
      nlinarith
    have hcn_le : c_norm ≤ |c_norm| := le_abs_self _
    -- t * (a * t) ≤ t * (-(|2*b| + |c_norm| + 1))
    have hstep1 : t * (a * t) ≤ t * (-(|2 * b| + |c_norm| + 1)) :=
      mul_le_mul_of_nonneg_left hkey (le_of_lt ht_pos)
    have hsq : t ^ 2 * a = t * (a * t) := by ring
    -- Chain: t²a + 2tb + c_norm = t(at) + 2tb + c_norm
    --   ≤ t(-(|2b|+|c|+1)) + 2tb + c_norm  = -t|2b| - t|c| - t + 2tb + c_norm
    --   ≤ -t|c| - t + c_norm  ≤ -t|c| - t + |c| ≤ -t < 0
    have step2 : t ^ 2 * a + 2 * t * b + c_norm ≤
        -t * |2 * b| - t * |c_norm| - t + 2 * t * b + c_norm := by linarith
    have step3 : -t * |2 * b| - t * |c_norm| - t + 2 * t * b + c_norm ≤
        -t * |c_norm| - t + |c_norm| := by linarith
    have step4 : -t * |c_norm| - t + |c_norm| ≤ -t := by
      have : |c_norm| * (1 - t) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
        linarith
      linarith
    linarith

/-- The forward tube is translation-invariant in the sense that adding a constant
    to all points preserves membership, provided the k=0 imaginary part is adjusted.

    Specifically, if w ∈ ForwardTube and δ is a constant with Im(δ) small enough
    relative to Im(w 0), then w + δ ∈ ForwardTube.

    The key fact: for k > 0, (w+δ)(k) - (w+δ)(k-1) = w(k) - w(k-1), so successive
    differences are preserved. For k = 0, the imaginary part shifts by Im(δ). -/
theorem forwardTube_translate_of_deep_enough {d n : ℕ} [NeZero d]
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ ForwardTube d n)
    (δ : Fin (d + 1) → ℂ)
    (hn : n ≥ 1)
    (hδ : InOpenForwardCone d (fun μ => (w ⟨0, by omega⟩ μ + δ μ).im)) :
    (fun k μ => w k μ + δ μ) ∈ ForwardTube d n := by
  intro k
  simp only [ForwardTube, Set.mem_setOf_eq] at hw ⊢
  by_cases hk : k.val = 0
  · -- k = 0: the condition is Im(w 0 + δ) ∈ V₊
    simp only [hk, ↓reduceDIte]
    have hk0 : k = ⟨0, by omega⟩ := Fin.eq_of_val_eq hk
    rw [hk0]
    convert hδ using 1
    ext μ; simp
  · -- k > 0: the successive difference (w+δ)(k) - (w+δ)(k-1) = w(k) - w(k-1)
    simp only [hk, ↓reduceDIte]
    have hk_orig := hw k
    simp only [hk, ↓reduceDIte] at hk_orig
    convert hk_orig using 1
    ext μ; simp [Complex.sub_im]

/-- Core algebraic lemma for PET translation invariance (n >= 1 case).

    In difference coordinates ξ_k = z_{k+1} - z_k, the forward tube condition
    depends only on the differences. A constant shift z ↦ z + c preserves all
    differences, so the tube condition is preserved for k > 0. The k = 0 absolute
    condition changes, but the union over complex Lorentz transforms in PET
    compensates: the shifted configuration can be expressed as a different Lorentz
    transform applied to a different forward tube member.

    The proof requires either:
    1. A formal difference-coordinate isomorphism and its compatibility with the
       absolute-coordinate ForwardTube definition, or
    2. An explicit algebraic construction using the transitivity of the complex
       Lorentz group on the forward light cone.

    Neither is currently available in the formalization infrastructure.

    Ref: Streater-Wightman §2.5; the proof is immediate in difference-coordinate
    formulations of the forward tube. -/
theorem forwardTube_lorentz_translate_aux_core {d n : ℕ} [NeZero d]
    (π : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ PermutedForwardTube d n π)
    (c : Fin (d + 1) → ℂ)
    (hn : ¬n = 0) :
    ∃ (Λ' : ComplexLorentzGroup d) (w' : Fin n → Fin (d + 1) → ℂ),
      w' ∈ PermutedForwardTube d n π ∧
      (fun k μ => ∑ ν, Λ'.val μ ν * w' k ν) =
        fun k μ => (∑ ν, Λ.val μ ν * w k ν) + c μ := by
  sorry

/-- Helper: translating all points in ForwardTube by a constant preserves the
    successive-difference conditions (k > 0) since the constant cancels in
    z_k - z_{k-1}. The k = 0 condition Im(z₀ + δ) ∈ V₊ is preserved when the
    original Im(z₀) is deep enough in V₊ to absorb Im(δ).

    More precisely: given w ∈ PermutedForwardTube π and δ ∈ ℂ^{d+1}, there exist
    Λ' ∈ ComplexLorentzGroup and w' ∈ PermutedForwardTube π such that
    Λ'·w' = Λ·w + c (pointwise), where δ = Λ⁻¹·c.

    Ref: Streater-Wightman, PCT Spin and Statistics, §2.5 -/
theorem forwardTube_lorentz_translate_aux {d n : ℕ} [NeZero d]
    (π : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ PermutedForwardTube d n π)
    (c : Fin (d + 1) → ℂ) :
    ∃ (Λ' : ComplexLorentzGroup d) (w' : Fin n → Fin (d + 1) → ℂ),
      w' ∈ PermutedForwardTube d n π ∧
      (fun k μ => ∑ ν, Λ'.val μ ν * w' k ν) =
        fun k μ => (∑ ν, Λ.val μ ν * w k ν) + c μ := by
  -- Strategy: use Λ' = Λ and w' = w + Λ⁻¹·c.
  -- Then Λ'·w' = Λ·(w + Λ⁻¹·c) = Λ·w + Λ·Λ⁻¹·c = Λ·w + c.
  -- The hard part is showing w' ∈ PermutedForwardTube.
  -- For n = 0, the statement is vacuous.
  by_cases hn : n = 0
  · subst hn
    exact ⟨Λ, w, hw, by ext k; exact Fin.elim0 k⟩
  · -- Strategy: Λ' = Λ, w' = w + Λ⁻¹·c (constant shift of all points).
    -- Then Λ'·w' = Λ·(w + Λ⁻¹·c) = Λ·w + c (matrix inverse cancels).
    -- Need: w' ∈ PermutedForwardTube π, i.e., fun k => w'(π k) ∈ ForwardTube.
    -- For k > 0: differences are preserved (constant shift cancels).
    -- For k = 0: need Im(w(π 0) + Λ⁻¹·c) ∈ V₊.
    -- Since Im(w(π 0)) ∈ V₊ (from hw) and V₊ is open, this holds when
    -- the perturbation Im(Λ⁻¹·c) is absorbed.
    -- By inOpenForwardCone_absorb_perturbation, ∃ t > 0 with
    -- t · Im(w(π 0)) + Im(Λ⁻¹·c) ∈ V₊.
    -- We use w_scaled = t · w (still in PFT by cone property) and
    -- w' = t · w + Λ⁻¹·c, with Λ' chosen so Λ'·w' = Λ·w + c.
    -- This requires Λ' = (1/t)·Λ, which is NOT in ComplexLorentzGroup.
    --
    -- Correct approach: work in difference coordinates where translation
    -- is trivially compatible, then transfer back. This requires a
    -- coordinate-change bridge not yet available.
    --
    -- Extract as atomic helper capturing the difference-coordinate argument.
    exact forwardTube_lorentz_translate_aux_core π Λ w hw c hn

/-- The permuted extended tube is closed under constant translation.

    For z ∈ PET, z + c ∈ PET for any constant c ∈ ℂ^{d+1}.

    In difference variables ξ_k = z_{k+1} - z_k, translation by c leaves all
    differences unchanged, so the tube condition is trivially preserved. In our
    absolute-coordinate formulation, the k = 0 condition (Im(z₀) ∈ V₊) changes
    under translation, but the union over all complex Lorentz transforms in PET
    compensates.

    Ref: The forward tube in difference variables is trivially translation-invariant;
    this lemma bridges the gap to our absolute-coordinate definition. -/
theorem permutedExtendedTube_translation_closed {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n) :
    (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n := by
  -- Unfold PET to get the witness: π, Λ, w with w ∈ PermutedFT π and z = Λ·w
  simp only [PermutedExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨π, Λ, w, hw, rfl⟩ := hz
  -- Use the helper to get Λ', w' with w' ∈ PermutedFT π and Λ'·w' = Λ·w + c
  obtain ⟨Λ', w', hw', heq⟩ := forwardTube_lorentz_translate_aux π Λ w hw c
  exact ⟨π, Λ', w', hw', heq.symm⟩

/-- The BV of x ↦ W_analytic(x + iεη + c) recovers W_n applied to the
    c-translated test function.

    By change of variables x → x - Re(c) in the Schwartz integral and
    the fact that Im(c) shifts the approach direction within V₊ (which
    doesn't change the BV by direction independence), the boundary value
    of the translated function is W_n(f(· - Re(c))).

    By translation invariance of W_n, this equals W_n(f).

    Blocked by: Formalizing the change of variables in the Bochner integral
    for Schwartz functions, and the direction-independence argument for the
    shifted approach direction iε·η + i·Im(c). These require integration
    infrastructure and the direction-independence theorem.

    Ref: Streater-Wightman §2.5; Vladimirov §26 -/
theorem W_analytic_translated_bv_eq {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        (Wfn.spectrum_condition n).choose
          (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wfn.W n f)) := by
  sorry

/-- Integrability of the translated holomorphic integrand.

    The function x ↦ W_a(x + iεη + c) * f(x) is integrable when W_a is holomorphic
    on ForwardTube and f is Schwartz. This requires polynomial growth of the translated
    slice, which follows from `polynomial_growth_on_slice` applied to z ↦ W_a(z + c).

    Blocked by: showing z ↦ W_a(z + c) is holomorphic on ForwardTube (requires c
    purely imaginary with small enough imaginary part, or translation-covariance
    of ForwardTube membership). More precisely, the translated function has polynomial
    growth on slices via the same Cauchy integral argument. -/
theorem forward_tube_bv_integrable_translated {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (c : Fin (d + 1) → ℂ)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η)
    (ε : ℝ) (hε : ε > 0) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) * (f x))
      MeasureTheory.volume := by
  sorry

/-- The difference ∫ (W_a(x+iεη+c) - W_a(x+iεη)) * f(x) dx splits into the difference
    of integrals, given integrability of each term. This is a routine consequence of
    linearity of the Bochner integral. -/
theorem translate_bv_integral_split {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (hη : InForwardCone d n η)
    (ε : ℝ) (hε : ε > 0) :
    (∫ x : NPointDomain d n,
      ((Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) -
       (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) *
      (f x)) =
    (∫ x : NPointDomain d n,
      (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) *
      (f x)) -
    (∫ x : NPointDomain d n,
      (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
      (f x)) := by
  have heq : ∀ x : NPointDomain d n,
      ((Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) -
       (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) *
      (f x) =
      (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) *
      (f x) -
      (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
      (f x) := fun x => by ring
  simp_rw [heq]
  exact MeasureTheory.integral_sub
    (forward_tube_bv_integrable_translated
      (Wfn.spectrum_condition n).choose
      (Wfn.spectrum_condition n).choose_spec.1
      c f η hη ε hε)
    (forward_tube_bv_integrable
      (Wfn.spectrum_condition n).choose
      (Wfn.spectrum_condition n).choose_spec.1
      f η hη ε hε)

theorem W_analytic_translate_same_bv {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          ((Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I + c μ) -
           (Wfn.spectrum_condition n).choose (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) *
          (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  intro f η hη
  -- Both BV limits equal W_n(f), so the difference → 0.
  have h1 := W_analytic_translated_bv_eq Wfn c f η hη
  have h2 := (Wfn.spectrum_condition n).choose_spec.2 f η hη
  -- Rewrite 0 as W_n(f) - W_n(f)
  rw [show (0 : ℂ) = Wfn.W n f - Wfn.W n f from (sub_self _).symm]
  -- The integral of the difference equals the difference of integrals
  -- for ε > 0 (by translate_bv_integral_split). Each integral converges
  -- to W_n(f), so the difference converges to 0.
  have h_sub := Filter.Tendsto.sub h1 h2
  -- h_sub : Tendsto (fun ε => ∫ W_a(x+iεη+c)f - ∫ W_a(x+iεη)f) → W_n(f) - W_n(f)
  -- We need: Tendsto (fun ε => ∫ (W_a(x+iεη+c) - W_a(x+iεη))f) → W_n(f) - W_n(f)
  -- These agree for ε > 0 by translate_bv_integral_split.
  refine Filter.Tendsto.congr' ?_ h_sub
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨Set.Ioi 0, self_mem_nhdsWithin,
    fun ε hε => (translate_bv_integral_split Wfn c f η hη ε hε).symm⟩

/-- The intersection FT ∩ (FT - c) is open.

    FT is open in the product topology, and translation by -c is a homeomorphism,
    so FT - c is open. The intersection of two open sets is open. -/
theorem forwardTube_isOpen_local {n : ℕ} : IsOpen (ForwardTube d n) := by
  simp only [ForwardTube, InOpenForwardCone, Set.setOf_forall]
  apply isOpen_iInter_of_finite; intro k
  have hcont : ∀ μ : Fin (d + 1), Continuous (fun z : Fin n → Fin (d + 1) → ℂ =>
      (z k μ - (if _ : (k : ℕ) = 0 then 0 else z ⟨(k : ℕ) - 1, by omega⟩) μ).im) := by
    intro μ
    apply Complex.continuous_im.comp
    apply Continuous.sub
    · exact (continuous_apply μ).comp (continuous_apply k)
    · by_cases hk : (k : ℕ) = 0
      · simp [hk]; exact continuous_const
      · simp [hk]
        exact (continuous_apply μ).comp (continuous_apply (⟨(k : ℕ) - 1, by omega⟩ : Fin n))
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (hcont 0)
  · unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    exact isOpen_lt
      (continuous_finset_sum _ fun i _ =>
        ((continuous_const.mul (hcont i)).mul (hcont i)))
      continuous_const

theorem forwardTube_inter_translate_isOpen {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ) :
    IsOpen {z : Fin n → Fin (d + 1) → ℂ |
      z ∈ ForwardTube d n ∧ (fun k μ => z k μ + c μ) ∈ ForwardTube d n} := by
  apply IsOpen.inter
  · exact forwardTube_isOpen_local
  · apply forwardTube_isOpen_local.preimage
    apply continuous_pi; intro k
    apply continuous_pi; intro μ
    have : Continuous (fun z : Fin n → Fin (d + 1) → ℂ => z k μ) :=
      (continuous_apply μ).comp (continuous_apply k)
    exact this.add continuous_const

/-- Distributional uniqueness on the forward tube intersection.

    If G is holomorphic on the intersection {z ∈ FT : z+c ∈ FT} and has zero
    distributional BV (∫ G(x+iεη)f(x) dx → 0 for all Schwartz f and approach
    directions η ∈ V₊^n), then G = 0 on the intersection.

    The intersection is itself a tube domain (over the intersection of the
    forward cone with its c-translate in imaginary coordinates), so the general
    `distributional_uniqueness_tube` applies after flattening.

    Blocked by: Transferring the tube domain structure of the intersection through
    the flattening equivalence and verifying the cone properties. This is a
    routine transfer lemma, parallel to `distributional_uniqueness_forwardTube`
    but for the intersected cone instead of the full forward cone. -/
theorem distributional_uniqueness_forwardTube_inter {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ)
    {F₁ F₂ : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁
      {z | z ∈ ForwardTube d n ∧ (fun k μ => z k μ + c μ) ∈ ForwardTube d n})
    (hF₂ : DifferentiableOn ℂ F₂
      {z | z ∈ ForwardTube d n ∧ (fun k μ => z k μ + c μ) ∈ ForwardTube d n})
    (h_agree : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (F₁ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) -
           F₂ (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)) :
    ∀ z, z ∈ ForwardTube d n → (fun k μ => z k μ + c μ) ∈ ForwardTube d n →
      F₁ z = F₂ z := by
  sorry

theorem W_analytic_translate_eq_on_forwardTube_inter {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ) :
    ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ForwardTube d n →
      (fun k μ => z k μ + c μ) ∈ ForwardTube d n →
      (Wfn.spectrum_condition n).choose (fun k μ => z k μ + c μ) =
      (Wfn.spectrum_condition n).choose z := by
  -- Apply distributional uniqueness on the intersection.
  -- F₁(z) = W_a(z+c), F₂(z) = W_a(z), both holomorphic on the intersection.
  -- Their distributional BV difference → 0 by W_analytic_translate_same_bv.
  let W_a := (Wfn.spectrum_condition n).choose
  have hW_hol := (Wfn.spectrum_condition n).choose_spec.1
  apply distributional_uniqueness_forwardTube_inter c
  · -- F₁(z) = W_a(z+c) is holomorphic on the intersection
    apply hW_hol.comp
    · -- z ↦ (fun k μ => z k μ + c μ) is differentiable (linear + constant)
      intro z _
      apply DifferentiableAt.differentiableWithinAt
      show DifferentiableAt ℂ (fun z : Fin n → Fin (d + 1) → ℂ => fun k μ => z k μ + c μ) z
      exact differentiableAt_id.add (differentiableAt_const _)
    · exact fun z hz => hz.2
  · -- F₂(z) = W_a(z) is holomorphic on FT, hence on the intersection
    exact hW_hol.mono (fun z hz => hz.1)
  · -- BV difference → 0
    exact W_analytic_translate_same_bv Wfn c

/-- The analytic continuation W_analytic (from spectrum_condition) is
    translation-invariant on the forward tube.

    Since W_n is translation-invariant as a distribution, its analytic continuation
    to the forward tube inherits this property: W_analytic(z + c) = W_analytic(z)
    for z, z + c ∈ ForwardTube.

    Ref: Streater-Wightman §2.5 -/
theorem W_analytic_translation_on_forwardTube {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ ForwardTube d n) :
    (Wfn.spectrum_condition n).choose (fun k μ => z k μ + c μ) =
    (Wfn.spectrum_condition n).choose z :=
  W_analytic_translate_eq_on_forwardTube_inter Wfn c z hz hzc

/-- The permuted extended tube is connected.

    PET = ⋃_{π,Λ} Λ·π·FT is connected because the forward tube FT is connected
    (it is convex), adjacent permutation sectors are joined via the edge-of-the-wedge
    theorem at Jost points (spacelike boundary configurations), and the complex Lorentz
    group is connected.

    This fact is used in the BHW uniqueness proof (Property 5 of
    `bargmann_hall_wightman_theorem` in Connectedness.lean) where it currently
    appears as a local sorry. This lemma extracts it as a standalone statement.

    Ref: Jost, "The General Theory of Quantized Fields" Ch. IV -/
theorem permutedExtendedTube_isConnected (d n : ℕ) [NeZero d] :
    IsConnected (PermutedExtendedTube d n) := by
  rw [← BHW_permutedExtendedTube_eq]
  exact BHW.isConnected_permutedExtendedTube (d := d) (n := n)

/-- The forward tube intersected with its c-translate is nonempty.

    For any c ∈ ℂ^{d+1}, there exists z ∈ FT with z + c ∈ FT. We construct such z
    by choosing Im(z₀) deep enough in V₊ that Im(z₀) + Im(c) remains in V₊, and
    choosing successive differences with large enough forward-cone components. -/
theorem forwardTube_inter_translate_nonempty {d n : ℕ} [NeZero d]
    (c : Fin (d + 1) → ℂ) :
    ∃ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ForwardTube d n ∧ (fun k μ => z k μ + c μ) ∈ ForwardTube d n := by
  -- Witness: z_k(μ) = i·(k+1)·M·δ_{μ,0} for M large enough.
  -- Successive differences have imaginary part M·e₀ ∈ V₊.
  -- For z+c at k=0, need (M + Im(c 0), Im(c 1), ...) ∈ V₊, ensured by large M.
  set Ssp := MinkowskiSpace.spatialNormSq d (fun μ => (c μ).im)
  set M : ℝ := 1 + |(c 0).im| + Real.sqrt Ssp
  have hSsp_nn : 0 ≤ Ssp := by
    simp only [Ssp, MinkowskiSpace.spatialNormSq]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hM_pos : M > 0 := by positivity
  have hMc_pos : M + (c 0).im > 0 := by
    have := neg_abs_le (c 0).im; linarith [Real.sqrt_nonneg Ssp]
  have hMc_gt_sqrt : M + (c 0).im > Real.sqrt Ssp := by
    have h1 : -|(c 0).im| ≤ (c 0).im := neg_abs_le (c 0).im
    linarith
  -- M·e₀ ∈ V₊
  have hMe0_cone : InOpenForwardCone d (fun μ => if μ = 0 then M else 0) := by
    refine ⟨by simp; exact hM_pos, ?_⟩
    rw [MinkowskiSpace.minkowskiNormSq_decomp]
    simp only [MinkowskiSpace.spatialNormSq, ↓reduceIte, Fin.succ_ne_zero]
    simp; nlinarith [sq_nonneg M]
  -- (M + Im(c 0), Im(c 1), ...) ∈ V₊
  have hMc_cone : InOpenForwardCone d
      (fun μ => if μ = 0 then M + (c 0).im else (c μ).im) := by
    refine ⟨by simp; exact hMc_pos, ?_⟩
    rw [MinkowskiSpace.minkowskiNormSq_decomp]
    simp only [↓reduceIte]
    -- spatialNormSq of the shifted vector = Ssp
    have hsp : MinkowskiSpace.spatialNormSq d
        (fun μ => if μ = 0 then M + (c 0).im else (c μ).im) = Ssp := by
      simp only [MinkowskiSpace.spatialNormSq, Ssp, Fin.succ_ne_zero, ↓reduceIte]
    rw [hsp]
    have h1 : (M + (c 0).im) ^ 2 > Ssp := by
      have hsq : Real.sqrt Ssp ^ 2 = Ssp := Real.sq_sqrt hSsp_nn
      have hge : Real.sqrt Ssp ≥ 0 := Real.sqrt_nonneg Ssp
      nlinarith [sq_abs (M + (c 0).im - Real.sqrt Ssp)]
    linarith
  -- The witness z
  set z : Fin n → Fin (d + 1) → ℂ :=
    fun k μ => if μ = 0 then Complex.I * ((↑(k : ℕ) + 1) * M) else 0
  -- Imaginary successive differences for z equal M·e₀
  have him_diff_z : ∀ k : Fin n, (fun μ =>
      (z k μ - (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) μ).im) =
      fun μ => if μ = 0 then M else 0 := by
    intro k; ext μ
    by_cases hk : (k : ℕ) = 0
    · simp [z, hk]; split_ifs with hμ
      · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
      · simp
    · simp only [z, hk, ↓reduceDIte]; split_ifs with hμ
      · subst hμ; simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im]
        have hk1 : (1 : ℕ) ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk
        rw [Nat.cast_sub hk1]; ring
      · simp
  -- For z+c at k > 0, c cancels in successive differences
  have him_diff_zc_pos : ∀ k : Fin n, (k : ℕ) ≠ 0 → (fun μ =>
      ((z k μ + c μ) - (if h : k.val = 0 then (0 : Fin (d+1) → ℂ) else
        fun μ => z ⟨k.val - 1, by omega⟩ μ + c μ) μ).im) =
      fun μ => (z k μ - (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) μ).im := by
    intro k hk; ext μ; simp [hk, Complex.sub_im]
  -- For z+c at k = 0, get (M + Im(c 0), Im(c_i))
  have him_diff_zc_zero : ∀ k : Fin n, (k : ℕ) = 0 → (fun μ =>
      ((z k μ + c μ) - (if h : k.val = 0 then (0 : Fin (d+1) → ℂ) else
        fun μ => z ⟨k.val - 1, by omega⟩ μ + c μ) μ).im) =
      fun μ => if μ = 0 then M + (c 0).im else (c μ).im := by
    intro k hk; ext μ; simp [hk]; split_ifs with hμ
    · subst hμ; simp [z, hk, Complex.mul_im, Complex.I_re, Complex.I_im]
    · simp [z, hμ]
  refine ⟨z, ?_, ?_⟩
  · -- z ∈ ForwardTube
    intro k; show InOpenForwardCone d _
    rw [him_diff_z]; exact hMe0_cone
  · -- z + c ∈ ForwardTube
    intro k; show InOpenForwardCone d _
    by_cases hk : (k : ℕ) = 0
    · rw [him_diff_zc_zero k hk]; exact hMc_cone
    · rw [him_diff_zc_pos k hk, him_diff_z]; exact hMe0_cone

/-- **BHW extension is translation invariant on the permuted extended tube.**

    The n-point Wightman function W_n(z₁, ..., zₙ) depends only on the differences
    z_k - z_{k-1}, hence is invariant under simultaneous translation z_k ↦ z_k + c
    for any constant c ∈ ℂ^{d+1}. The BHW extension inherits this property.

    **Proof outline.** By BHW uniqueness (property 5 of `bargmann_hall_wightman`):
    1. F_ext is holomorphic on PET (BHW property 1).
    2. G(z) := F_ext(z + c) is holomorphic on PET (by `permutedExtendedTube_translation_closed`
       ensuring z + c ∈ PET, composed with the holomorphic affine map z ↦ z + c).
    3. G and F_ext agree on FT ∩ (FT - c): for z in this set, G(z) = F_ext(z+c) = W_analytic(z+c)
       = W_analytic(z) = F_ext(z) (using `W_analytic_translation_on_forwardTube` and BHW property 2).
    4. FT ∩ (FT - c) is nonempty and open in PET (`forwardTube_inter_translate_nonempty`).
    5. By the identity theorem on the connected domain PET, G = F_ext everywhere on PET.

    Ref: Streater-Wightman §2.5 (translation invariance);
    Jost, "The General Theory of Quantized Fields" §III.1 -/
theorem bhw_translation_invariant {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n) :
    (W_analytic_BHW Wfn n).val (fun k μ => z k μ + c μ) =
    (W_analytic_BHW Wfn n).val z := by
  -- Abbreviations
  set F_ext := (W_analytic_BHW Wfn n).val with hF_ext_def
  set W_analytic := (Wfn.spectrum_condition n).choose
  set G : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z => F_ext (fun k μ => z k μ + c μ)
  -- BHW properties
  have hF_holo := (W_analytic_BHW Wfn n).property.1
  have hF_eq := (W_analytic_BHW Wfn n).property.2.1
  -- PET topology
  have hPET_open : IsOpen (PermutedExtendedTube d n) :=
    BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube
  have hPET_conn := permutedExtendedTube_isConnected d n
  have hFT_open : IsOpen (ForwardTube d n) :=
    BHW_forwardTube_eq (d := d) (n := n) ▸ BHW.isOpen_forwardTube
  -- Step 1: G is holomorphic on PET
  -- The translation map τ(z)(k)(μ) = z(k)(μ) + c(μ) sends PET into PET
  -- and is holomorphic, so G = F_ext ∘ τ is holomorphic on PET.
  have hG_holo : DifferentiableOn ℂ G (PermutedExtendedTube d n) := by
    intro z₀ hz₀
    -- z₀ + c ∈ PET
    have hz₀c := permutedExtendedTube_translation_closed c z₀ hz₀
    -- F_ext is differentiable at z₀ + c within PET
    have hF_at := hF_holo (fun k μ => z₀ k μ + c μ) hz₀c
    -- The translation map is differentiable
    -- G = F_ext ∘ τ where τ is affine, and τ maps PET → PET
    -- Use DifferentiableWithinAt of composition
    show DifferentiableWithinAt ℂ G (PermutedExtendedTube d n) z₀
    change DifferentiableWithinAt ℂ
      (fun z => F_ext (fun k μ => z k μ + c μ)) (PermutedExtendedTube d n) z₀
    apply DifferentiableWithinAt.comp z₀ hF_at
    · exact differentiableWithinAt_id.add (differentiableWithinAt_const _)
    · intro w hw
      exact permutedExtendedTube_translation_closed c w hw
  -- Step 2: G and F_ext agree on FT ∩ (FT - c)
  -- For z ∈ FT with z + c ∈ FT:
  --   G(z) = F_ext(z + c) = W_analytic(z + c) = W_analytic(z) = F_ext(z)
  have hagree_on_FT : ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ ForwardTube d n → (fun k μ => z k μ + c μ) ∈ ForwardTube d n →
      G z = F_ext z := by
    intro w hw hwc
    show F_ext (fun k μ => w k μ + c μ) = F_ext w
    simp only [hF_ext_def]
    rw [hF_eq _ hwc, hF_eq _ hw]
    exact W_analytic_translation_on_forwardTube Wfn c w hw hwc
  -- Step 3: Find z₀ ∈ FT ∩ (FT - c) (nonempty intersection)
  obtain ⟨z₀, hz₀_ft, hz₀c_ft⟩ := forwardTube_inter_translate_nonempty c
  have hz₀_pet : z₀ ∈ PermutedExtendedTube d n :=
    (BHW_permutedExtendedTube_eq (d := d) (n := n) ▸
      BHW.forwardTube_subset_permutedExtendedTube)
      (BHW_forwardTube_eq (d := d) (n := n) ▸ hz₀_ft)
  -- Step 4: G and F_ext agree in a neighborhood of z₀
  -- FT is open and z₀ ∈ FT, so nhds z₀ contains FT-elements.
  -- FT ∩ (FT - c) is open (intersection of two open sets) and contains z₀.
  have hagree_nhds : G =ᶠ[nhds z₀] F_ext := by
    have hU_open : IsOpen (ForwardTube d n ∩
        {w | (fun k μ => w k μ + c μ) ∈ ForwardTube d n}) := by
      apply IsOpen.inter hFT_open
      -- {w | w + c ∈ FT} is open: preimage of FT under continuous translation
      apply hFT_open.preimage
      exact continuous_id.add continuous_const
    have hz₀_mem : z₀ ∈ ForwardTube d n ∩
        {w | (fun k μ => w k μ + c μ) ∈ ForwardTube d n} :=
      ⟨hz₀_ft, hz₀c_ft⟩
    apply Filter.eventuallyEq_of_mem (hU_open.mem_nhds hz₀_mem)
    intro w ⟨hw_ft, hwc_ft⟩
    exact hagree_on_FT w hw_ft hwc_ft
  -- Step 5: By identity theorem on connected PET, G = F_ext on all of PET
  have h_eq := identity_theorem_product hPET_open hPET_conn hG_holo hF_holo hz₀_pet hagree_nhds
  -- Apply at z
  exact h_eq hz

/-- The smeared BHW extension equals the smeared W_analytic for approach directions
    within the forward tube cone.

    When the approach direction η has successive differences in V₊ (not just
    per-component V₊), the point x + iεη lies in the forward tube for all ε > 0.
    Since F_ext = W_analytic on the forward tube (BHW property 2), the integrals
    agree pointwise in ε, so the limits (distributional boundary values) also agree.

    This captures the forward-tube membership calculation: for z_k = x_k + iεη_k,
    the successive difference of imaginary parts is ε(η_k - η_{k-1}), which lies in
    V₊ when η has successive differences in V₊ and ε > 0 (V₊ is a cone).

    Ref: Streater-Wightman, Theorem 2-11; BHW property 2 -/
theorem bhw_smeared_eq_W_analytic_forwardTube_direction {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη_ft : ∀ k : Fin n,
      let prev := if _h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩
      InOpenForwardCone d (fun μ => η k μ - prev μ))
    (ε : ℝ) (hε : ε > 0) :
    (∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n).val
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
    (∫ x : NPointDomain d n,
      (Wfn.spectrum_condition n).choose
        (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
  congr 1; ext x; congr 1
  -- F_ext and W_analytic agree at x + iεη because x + iεη ∈ ForwardTube
  apply (W_analytic_BHW Wfn n).property.2.1
  -- x + iεη ∈ ForwardTube: successive differences of Im parts are ε·(η_k - η_{k-1}) ∈ V₊
  intro k
  show InOpenForwardCone d _
  -- The imaginary part of the successive difference is ε·(η_k - η_{k-1})
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
  exact inOpenForwardCone_smul d ε hε _ (hη_ft k)

/-- Convex interpolation of approach directions: if η, η' ∈ ForwardConeAbs (successive
    diffs in V₊), then for any s ∈ [0,1], the convex combination (1-s)η + sη' also has
    successive diffs in V₊.

    This is because ForwardConeAbs is convex (forwardConeAbs_convex). The successive
    difference of (1-s)η + sη' is (1-s)(η_k - η_{k-1}) + s(η'_k - η'_{k-1}), a convex
    combination of V₊ elements. -/
theorem convex_approach_direction {d n : ℕ} [NeZero d]
    (η η' : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η)
    (hη' : InForwardCone d n η')
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    InForwardCone d n (fun k μ => (1 - s) * η k μ + s * η' k μ) := by
  -- ForwardConeAbs is convex, and InForwardCone ↔ ForwardConeAbs membership
  rw [inForwardCone_iff_mem_forwardConeAbs]
  exact forwardConeAbs_convex d n hη hη' (by linarith : 0 ≤ 1 - s) hs0
    (by ring : (1 - s) + s = 1)

/-- The BV limit along a convex combination of approach directions equals the
    BV limit along either endpoint.

    If the BV limit exists along η (giving L), then for any s ∈ [0,1], the BV
    limit along η_s = (1-s)η + sη' also equals L. This is because:
    1. The function Φ(s) := lim_{ε→0+} ∫ F(x + iε·η_s) f(x) dx is well-defined
       for all s ∈ [0,1] (η_s ∈ V₊ by convexity of V₊)
    2. Φ is constant on [0,1]: the holomorphic dependence on the approach parameter
       and the Cauchy integral formula show Φ is analytic in s, and the dominated
       convergence + polynomial growth estimates show it's continuous. A continuous
       function on a connected set that's locally constant is constant.
    3. Φ(0) = L, so Φ(1) = L.

    This is the core of Vladimirov's direction-independence theorem (Ch.12).

    Blocked by: The holomorphic parameter dependence (Cauchy integral formula for
    the s-parameter) and the interchange of limit and integral (dominated convergence
    using polynomial growth estimates from Vladimirov Thm 25.5).

    Ref: Vladimirov §12.4; Streater-Wightman, Theorem 2-11 -/
theorem bv_limit_constant_along_convex_path {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (PermutedExtendedTube d n))
    (f : SchwartzNPoint d n)
    (η η' : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η)
    (hη' : InForwardCone d n η')
    (L : ℂ)
    (hL : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L))
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ↑(x k μ) + ε * ↑((1 - s) * η k μ + s * η' k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  sorry

theorem distributional_bv_direction_independence {d n : ℕ} [NeZero d]
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (PermutedExtendedTube d n))
    (f : SchwartzNPoint d n)
    (η η' : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η)
    (hη' : InForwardCone d n η')
    (L : ℂ)
    (hL : Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        F (fun k μ => ↑(x k μ) + ε * ↑(η' k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  -- Use bv_limit_constant_along_convex_path with s = 1:
  -- η₁ = (1-1)·η + 1·η' = η'
  have h := bv_limit_constant_along_convex_path F hF f η η' hη hη' L hL 1 (by norm_num) le_rfl
  -- Simplify: (1-1)*η k μ + 1*η' k μ = η' k μ
  simp only [sub_self, zero_mul, zero_add, one_mul] at h
  exact h

/-- The BHW extension has the same distributional boundary values as W_n.

    The BHW extension F_ext agrees with W_analytic on the forward tube, and
    W_analytic has distributional boundary values recovering W_n by `spectrum_condition`.
    Therefore F_ext also has these boundary values: for η with each η_k ∈ V+,
    lim_{ε→0+} ∫ F_ext(x + iεη) f(x) dx = W_n(f).

    **Proof strategy:** We decompose the argument into two steps:

    1. **Forward tube directions** (`bhw_smeared_eq_W_analytic_forwardTube_direction`):
       For approach directions η where successive differences η_k - η_{k-1} ∈ V+,
       the point x + iεη lies in the forward tube, so F_ext = W_analytic pointwise.
       The integrals agree, and `spectrum_condition` gives the BV limit = W_n(f).

    2. **Direction independence** (`distributional_bv_direction_independence`):
       The distributional BV of a holomorphic function on a tube domain is independent
       of the approach direction within the cone. This standard result (Vladimirov,
       Streater-Wightman Thm 2-11) extends the BV from one ForwardConeAbs direction
       to any other.

    **Approach direction convention:** This theorem uses `InForwardCone d n η` (successive
    differences in V₊), matching `spectrum_condition` and `IsWickRotationPair`.

    Ref: Streater-Wightman Theorem 2-11 -/
theorem bhw_distributional_boundary_values {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (W_analytic_BHW Wfn n).val
            (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Wfn.W n f)) := by
  intro f η hη
  -- Step 1: Construct a "nice" approach direction η₀ with successive differences in V₊.
  -- Define η₀_k(μ) := (k+1) · η_0(μ), so that:
  --   η₀_0 = η_0 ∈ V₊
  --   η₀_k - η₀_{k-1} = η_0 ∈ V₊  for all k > 0
  -- This ensures x + iεη₀ ∈ ForwardTube for all ε > 0.
  -- Each η₀_k = (k+1) · η_0 ∈ V₊ since V₊ is a cone.
  -- We pick η_0 from the given η (using η applied to any valid index).
  -- For this to work, we need n > 0. When n = 0, the statement is vacuous
  -- (Fin 0 is empty, so the integral is trivially equal).
  by_cases hn : n = 0
  · -- n = 0: the integral over Fin 0 → ... is a degenerate case.
    -- The integrand doesn't depend on ε (since Fin 0 is empty), so the
    -- function is constant and trivially converges.
    subst hn
    -- With n = 0, Fin 0 is empty, so z(x,ε) doesn't depend on ε.
    -- F_ext = W_analytic on ForwardTube, and ForwardTube d 0 = univ (vacuous conditions).
    -- The integrand is the same for F_ext and W_analytic, and spectrum_condition gives the limit.
    -- Step 1: F_ext and W_analytic agree at all points (ForwardTube d 0 = univ)
    have hft_univ : ∀ z : Fin 0 → Fin (d+1) → ℂ, z ∈ ForwardTube d 0 := by
      intro z k; exact Fin.elim0 k
    -- Step 2: The integrands are equal for all ε
    have hcongr : ∀ ε : ℝ,
        (∫ x : NPointDomain d 0,
          (W_analytic_BHW Wfn 0).val
            (fun k μ => ↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) * f x) =
        (∫ x : NPointDomain d 0,
          (Wfn.spectrum_condition 0).choose
            (fun k μ => ↑(x k μ) + ↑ε * ↑(η k μ) * Complex.I) * f x) := by
      intro ε; congr 1; ext x; congr 1
      exact (W_analytic_BHW Wfn 0).property.2.1 _ (hft_univ _)
    simp_rw [hcongr]
    -- Step 3: spectrum_condition gives the limit for W_analytic
    have hη_cone : InForwardCone d 0 η := fun k => Fin.elim0 k
    exact (Wfn.spectrum_condition 0).choose_spec.2 f η hη_cone
  · -- n > 0: construct the nice approach direction
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    -- Extract η(0) ∈ V⁺ from InForwardCone (the 0th successive difference is η(0) - 0)
    have hη_first : InOpenForwardCone d (η ⟨0, hn_pos⟩) := by
      have h := hη ⟨0, hn_pos⟩
      simp only [dite_true] at h
      simpa [Pi.zero_apply, sub_zero] using h
    set η₀ : Fin n → Fin (d + 1) → ℝ :=
      fun k μ => (↑k.val + 1) * η ⟨0, hn_pos⟩ μ with hη₀_def
    -- η₀ has successive differences in V₊ (each difference = η_0)
    have hη₀_fc : InForwardCone d n η₀ := by
      intro k
      simp only [hη₀_def]
      split
      case isTrue h =>
        -- k = 0: difference is (0+1) · η_0 - 0 = η_0 ∈ V₊
        simp [h]
        exact hη_first
      case isFalse h =>
        -- k > 0: difference is (k+1)·η_0 - ((k-1)+1)·η_0 = η_0 ∈ V₊
        -- The difference simplifies to ((k+1) - k) · η_0 = η_0
        have hk_pos : 0 < k.val := Nat.pos_of_ne_zero h
        have h_diff : (fun μ => (↑k.val + 1) * η ⟨0, hn_pos⟩ μ -
            (↑(k.val - 1) + 1) * η ⟨0, hn_pos⟩ μ) =
            fun μ => η ⟨0, hn_pos⟩ μ := by
          ext μ
          have hcast : (↑(k.val - 1) : ℝ) = (↑k.val : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ k.val)]
            simp
          rw [hcast]; ring
        rw [h_diff]
        exact hη_first
    -- Step 2: BV of F_ext for η₀.
    -- spectrum_condition gives BV of W_analytic for η₀:
    --   lim ∫ W_analytic(x + iεη₀) f(x) dx = W_n(f)
    have h_sc := (Wfn.spectrum_condition n).choose_spec.2 f η₀ hη₀_fc
    -- F_ext = W_analytic on forward tube, and x + iεη₀ ∈ FT, so integrals agree
    have h_bv_η₀ : Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          (W_analytic_BHW Wfn n).val
            (fun k μ => ↑(x k μ) + ε * ↑(η₀ k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Wfn.W n f)) := by
      -- The F_ext integral equals the W_analytic integral for each ε > 0
      apply Filter.Tendsto.congr' _ h_sc
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨Set.Ioi 0, self_mem_nhdsWithin, fun ε hε =>
        (bhw_smeared_eq_W_analytic_forwardTube_direction Wfn f η₀ hη₀_fc ε hε).symm⟩
    -- Step 3: Apply direction independence to go from η₀ to arbitrary η
    exact distributional_bv_direction_independence
      (W_analytic_BHW Wfn n).val
      (W_analytic_BHW Wfn n).property.1
      f η₀ η hη₀_fc hη (Wfn.W n f) h_bv_η₀

/-! #### Schwinger function construction -/

/-- Define Schwinger functions from Wightman functions via Wick rotation.

    The construction uses the BHW extension F_ext (from `W_analytic_BHW`) composed
    with the Wick rotation map (τ,x⃗) ↦ (iτ,x⃗):

      S_n(f) = ∫_x F_ext_n(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ) f(x₁,...,xₙ) dx

    where F_ext is the BHW extension of W_analytic to the permuted extended tube.
    We use F_ext rather than W_analytic because F_ext is defined and well-behaved
    on all Euclidean points (not just time-ordered ones), and carries the complex
    Lorentz invariance and permutation symmetry needed for E1b and E3.

    Ref: OS I (1973), Section 5; Streater-Wightman, Chapter 3 -/
def constructSchwingerFunctions (Wfn : WightmanFunctions d) :
    SchwingerFunctions d :=
  fun n f =>
    ∫ x : NPointDomain d n,
      (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * (f x)

end
