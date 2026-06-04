import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2BaseStep

/-!
# OS II Delta-Smearing Bridge

OS II Chapter V.2 upgrades distributional real-slice identities to pointwise
scalar-product identities by smearing with delta families and passing to the
limit.  This file records the neutral analysis part of that step for
normalized nonnegative Schwartz approximate identities.
-/

noncomputable section

open Complex Topology MeasureTheory Filter
open scoped Classical NNReal BigOperators

namespace OSReconstruction

/-- The positive-time approximate identity already constructed in the `k = 2`
base-step file supplies the exact data needed by the OS-II delta-smearing
bridge: nonnegativity, real values, normalization, compact support,
positive-time support, ordinary support inside a shrinking ball, and a radius
sequence tending to zero. -/
theorem exists_positiveTime_shrinking_schwartz_approx_identity_for_delta_bridge
    {d : ℕ} [NeZero d] :
    ∃ (φ : ℕ → SchwartzSpacetime d) (r : ℕ → ℝ),
      (∀ n x, 0 ≤ (φ n x).re) ∧
      (∀ n x, (φ n x).im = 0) ∧
      (∀ n, ∫ x : SpacetimeDim d, φ n x = 1) ∧
      (∀ n, HasCompactSupport (φ n : SpacetimeDim d → ℂ)) ∧
      (∀ n, tsupport (φ n : SpacetimeDim d → ℂ) ⊆
        {x : SpacetimeDim d | 0 < x 0}) ∧
      (∀ n, Function.support (φ n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (r n)) ∧
      Tendsto r atTop (𝓝 0) := by
  obtain ⟨φ, hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_pos, hφ_ball⟩ :=
    exists_approx_identity_sequence (d := d)
  let r : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  refine ⟨φ, r, hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_pos, ?_, ?_⟩
  · intro n x hx
    exact hφ_ball n (subset_tsupport _ hx)
  · simpa [r, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝 0))

/-- A normalized nonnegative Schwartz bump supported in the finite positive
orthant and in an arbitrarily small ball around `0`.  This is the
finite-dimensional version needed when OS II smears all positive time-difference
variables at once. -/
theorem exists_positiveOrthant_approx_identity_schwartz
    {m : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ x : Fin m → ℝ, 0 ≤ (φ x).re) ∧
      (∀ x : Fin m → ℝ, (φ x).im = 0) ∧
      (∫ x : Fin m → ℝ, φ x = 1) ∧
      HasCompactSupport (φ : (Fin m → ℝ) → ℂ) ∧
      tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ {x | ∀ i : Fin m, 0 < x i} ∧
      tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ Metric.ball 0 ε := by
  let c : Fin m → ℝ := fun _ => ε / 2
  let b : ContDiffBump c := ⟨ε / 8, ε / 4, by linarith, by linarith⟩
  let f : (Fin m → ℝ) → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let g₀ := HasCompactSupport.toSchwartzMap hf_compact hf_smooth
  have hg₀_int_ne : ∫ x : Fin m → ℝ, g₀ x ≠ 0 := by
    change ∫ x, (↑(b x) : ℂ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt b.integral_pos)
  let φ : SchwartzMap (Fin m → ℝ) ℂ := (∫ x : Fin m → ℝ, g₀ x)⁻¹ • g₀
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [φ, SchwartzMap.smul_apply, smul_eq_mul]
    rw [Complex.mul_re]
    have hg₀_im : (g₀ x).im = 0 := Complex.ofReal_im (b x)
    have hg₀_re : 0 ≤ (g₀ x).re := Complex.ofReal_re (b x) ▸ b.nonneg
    have hint_im : (∫ u : Fin m → ℝ, g₀ u).im = 0 := by
      rw [show (fun u => g₀ u) = (fun u => (↑(b u) : ℂ)) from rfl]
      rw [integral_complex_ofReal]
      simp
    have hinv_im : ((∫ u : Fin m → ℝ, g₀ u)⁻¹).im = 0 := by
      rw [Complex.inv_im, hint_im]
      ring_nf
    rw [hg₀_im, hinv_im]
    ring_nf
    apply mul_nonneg _ hg₀_re
    rw [Complex.inv_re]
    apply div_nonneg
    · change 0 ≤ (∫ u, (↑(b u) : ℂ)).re
      rw [integral_complex_ofReal]
      simp only [Complex.ofReal_re]
      exact le_of_lt b.integral_pos
    · exact Complex.normSq_nonneg _
  · intro x
    simp only [φ, SchwartzMap.smul_apply, smul_eq_mul]
    rw [Complex.mul_im]
    have hg₀_im : (g₀ x).im = 0 := Complex.ofReal_im (b x)
    have hint_im : (∫ u : Fin m → ℝ, g₀ u).im = 0 := by
      rw [show (fun u => g₀ u) = (fun u => (↑(b u) : ℂ)) from rfl]
      rw [integral_complex_ofReal]
      simp
    have hinv_im : ((∫ u : Fin m → ℝ, g₀ u)⁻¹).im = 0 := by
      rw [Complex.inv_im, hint_im]
      ring_nf
    rw [hg₀_im, hinv_im]
    ring_nf
  · change ∫ x : Fin m → ℝ, (∫ u : Fin m → ℝ, g₀ u)⁻¹ • g₀ x = 1
    rw [MeasureTheory.integral_smul]
    simpa [smul_eq_mul] using inv_mul_cancel₀ hg₀_int_ne
  · exact hf_compact.smul_left
  · intro x hx i
    have hsubset : tsupport (φ : (Fin m → ℝ) → ℂ) ⊆
        tsupport (g₀ : (Fin m → ℝ) → ℂ) := by
      exact tsupport_smul_subset_right
        (fun _ : Fin m → ℝ => (∫ u : Fin m → ℝ, g₀ u)⁻¹)
        (g₀ : (Fin m → ℝ) → ℂ)
    have hx_supp : x ∈ Metric.closedBall c (ε / 4 : ℝ) := by
      have h_tsup_f : tsupport f ⊆ Metric.closedBall c (ε / 4) := by
        intro y hy
        rw [← b.tsupport_eq]
        exact tsupport_comp_subset Complex.ofReal_zero _ hy
      exact h_tsup_f (hsubset hx)
    rw [Metric.mem_closedBall] at hx_supp
    have hcoord : |x i - ε / 2| ≤ ε / 4 := by
      calc
        |x i - ε / 2| = |x i - c i| := by simp [c]
        _ = ‖(x - c) i‖ := by simp [Pi.sub_apply, Real.norm_eq_abs]
        _ ≤ ‖x - c‖ := norm_le_pi_norm _ i
        _ = dist x c := by rw [dist_eq_norm]
        _ ≤ ε / 4 := hx_supp
    have hcoord' := abs_le.mp hcoord
    linarith
  · intro x hx
    have hsubset : tsupport (φ : (Fin m → ℝ) → ℂ) ⊆
        tsupport (g₀ : (Fin m → ℝ) → ℂ) := by
      exact tsupport_smul_subset_right
        (fun _ : Fin m → ℝ => (∫ u : Fin m → ℝ, g₀ u)⁻¹)
        (g₀ : (Fin m → ℝ) → ℂ)
    have hx_supp : x ∈ Metric.closedBall c (ε / 4 : ℝ) := by
      have h_tsup_f : tsupport f ⊆ Metric.closedBall c (ε / 4) := by
        intro y hy
        rw [← b.tsupport_eq]
        exact tsupport_comp_subset Complex.ofReal_zero _ hy
      exact h_tsup_f (hsubset hx)
    rw [Metric.mem_ball]
    have hc : dist c (0 : Fin m → ℝ) ≤ ε / 2 := by
      rw [dist_eq_norm]
      exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => by
        simp [c, Real.norm_eq_abs, abs_of_pos hε])
    have hx' : dist x c ≤ ε / 4 := by
      simpa [Metric.mem_closedBall] using hx_supp
    linarith [dist_triangle x c 0]

/-- A sequence of normalized nonnegative Schwartz bumps supported in the
positive orthant with ordinary supports shrinking to `0`. -/
theorem exists_positiveOrthant_shrinking_schwartz_approx_identity_for_delta_bridge
    (m : ℕ) :
    ∃ (φ : ℕ → SchwartzMap (Fin m → ℝ) ℂ) (r : ℕ → ℝ),
      (∀ n x, 0 ≤ (φ n x).re) ∧
      (∀ n x, (φ n x).im = 0) ∧
      (∀ n, ∫ x : Fin m → ℝ, φ n x = 1) ∧
      (∀ n, HasCompactSupport (φ n : (Fin m → ℝ) → ℂ)) ∧
      (∀ n, tsupport (φ n : (Fin m → ℝ) → ℂ) ⊆
        {x | ∀ i : Fin m, 0 < x i}) ∧
      (∀ n, Function.support (φ n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (r n)) ∧
      Tendsto r atTop (𝓝 0) := by
  let φ : ℕ → SchwartzMap (Fin m → ℝ) ℂ := fun n =>
    Classical.choose
      (exists_positiveOrthant_approx_identity_schwartz
        (m := m) (1 / (n + 1 : ℝ)) (by positivity))
  have hs :
      ∀ n,
        (∀ x : Fin m → ℝ, 0 ≤ ((φ n) x).re) ∧
        (∀ x : Fin m → ℝ, ((φ n) x).im = 0) ∧
        (∫ x : Fin m → ℝ, φ n x = 1) ∧
        HasCompactSupport (φ n : (Fin m → ℝ) → ℂ) ∧
        tsupport (φ n : (Fin m → ℝ) → ℂ) ⊆
          {x | ∀ i : Fin m, 0 < x i} ∧
        tsupport (φ n : (Fin m → ℝ) → ℂ) ⊆
          Metric.ball (0 : Fin m → ℝ) (1 / (n + 1 : ℝ)) := by
    intro n
    simpa [φ] using
      (Classical.choose_spec
        (exists_positiveOrthant_approx_identity_schwartz
          (m := m) (1 / (n + 1 : ℝ)) (by positivity)))
  let r : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  refine ⟨φ, r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    exact (hs n).1 x
  · intro n x
    exact (hs n).2.1 x
  · intro n
    exact (hs n).2.2.1
  · intro n
    exact (hs n).2.2.2.1
  · intro n
    exact (hs n).2.2.2.2.1
  · intro n x hx
    exact (hs n).2.2.2.2.2 (subset_tsupport _ hx)
  · simpa [r, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝 0))

/-- Translating a positive-orthant compact-support test by a positive-orthant
center keeps the translated test supported in the positive orthant. -/
theorem translate_positiveOrthant_schwartz_mem
    {m : ℕ}
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (hφ_pos : tsupport (φ : (Fin m → ℝ) → ℂ) ⊆
      {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i})
    (hφ_compact : HasCompactSupport (φ : (Fin m → ℝ) → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i) :
    tsupport (SCV.translateSchwartz (-x0) φ : (Fin m → ℝ) → ℂ) ⊆
        {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i} ∧
      HasCompactSupport
        (SCV.translateSchwartz (-x0) φ : (Fin m → ℝ) → ℂ) := by
  constructor
  · intro x hx i
    have hx_pre :
        x + (-x0) ∈ tsupport (φ : (Fin m → ℝ) → ℂ) := by
      exact tsupport_comp_subset_preimage
        (φ : (Fin m → ℝ) → ℂ)
        (f := fun y : Fin m → ℝ => y + (-x0))
        (Homeomorph.addRight (-x0)).continuous hx
    have hpre : 0 < (x + (-x0)) i := hφ_pos hx_pre i
    have hx_gt : x0 i < x i := by
      simpa [Pi.add_apply, sub_eq_add_neg] using hpre
    exact lt_trans (hx0 i) hx_gt
  · simpa [SCV.translateSchwartz_apply, Function.comp_def] using
      hφ_compact.comp_homeomorph (Homeomorph.addRight (-x0))

/-- Translation rewrites pairings against a shifted finite-dimensional Schwartz
bump into the weighted shifted form used by the approximate-identity theorem. -/
theorem integral_mul_translated_schwartz_eq_integral_weighted_shift_fin
    {m : ℕ}
    (F : (Fin m → ℝ) → ℂ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (x0 : Fin m → ℝ) :
    ∫ ξ : Fin m → ℝ, F ξ * (SCV.translateSchwartz (-x0) φ) ξ =
      ∫ y : Fin m → ℝ, φ y * F (x0 + y) := by
  calc
    ∫ ξ : Fin m → ℝ, F ξ * (SCV.translateSchwartz (-x0) φ) ξ
        =
          ∫ y : Fin m → ℝ,
            (fun ξ : Fin m → ℝ =>
              F ξ * (SCV.translateSchwartz (-x0) φ) ξ) (y + x0) := by
            symm
            exact MeasureTheory.integral_add_right_eq_self
              (μ := (volume : Measure (Fin m → ℝ)))
              (f := fun ξ : Fin m → ℝ =>
                F ξ * (SCV.translateSchwartz (-x0) φ) ξ)
              x0
    _ = ∫ y : Fin m → ℝ, φ y * F (x0 + y) := by
          refine integral_congr_ae ?_
          filter_upwards with y
          rw [SCV.translateSchwartz_apply]
          simp [add_assoc, add_comm, mul_comm]

/-- Submodule-valued form of the positive-time delta family.  This is the
interface consumed by the reduced positive-time Schwinger pairing lemmas. -/
theorem exists_positiveTimeCompactSupport_delta_submodule_sequence_for_delta_bridge
    {d : ℕ} [NeZero d] :
    ∃ (ψ : ℕ → positiveTimeCompactSupportSubmodule d) (r : ℕ → ℝ),
      (∀ n x,
        0 ≤ (((ψ n : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d) x).re) ∧
      (∀ n x,
        (((ψ n : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d) x).im = 0) ∧
      (∀ n,
        ∫ x : SpacetimeDim d,
          ((ψ n : positiveTimeCompactSupportSubmodule d) :
            SchwartzSpacetime d) x = 1) ∧
      (∀ n,
        tsupport ((((ψ n : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ)) ⊆
          {x : SpacetimeDim d | 0 < x 0}) ∧
      (∀ n,
        HasCompactSupport ((((ψ n : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ))) ∧
      (∀ n,
        Function.support ((((ψ n : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ)) ⊆
          Metric.ball (0 : SpacetimeDim d) (r n)) ∧
      Tendsto r atTop (𝓝 0) := by
  obtain ⟨φ, r, hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_pos,
    hφ_support, hr⟩ :=
    exists_positiveTime_shrinking_schwartz_approx_identity_for_delta_bridge
      (d := d)
  let ψ : ℕ → positiveTimeCompactSupportSubmodule d := fun n =>
    ⟨φ n, ⟨hφ_pos n, hφ_compact n⟩⟩
  refine ⟨ψ, r, ?_, ?_, ?_, ?_, ?_, ?_, hr⟩
  · intro n x
    simpa [ψ] using hφ_nonneg n x
  · intro n x
    simpa [ψ] using hφ_real n x
  · intro n
    simpa [ψ] using hφ_int n
  · intro n
    simpa [ψ] using hφ_pos n
  · intro n
    simpa [ψ] using hφ_compact n
  · intro n
    simpa [ψ] using hφ_support n

/-- Translating a positive-time compact-support test by a positive-time center
keeps it in the positive-time compact-support submodule. -/
theorem translate_positiveTime_schwartz_mem_positiveTimeCompactSupport
    {d : ℕ}
    (φ : SchwartzSpacetime d)
    (hφ_pos : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | 0 < x 0})
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (x0 : SpacetimeDim d) (hx0 : 0 < x0 0) :
    (SCV.translateSchwartz (-x0) φ : SchwartzSpacetime d) ∈
      positiveTimeCompactSupportSubmodule d := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx_pre :
        x + (-x0) ∈ tsupport (φ : SpacetimeDim d → ℂ) := by
      exact tsupport_comp_subset_preimage
        (φ : SpacetimeDim d → ℂ)
        (f := fun y : SpacetimeDim d => y + (-x0))
        (Homeomorph.addRight (-x0)).continuous hx
    have hpre : 0 < (x + (-x0)) 0 := hφ_pos hx_pre
    have hx_gt : x0 0 < x 0 := by
      simpa [Pi.add_apply, sub_eq_add_neg] using hpre
    exact lt_trans hx0 hx_gt
  · simpa [SCV.translateSchwartz_apply, Function.comp_def] using
      hφ_compact.comp_homeomorph (Homeomorph.addRight (-x0))

/-- Translation rewrites pairings against a shifted delta bump into the
weighted shifted form used by the neutral approximate-identity theorem. -/
theorem integral_mul_translated_schwartz_eq_integral_weighted_shift
    {d : ℕ}
    (F : SpacetimeDim d → ℂ)
    (φ : SchwartzSpacetime d)
    (x0 : SpacetimeDim d) :
    ∫ ξ : SpacetimeDim d, F ξ * (SCV.translateSchwartz (-x0) φ) ξ =
      ∫ y : SpacetimeDim d, φ y * F (x0 + y) := by
  calc
    ∫ ξ : SpacetimeDim d, F ξ * (SCV.translateSchwartz (-x0) φ) ξ
        =
          ∫ y : SpacetimeDim d,
            (fun ξ : SpacetimeDim d =>
              F ξ * (SCV.translateSchwartz (-x0) φ) ξ) (y + x0) := by
            symm
            exact MeasureTheory.integral_add_right_eq_self
              (μ := (volume : Measure (SpacetimeDim d)))
              (f := fun ξ : SpacetimeDim d =>
                F ξ * (SCV.translateSchwartz (-x0) φ) ξ)
              x0
    _ = ∫ y : SpacetimeDim d, φ y * F (x0 + y) := by
          refine integral_congr_ae ?_
          filter_upwards with y
          rw [SCV.translateSchwartz_apply]
          simp [add_assoc, add_comm, mul_comm]

/-- A normalized nonnegative Schwartz approximate identity whose support
shrinks to `0` recovers a continuous value under translation. -/
theorem tendsto_integral_shrinking_schwartz_approx_identity
    {m : ℕ}
    (φ : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (r : ℕ → ℝ)
    (F : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ n x).re)
    (hφ_real : ∀ n x, (φ n x).im = 0)
    (hφ_int : ∀ n, ∫ x : Fin m → ℝ, φ n x = 1)
    (hφ_support :
      ∀ n, Function.support (φ n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (r n))
    (hr : Tendsto r atTop (𝓝 0))
    (hF_cont : ContinuousAt F x0)
    (hF_int :
      ∀ n, Integrable (fun y : Fin m → ℝ => φ n y * F (x0 + y))) :
    Tendsto
      (fun n => ∫ y : Fin m → ℝ, φ n y * F (x0 + y))
      atTop
      (𝓝 (F x0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rw [Metric.continuousAt_iff] at hF_cont
  obtain ⟨δ, hδ_pos, hδ⟩ := hF_cont (ε / 2) hε2
  have hr_small : ∀ᶠ n : ℕ in atTop, r n < δ := by
    have hdist : ∀ᶠ n : ℕ in atTop, dist (r n) 0 < δ :=
      (Metric.tendsto_nhds.mp hr) δ hδ_pos
    filter_upwards [hdist] with n hn
    rw [Real.dist_eq] at hn
    have hn' : |r n| < δ := by simpa using hn
    exact lt_of_le_of_lt (le_abs_self (r n)) hn'
  filter_upwards [hr_small] with n hn_small
  have hφ_int_norm : ∫ y : Fin m → ℝ, ‖φ n y‖ = 1 := by
    have hnorm_re : ∀ y : Fin m → ℝ, ‖φ n y‖ = (φ n y).re := by
      intro y
      rw [← Complex.re_eq_norm.mpr ⟨hφ_nonneg n y, (hφ_real n y).symm⟩]
    simp_rw [hnorm_re]
    rw [show (fun y : Fin m → ℝ => (φ n y).re) =
        (fun y : Fin m → ℝ => RCLike.re (φ n y)) from rfl]
    rw [integral_re (SchwartzMap.integrable (φ n))]
    have := congrArg Complex.re (hφ_int n)
    simpa using this
  have hconst_int :
      Integrable (fun y : Fin m → ℝ => φ n y * F x0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (SchwartzMap.integrable (φ n)).mul_const (F x0)
  have hdiff_int :
      Integrable
        (fun y : Fin m → ℝ => φ n y * (F (x0 + y) - F x0)) := by
    have hsub := (hF_int n).sub hconst_int
    refine hsub.congr ?_
    filter_upwards with y
    change
      (φ n y * F (x0 + y)) - (φ n y * F x0) =
        φ n y * (F (x0 + y) - F x0)
    ring
  have hrewrite :
      (∫ y : Fin m → ℝ, φ n y * F (x0 + y)) - F x0 =
        ∫ y : Fin m → ℝ, φ n y * (F (x0 + y) - F x0) := by
    have hconst_integral :
        ∫ y : Fin m → ℝ, φ n y * F x0 = F x0 := by
      calc
        ∫ y : Fin m → ℝ, φ n y * F x0
            = (∫ y : Fin m → ℝ, φ n y) * F x0 := by
                simpa using
                  (MeasureTheory.integral_mul_const
                    (μ := volume) (r := F x0)
                    (f := fun y : Fin m → ℝ => φ n y))
        _ = F x0 := by rw [hφ_int n, one_mul]
    calc
      (∫ y : Fin m → ℝ, φ n y * F (x0 + y)) - F x0
          =
        (∫ y : Fin m → ℝ, φ n y * F (x0 + y)) -
          (∫ y : Fin m → ℝ, φ n y * F x0) := by
            rw [hconst_integral]
      _ =
        ∫ y : Fin m → ℝ,
          (φ n y * F (x0 + y)) - (φ n y * F x0) := by
            rw [integral_sub (hF_int n) hconst_int]
      _ =
        ∫ y : Fin m → ℝ, φ n y * (F (x0 + y) - F x0) := by
            congr 1
            ext y
            ring
  have hpoint_bound :
      ∀ y : Fin m → ℝ,
        ‖φ n y * (F (x0 + y) - F x0)‖ ≤ ‖φ n y‖ * (ε / 2) := by
    intro y
    by_cases hy_zero : φ n y = 0
    · simp [hy_zero]
    · have hy_support :
          y ∈ Function.support (φ n : (Fin m → ℝ) → ℂ) := by
        simpa [Function.mem_support] using hy_zero
      have hy_ball : y ∈ Metric.ball (0 : Fin m → ℝ) (r n) :=
        hφ_support n hy_support
      have hy_norm_lt : ‖y‖ < δ := by
        have hy_dist : dist y (0 : Fin m → ℝ) < r n :=
          Metric.mem_ball.mp hy_ball
        have hy_dist' : ‖y‖ < r n := by
          simpa [dist_eq_norm] using hy_dist
        exact lt_trans hy_dist' hn_small
      have hy_dist_x : dist (x0 + y) x0 < δ := by
        rw [dist_eq_norm]
        simpa [add_sub_cancel_left] using hy_norm_lt
      have hF_close : dist (F (x0 + y)) (F x0) < ε / 2 :=
        hδ hy_dist_x
      rw [dist_eq_norm] at hF_close
      calc
        ‖φ n y * (F (x0 + y) - F x0)‖
            = ‖φ n y‖ * ‖F (x0 + y) - F x0‖ := norm_mul _ _
        _ ≤ ‖φ n y‖ * (ε / 2) := by
              exact mul_le_mul_of_nonneg_left (le_of_lt hF_close) (norm_nonneg _)
  have hnorm_integral :
      ‖∫ y : Fin m → ℝ, φ n y * (F (x0 + y) - F x0)‖ ≤ ε / 2 := by
    have hupper_int :
        Integrable (fun y : Fin m → ℝ => ‖φ n y‖ * (ε / 2)) := by
      simpa using (SchwartzMap.integrable (φ n)).norm.mul_const (ε / 2)
    calc
      ‖∫ y : Fin m → ℝ, φ n y * (F (x0 + y) - F x0)‖
          ≤ ∫ y : Fin m → ℝ, ‖φ n y * (F (x0 + y) - F x0)‖ :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ y : Fin m → ℝ, ‖φ n y‖ * (ε / 2) := by
            exact integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              hupper_int
              (Filter.Eventually.of_forall hpoint_bound)
      _ = (∫ y : Fin m → ℝ, ‖φ n y‖) * (ε / 2) := by
            rw [integral_mul_const]
      _ = ε / 2 := by rw [hφ_int_norm, one_mul]
  rw [dist_eq_norm]
  calc
    ‖(∫ y : Fin m → ℝ, φ n y * F (x0 + y)) - F x0‖
        = ‖∫ y : Fin m → ℝ, φ n y * (F (x0 + y) - F x0)‖ := by
            rw [hrewrite]
    _ ≤ ε / 2 := hnorm_integral
    _ < ε := by linarith

/-- If two continuous scalar real-edge candidates have the same smearings
against every member of a shrinking normalized Schwartz approximate identity,
then they have the same value at the center point. -/
theorem eq_of_equal_shrinking_schwartz_approx_identity_integrals
    {m : ℕ}
    (φ : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (r : ℕ → ℝ)
    (F G : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ n x).re)
    (hφ_real : ∀ n x, (φ n x).im = 0)
    (hφ_int : ∀ n, ∫ x : Fin m → ℝ, φ n x = 1)
    (hφ_support :
      ∀ n, Function.support (φ n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (r n))
    (hr : Tendsto r atTop (𝓝 0))
    (hF_cont : ContinuousAt F x0)
    (hG_cont : ContinuousAt G x0)
    (hF_int :
      ∀ n, Integrable (fun y : Fin m → ℝ => φ n y * F (x0 + y)))
    (hG_int :
      ∀ n, Integrable (fun y : Fin m → ℝ => φ n y * G (x0 + y)))
    (hsmear :
      ∀ n,
        (∫ y : Fin m → ℝ, φ n y * F (x0 + y)) =
          ∫ y : Fin m → ℝ, φ n y * G (x0 + y)) :
    F x0 = G x0 := by
  have hF_tendsto :
      Tendsto
        (fun n => ∫ y : Fin m → ℝ, φ n y * F (x0 + y))
        atTop
        (𝓝 (F x0)) :=
    tendsto_integral_shrinking_schwartz_approx_identity
      φ r F x0 hφ_nonneg hφ_real hφ_int hφ_support hr hF_cont hF_int
  have hG_tendsto :
      Tendsto
        (fun n => ∫ y : Fin m → ℝ, φ n y * G (x0 + y))
        atTop
        (𝓝 (G x0)) :=
    tendsto_integral_shrinking_schwartz_approx_identity
      φ r G x0 hφ_nonneg hφ_real hφ_int hφ_support hr hG_cont hG_int
  have hF_as_G :
      Tendsto
        (fun n => ∫ y : Fin m → ℝ, φ n y * G (x0 + y))
        atTop
        (𝓝 (F x0)) := by
    simpa [hsmear] using hF_tendsto
  exact tendsto_nhds_unique hF_as_G hG_tendsto

/-- Eventual form of the delta-smearing uniqueness step.  This is the version
needed after translating a shrinking positive-time delta family to a fixed
positive-time center: the translated tests lie in the positive-time submodule
for all sufficiently large sequence indices, not necessarily for the finitely
many early ones. -/
theorem eq_of_eventually_equal_shrinking_schwartz_approx_identity_integrals
    {m : ℕ}
    (φ : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (r : ℕ → ℝ)
    (F G : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ n x).re)
    (hφ_real : ∀ n x, (φ n x).im = 0)
    (hφ_int : ∀ n, ∫ x : Fin m → ℝ, φ n x = 1)
    (hφ_support :
      ∀ n, Function.support (φ n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (r n))
    (hr : Tendsto r atTop (𝓝 0))
    (hF_cont : ContinuousAt F x0)
    (hG_cont : ContinuousAt G x0)
    (hF_int :
      ∀ n, Integrable (fun y : Fin m → ℝ => φ n y * F (x0 + y)))
    (hG_int :
      ∀ n, Integrable (fun y : Fin m → ℝ => φ n y * G (x0 + y)))
    (hsmear :
      (fun n =>
        ∫ y : Fin m → ℝ, φ n y * F (x0 + y)) =ᶠ[atTop]
        fun n =>
          ∫ y : Fin m → ℝ, φ n y * G (x0 + y)) :
    F x0 = G x0 := by
  have hF_tendsto :
      Tendsto
        (fun n => ∫ y : Fin m → ℝ, φ n y * F (x0 + y))
        atTop
        (𝓝 (F x0)) :=
    tendsto_integral_shrinking_schwartz_approx_identity
      φ r F x0 hφ_nonneg hφ_real hφ_int hφ_support hr hF_cont hF_int
  have hG_tendsto :
      Tendsto
        (fun n => ∫ y : Fin m → ℝ, φ n y * G (x0 + y))
        atTop
        (𝓝 (G x0)) :=
    tendsto_integral_shrinking_schwartz_approx_identity
      φ r G x0 hφ_nonneg hφ_real hφ_int hφ_support hr hG_cont hG_int
  have hF_as_G :
      Tendsto
        (fun n => ∫ y : Fin m → ℝ, φ n y * G (x0 + y))
        atTop
        (𝓝 (F x0)) :=
    Filter.Tendsto.congr' hsmear hF_tendsto
  exact tendsto_nhds_unique hF_as_G hG_tendsto

/-- Finite positive-orthant analogue of
`eq_of_equal_positiveTime_translated_delta_smearings`: equality on the
translated members of a shrinking approximate identity already suffices for
pointwise equality at the center. -/
theorem eq_of_equal_positiveOrthant_translated_delta_smearings
    {m : ℕ}
    (φ : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (r : ℕ → ℝ)
    (F G : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ n x).re)
    (hφ_real : ∀ n x, (φ n x).im = 0)
    (hφ_int : ∀ n, ∫ x : Fin m → ℝ, φ n x = 1)
    (hφ_support :
      ∀ n, Function.support (φ n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (r n))
    (hr : Tendsto r atTop (𝓝 0))
    (hF_cont : ContinuousAt F x0)
    (hG_cont : ContinuousAt G x0)
    (hF_int :
      ∀ n, Integrable (fun y : Fin m → ℝ => φ n y * F (x0 + y)))
    (hG_int :
      ∀ n, Integrable (fun y : Fin m → ℝ => φ n y * G (x0 + y)))
    (hsmear :
      ∀ n,
        (∫ ξ : Fin m → ℝ,
          F ξ * (SCV.translateSchwartz (-x0) (φ n)) ξ) =
          ∫ ξ : Fin m → ℝ,
            G ξ * (SCV.translateSchwartz (-x0) (φ n)) ξ) :
    F x0 = G x0 := by
  exact
    eq_of_equal_shrinking_schwartz_approx_identity_integrals
      φ r F G x0
      hφ_nonneg hφ_real hφ_int hφ_support hr hF_cont hG_cont
      hF_int hG_int
      (fun n => by
        calc
          ∫ y : Fin m → ℝ, φ n y * F (x0 + y)
              =
                ∫ ξ : Fin m → ℝ,
                  F ξ * (SCV.translateSchwartz (-x0) (φ n)) ξ := by
                  exact
                    (integral_mul_translated_schwartz_eq_integral_weighted_shift_fin
                      (m := m) F (φ n) x0).symm
          _ =
                ∫ ξ : Fin m → ℝ,
                  G ξ * (SCV.translateSchwartz (-x0) (φ n)) ξ :=
                  hsmear n
          _ =
                ∫ y : Fin m → ℝ, φ n y * G (x0 + y) := by
                  exact
                    integral_mul_translated_schwartz_eq_integral_weighted_shift_fin
                      (m := m) G (φ n) x0)

/-- Positive-orthant version of the OS-II delta-smearing pointwise recovery:
if two continuous scalar real-edge candidates have the same distributional
pairing against every compactly supported Schwartz test in the positive orthant,
then they agree at each positive-orthant center. -/
theorem eq_of_positiveOrthant_distribution_eq_on_translated_delta_family
    {m : ℕ}
    (φ : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (r : ℕ → ℝ)
    (F G : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ n x).re)
    (hφ_real : ∀ n x, (φ n x).im = 0)
    (hφ_int : ∀ n, ∫ x : Fin m → ℝ, φ n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ n : (Fin m → ℝ) → ℂ))
    (hφ_pos : ∀ n, tsupport (φ n : (Fin m → ℝ) → ℂ) ⊆
      {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i})
    (hφ_support :
      ∀ n, Function.support (φ n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (r n))
    (hr : Tendsto r atTop (𝓝 0))
    (hF_cont : ContinuousAt F x0)
    (hG_cont : ContinuousAt G x0)
    (hF_int :
      ∀ n, Integrable (fun y : Fin m → ℝ => φ n y * F (x0 + y)))
    (hG_int :
      ∀ n, Integrable (fun y : Fin m → ℝ => φ n y * G (x0 + y)))
    (hpair :
      ∀ h : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (h : (Fin m → ℝ) → ℂ) →
        tsupport (h : (Fin m → ℝ) → ℂ) ⊆
          {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i} →
        (∫ ξ : Fin m → ℝ, F ξ * h ξ) =
          ∫ ξ : Fin m → ℝ, G ξ * h ξ) :
    F x0 = G x0 := by
  exact
    eq_of_equal_shrinking_schwartz_approx_identity_integrals
      φ r F G x0 hφ_nonneg hφ_real hφ_int hφ_support hr hF_cont hG_cont
      hF_int hG_int
      (fun n => by
        let hδ : SchwartzMap (Fin m → ℝ) ℂ := SCV.translateSchwartz (-x0) (φ n)
        have hδ_mem := translate_positiveOrthant_schwartz_mem
          (m := m) (φ n) (hφ_pos n) (hφ_compact n) x0 hx0
        calc
          ∫ y : Fin m → ℝ, φ n y * F (x0 + y)
              =
                ∫ ξ : Fin m → ℝ, F ξ * hδ ξ := by
                  exact
                    (integral_mul_translated_schwartz_eq_integral_weighted_shift_fin
                      (m := m) F (φ n) x0).symm
          _ =
                ∫ ξ : Fin m → ℝ, G ξ * hδ ξ :=
                  hpair hδ hδ_mem.2 hδ_mem.1
          _ =
                ∫ y : Fin m → ℝ, φ n y * G (x0 + y) := by
                  exact integral_mul_translated_schwartz_eq_integral_weighted_shift_fin
                    (m := m) G (φ n) x0)

/-- Closed positive-orthant pointwise recovery: the shrinking delta family is
chosen internally from the checked compactly supported Schwartz construction. -/
theorem eq_of_positiveOrthant_distribution_eq
    {m : ℕ}
    (F G : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (hF_cont : ContinuousAt F x0)
    (hG_cont : ContinuousAt G x0)
    (hF_int :
      ∀ h : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (h : (Fin m → ℝ) → ℂ) →
        tsupport (h : (Fin m → ℝ) → ℂ) ⊆
          {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i} →
        Integrable (fun y : Fin m → ℝ => h y * F (x0 + y)))
    (hG_int :
      ∀ h : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (h : (Fin m → ℝ) → ℂ) →
        tsupport (h : (Fin m → ℝ) → ℂ) ⊆
          {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i} →
        Integrable (fun y : Fin m → ℝ => h y * G (x0 + y)))
    (hpair :
      ∀ h : SchwartzMap (Fin m → ℝ) ℂ,
        HasCompactSupport (h : (Fin m → ℝ) → ℂ) →
        tsupport (h : (Fin m → ℝ) → ℂ) ⊆
          {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i} →
        (∫ ξ : Fin m → ℝ, F ξ * h ξ) =
          ∫ ξ : Fin m → ℝ, G ξ * h ξ) :
    F x0 = G x0 := by
  obtain ⟨φ, r, hφ_nonneg, hφ_real, hφ_int, hφ_compact, hφ_pos,
    hφ_support, hr⟩ :=
    exists_positiveOrthant_shrinking_schwartz_approx_identity_for_delta_bridge m
  exact
    eq_of_positiveOrthant_distribution_eq_on_translated_delta_family
      φ r F G x0 hx0 hφ_nonneg hφ_real hφ_int hφ_compact hφ_pos hφ_support
      hr hF_cont hG_cont
      (fun n => hF_int (φ n) (hφ_compact n) (hφ_pos n))
      (fun n => hG_int (φ n) (hφ_compact n) (hφ_pos n))
      hpair

/-- A compactly supported Schwartz test whose support lies in the positive
orthant gives an integrable shifted pairing against any scalar branch that is
continuous on the positive orthant. -/
theorem integrable_positiveOrthant_schwartz_mul_continuousOn_shift
    {m : ℕ}
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (F : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ)
    (hx0 : ∀ i : Fin m, 0 < x0 i)
    (hh_compact : HasCompactSupport (h : (Fin m → ℝ) → ℂ))
    (hh_pos : tsupport (h : (Fin m → ℝ) → ℂ) ⊆
      {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i})
    (hF_cont : ContinuousOn F {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i}) :
    Integrable (fun y : Fin m → ℝ => h y * F (x0 + y)) := by
  let K : Set (Fin m → ℝ) := tsupport (h : (Fin m → ℝ) → ℂ)
  let f : (Fin m → ℝ) → ℂ := fun y => h y * F (x0 + y)
  have hK_compact : IsCompact K := hh_compact
  have hmaps :
      Set.MapsTo (fun y : Fin m → ℝ => x0 + y) K
        {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i} := by
    intro y hy i
    exact add_pos (hx0 i) ((hh_pos hy) i)
  have hshift_cont :
      ContinuousOn (fun y : Fin m → ℝ => F (x0 + y)) K := by
    exact hF_cont.comp
      ((continuous_const.add continuous_id).continuousOn) hmaps
  have hf_cont : ContinuousOn f K := by
    exact (SchwartzMap.continuous h).continuousOn.mul hshift_cont
  have hf_integrableOn : IntegrableOn f K :=
    hf_cont.integrableOn_compact hK_compact
  have hindicator_integrable : Integrable (K.indicator f) := by
    rw [integrable_indicator_iff hK_compact.measurableSet]
    exact hf_integrableOn
  have hindicator_eq : K.indicator f = f := by
    funext y
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy]
    · have hzero : h y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [Set.indicator_of_notMem hy, f, hzero]
  simpa [hindicator_eq, f] using hindicator_integrable

/-- Pointwise recovery from equality of translated positive-time delta
smearings.  This is the distribution-to-pointwise limit step used after the
OS pairing identity has been tested on the translated bumps. -/
theorem eq_of_equal_positiveTime_translated_delta_smearings
    {d : ℕ}
    (φ : ℕ → SchwartzSpacetime d)
    (r : ℕ → ℝ)
    (F G : SpacetimeDim d → ℂ)
    (x0 : SpacetimeDim d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ n x).re)
    (hφ_real : ∀ n x, (φ n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ n x = 1)
    (hφ_support :
      ∀ n, Function.support (φ n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (r n))
    (hr : Tendsto r atTop (𝓝 0))
    (hF_cont : ContinuousAt F x0)
    (hG_cont : ContinuousAt G x0)
    (hF_int :
      ∀ n, Integrable (fun y : SpacetimeDim d => φ n y * F (x0 + y)))
    (hG_int :
      ∀ n, Integrable (fun y : SpacetimeDim d => φ n y * G (x0 + y)))
    (hsmear :
      ∀ n,
        (∫ ξ : SpacetimeDim d, F ξ * (SCV.translateSchwartz (-x0) (φ n)) ξ) =
          ∫ ξ : SpacetimeDim d, G ξ * (SCV.translateSchwartz (-x0) (φ n)) ξ) :
    F x0 = G x0 := by
  exact
    eq_of_equal_shrinking_schwartz_approx_identity_integrals
      (m := d + 1) φ r F G x0
      hφ_nonneg hφ_real hφ_int hφ_support hr hF_cont hG_cont
      hF_int hG_int
      (fun n => by
        calc
          ∫ y : SpacetimeDim d, φ n y * F (x0 + y)
              =
                ∫ ξ : SpacetimeDim d,
                  F ξ * (SCV.translateSchwartz (-x0) (φ n)) ξ := by
                  exact (integral_mul_translated_schwartz_eq_integral_weighted_shift
                    (d := d) F (φ n) x0).symm
          _ =
                ∫ ξ : SpacetimeDim d,
                  G ξ * (SCV.translateSchwartz (-x0) (φ n)) ξ :=
                  hsmear n
          _ =
                ∫ y : SpacetimeDim d, φ n y * G (x0 + y) := by
                  exact integral_mul_translated_schwartz_eq_integral_weighted_shift
                    (d := d) G (φ n) x0)

/-- If two scalar functions have the same distributional pairing against every
positive-time compact-support test, then any positive-time translated delta
family upgrades that pairing identity to pointwise equality at the center. -/
theorem eq_of_positiveTime_distribution_eq_on_translated_delta_family
    {d : ℕ}
    (φ : ℕ → SchwartzSpacetime d)
    (r : ℕ → ℝ)
    (F G : SpacetimeDim d → ℂ)
    (x0 : SpacetimeDim d) (hx0 : 0 < x0 0)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ n x).re)
    (hφ_real : ∀ n x, (φ n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ n : SpacetimeDim d → ℂ))
    (hφ_pos : ∀ n, tsupport (φ n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | 0 < x 0})
    (hφ_support :
      ∀ n, Function.support (φ n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (r n))
    (hr : Tendsto r atTop (𝓝 0))
    (hF_cont : ContinuousAt F x0)
    (hG_cont : ContinuousAt G x0)
    (hF_int :
      ∀ n, Integrable (fun y : SpacetimeDim d => φ n y * F (x0 + y)))
    (hG_int :
      ∀ n, Integrable (fun y : SpacetimeDim d => φ n y * G (x0 + y)))
    (hpair :
      ∀ h : positiveTimeCompactSupportSubmodule d,
        (∫ ξ : SpacetimeDim d,
          F ξ * ((h : positiveTimeCompactSupportSubmodule d) :
            SchwartzSpacetime d) ξ) =
          ∫ ξ : SpacetimeDim d,
            G ξ * ((h : positiveTimeCompactSupportSubmodule d) :
              SchwartzSpacetime d) ξ) :
    F x0 = G x0 := by
  exact
    eq_of_equal_positiveTime_translated_delta_smearings
      (d := d) φ r F G x0
      hφ_nonneg hφ_real hφ_int hφ_support hr
      hF_cont hG_cont hF_int hG_int
      (fun n => by
        let hδ : positiveTimeCompactSupportSubmodule d :=
          ⟨SCV.translateSchwartz (-x0) (φ n),
            translate_positiveTime_schwartz_mem_positiveTimeCompactSupport
              (d := d) (φ n) (hφ_pos n) (hφ_compact n) x0 hx0⟩
        simpa [hδ] using hpair hδ)

/-- Fixed-probe pointwise OS-II real-edge recovery from positive-time delta
smearing.

The fixed-probe pairing theorem identifies the Bochner Laplace-Fourier kernel
with the translated product-shell Schwinger scalar as distributions on
positive-time compact-support tests.  The translated delta bridge upgrades that
identity to a pointwise equality at any positive-time center. -/
theorem fixed_probe_laplaceFourier_eq_translatedProductShell_of_delta_bridge
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzSpacetime d)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hμ_repr : ∀ (t : ℝ) (a : Fin d → ℝ), 0 < t →
      osSemigroupGroupMatrixElement (d := d) OS lgc
        (((show OSPreHilbertSpace OS from
          ⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d φ : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) φ hφ_compact hφ_neg)⟧) : OSHilbertSpace OS))
        t a =
          ∫ p : ℝ × (Fin d → ℝ),
            Complex.exp (-(↑(t * p.1) : ℂ)) *
              Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ)
    (ψδ : ℕ → SchwartzSpacetime d)
    (r : ℕ → ℝ)
    (x0 : SpacetimeDim d) (hx0 : 0 < x0 0)
    (hψδ_nonneg : ∀ n x, 0 ≤ (ψδ n x).re)
    (hψδ_real : ∀ n x, (ψδ n x).im = 0)
    (hψδ_int : ∀ n, ∫ x : SpacetimeDim d, ψδ n x = 1)
    (hψδ_compact : ∀ n, HasCompactSupport (ψδ n : SpacetimeDim d → ℂ))
    (hψδ_pos : ∀ n, tsupport (ψδ n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | 0 < x 0})
    (hψδ_support :
      ∀ n, Function.support (ψδ n : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (r n))
    (hr : Tendsto r atTop (𝓝 0))
    (hLF_cont : ContinuousAt (laplaceFourierKernel (d := d) μ) x0)
    (hTPS_cont : ContinuousAt
      (fun ξ : SpacetimeDim d =>
        if 0 < ξ 0 then
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical
            (twoPointProductLift φ
              (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
        else 0) x0)
    (hLF_int :
      ∀ n, Integrable (fun y : SpacetimeDim d =>
        ψδ n y * laplaceFourierKernel (d := d) μ (x0 + y)))
    (hTPS_int :
      ∀ n, Integrable (fun y : SpacetimeDim d =>
        ψδ n y *
          (if 0 < (x0 + y) 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift φ
                (SCV.translateSchwartz (-(x0 + y))
                  (reflectedSchwartzSpacetime φ))))
          else 0))) :
    laplaceFourierKernel (d := d) μ x0 =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          (SCV.translateSchwartz (-x0) (reflectedSchwartzSpacetime φ)))) := by
  let TPS : SpacetimeDim d → ℂ := fun ξ =>
    if 0 < ξ 0 then
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime φ))))
    else 0
  have hpoint :
      laplaceFourierKernel (d := d) μ x0 = TPS x0 := by
    exact
      eq_of_positiveTime_distribution_eq_on_translated_delta_family
        (d := d) ψδ r
        (laplaceFourierKernel (d := d) μ) TPS
        x0 hx0 hψδ_nonneg hψδ_real hψδ_int hψδ_compact hψδ_pos
        hψδ_support hr hLF_cont hTPS_cont hLF_int hTPS_int
        (fun h => by
          simpa [TPS] using
            integral_laplaceFourierKernel_mul_eq_translatedProductShell_integral_local
              (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμ_repr h)
  simpa [TPS, hx0] using hpoint

end OSReconstruction
