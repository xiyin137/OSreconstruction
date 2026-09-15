/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIDeltaSmearing















noncomputable section

open Complex Topology MeasureTheory Filter
open scoped Classical BigOperators

namespace OSReconstruction
namespace OSIIChapterV

/-- A normalized shrinking Schwartz family recovers a parameterized kernel
uniformly on `K` whenever the kernel is uniformly continuous in the shrinking
coordinate there.

This is the scalar convergence principle needed for locally uniform
delta-source Hilbert fields. The parameter may be complex; only the
finite-dimensional integration variable is required to shrink. -/
theorem tendstoUniformlyOn_integral_shrinking_schwartz_approx_identity
    {ι P : Type*} {m : ℕ}
    [PseudoMetricSpace P]
    (l : Filter ι)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (ρ : ι → ℝ)
    (F : P → (Fin m → ℝ) → ℂ)
    (x0 : P → (Fin m → ℝ))
    (K : Set P)
    (hψ_nonneg : ∀ i x, 0 ≤ (ψ i x).re)
    (hψ_real : ∀ i x, (ψ i x).im = 0)
    (hψ_int : ∀ i, ∫ x : Fin m → ℝ, ψ i x = 1)
    (hψ_support :
      ∀ i, Function.support (ψ i : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (ρ i))
    (hρ : Tendsto ρ l (𝓝 0))
    (hF_uniform :
      ∀ ε > 0, ∃ δ > 0,
        ∀ p ∈ K, ∀ y : Fin m → ℝ, ‖y‖ < δ →
          dist (F p (x0 p + y)) (F p (x0 p)) < ε)
    (hF_int :
      ∀ i p, p ∈ K →
        Integrable
          (fun y : Fin m → ℝ =>
            ψ i y * F p (x0 p + y))) :
    TendstoUniformlyOn
      (fun i p =>
        ∫ y : Fin m → ℝ, ψ i y * F p (x0 p + y))
      (fun p => F p (x0 p)) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δ, hδ_pos, hδ⟩ := hF_uniform (ε / 2) hε2
  have hρ_small : ∀ᶠ i in l, ρ i < δ := by
    have hdist : ∀ᶠ i in l, dist (ρ i) 0 < δ :=
      (Metric.tendsto_nhds.mp hρ) δ hδ_pos
    filter_upwards [hdist] with i hi
    rw [Real.dist_eq] at hi
    exact lt_of_le_of_lt (le_abs_self (ρ i)) (by simpa using hi)
  filter_upwards [hρ_small] with i hi
  intro p hp
  have hψ_int_norm :
      ∫ y : Fin m → ℝ, ‖ψ i y‖ = 1 := by
    exact
      integral_norm_eq_one_of_nonnegative_real_schwartz
        (ψ i) (hψ_nonneg i) (hψ_real i) (hψ_int i)
  have hconst_int :
      Integrable
        (fun y : Fin m → ℝ => ψ i y * F p (x0 p)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (SchwartzMap.integrable (ψ i)).mul_const (F p (x0 p))
  have hdiff_int :
      Integrable
        (fun y : Fin m → ℝ =>
          ψ i y * (F p (x0 p + y) - F p (x0 p))) := by
    have hmain := hF_int i p hp
    have hsub := hmain.sub hconst_int
    exact hsub.congr (Filter.Eventually.of_forall (fun y => by simp [mul_sub]))
  have hrewrite :
      (∫ y : Fin m → ℝ, ψ i y * F p (x0 p + y)) - F p (x0 p) =
        ∫ y : Fin m → ℝ,
          ψ i y * (F p (x0 p + y) - F p (x0 p)) := by
    have hconst_integral :
        ∫ y : Fin m → ℝ, ψ i y * F p (x0 p) = F p (x0 p) := by
      calc
        ∫ y : Fin m → ℝ, ψ i y * F p (x0 p)
            = (∫ y : Fin m → ℝ, ψ i y) * F p (x0 p) := by
                simpa using
                  (MeasureTheory.integral_mul_const
                    (μ := volume) (r := F p (x0 p))
                    (f := fun y : Fin m → ℝ => ψ i y))
        _ = F p (x0 p) := by rw [hψ_int i, one_mul]
    calc
      (∫ y : Fin m → ℝ, ψ i y * F p (x0 p + y)) - F p (x0 p)
          =
        (∫ y : Fin m → ℝ, ψ i y * F p (x0 p + y)) -
          (∫ y : Fin m → ℝ, ψ i y * F p (x0 p)) := by
            rw [hconst_integral]
      _ =
        ∫ y : Fin m → ℝ,
          (ψ i y * F p (x0 p + y)) -
            (ψ i y * F p (x0 p)) := by
            rw [integral_sub (hF_int i p hp) hconst_int]
      _ =
        ∫ y : Fin m → ℝ,
          ψ i y * (F p (x0 p + y) - F p (x0 p)) := by
            congr 1
            ext y
            ring
  have hpoint_bound :
      ∀ y : Fin m → ℝ,
        ‖ψ i y * (F p (x0 p + y) - F p (x0 p))‖ ≤
          ‖ψ i y‖ * (ε / 2) := by
    intro y
    by_cases hy_zero : ψ i y = 0
    · simp [hy_zero]
    · have hy_support :
          y ∈ Function.support (ψ i : (Fin m → ℝ) → ℂ) := by
        simpa [Function.mem_support] using hy_zero
      have hy_ball := hψ_support i hy_support
      have hy_norm_lt : ‖y‖ < δ := by
        have hy_dist : dist y (0 : Fin m → ℝ) < ρ i :=
          Metric.mem_ball.mp hy_ball
        have hy_dist' : ‖y‖ < ρ i := by
          simpa [dist_eq_norm] using hy_dist
        exact lt_trans hy_dist' hi
      have hF_close :
          dist (F p (x0 p + y)) (F p (x0 p)) < ε / 2 :=
        hδ p hp y hy_norm_lt
      rw [dist_eq_norm] at hF_close
      calc
        ‖ψ i y * (F p (x0 p + y) - F p (x0 p))‖
            = ‖ψ i y‖ * ‖F p (x0 p + y) - F p (x0 p)‖ :=
                norm_mul _ _
        _ ≤ ‖ψ i y‖ * (ε / 2) := by
              exact mul_le_mul_of_nonneg_left
                (le_of_lt hF_close) (norm_nonneg _)
  have hnorm_integral :
      ‖∫ y : Fin m → ℝ,
          ψ i y * (F p (x0 p + y) - F p (x0 p))‖ ≤ ε / 2 := by
    have hupper_int :
        Integrable
          (fun y : Fin m → ℝ => ‖ψ i y‖ * (ε / 2)) := by
      simpa using
        (SchwartzMap.integrable (ψ i)).norm.mul_const (ε / 2)
    calc
      ‖∫ y : Fin m → ℝ,
          ψ i y * (F p (x0 p + y) - F p (x0 p))‖
          ≤ ∫ y : Fin m → ℝ,
              ‖ψ i y * (F p (x0 p + y) - F p (x0 p))‖ :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ y : Fin m → ℝ, ‖ψ i y‖ * (ε / 2) := by
            exact integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              hupper_int
              (Filter.Eventually.of_forall hpoint_bound)
      _ = (∫ y : Fin m → ℝ, ‖ψ i y‖) * (ε / 2) := by
            rw [integral_mul_const]
      _ = ε / 2 := by rw [hψ_int_norm, one_mul]
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖(∫ y : Fin m → ℝ, ψ i y * F p (x0 p + y)) - F p (x0 p)‖
        =
      ‖∫ y : Fin m → ℝ,
          ψ i y * (F p (x0 p + y) - F p (x0 p))‖ := by
        rw [hrewrite]
    _ ≤ ε / 2 := hnorm_integral
    _ < ε := by linarith

/-- Joint continuity on a compact parameter set and one fixed closed ball
supplies the uniform kernel hypothesis in
`tendstoUniformlyOn_integral_shrinking_schwartz_approx_identity`. -/
theorem tendstoUniformlyOn_integral_shrinking_schwartz_approx_identity_of_compact
    {ι P : Type*} {m : ℕ}
    [PseudoMetricSpace P]
    (l : Filter ι)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (ρ : ι → ℝ)
    (F : P → (Fin m → ℝ) → ℂ)
    (x0 : P → (Fin m → ℝ))
    (K : Set P)
    (hK : IsCompact K)
    (R : ℝ)
    (hR : 0 < R)
    (hψ_nonneg : ∀ i x, 0 ≤ (ψ i x).re)
    (hψ_real : ∀ i x, (ψ i x).im = 0)
    (hψ_int : ∀ i, ∫ x : Fin m → ℝ, ψ i x = 1)
    (hψ_support :
      ∀ i, Function.support (ψ i : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (ρ i))
    (hρ : Tendsto ρ l (𝓝 0))
    (hF_cont :
      ContinuousOn
        (Function.uncurry fun p y => F p (x0 p + y))
        (K ×ˢ Metric.closedBall (0 : Fin m → ℝ) R))
    (hF_int :
      ∀ i p, p ∈ K →
        Integrable
          (fun y : Fin m → ℝ =>
            ψ i y * F p (x0 p + y))) :
    TendstoUniformlyOn
      (fun i p =>
        ∫ y : Fin m → ℝ, ψ i y * F p (x0 p + y))
      (fun p => F p (x0 p)) l K := by
  let G : P × (Fin m → ℝ) → ℂ :=
    Function.uncurry fun p y => F p (x0 p + y)
  have hcompact :
      IsCompact (K ×ˢ Metric.closedBall (0 : Fin m → ℝ) R) :=
    hK.prod (isCompact_closedBall (0 : Fin m → ℝ) R)
  have hG_uniform :
      UniformContinuousOn G
        (K ×ˢ Metric.closedBall (0 : Fin m → ℝ) R) :=
    hcompact.uniformContinuousOn_of_continuous (by simpa [G] using hF_cont)
  have hF_uniform :
      ∀ ε > 0, ∃ δ > 0,
        ∀ p ∈ K, ∀ y : Fin m → ℝ, ‖y‖ < δ →
          dist (F p (x0 p + y)) (F p (x0 p)) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hGδ⟩ :=
      Metric.uniformContinuousOn_iff.mp hG_uniform ε hε
    refine ⟨min δ R, lt_min hδ hR, ?_⟩
    intro p hp y hy
    have hyδ : ‖y‖ < δ := hy.trans_le (min_le_left _ _)
    have hyR : ‖y‖ < R := hy.trans_le (min_le_right _ _)
    have hy_ball :
        y ∈ Metric.closedBall (0 : Fin m → ℝ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hyR
    have hzero_ball :
        (0 : Fin m → ℝ) ∈ Metric.closedBall (0 : Fin m → ℝ) R := by
      simp [hR.le]
    have hpair_dist :
        dist (p, y) (p, (0 : Fin m → ℝ)) < δ := by
      simpa [Prod.dist_eq, dist_zero_right] using hyδ
    simpa [G] using
      hGδ (p, y) ⟨hp, hy_ball⟩
        (p, (0 : Fin m → ℝ)) ⟨hp, hzero_ball⟩ hpair_dist
  exact
    tendstoUniformlyOn_integral_shrinking_schwartz_approx_identity
      l ψ ρ F x0 K hψ_nonneg hψ_real hψ_int hψ_support hρ
      hF_uniform hF_int

/-- Compact-parameter uniform version of the two-family tensor-delta theorem.

This is the direct scalar input for
`LocallyUniformPairwiseInnerLimitData`: the parameter is the complex
Hilbert-field coordinate, while the two natural-number indices are the
independently shrinking reflected-left and right source scales. -/
theorem
    tendstoUniformlyOn_integral_tensorPair_shrinking_schwartz_approx_identities_of_compact
    {P : Type*} [PseudoMetricSpace P]
    {m : ℕ}
    (φLeft φRight : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (rLeft rRight : ℕ → ℝ)
    (F : P → (Fin (m + m) → ℝ) → ℂ)
    (x0 : P → (Fin (m + m) → ℝ))
    (K : Set P)
    (hK : IsCompact K)
    (R : ℝ)
    (hR : 0 < R)
    (hLeft_nonneg : ∀ n x, 0 ≤ (φLeft n x).re)
    (hRight_nonneg : ∀ n x, 0 ≤ (φRight n x).re)
    (hLeft_real : ∀ n x, (φLeft n x).im = 0)
    (hRight_real : ∀ n x, (φRight n x).im = 0)
    (hLeft_int : ∀ n, ∫ x : Fin m → ℝ, φLeft n x = 1)
    (hRight_int : ∀ n, ∫ x : Fin m → ℝ, φRight n x = 1)
    (hLeft_support :
      ∀ n, Function.support (φLeft n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (rLeft n))
    (hRight_support :
      ∀ n, Function.support (φRight n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (rRight n))
    (hrLeft : Tendsto rLeft atTop (𝓝 0))
    (hrRight : Tendsto rRight atTop (𝓝 0))
    (hF_cont :
      ContinuousOn
        (Function.uncurry fun p y => F p (x0 p + y))
        (K ×ˢ Metric.closedBall (0 : Fin (m + m) → ℝ) R))
    (hF_int :
      ∀ (pq : ℕ × ℕ) p, p ∈ K →
        Integrable
          (fun y : Fin (m + m) → ℝ =>
            ((φLeft pq.1).tensorProduct (φRight pq.2)) y *
              F p (x0 p + y))) :
    TendstoUniformlyOn
      (fun (pq : ℕ × ℕ) p =>
        ∫ y : Fin (m + m) → ℝ,
          ((φLeft pq.1).tensorProduct (φRight pq.2)) y *
            F p (x0 p + y))
      (fun p => F p (x0 p)) atTop K := by
  let ψ : (ℕ × ℕ) → SchwartzMap (Fin (m + m) → ℝ) ℂ :=
    fun pq => (φLeft pq.1).tensorProduct (φRight pq.2)
  let ρ : (ℕ × ℕ) → ℝ := fun pq => rLeft pq.1 + rRight pq.2
  have hψ_nonneg :
      ∀ pq z, 0 ≤ (ψ pq z).re := by
    intro pq z
    rw [show ψ pq z =
      φLeft pq.1 (splitFirst m m z) *
        φRight pq.2 (splitLast m m z) by rfl]
    rw [Complex.mul_re, hLeft_real, hRight_real]
    simp only [mul_zero, sub_zero]
    exact mul_nonneg (hLeft_nonneg _ _) (hRight_nonneg _ _)
  have hψ_real :
      ∀ pq z, (ψ pq z).im = 0 := by
    intro pq z
    rw [show ψ pq z =
      φLeft pq.1 (splitFirst m m z) *
        φRight pq.2 (splitLast m m z) by rfl]
    rw [Complex.mul_im, hLeft_real, hRight_real]
    ring
  have hψ_int :
      ∀ pq, ∫ z : Fin (m + m) → ℝ, ψ pq z = 1 := by
    intro pq
    change
      (SchwartzMap.integralCLM ℂ
        (volume : Measure (Fin (m + m) → ℝ))) (ψ pq) = 1
    rw [← integral_integrateHeadBlock (m := m) (n := m) (ψ pq)]
    rw [show ψ pq =
      (φLeft pq.1).tensorProduct (φRight pq.2) by rfl]
    rw [integrateHeadBlock_tensorProduct]
    have hleft :
        (SchwartzMap.integralCLM ℂ
          (volume : Measure (Fin m → ℝ))) (φLeft pq.1) = 1 := by
      simpa only [SchwartzMap.integralCLM_apply] using hLeft_int pq.1
    rw [hleft, one_smul]
    simpa only [SchwartzMap.integralCLM_apply] using hRight_int pq.2
  have hψ_support :
      ∀ pq,
        Function.support (ψ pq : (Fin (m + m) → ℝ) → ℂ) ⊆
          Metric.ball (0 : Fin (m + m) → ℝ) (ρ pq) := by
    intro pq z hz
    have hz_mul :
        φLeft pq.1 (splitFirst m m z) *
            φRight pq.2 (splitLast m m z) ≠ 0 := by
      simpa only [Function.mem_support, ψ,
        SchwartzMap.tensorProduct_apply] using hz
    have hleft_ne : φLeft pq.1 (splitFirst m m z) ≠ 0 :=
      (mul_ne_zero_iff.mp hz_mul).1
    have hright_ne : φRight pq.2 (splitLast m m z) ≠ 0 :=
      (mul_ne_zero_iff.mp hz_mul).2
    have hleft_ball :=
      hLeft_support pq.1
        (show splitFirst m m z ∈
          Function.support (φLeft pq.1 : (Fin m → ℝ) → ℂ) by
            simpa only [Function.mem_support] using hleft_ne)
    have hright_ball :=
      hRight_support pq.2
        (show splitLast m m z ∈
          Function.support (φRight pq.2 : (Fin m → ℝ) → ℂ) by
            simpa only [Function.mem_support] using hright_ne)
    rw [Metric.mem_ball, dist_zero_right] at hleft_ball hright_ball ⊢
    exact
      (norm_le_splitFirst_add_splitLast m m z).trans_lt
        (add_lt_add hleft_ball hright_ball)
  have hρ : Tendsto ρ atTop (𝓝 0) := by
    have hfst :
        Tendsto (fun pq : ℕ × ℕ => pq.1) atTop atTop := by
      rw [← Filter.prod_atTop_atTop_eq]
      exact Filter.tendsto_fst
    have hsnd :
        Tendsto (fun pq : ℕ × ℕ => pq.2) atTop atTop := by
      rw [← Filter.prod_atTop_atTop_eq]
      exact Filter.tendsto_snd
    simpa only [ρ, Function.comp_apply, add_zero] using
      (hrLeft.comp hfst).add (hrRight.comp hsnd)
  exact
    tendstoUniformlyOn_integral_shrinking_schwartz_approx_identity_of_compact
      atTop ψ ρ F x0 K hK R hR
      hψ_nonneg hψ_real hψ_int hψ_support hρ
      hF_cont (by simpa only [ψ] using hF_int)

/-- Two independently shrinking normalized Schwartz families form a joint
approximate identity on the concatenated coordinate space. -/
theorem tendsto_integral_tensorPair_shrinking_schwartz_approx_identities
    {m : ℕ}
    (φLeft φRight : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (rLeft rRight : ℕ → ℝ)
    (F : (Fin (m + m) → ℝ) → ℂ)
    (x0 : Fin (m + m) → ℝ)
    (hLeft_nonneg : ∀ n x, 0 ≤ (φLeft n x).re)
    (hRight_nonneg : ∀ n x, 0 ≤ (φRight n x).re)
    (hLeft_real : ∀ n x, (φLeft n x).im = 0)
    (hRight_real : ∀ n x, (φRight n x).im = 0)
    (hLeft_int : ∀ n, ∫ x : Fin m → ℝ, φLeft n x = 1)
    (hRight_int : ∀ n, ∫ x : Fin m → ℝ, φRight n x = 1)
    (hLeft_support :
      ∀ n, Function.support (φLeft n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (rLeft n))
    (hRight_support :
      ∀ n, Function.support (φRight n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (rRight n))
    (hrLeft : Tendsto rLeft atTop (𝓝 0))
    (hrRight : Tendsto rRight atTop (𝓝 0))
    (hF_cont : ContinuousAt F x0)
    (hF_int :
      ∀ pq : ℕ × ℕ,
        Integrable
          (fun y : Fin (m + m) → ℝ =>
            ((φLeft pq.1).tensorProduct (φRight pq.2)) y * F (x0 + y))) :
    Tendsto
      (fun pq : ℕ × ℕ =>
        ∫ y : Fin (m + m) → ℝ,
          ((φLeft pq.1).tensorProduct (φRight pq.2)) y * F (x0 + y))
      atTop
      (𝓝 (F x0)) := by
  let ψ : (ℕ × ℕ) → SchwartzMap (Fin (m + m) → ℝ) ℂ :=
    fun pq => (φLeft pq.1).tensorProduct (φRight pq.2)
  let ρ : (ℕ × ℕ) → ℝ := fun pq => rLeft pq.1 + rRight pq.2
  have hψ_nonneg :
      ∀ pq z, 0 ≤ (ψ pq z).re := by
    intro pq z
    rw [show ψ pq z =
      φLeft pq.1 (splitFirst m m z) *
        φRight pq.2 (splitLast m m z) by rfl]
    rw [Complex.mul_re, hLeft_real, hRight_real]
    simp only [mul_zero, sub_zero]
    exact mul_nonneg (hLeft_nonneg _ _) (hRight_nonneg _ _)
  have hψ_real :
      ∀ pq z, (ψ pq z).im = 0 := by
    intro pq z
    rw [show ψ pq z =
      φLeft pq.1 (splitFirst m m z) *
        φRight pq.2 (splitLast m m z) by rfl]
    rw [Complex.mul_im, hLeft_real, hRight_real]
    ring
  have hψ_int :
      ∀ pq, ∫ z : Fin (m + m) → ℝ, ψ pq z = 1 := by
    intro pq
    change
      (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume :
          MeasureTheory.Measure (Fin (m + m) → ℝ))) (ψ pq) = 1
    rw [← integral_integrateHeadBlock (m := m) (n := m) (ψ pq)]
    rw [show ψ pq =
      (φLeft pq.1).tensorProduct (φRight pq.2) by rfl]
    rw [integrateHeadBlock_tensorProduct]
    have hleft :
        (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume :
            MeasureTheory.Measure (Fin m → ℝ))) (φLeft pq.1) = 1 := by
      simpa only [SchwartzMap.integralCLM_apply] using hLeft_int pq.1
    rw [hleft, one_smul]
    simpa only [SchwartzMap.integralCLM_apply] using hRight_int pq.2
  have hψ_support :
      ∀ pq,
        Function.support (ψ pq : (Fin (m + m) → ℝ) → ℂ) ⊆
          Metric.ball (0 : Fin (m + m) → ℝ) (ρ pq) := by
    intro pq z hz
    have hz_mul :
        φLeft pq.1 (splitFirst m m z) *
            φRight pq.2 (splitLast m m z) ≠ 0 := by
      simpa only [Function.mem_support, ψ, SchwartzMap.tensorProduct_apply] using hz
    have hleft_ne : φLeft pq.1 (splitFirst m m z) ≠ 0 :=
      (mul_ne_zero_iff.mp hz_mul).1
    have hright_ne : φRight pq.2 (splitLast m m z) ≠ 0 :=
      (mul_ne_zero_iff.mp hz_mul).2
    have hleft_ball :=
      hLeft_support pq.1
        (show splitFirst m m z ∈
          Function.support (φLeft pq.1 : (Fin m → ℝ) → ℂ) by
            simpa only [Function.mem_support] using hleft_ne)
    have hright_ball :=
      hRight_support pq.2
        (show splitLast m m z ∈
          Function.support (φRight pq.2 : (Fin m → ℝ) → ℂ) by
            simpa only [Function.mem_support] using hright_ne)
    rw [Metric.mem_ball, dist_zero_right] at hleft_ball hright_ball ⊢
    exact
      (norm_le_splitFirst_add_splitLast m m z).trans_lt
        (add_lt_add hleft_ball hright_ball)
  have hρ : Tendsto ρ atTop (𝓝 0) := by
    have hfst :
        Tendsto (fun pq : ℕ × ℕ => pq.1) atTop atTop := by
      rw [← Filter.prod_atTop_atTop_eq]
      exact Filter.tendsto_fst
    have hsnd :
        Tendsto (fun pq : ℕ × ℕ => pq.2) atTop atTop := by
      rw [← Filter.prod_atTop_atTop_eq]
      exact Filter.tendsto_snd
    simpa only [ρ, Function.comp_apply, add_zero] using
      (hrLeft.comp hfst).add (hrRight.comp hsnd)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rw [Metric.continuousAt_iff] at hF_cont
  obtain ⟨δ, hδ_pos, hδ⟩ := hF_cont (ε / 2) hε2
  have hρ_small : ∀ᶠ pq : ℕ × ℕ in atTop, ρ pq < δ := by
    have hdist :
        ∀ᶠ pq : ℕ × ℕ in atTop, dist (ρ pq) 0 < δ :=
      (Metric.tendsto_nhds.mp hρ) δ hδ_pos
    filter_upwards [hdist] with pq hpq
    rw [Real.dist_eq] at hpq
    exact lt_of_le_of_lt (le_abs_self (ρ pq)) (by simpa using hpq)
  filter_upwards [hρ_small] with pq hpq_small
  have hψ_int_norm :
      ∫ y : Fin (m + m) → ℝ, ‖ψ pq y‖ = 1 := by
    exact
      integral_norm_eq_one_of_nonnegative_real_schwartz
        (ψ pq) (hψ_nonneg pq) (hψ_real pq) (hψ_int pq)
  have hconst_int :
      Integrable
        (fun y : Fin (m + m) → ℝ => ψ pq y * F x0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (SchwartzMap.integrable (ψ pq)).mul_const (F x0)
  have hdiff_int :
      Integrable
        (fun y : Fin (m + m) → ℝ =>
          ψ pq y * (F (x0 + y) - F x0)) := by
    have hmain :
        Integrable
          (fun y : Fin (m + m) → ℝ =>
            ψ pq y * F (x0 + y)) := by
      simpa only [ψ] using hF_int pq
    have hsub := hmain.sub hconst_int
    exact hsub.congr (Filter.Eventually.of_forall (fun y => by simp [mul_sub]))
  have hrewrite :
      (∫ y : Fin (m + m) → ℝ, ψ pq y * F (x0 + y)) - F x0 =
        ∫ y : Fin (m + m) → ℝ,
          ψ pq y * (F (x0 + y) - F x0) := by
    have hconst_integral :
        ∫ y : Fin (m + m) → ℝ, ψ pq y * F x0 = F x0 := by
      calc
        ∫ y : Fin (m + m) → ℝ, ψ pq y * F x0
            = (∫ y : Fin (m + m) → ℝ, ψ pq y) * F x0 := by
                simpa using
                  (MeasureTheory.integral_mul_const
                    (μ := volume) (r := F x0)
                    (f := fun y : Fin (m + m) → ℝ => ψ pq y))
        _ = F x0 := by rw [hψ_int pq, one_mul]
    calc
      (∫ y : Fin (m + m) → ℝ, ψ pq y * F (x0 + y)) - F x0
          =
        (∫ y : Fin (m + m) → ℝ, ψ pq y * F (x0 + y)) -
          (∫ y : Fin (m + m) → ℝ, ψ pq y * F x0) := by
            rw [hconst_integral]
      _ =
        ∫ y : Fin (m + m) → ℝ,
          (ψ pq y * F (x0 + y)) - (ψ pq y * F x0) := by
            rw [integral_sub (hF_int pq) hconst_int]
      _ =
        ∫ y : Fin (m + m) → ℝ,
          ψ pq y * (F (x0 + y) - F x0) := by
            congr 1
            ext y
            ring
  have hpoint_bound :
      ∀ y : Fin (m + m) → ℝ,
        ‖ψ pq y * (F (x0 + y) - F x0)‖ ≤
          ‖ψ pq y‖ * (ε / 2) := by
    intro y
    by_cases hy_zero : ψ pq y = 0
    · simp [hy_zero]
    · have hy_support :
          y ∈ Function.support
            (ψ pq : (Fin (m + m) → ℝ) → ℂ) := by
        simpa [Function.mem_support] using hy_zero
      have hy_ball := hψ_support pq hy_support
      have hy_norm_lt : ‖y‖ < δ := by
        have hy_dist : dist y (0 : Fin (m + m) → ℝ) < ρ pq :=
          Metric.mem_ball.mp hy_ball
        have hy_dist' : ‖y‖ < ρ pq := by
          simpa [dist_eq_norm] using hy_dist
        exact lt_trans hy_dist' hpq_small
      have hy_dist_x : dist (x0 + y) x0 < δ := by
        rw [dist_eq_norm]
        simpa [add_sub_cancel_left] using hy_norm_lt
      have hF_close : dist (F (x0 + y)) (F x0) < ε / 2 :=
        hδ hy_dist_x
      rw [dist_eq_norm] at hF_close
      calc
        ‖ψ pq y * (F (x0 + y) - F x0)‖
            = ‖ψ pq y‖ * ‖F (x0 + y) - F x0‖ := norm_mul _ _
        _ ≤ ‖ψ pq y‖ * (ε / 2) := by
              exact mul_le_mul_of_nonneg_left
                (le_of_lt hF_close) (norm_nonneg _)
  have hnorm_integral :
      ‖∫ y : Fin (m + m) → ℝ,
          ψ pq y * (F (x0 + y) - F x0)‖ ≤ ε / 2 := by
    have hupper_int :
        Integrable
          (fun y : Fin (m + m) → ℝ => ‖ψ pq y‖ * (ε / 2)) := by
      simpa using
        (SchwartzMap.integrable (ψ pq)).norm.mul_const (ε / 2)
    calc
      ‖∫ y : Fin (m + m) → ℝ,
          ψ pq y * (F (x0 + y) - F x0)‖
          ≤ ∫ y : Fin (m + m) → ℝ,
              ‖ψ pq y * (F (x0 + y) - F x0)‖ :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ y : Fin (m + m) → ℝ, ‖ψ pq y‖ * (ε / 2) := by
            exact integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              hupper_int
              (Filter.Eventually.of_forall hpoint_bound)
      _ = (∫ y : Fin (m + m) → ℝ, ‖ψ pq y‖) * (ε / 2) := by
            rw [integral_mul_const]
      _ = ε / 2 := by rw [hψ_int_norm, one_mul]
  rw [dist_eq_norm]
  change
    ‖(∫ y : Fin (m + m) → ℝ, ψ pq y * F (x0 + y)) - F x0‖ < ε
  calc
    ‖(∫ y : Fin (m + m) → ℝ, ψ pq y * F (x0 + y)) - F x0‖
        = ‖∫ y : Fin (m + m) → ℝ,
            ψ pq y * (F (x0 + y) - F x0)‖ := by rw [hrewrite]
    _ ≤ ε / 2 := hnorm_integral
    _ < ε := by linarith

end OSIIChapterV
end OSReconstruction
