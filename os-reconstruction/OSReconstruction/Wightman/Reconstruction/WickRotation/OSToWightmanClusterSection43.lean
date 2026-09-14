import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransformCarrier

/-!
# Section 4.3 Input for Wightman Clustering

This module connects the source-separated single-split cluster theorem to the
compiled Section 4.3 transform-component carrier. The two one-factor
comparisons are consequences rather than hypotheses, and the translated shell
is the exact source shell already controlled by the analytic core.
-/

noncomputable section

open scoped Topology FourierTransform
open Set MeasureTheory Filter

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private def section43TranslateNPointDomainHomeomorph {n : ℕ}
    (a : SpacetimeDim d) :
    NPointDomain d n ≃ₜ NPointDomain d n where
  toFun := fun x i => x i - a
  invFun := fun x i => x i + a
  left_inv x := by
    ext i μ
    simp
  right_inv x := by
    ext i μ
    simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (continuous_apply i).sub continuous_const
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact (continuous_apply i).add continuous_const

omit [NeZero d] in
theorem translateSchwartzNPoint_hasCompactSupport
    {n : ℕ} (a : SpacetimeDim d) (g : SchwartzNPoint d n)
    (hg_compact : HasCompactSupport (g : NPointDomain d n → ℂ)) :
    HasCompactSupport
      (translateSchwartzNPoint (d := d) a g : NPointDomain d n → ℂ) := by
  simpa [translateSchwartzNPoint_apply, sub_eq_add_neg] using
    hg_compact.comp_homeomorph
      (section43TranslateNPointDomainHomeomorph (d := d) (n := n) a)

/-- Spatial translation on a Section 4.3 positive-energy representative,
written in cumulative-momentum coordinates. -/
private noncomputable def section43SpatialTranslationPhaseCLM
    (d n : ℕ) [NeZero d] (a : Fin d → ℝ) :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43CumulativeTailMomentumCLE d n).symm).comp
    ((section43TotalMomentumPhaseCLM d n (-(Fin.cons 0 a))).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43CumulativeTailMomentumCLE d n)))

private theorem flatten_translateSchwartzNPoint_spatial
    (n : ℕ) (a : Fin d → ℝ) (ψ : SchwartzNPoint d n) :
    flattenSchwartzNPoint (d := d)
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) ψ) =
      SCV.translateSchwartz
        (-(section43DiagonalTranslationFlat d n (Fin.cons 0 a)))
        (flattenSchwartzNPoint (d := d) ψ) := by
  ext u
  rw [flattenSchwartzNPoint_apply, SCV.translateSchwartz_apply,
    flattenSchwartzNPoint_apply, translateSchwartzNPoint_apply]
  congr 1
  ext k μ
  simp [section43DiagonalTranslationFlat, sub_eq_add_neg]

/-- The deterministic Section 4.3 frequency representative intertwines
spatial translation with the total-momentum phase. -/
private theorem section43FrequencyRepresentative_translate_spatial
    (n : ℕ) (a : Fin d → ℝ) (ψ : SchwartzNPoint d n) :
    section43FrequencyRepresentative d n
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) ψ) =
      section43SpatialTranslationPhaseCLM d n a
        (section43FrequencyRepresentative d n ψ) := by
  ext q
  simp only [section43FrequencyRepresentative, section43SpatialTranslationPhaseCLM,
    ContinuousLinearMap.comp_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  rw [flatten_translateSchwartzNPoint_spatial]
  have h := congrArg
    (fun K : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ =>
      K ((section43CumulativeTailMomentumCLE d n).symm q))
    (physicsFourierFlatCLM_diagonalTranslate_eq_phaseCLM
      d n (-(Fin.cons 0 a)) (flattenSchwartzNPoint (d := d) ψ))
  simpa [section43DiagonalTranslationFlat] using h

/-- A diagonal spatial translation becomes a translation in only the first
spatial difference coordinate. -/
private noncomputable def section43FirstSpatialDifference
    (n : ℕ) (hn : 0 < n) (a : Fin d → ℝ) :
    EuclideanSpace ℝ (Fin n × Fin d) :=
  (EuclideanSpace.equiv (Fin n × Fin d) ℝ).symm
    (fun p => if p.1 = (⟨0, hn⟩ : Fin n) then a p.2 else 0)

omit [NeZero d] in
@[simp] private theorem section43FirstSpatialDifference_apply
    (n : ℕ) (hn : 0 < n) (a : Fin d → ℝ) (p : Fin n × Fin d) :
    section43FirstSpatialDifference (d := d) n hn a p =
      if p.1 = (⟨0, hn⟩ : Fin n) then a p.2 else 0 := by
  simp [section43FirstSpatialDifference]

private theorem section43DiffPullback_translate_spatial_apply
    (n : ℕ) (hn : 0 < n) (a : Fin d → ℝ)
    (g : SchwartzNPoint d n)
    (hg_ord : tsupport (g : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hga_ord :
      tsupport
          (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g :
            NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (τ : Fin n → ℝ) (η : EuclideanSpace ℝ (Fin n × Fin d)) :
    nPointTimeSpatialSchwartzCLE (d := d) (n := n)
        (section43DiffPullbackCLM d n
          ⟨translateSchwartzNPoint (d := d) (Fin.cons 0 a) g, hga_ord⟩)
        (τ, η) =
      nPointTimeSpatialSchwartzCLE (d := d) (n := n)
        (section43DiffPullbackCLM d n ⟨g, hg_ord⟩)
        (τ, η - section43FirstSpatialDifference (d := d) n hn a) := by
  rw [nPointTimeSpatialSchwartzCLE_section43DiffPullbackCLM_apply,
    nPointTimeSpatialSchwartzCLE_section43DiffPullbackCLM_apply,
    translateSchwartzNPoint_apply]
  congr 1
  ext k μ
  simp only [Pi.sub_apply]
  rw [section43DiffCoordRealCLE_symm_apply,
    section43DiffCoordRealCLE_symm_apply]
  refine Fin.cases ?_ (fun r => ?_) μ
  ·
    simp [nPointTimeSpatialCLE]
  · simp [nPointTimeSpatialCLE, section43FirstSpatialDifference_apply,
      Finset.sum_sub_distrib]

private theorem partialFourierSpatial_diffPullback_translate_spatial
    (n : ℕ) (hn : 0 < n) (a : Fin d → ℝ)
    (g : SchwartzNPoint d n)
    (hg_ord : tsupport (g : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hga_ord :
      tsupport
          (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g :
            NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (τ : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := n)
        (section43DiffPullbackCLM d n
          ⟨translateSchwartzNPoint (d := d) (Fin.cons 0 a) g, hga_ord⟩)
        (τ, ξ) =
      ((((𝐞 (-(inner ℝ
          (section43FirstSpatialDifference (d := d) n hn a) ξ))) :
          Circle) : ℂ)) *
        partialFourierSpatial_fun (d := d) (n := n)
          (section43DiffPullbackCLM d n ⟨g, hg_ord⟩) (τ, ξ) := by
  rw [partialFourierSpatial_fun_eq_integral,
    partialFourierSpatial_fun_eq_integral]
  let b := section43FirstSpatialDifference (d := d) n hn a
  let F : EuclideanSpace ℝ (Fin n × Fin d) → ℂ := fun η =>
    nPointTimeSpatialSchwartzCLE (d := d) (n := n)
      (section43DiffPullbackCLM d n ⟨g, hg_ord⟩) (τ, η)
  let L :
      EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] ℝ :=
    innerₗ (EuclideanSpace ℝ (Fin n × Fin d))
  have htranslate :
      (fun η : EuclideanSpace ℝ (Fin n × Fin d) =>
        nPointTimeSpatialSchwartzCLE (d := d) (n := n)
          (section43DiffPullbackCLM d n
            ⟨translateSchwartzNPoint (d := d) (Fin.cons 0 a) g, hga_ord⟩)
          (τ, η)) =
        F ∘ fun η => η + (-b) := by
    funext η
    simpa [F, b, sub_eq_add_neg] using
      section43DiffPullback_translate_spatial_apply
        (d := d) n hn a g hg_ord hga_ord τ η
  have hfourier := congr_fun
    (VectorFourier.fourierIntegral_comp_add_right
      (V := EuclideanSpace ℝ (Fin n × Fin d))
      (W := EuclideanSpace ℝ (Fin n × Fin d)) (E := ℂ)
      Real.fourierChar volume L F (-b)) ξ
  have hintegral :
      (∫ η : EuclideanSpace ℝ (Fin n × Fin d),
        𝐞 (-(inner ℝ η ξ)) •
          nPointTimeSpatialSchwartzCLE (d := d) (n := n)
            (section43DiffPullbackCLM d n
              ⟨translateSchwartzNPoint (d := d) (Fin.cons 0 a) g, hga_ord⟩)
            (τ, η)) =
        VectorFourier.fourierIntegral Real.fourierChar volume L
          (F ∘ fun η => η + (-b)) ξ := by
    rw [VectorFourier.fourierIntegral]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with η
    rw [congr_fun htranslate η]
    simp [L]
  rw [hintegral]
  simpa [VectorFourier.fourierIntegral, F, L, b, Circle.smul_def,
    inner_neg_left] using hfourier

omit [NeZero d] in
private theorem sum_section43CumulativeTailMomentumCLE_symm
    (n : ℕ) (hn : 0 < n) (q : NPointDomain d n) (μ : Fin (d + 1)) :
    (∑ k : Fin n,
      (q k μ -
        if h : k.val + 1 < n then q ⟨k.val + 1, h⟩ μ else 0)) =
      q ⟨0, hn⟩ μ := by
  let f : ℕ → ℝ := fun k =>
    if h : k < n then q ⟨k, h⟩ μ else 0
  have htel := @Finset.sum_range_sub ℝ _ f n
  have hforward :
      (∑ k ∈ Finset.range n, (f k - f (k + 1))) =
        f 0 - f n := by
    calc
      (∑ k ∈ Finset.range n, (f k - f (k + 1))) =
          -(∑ k ∈ Finset.range n, (f (k + 1) - f k)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
      _ = -(f n - f 0) := by rw [htel]
      _ = f 0 - f n := by ring
  have hsum :
      (∑ k : Fin n,
        (q k μ -
          if h : k.val + 1 < n then q ⟨k.val + 1, h⟩ μ else 0)) =
        ∑ k : Fin n, (f k.val - f (k.val + 1)) := by
    apply Finset.sum_congr rfl
    intro k _hk
    simp [f, k.isLt]
  rw [hsum]
  have hfin :
      (∑ k : Fin n, (f k.val - f (k.val + 1))) =
        f 0 - f n := by
    rw [Finset.sum_fin_eq_sum_range]
    calc
      (∑ k ∈ Finset.range n,
          if h : k < n then f (⟨k, h⟩ : Fin n).val -
            f ((⟨k, h⟩ : Fin n).val + 1) else 0) =
          ∑ k ∈ Finset.range n, (f k - f (k + 1)) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [Finset.mem_range.mp hk]
      _ = f 0 - f n := hforward
  rw [hfin]
  simp [f, hn]

private theorem section43TotalMomentumFlat_cumulative_symm
    (n : ℕ) (hn : 0 < n) (q : NPointDomain d n) (μ : Fin (d + 1)) :
    section43TotalMomentumFlat d n
        ((section43CumulativeTailMomentumCLE d n).symm q) μ =
      if μ = 0 then q ⟨0, hn⟩ μ
      else -(2 * Real.pi) * q ⟨0, hn⟩ μ := by
  rw [section43TotalMomentumFlat]
  simp_rw [section43CumulativeTailMomentumCLE_symm_apply]
  by_cases hμ : μ = 0
  · simp only [hμ, ↓reduceIte]
    simpa using
      (sum_section43CumulativeTailMomentumCLE_symm
        (d := d) n hn q (0 : Fin (d + 1)))
  · simp only [hμ, ↓reduceIte, ← Finset.mul_sum]
    rw [sum_section43CumulativeTailMomentumCLE_symm (d := d) n hn q μ]

private theorem inner_section43FirstSpatialDifference_qSpatial
    (n : ℕ) (hn : 0 < n) (a : Fin d → ℝ) (q : NPointDomain d n) :
    inner ℝ (section43FirstSpatialDifference (d := d) n hn a)
        (section43QSpatial (d := d) (n := n) q) =
      ∑ j : Fin d, a j * q ⟨0, hn⟩ (Fin.succ j) := by
  have hinner :
      inner ℝ (section43FirstSpatialDifference (d := d) n hn a)
          (section43QSpatial (d := d) (n := n) q) =
        ∑ p : Fin n × Fin d,
          section43QSpatial (d := d) (n := n) q p *
            section43FirstSpatialDifference (d := d) n hn a p := by
    rw [PiLp.inner_apply]
    rfl
  rw [hinner, ← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp only [section43FirstSpatialDifference_apply, ↓reduceIte, mul_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    congr 1
  · intro k _hk hk0
    simp [section43FirstSpatialDifference_apply, hk0]
  · intro hzero
    exact False.elim (hzero (Finset.mem_univ _))

private theorem section43SpatialFourierPhase_eq_totalMomentumPhase
    (n : ℕ) (hn : 0 < n) (a : Fin d → ℝ) (q : NPointDomain d n) :
    ((((𝐞 (-(inner ℝ
        (section43FirstSpatialDifference (d := d) n hn a)
        (section43QSpatial (d := d) (n := n) q)))) : Circle) : ℂ)) =
      Complex.exp
        (-(Complex.I *
          ∑ μ : Fin (d + 1),
            ((-(((Fin.cons (0 : ℝ) a) : Fin (d + 1) → ℝ) μ) : ℝ) : ℂ) *
              (section43TotalMomentumFlat d n
                ((section43CumulativeTailMomentumCLE d n).symm q) μ : ℂ))) := by
  rw [Real.fourierChar_apply,
    inner_section43FirstSpatialDifference_qSpatial (d := d) n hn a q]
  simp_rw [section43TotalMomentumFlat_cumulative_symm (d := d) n hn q]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, neg_zero, Complex.ofReal_zero,
    zero_mul, zero_add, Fin.cons_succ, Fin.succ_ne_zero, ↓reduceIte]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  congr 1
  rw [Finset.mul_sum]
  simp only [mul_assoc]

/-- Spatial translation of an ordered Euclidean source becomes the expected
total-momentum phase on its Section 4.3 Fourier-Laplace integral. -/
private theorem section43FourierLaplaceIntegral_translate_spatial
    (n : ℕ) (hn : 0 < n) (a : Fin d → ℝ)
    (g : SchwartzNPoint d n)
    (hg_ord : tsupport (g : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hga_ord :
      tsupport
          (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g :
            NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (q : NPointDomain d n) :
    section43FourierLaplaceIntegral d n
        ⟨translateSchwartzNPoint (d := d) (Fin.cons 0 a) g, hga_ord⟩ q =
      Complex.exp
          (-(Complex.I *
            ∑ μ : Fin (d + 1),
              ((-(((Fin.cons (0 : ℝ) a) : Fin (d + 1) → ℝ) μ) : ℝ) : ℂ) *
                (section43TotalMomentumFlat d n
                  ((section43CumulativeTailMomentumCLE d n).symm q) μ : ℂ))) *
        section43FourierLaplaceIntegral d n ⟨g, hg_ord⟩ q := by
  rw [section43FourierLaplaceIntegral, section43FourierLaplaceIntegral]
  let c : ℂ :=
    Complex.exp
      (-(Complex.I *
        ∑ μ : Fin (d + 1),
          ((-(((Fin.cons (0 : ℝ) a) : Fin (d + 1) → ℝ) μ) : ℝ) : ℂ) *
            (section43TotalMomentumFlat d n
              ((section43CumulativeTailMomentumCLE d n).symm q) μ : ℂ)))
  let F : (Fin n → ℝ) → ℂ := fun τ =>
    Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
      partialFourierSpatial_fun
        (d := d) (n := n) (section43DiffPullbackCLM d n ⟨g, hg_ord⟩)
        (τ, section43QSpatial (d := d) (n := n) q)
  change
    (∫ τ : Fin n → ℝ,
      Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
        partialFourierSpatial_fun
          (d := d) (n := n)
          (section43DiffPullbackCLM d n
            ⟨translateSchwartzNPoint (d := d) (Fin.cons 0 a) g, hga_ord⟩)
          (τ, section43QSpatial (d := d) (n := n) q)) =
      c * ∫ τ : Fin n → ℝ, F τ
  calc
    _ = ∫ τ : Fin n → ℝ, c * F τ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with τ
      rw [partialFourierSpatial_diffPullback_translate_spatial
        (d := d) n hn a g hg_ord hga_ord τ
        (section43QSpatial (d := d) (n := n) q)]
      rw [section43SpatialFourierPhase_eq_totalMomentumPhase
        (d := d) n hn a q]
      simp only [c, F]
      ring
    _ = c * ∫ τ : Fin n → ℝ, F τ :=
      MeasureTheory.integral_const_mul c F

/-- A Section 4.3 Fourier-Laplace representative is transported by diagonal
spatial translation through the total-momentum phase operator. -/
private theorem section43FourierLaplaceRepresentative_translate_spatial
    (n : ℕ) (hn : 0 < n) (a : Fin d → ℝ)
    (g : SchwartzNPoint d n)
    (hg_ord : tsupport (g : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hga_ord :
      tsupport
          (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g :
            NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (Φ : SchwartzNPoint d n)
    (hΦ : section43FourierLaplaceRepresentative d n ⟨g, hg_ord⟩ Φ) :
    section43FourierLaplaceRepresentative d n
      ⟨translateSchwartzNPoint (d := d) (Fin.cons 0 a) g, hga_ord⟩
      (section43SpatialTranslationPhaseCLM d n a Φ) := by
  intro q hq
  simp only [section43SpatialTranslationPhaseCLM,
    ContinuousLinearMap.comp_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    section43TotalMomentumPhaseCLM_apply]
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [hΦ q hq]
  exact
    (section43FourierLaplaceIntegral_translate_spatial
      (d := d) n hn a g hg_ord hga_ord q).symm

/-- Spatial translation commutes with the Section 4.3 transform component,
expressed through the deterministic frequency projection. -/
theorem
    section43FrequencyProjection_translate_spatial_of_transformComponent
    (n : ℕ) (hn : 0 < n) (a : Fin d → ℝ)
    (ψ : SchwartzNPoint d n)
    (g : SchwartzNPoint d n)
    (hg_ord : tsupport (g : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hg_compact : HasCompactSupport (g : NPointDomain d n → ℂ))
    (hga_ord :
      tsupport
          (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g :
            NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (hga_compact :
      HasCompactSupport
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g :
          NPointDomain d n → ℂ))
    (hψ_freq :
      section43FrequencyProjection (d := d) n ψ =
        section43FourierLaplaceTransformComponent d n
          g hg_ord hg_compact) :
    section43FrequencyProjection (d := d) n
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) ψ) =
      section43FourierLaplaceTransformComponent d n
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)
        hga_ord hga_compact := by
  obtain ⟨Φ, hΦ_rep, hΦ_q⟩ :=
    section43FourierLaplaceTransformComponent_has_representative
      d n g hg_ord hg_compact
  have hψ_rep :
      section43FourierLaplaceRepresentative d n ⟨g, hg_ord⟩
        (section43FrequencyRepresentative d n ψ) :=
    section43FrequencyRepresentative_is_fourierLaplaceRepresentative_of_quotient_eq
      d n ψ ⟨g, hg_ord⟩ Φ hΦ_rep (hψ_freq.trans hΦ_q.symm)
  have htranslated_rep :
      section43FourierLaplaceRepresentative d n
        ⟨translateSchwartzNPoint (d := d) (Fin.cons 0 a) g, hga_ord⟩
        (section43FrequencyRepresentative d n
          (translateSchwartzNPoint (d := d) (Fin.cons 0 a) ψ)) := by
    rw [section43FrequencyRepresentative_translate_spatial
      (d := d) n a ψ]
    exact section43FourierLaplaceRepresentative_translate_spatial
      (d := d) n hn a g hg_ord hga_ord
        (section43FrequencyRepresentative d n ψ) hψ_rep
  simpa [section43FrequencyProjection] using
    section43FourierLaplaceRepresentative_quotient_eq_transformComponent
      d n
      (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)
      hga_ord hga_compact
      (section43FrequencyRepresentative d n
        (translateSchwartzNPoint (d := d) (Fin.cons 0 a) ψ))
      htranslated_rep

end OSReconstruction
