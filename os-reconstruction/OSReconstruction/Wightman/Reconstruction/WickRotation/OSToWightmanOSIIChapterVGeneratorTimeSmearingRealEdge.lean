/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeSpatialCurrying
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorGlobalProfile
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTwoScaleAssembly
















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A finite-dimensional Schwartz approximate identity. The tests need not be
coordinatewise products; this coordinate-invariant form is what survives an
invertible block-global affine change of variables. -/
structure SchwartzTimeApproximateIdentity (n : ℕ) where
  test : ℕ → SchwartzMap (Fin n → ℝ) ℂ
  radius : ℕ → ℝ
  nonnegative :
    ∀ N x, 0 ≤ ((test N) x).re
  real :
    ∀ N x, ((test N) x).im = 0
  integral_one :
    ∀ N, ∫ x : Fin n → ℝ, test N x = 1
  compact :
    ∀ N, HasCompactSupport (test N : (Fin n → ℝ) → ℂ)
  support :
    ∀ N,
      Function.support
          (test N : (Fin n → ℝ) → ℂ) ⊆
        Metric.ball 0 (radius N)
  radius_tendsto :
    Tendsto radius atTop (𝓝 0)

namespace SchwartzTimeApproximateIdentity

/-- Discarding finitely many initial scales preserves a Schwartz approximate
identity. -/
noncomputable def tail
    {n : ℕ}
    (I : SchwartzTimeApproximateIdentity n)
    (N0 : ℕ) :
    SchwartzTimeApproximateIdentity n where
  test N := I.test (N + N0)
  radius N := I.radius (N + N0)
  nonnegative N := I.nonnegative (N + N0)
  real N := I.real (N + N0)
  integral_one N := I.integral_one (N + N0)
  compact N := I.compact (N + N0)
  support N := I.support (N + N0)
  radius_tendsto :=
    I.radius_tendsto.comp (tendsto_add_atTop_nat N0)

end SchwartzTimeApproximateIdentity

/-- A shrinking approximate identity whose tests are genuine finite products
of one-dimensional compact strict-positive Section 4.3 time sources. -/
structure Section43ProductTimeApproximateIdentity (n : ℕ) where
  factors :
    ℕ → Fin n → Section43CompactPositiveTimeSource1D
  radius : ℕ → ℝ
  factor_nonnegative :
    ∀ N i x, 0 ≤ ((factors N i).f x).re
  factor_real :
    ∀ N i x, ((factors N i).f x).im = 0
  factor_integral_one :
    ∀ N i, ∫ x : ℝ, (factors N i).f x = 1
  factor_support :
    ∀ N i,
      Function.support ((factors N i).f : ℝ → ℂ) ⊆
        Metric.ball 0 (radius N)
  nonnegative :
    ∀ N x,
      0 ≤ ((section43TimeProductSource (factors N)).f x).re
  real :
    ∀ N x,
      ((section43TimeProductSource (factors N)).f x).im = 0
  integral_one :
    ∀ N,
      ∫ x : Fin n → ℝ,
        (section43TimeProductSource (factors N)).f x = 1
  support :
    ∀ N,
      Function.support
          ((section43TimeProductSource (factors N)).f :
            (Fin n → ℝ) → ℂ) ⊆
        Metric.ball 0 (radius N)
  radius_tendsto :
    Tendsto radius atTop (𝓝 0)

namespace Section43ProductTimeApproximateIdentity

/-- Every product approximate identity has a strictly positive support
radius. This follows from normalization and the shrinking-support contract,
including in zero time variables. -/
theorem radius_pos
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (N : ℕ) :
    0 < I.radius N := by
  have hexists :
      ∃ x : Fin n → ℝ,
        (section43TimeProductSource (I.factors N)).f x ≠ 0 := by
    by_contra h
    push Not at h
    have hzero :
        (section43TimeProductSource (I.factors N)).f =
          (0 : SchwartzMap (Fin n → ℝ) ℂ) := by
      ext x
      exact h x
    have hint := I.integral_one N
    rw [hzero] at hint
    simp at hint
  obtain ⟨x, hx⟩ := hexists
  have hx_support :
      x ∈ Function.support
        ((section43TimeProductSource (I.factors N)).f :
          (Fin n → ℝ) → ℂ) := by
    simpa [Function.mem_support] using hx
  have hx_ball := I.support N hx_support
  rw [Metric.mem_ball, dist_zero_right] at hx_ball
  exact (norm_nonneg x).trans_lt hx_ball

/-- Restrict a factorwise product approximate identity along any finite
coordinate map. Every selected coordinate remains a normalized shrinking
one-dimensional delta source, so the resulting product is again a genuine
product approximate identity. -/
noncomputable def reindex
    {n m : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (e : Fin m → Fin n) :
    Section43ProductTimeApproximateIdentity m where
  factors N i := I.factors N (e i)
  radius := I.radius
  factor_nonnegative N i := I.factor_nonnegative N (e i)
  factor_real N i := I.factor_real N (e i)
  factor_integral_one N i := I.factor_integral_one N (e i)
  factor_support N i := I.factor_support N (e i)
  nonnegative := by
    intro N x
    simp only [section43TimeProductSource, section43TimeProductTensor,
      SchwartzMap.productTensor_apply]
    have hprod :
        0 ≤ (∏ i : Fin m, (I.factors N (e i)).f (x i)).re ∧
          (∏ i : Fin m, (I.factors N (e i)).f (x i)).im = 0 := by
      classical
      refine Finset.induction_on (Finset.univ : Finset (Fin m)) ?_ ?_
      · simp
      · intro a s has ih
        rw [Finset.prod_insert has]
        have ha_nonneg :
            0 ≤ ((I.factors N (e a)).f (x a)).re :=
          I.factor_nonnegative N (e a) (x a)
        have ha_real :
            ((I.factors N (e a)).f (x a)).im = 0 :=
          I.factor_real N (e a) (x a)
        constructor
        · rw [Complex.mul_re, ha_real, ih.2]
          ring_nf
          exact mul_nonneg ha_nonneg ih.1
        · rw [Complex.mul_im, ha_real, ih.2]
          ring
    exact hprod.1
  real := by
    intro N x
    simp only [section43TimeProductSource, section43TimeProductTensor,
      SchwartzMap.productTensor_apply]
    classical
    refine Finset.induction_on (Finset.univ : Finset (Fin m)) ?_ ?_
    · simp
    · intro a s has ih
      rw [Finset.prod_insert has, Complex.mul_im,
        I.factor_real N (e a) (x a), ih]
      ring
  integral_one := by
    intro N
    have hraw :=
      section43TimeProductSource_integral_eq_product_raw
        (gs := fun i : Fin m => I.factors N (e i))
        (σ := fun _ : Fin m => 0)
    calc
      ∫ x : Fin m → ℝ,
          (section43TimeProductSource
            (fun i : Fin m => I.factors N (e i))).f x =
        ∫ x : Fin m → ℝ,
          Complex.exp
              (-(∑ i : Fin m,
                (x i : ℂ) * ((0 : ℝ) : ℂ))) *
            (section43TimeProductSource
              (fun i : Fin m => I.factors N (e i))).f x := by
          simp
      _ =
        ∏ i : Fin m,
          ∫ t : ℝ,
            Complex.exp
                (-(t : ℂ) *
                  (((fun _ : Fin m => 0) i : ℝ) : ℂ)) *
              (I.factors N (e i)).f t := hraw
      _ = ∏ _i : Fin m, (1 : ℂ) := by
        refine Finset.prod_congr rfl ?_
        intro i _hi
        simpa using I.factor_integral_one N (e i)
      _ = 1 := by simp
  support := by
    intro N x hx
    rw [Metric.mem_ball, dist_zero_right,
      pi_norm_lt_iff (I.radius_pos N)]
    intro i
    have hx_prod_ne :
        (∏ j : Fin m, (I.factors N (e j)).f (x j)) ≠ 0 := by
      simpa [Function.mem_support, section43TimeProductSource,
        section43TimeProductTensor, SchwartzMap.productTensor_apply] using hx
    have hxi_ne : (I.factors N (e i)).f (x i) ≠ 0 := by
      intro hzero
      exact hx_prod_ne
        (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
    have hxi_support :
        x i ∈ Function.support
          ((I.factors N (e i)).f : ℝ → ℂ) := by
      simpa [Function.mem_support] using hxi_ne
    have hxi_ball := I.factor_support N (e i) hxi_support
    simpa [Metric.mem_ball, dist_zero_right] using hxi_ball
  radius_tendsto := I.radius_tendsto

/-- The compact strict-positive multitime source at scale `N`. -/
noncomputable def source
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (N : ℕ) :
    Section43CompactStrictPositiveTimeSource n :=
  section43TimeProductSource (I.factors N)

/-- The underlying Schwartz test at scale `N`. -/
noncomputable def test
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (N : ℕ) :
    SchwartzMap (Fin n → ℝ) ℂ :=
  (I.source N).f

@[simp] theorem test_apply
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (N : ℕ) (x : Fin n → ℝ) :
    I.test N x =
      (section43TimeProductSource (I.factors N)).f x := rfl

theorem test_compact
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (N : ℕ) :
    HasCompactSupport (I.test N : (Fin n → ℝ) → ℂ) :=
  (I.source N).compact

theorem test_positive
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (N : ℕ) :
    tsupport (I.test N : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n :=
  (I.source N).positive

/-- Translate the shrinking positive-orthant bump to a fixed strict-positive
time configuration. Since the original bump is itself supported in the
strict-positive orthant, the translated source stays strictly to the future
of the center at every scale, not merely eventually. -/
noncomputable def translatedSource
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n)
    (N : ℕ) :
    Section43CompactStrictPositiveTimeSource n where
  f := SCV.translateSchwartz (-τ) (I.test N)
  positive := by
    exact
      (translate_positiveOrthant_schwartz_mem
        (I.test N)
        (by simpa [section43TimeStrictPositiveRegion] using I.test_positive N)
        (I.test_compact N) τ
        (by simpa [section43TimeStrictPositiveRegion] using hτ)).1
  compact := by
    exact
      (translate_positiveOrthant_schwartz_mem
        (I.test N)
        (by simpa [section43TimeStrictPositiveRegion] using I.test_positive N)
        (I.test_compact N) τ
        (by simpa [section43TimeStrictPositiveRegion] using hτ)).2

@[simp] theorem translatedSource_f
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n)
    (N : ℕ) :
    (I.translatedSource τ hτ N).f =
      SCV.translateSchwartz (-τ) (I.test N) := rfl

/-- Translating a strict-positive approximate-identity test to `τ` places
its entire time support coordinatewise above `τ`. -/
theorem translatedSource_tsupport_anchor_le
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n)
    (N : ℕ) :
    ∀ ξ ∈ tsupport
        ((I.translatedSource τ hτ N).f : (Fin n → ℝ) → ℂ),
      ∀ i, τ i ≤ ξ i := by
  intro ξ hξ
  let lower : Set (Fin n → ℝ) := {ξ | ∀ i, τ i ≤ ξ i}
  have hlower_closed : IsClosed lower := by
    dsimp [lower]
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i : Fin n =>
      isClosed_le
        (continuous_const : Continuous fun _ : Fin n → ℝ => τ i)
        (continuous_apply i)
  have hsupport :
      Function.support
          ((I.translatedSource τ hτ N).f : (Fin n → ℝ) → ℂ) ⊆
        lower := by
    intro ξ hξ i
    have hξ_source :
        ξ - τ ∈ Function.support (I.test N : (Fin n → ℝ) → ℂ) := by
      simpa [translatedSource_f, sub_eq_add_neg] using
        (SCV.mem_support_translateSchwartz_iff
          (-τ) (I.test N) ξ).mp hξ
    have hpositive :=
      I.test_positive N (subset_tsupport (I.test N) hξ_source) i
    dsimp [section43TimeStrictPositiveRegion] at hpositive
    simpa only [Pi.sub_apply] using
      (le_of_lt (sub_pos.mp hpositive))
  exact (closure_minimal hsupport hlower_closed) hξ

/-- The actual positive-time Euclidean source obtained by combining the
translated time delta with an arbitrary spatial Schwartz factor. -/
noncomputable def translatedPositiveTimeSpatialSource
    {d n : ℕ} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (N : ℕ) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  section43PositiveTimeSpatialSourceCLM
    d n (I.translatedSource τ hτ N) χ

@[simp] theorem translatedPositiveTimeSpatialSource_coe
    {d n : ℕ} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (N : ℕ) :
    (I.translatedPositiveTimeSpatialSource τ hτ χ N).1 =
      section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (SCV.translateSchwartz (-τ) (I.test N)) := rfl

/-- A tail of the shrinking approximate identity, translated to one fixed
strict-positive anchor, lies in a single compact strict-positive time
carrier. -/
structure AnchoredCompactTimeCarrierData
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ) where
  tailStart : ℕ
  carrier : Set (Fin n → ℝ)
  carrier_compact : IsCompact carrier
  carrier_positive :
    carrier ⊆ section43TimeStrictPositiveRegion n
  translated_support :
    ∀ N,
      tsupport
          (SCV.translateSchwartz (-τ) (I.test (N + tailStart)) :
            (Fin n → ℝ) → ℂ) ⊆
        carrier

/-- Because the untranslated product tests already lie in the strict-positive
orthant, all translated scales fit in one compact positive carrier without
discarding any initial scales. -/
theorem exists_anchoredCompactTimeCarrierData_zeroTail
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n) :
    ∃ C : AnchoredCompactTimeCarrierData I τ, C.tailStart = 0 := by
  obtain ⟨R0, hR0⟩ :=
    (Metric.isBounded_range_of_tendsto I.radius I.radius_tendsto
      ).subset_closedBall (0 : ℝ)
  let R : ℝ := |R0| + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  let lower : Set (Fin n → ℝ) := {ξ | ∀ i, τ i ≤ ξ i}
  have hlower_closed : IsClosed lower := by
    dsimp [lower]
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i : Fin n =>
      isClosed_le
        (continuous_const : Continuous fun _ : Fin n → ℝ => τ i)
        (continuous_apply i)
  let K : Set (Fin n → ℝ) := Metric.closedBall τ R ∩ lower
  have hK_compact : IsCompact K := by
    dsimp [K]
    exact (isCompact_closedBall τ R).inter_right hlower_closed
  have hK_positive :
      K ⊆ section43TimeStrictPositiveRegion n := by
    intro ξ hξ i
    have hξ_lower : ∀ j, τ j ≤ ξ j := by
      simpa [K, lower] using hξ.2
    exact lt_of_lt_of_le (hτ i) (hξ_lower i)
  refine
    ⟨{
      tailStart := 0
      carrier := K
      carrier_compact := hK_compact
      carrier_positive := hK_positive
      translated_support := ?_ }, rfl⟩
  intro N
  refine closure_minimal ?_ hK_compact.isClosed
  intro ξ hξ
  have hξ_source :
      ξ - τ ∈ Function.support (I.test N : (Fin n → ℝ) → ℂ) := by
    simpa [sub_eq_add_neg] using
      (SCV.mem_support_translateSchwartz_iff
        (-τ) (I.test N) ξ).mp hξ
  have hrange : I.radius N ∈ Set.range I.radius := ⟨N, rfl⟩
  have hradius_abs : |I.radius N| ≤ R0 := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hR0 hrange
  have hradius : I.radius N ≤ R := by
    calc
      I.radius N ≤ |I.radius N| := le_abs_self _
      _ ≤ R0 := hradius_abs
      _ ≤ |R0| := le_abs_self _
      _ ≤ R := by dsimp [R]; linarith
  have hξ_radius : ‖ξ - τ‖ < I.radius N := by
    simpa [Metric.mem_ball, dist_zero_right] using I.support N hξ_source
  constructor
  · rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_trans (le_of_lt hξ_radius) hradius
  · intro i
    have hpositive :=
      I.test_positive N (subset_tsupport (I.test N) hξ_source) i
    dsimp [section43TimeStrictPositiveRegion] at hpositive
    simpa only [Pi.sub_apply] using
      (le_of_lt (sub_pos.mp hpositive))

/-- The zero-tail anchored carrier may be selected with the packet anchor as
a coordinatewise lower bound.  The translated tests already have this
one-sided support property, so intersecting with the closed lower orthant
retains every scale. -/
theorem exists_anchoredCompactTimeCarrierData_zeroTail_lower
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n) :
    ∃ C : AnchoredCompactTimeCarrierData I τ,
      C.tailStart = 0 ∧
        ∀ ξ ∈ C.carrier, ∀ i, τ i ≤ ξ i := by
  obtain ⟨C, hC⟩ :=
    I.exists_anchoredCompactTimeCarrierData_zeroTail τ hτ
  let lower : Set (Fin n → ℝ) := {ξ | ∀ i, τ i ≤ ξ i}
  have hlower_closed : IsClosed lower := by
    dsimp [lower]
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i : Fin n =>
      isClosed_le
        (continuous_const : Continuous fun _ : Fin n → ℝ => τ i)
        (continuous_apply i)
  have htranslated_lower :
      ∀ N,
        tsupport
            (SCV.translateSchwartz (-τ) (I.test N) :
              (Fin n → ℝ) → ℂ) ⊆
          lower := by
    intro N
    apply closure_minimal
    · intro ξ hξ
      have hξ_source :
          ξ - τ ∈ Function.support (I.test N : (Fin n → ℝ) → ℂ) := by
        simpa [sub_eq_add_neg] using
          (SCV.mem_support_translateSchwartz_iff
            (-τ) (I.test N) ξ).mp hξ
      intro i
      have hpositive :=
        I.test_positive N (subset_tsupport (I.test N) hξ_source) i
      dsimp [section43TimeStrictPositiveRegion] at hpositive
      simpa only [Pi.sub_apply] using
        (le_of_lt (sub_pos.mp hpositive))
    · exact hlower_closed
  let C' : AnchoredCompactTimeCarrierData I τ := {
    tailStart := C.tailStart
    carrier := C.carrier ∩ lower
    carrier_compact := C.carrier_compact.inter_right hlower_closed
    carrier_positive := inter_subset_left.trans C.carrier_positive
    translated_support := by
      intro N
      rw [hC]
      exact fun ξ hξ =>
        ⟨C.translated_support N (by simpa [hC] using hξ),
          htranslated_lower N hξ⟩ }
  refine ⟨C', hC, ?_⟩
  intro ξ hξ i
  exact hξ.2 i

/-- After removing finitely many coarse scales, all translated delta sources
and all of their spatial Schwartz factors share one compact strict-positive
difference-time carrier.

This is the scale-uniform support statement needed by the reflected
continuation machinery. The tail shift is harmless for every `atTop` limit
and avoids imposing an artificial bound on the finitely many initial support
radii. -/
theorem
    exists_tail_translatedPositiveTimeSpatialSource_uniformCompactSupport
    {d n : ℕ} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n) :
    ∃ N0 : ℕ,
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun p :
            ℕ × SchwartzMap (Section43SpatialSpace d n) ℂ =>
          (I.translatedPositiveTimeSpatialSource
            τ hτ p.2 (p.1 + N0)).1) := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp
      ((isOpen_section43TimeStrictPositiveRegion n).mem_nhds hτ)
  let R : ℝ := ε / 2
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hclosed_positive :
      Metric.closedBall τ R ⊆
        section43TimeStrictPositiveRegion n := by
    intro ξ hξ
    apply hball
    rw [Metric.mem_ball]
    have hξR : dist ξ τ ≤ R := Metric.mem_closedBall.mp hξ
    exact hξR.trans_lt (by dsimp [R]; linarith)
  have htranslated :=
    eventually_translate_shrinking_schwartz_supportsInOpen_and_mapsTo
      I.test I.radius τ (Metric.ball τ R)
      I.test_compact I.support I.radius_tendsto
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
  rw [Filter.eventually_atTop] at htranslated
  obtain ⟨N0, hN0⟩ := htranslated
  refine ⟨N0, Metric.closedBall τ R,
    isCompact_closedBall τ R, hclosed_positive, ?_⟩
  intro p x hx
  have htime :
      section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n x) ∈
        tsupport
          (SCV.translateSchwartz (-τ) (I.test (p.1 + N0)) :
            (Fin n → ℝ) → ℂ) := by
    exact
      osiiA0_orderedPullback_tsupport_subset_timeSet
        (d := d) p.2
        (SCV.translateSchwartz (-τ) (I.test (p.1 + N0)))
        (tsupport
          (SCV.translateSchwartz (-τ) (I.test (p.1 + N0)) :
            (Fin n → ℝ) → ℂ))
        (Subset.refl _)
        (by
          simpa [translatedPositiveTimeSpatialSource_coe] using hx)
  have htail :
      SCV.SupportsInOpen
          (SCV.translateSchwartz (-τ) (I.test (p.1 + N0)) :
            (Fin n → ℝ) → ℂ)
          (Metric.ball τ R) :=
    (hN0 (p.1 + N0) (by omega)).1
  exact Metric.ball_subset_closedBall (htail.2 htime)

/-- Forget the product presentation and retain the coordinate-invariant
Schwartz approximate-identity data. -/
noncomputable def toSchwartzTimeApproximateIdentity
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n) :
    SchwartzTimeApproximateIdentity n where
  test := I.test
  radius := I.radius
  nonnegative := I.nonnegative
  real := I.real
  integral_one := I.integral_one
  compact := I.test_compact
  support := I.support
  radius_tendsto := I.radius_tendsto

/-- Product-form shrinking approximate identities exist in every finite
number of time variables. -/
theorem nonempty (n : ℕ) :
    Nonempty (Section43ProductTimeApproximateIdentity n) := by
  let radius : ℕ → ℝ := fun N => 1 / (N + 1 : ℝ)
  have hradius_pos : ∀ N, 0 < radius N := by
    intro N
    dsimp [radius]
    positivity
  let factor : ℕ → Section43CompactPositiveTimeSource1D := fun N =>
    Classical.choose
      (exists_section43CompactPositiveTimeSource1D_approx_identity
        (radius N / 2) (by positivity))
  have hfactor :
      ∀ N,
        (∀ x : ℝ, 0 ≤ ((factor N).f x).re) ∧
        (∀ x : ℝ, ((factor N).f x).im = 0) ∧
        (∫ x : ℝ, (factor N).f x = 1) ∧
        Function.support ((factor N).f : ℝ → ℂ) ⊆
          Metric.ball (0 : ℝ) (radius N / 2) := by
    intro N
    simpa [factor] using
      (Classical.choose_spec
        (exists_section43CompactPositiveTimeSource1D_approx_identity
          (radius N / 2) (by positivity)))
  let factors :
      ℕ → Fin n → Section43CompactPositiveTimeSource1D :=
    fun N _ => factor N
  exact ⟨{
    factors := factors
    radius := radius
    factor_nonnegative := by
      intro N i x
      exact (hfactor N).1 x
    factor_real := by
      intro N i x
      exact (hfactor N).2.1 x
    factor_integral_one := by
      intro N i
      exact (hfactor N).2.2.1
    factor_support := by
      intro N i x hx
      have hx_half := (hfactor N).2.2.2 hx
      rw [Metric.mem_ball, dist_zero_right] at hx_half ⊢
      exact hx_half.trans (by
        have hpos := hradius_pos N
        linarith)
    nonnegative := by
      intro N x
      simp only [section43TimeProductSource, section43TimeProductTensor,
        SchwartzMap.productTensor_apply, factors]
      have hprod :
          0 ≤ (∏ i : Fin n, (factor N).f (x i)).re ∧
            (∏ i : Fin n, (factor N).f (x i)).im = 0 := by
        classical
        refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
        · simp
        · intro a s has ih
          rw [Finset.prod_insert has]
          have ha_nonneg : 0 ≤ ((factor N).f (x a)).re :=
            (hfactor N).1 (x a)
          have ha_real : ((factor N).f (x a)).im = 0 :=
            (hfactor N).2.1 (x a)
          constructor
          · rw [Complex.mul_re, ha_real, ih.2]
            ring_nf
            exact mul_nonneg ha_nonneg ih.1
          · rw [Complex.mul_im, ha_real, ih.2]
            ring
      exact hprod.1
    real := by
      intro N x
      simp only [section43TimeProductSource, section43TimeProductTensor,
        SchwartzMap.productTensor_apply, factors]
      classical
      refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
      · simp
      · intro a s has ih
        rw [Finset.prod_insert has, Complex.mul_im,
          (hfactor N).2.1 (x a), ih]
        ring
    integral_one := by
      intro N
      have hraw :=
        section43TimeProductSource_integral_eq_product_raw
          (gs := factors N) (σ := fun _ : Fin n => 0)
      calc
        ∫ x : Fin n → ℝ,
            (section43TimeProductSource (factors N)).f x =
          ∫ x : Fin n → ℝ,
            Complex.exp
                (-(∑ i : Fin n,
                  (x i : ℂ) * ((0 : ℝ) : ℂ))) *
              (section43TimeProductSource (factors N)).f x := by
            simp
        _ =
          ∏ i : Fin n,
            ∫ t : ℝ,
              Complex.exp
                  (-(t : ℂ) *
                    (((fun _ : Fin n => 0) i : ℝ) : ℂ)) *
                (factors N i).f t := hraw
        _ = ∏ _i : Fin n, (1 : ℂ) := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          simpa [factors] using (hfactor N).2.2.1
        _ = 1 := by simp
    support := by
      intro N x hx
      rw [Metric.mem_ball, dist_zero_right,
        pi_norm_lt_iff (hradius_pos N)]
      intro i
      have hx_prod_ne :
          (∏ j : Fin n, (factor N).f (x j)) ≠ 0 := by
        simpa [Function.mem_support, section43TimeProductSource,
          section43TimeProductTensor, SchwartzMap.productTensor_apply,
          factors] using hx
      have hxi_ne : (factor N).f (x i) ≠ 0 := by
        intro hzero
        exact hx_prod_ne
          (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
      have hxi_support :
          x i ∈ Function.support ((factor N).f : ℝ → ℂ) := by
        simpa [Function.mem_support] using hxi_ne
      have hxi_ball := (hfactor N).2.2.2 hxi_support
      have hxi_half :
          ‖x i‖ < radius N / 2 := by
        simpa [Metric.mem_ball, dist_zero_right] using hxi_ball
      exact hxi_half.trans (by
        have hpos := hradius_pos N
        linarith)
    radius_tendsto := by
      simpa [radius, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto
            (fun N : ℕ => 1 / ((N : ℝ) + 1))
            atTop (𝓝 0)) }⟩

end Section43ProductTimeApproximateIdentity

namespace GeneratorSpatialTwoScaleApproximationFamily
namespace CommonPositiveRealEdgeData

variable {d k : ℕ}

end CommonPositiveRealEdgeData
end GeneratorSpatialTwoScaleApproximationFamily

end OSIIChapterV
end OSReconstruction
