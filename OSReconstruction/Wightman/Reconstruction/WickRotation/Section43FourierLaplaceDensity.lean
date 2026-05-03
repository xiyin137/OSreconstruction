import OSReconstruction.Mathlib429Compat
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceCompactDifferentiation

/-!
# Section 4.3 Fourier-Laplace Density

This file contains the pure-analysis density packet needed by the final
Section 4.3 positivity closure.  It deliberately stays below the Wightman /
OS-Hilbert layers: the theorems here should mention only Schwartz maps,
Fourier-Laplace kernels, and the positive-energy quotient.
-/

noncomputable section

open scoped Topology FourierTransform BoundedContinuousFunction
open Set MeasureTheory Filter

namespace OSReconstruction

/-- Compact Schwartz source on the strict positive half-line.  The strict
support condition is the one-dimensional analogue of compact support inside
`OrderedPositiveTimeRegion`. -/
structure Section43CompactPositiveTimeSource1D where
  f : SchwartzMap ℝ ℂ
  positive :
    tsupport (f : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)
  compact : HasCompactSupport (f : ℝ → ℂ)

/-- A one-dimensional ambient representative of the compact one-sided Laplace
transform, modulo equality on the closed half-line. -/
def section43OneSidedLaplaceRepresentative1D
    (g : Section43CompactPositiveTimeSource1D)
    (Φ : SchwartzMap ℝ ℂ) : Prop :=
  ∀ σ : ℝ, 0 ≤ σ →
    Φ σ =
      ∫ t : ℝ,
        Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t

/-- The raw one-sided Laplace scalar associated to a compact strict-positive
source. -/
noncomputable def section43OneSidedLaplaceRaw
    (g : Section43CompactPositiveTimeSource1D) (σ : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t

/-- The candidate for the `r`-th real derivative of the compact one-sided
Laplace transform.  Compact source support makes this integral meaningful for
every real `σ`, including the cutoff transition strip. -/
noncomputable def section43OneSidedLaplaceRawDerivCandidate
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ : ℝ) : ℂ :=
  ∫ t : ℝ,
    ((-t : ℂ) ^ r *
      Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t

@[simp] theorem section43OneSidedLaplaceRawDerivCandidate_zero
    (g : Section43CompactPositiveTimeSource1D) (σ : ℝ) :
    section43OneSidedLaplaceRawDerivCandidate g 0 σ =
      section43OneSidedLaplaceRaw g σ := by
  unfold section43OneSidedLaplaceRawDerivCandidate section43OneSidedLaplaceRaw
  simp

theorem section43OneSidedLaplaceRawDerivCandidate_integrable
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ : ℝ) :
    Integrable
      (fun t : ℝ =>
        ((-t : ℂ) ^ r *
          Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t) := by
  have hcont :
      Continuous
        (fun t : ℝ =>
          ((-t : ℂ) ^ r *
            Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t) := by
    have h :
        Continuous
          (((fun t : ℝ => (-t : ℂ) ^ r) *
              (fun t : ℝ =>
                Complex.exp (-(t : ℂ) * (σ : ℂ)))) *
            (g.f : ℝ → ℂ)) := by
      exact (((Complex.continuous_ofReal.comp continuous_id).neg.pow r).mul
        (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp continuous_id).neg.mul
            (continuous_const : Continuous (fun _ : ℝ => (σ : ℂ)))))).mul
        g.f.continuous
    simpa [Pi.mul_apply] using h
  have hcomp :
      HasCompactSupport
        (fun t : ℝ =>
          ((-t : ℂ) ^ r *
            Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t) := by
    simpa [Pi.mul_apply] using
      (HasCompactSupport.mul_left
        (f := fun t : ℝ =>
          (-t : ℂ) ^ r * Complex.exp (-(t : ℂ) * (σ : ℂ)))
        (f' := (g.f : ℝ → ℂ)) g.compact)
  exact hcont.integrable_of_hasCompactSupport hcomp

theorem section43OneSidedLaplaceRawDerivKernel_hasDerivAt
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (t σ : ℝ) :
    HasDerivAt
      (fun σ : ℝ =>
        ((-t : ℂ) ^ r *
          Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t)
      (((-t : ℂ) ^ (r + 1) *
        Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t)
      σ := by
  have hexp :
      HasDerivAt
        (fun σ : ℝ => Complex.exp (-(t : ℂ) * (σ : ℂ)))
        (-(t : ℂ) * Complex.exp (-(t : ℂ) * (σ : ℂ))) σ := by
    have hlin :
        HasDerivAt (fun σ : ℝ => -(t : ℂ) * (σ : ℂ)) (-(t : ℂ)) σ := by
      have hmul :
          HasDerivAt (fun σ : ℝ => (t : ℂ) * (σ : ℂ)) (t : ℂ) σ := by
        simpa using
          ((hasDerivAt_const (x := σ) (c := (t : ℂ))).mul
            (Complex.ofRealCLM.hasDerivAt (x := σ)))
      simpa [neg_mul] using hmul.neg
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.cexp
  have h := (hexp.const_mul ((-t : ℂ) ^ r)).mul_const (g.f t)
  convert h using 1
  ring

theorem Section43CompactPositiveTimeSource1D.tsupport_subset_Ici
    (g : Section43CompactPositiveTimeSource1D) :
    tsupport (g.f : ℝ → ℂ) ⊆ Set.Ici (0 : ℝ) := by
  intro t ht
  exact le_of_lt (Set.mem_Ioi.mp (g.positive ht))

theorem Section43CompactPositiveTimeSource1D.pos_of_ne_zero
    (g : Section43CompactPositiveTimeSource1D)
    {t : ℝ} (ht : g.f t ≠ 0) :
    0 < t :=
  g.positive (subset_tsupport _ ht)

theorem Section43CompactPositiveTimeSource1D.eq_zero_of_not_pos
    (g : Section43CompactPositiveTimeSource1D)
    {t : ℝ} (ht : ¬ 0 < t) :
    g.f t = 0 := by
  by_contra hne
  exact ht (g.pos_of_ne_zero hne)

theorem section43OneSidedLaplaceRaw_eq_complexLaplaceTransform
    (g : Section43CompactPositiveTimeSource1D) (σ : ℝ) :
    section43OneSidedLaplaceRaw g σ =
      section43ComplexLaplaceTransform (g.f : ℝ → ℂ) (σ : ℂ) := by
  unfold section43OneSidedLaplaceRaw section43ComplexLaplaceTransform
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  congr 1
  ring_nf

theorem section43OneSidedLaplaceRaw_integrable_of_nonneg
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    Integrable
      (fun t : ℝ =>
        Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t) := by
  have hbase :=
    section43ComplexLaplaceTransform_integrable_of_nonneg_re
      (f := g.f) g.tsupport_subset_Ici (σ : ℂ) (by simpa using hσ)
  refine hbase.congr ?_
  filter_upwards with t
  congr 1
  ring_nf

theorem section43OneSidedLaplaceRaw_eq_fourierInvPairingCanonicalExtension_of_pos
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 < σ) :
    section43OneSidedLaplaceRaw g σ =
      section43FourierInvPairingCanonicalExtension g.f
        ((σ / (2 * Real.pi)) * Complex.I) := by
  rw [section43OneSidedLaplaceRaw_eq_complexLaplaceTransform]
  exact section43ComplexLaplaceTransform_eq_fourierInvPairingCanonicalExtension_of_pos
    (f := g.f) g.tsupport_subset_Ici hσ

theorem section43SmoothCutoff_complex_iteratedFDeriv_support_subset_Ici_neg_one :
    ∀ r : ℕ, ∀ σ : ℝ,
      iteratedFDeriv ℝ r (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ ≠ 0 →
        σ ∈ Set.Ici (-1 : ℝ) := by
  intro r σ hne
  by_contra hσ_mem
  have hσ_lt : σ < -1 := by
    simpa [Set.mem_Ici, not_le] using hσ_mem
  have hEqNeg : Set.EqOn (fun ξ : ℝ => (SCV.smoothCutoff ξ : ℂ))
      (fun _ => 0) (Set.Iio (-1 : ℝ)) := by
    intro ξ hξ
    show (SCV.smoothCutoff ξ : ℂ) = 0
    exact_mod_cast SCV.smoothCutoff_zero_of_le_neg_one (le_of_lt hξ)
  have hDerivNeg : Set.EqOn
      (iteratedDeriv r (fun ξ : ℝ => (SCV.smoothCutoff ξ : ℂ)))
      (fun _ => 0) (Set.Iio (-1 : ℝ)) :=
    hEqNeg.iteratedDeriv_of_isOpen isOpen_Iio r |>.trans
      (by intro x _; simp)
  have hderiv_zero :
      iteratedDeriv r (fun ξ : ℝ => (SCV.smoothCutoff ξ : ℂ)) σ = 0 :=
    hDerivNeg (Set.mem_Iio.mpr hσ_lt)
  have hF_zero :
      iteratedFDeriv ℝ r (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ = 0 := by
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hderiv_zero, norm_zero]
  exact hne hF_zero

noncomputable def section43OneSidedLaplaceCutoffFun
    (g : Section43CompactPositiveTimeSource1D) (σ : ℝ) : ℂ :=
  (SCV.smoothCutoff σ : ℂ) * section43OneSidedLaplaceRaw g σ

theorem section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    section43OneSidedLaplaceCutoffFun g σ =
      section43OneSidedLaplaceRaw g σ := by
  change (SCV.smoothCutoff σ : ℂ) * section43OneSidedLaplaceRaw g σ =
    section43OneSidedLaplaceRaw g σ
  have hcut : (SCV.smoothCutoff σ : ℂ) = 1 := by
    exact_mod_cast SCV.smoothCutoff_one_of_nonneg hσ
  rw [hcut]
  simp

/-- Compact support inside the strict positive half-line is uniformly separated
from the boundary. -/
theorem exists_positive_margin_of_compact_tsupport_subset_Ioi
    (g : SchwartzMap ℝ ℂ)
    (hg_pos : tsupport (g : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hg_compact : HasCompactSupport (g : ℝ → ℂ)) :
    ∃ δ > 0, tsupport (g : ℝ → ℂ) ⊆ Set.Ici δ := by
  classical
  let K : Set ℝ := tsupport (g : ℝ → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using hg_compact
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0, hx0_min⟩ :=
      hK_compact.exists_isMinOn hne continuous_id.continuousOn
    have hx0_pos : 0 < x0 := hg_pos hx0
    refine ⟨x0 / 2, by linarith, ?_⟩
    intro x hx
    have hle : x0 ≤ x := isMinOn_iff.mp hx0_min x hx
    exact Set.mem_Ici.mpr (by linarith)
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

theorem exists_Icc_bounds_of_compact_tsupport_subset_Ici
    (g : SchwartzMap ℝ ℂ)
    {δ : ℝ}
    (hδ : tsupport (g : ℝ → ℂ) ⊆ Set.Ici δ)
    (hg_compact : HasCompactSupport (g : ℝ → ℂ)) :
    ∃ R, δ ≤ R ∧ tsupport (g : ℝ → ℂ) ⊆ Set.Icc δ R := by
  classical
  let K : Set ℝ := tsupport (g : ℝ → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using hg_compact
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0, hx0_max⟩ :=
      hK_compact.exists_isMaxOn hne continuous_id.continuousOn
    have hδx0 : δ ≤ x0 := hδ hx0
    refine ⟨x0, hδx0, ?_⟩
    intro x hx
    exact Set.mem_Icc.mpr ⟨hδ hx, isMaxOn_iff.mp hx0_max x hx⟩
  · refine ⟨δ, le_rfl, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

theorem exists_positive_Icc_bounds_of_compactPositiveTimeSource
    (g : Section43CompactPositiveTimeSource1D) :
    ∃ δ R, 0 < δ ∧ δ ≤ R ∧
      tsupport (g.f : ℝ → ℂ) ⊆ Set.Icc δ R := by
  rcases exists_positive_margin_of_compact_tsupport_subset_Ioi
      g.f g.positive g.compact with
    ⟨δ, hδ_pos, hδ_supp⟩
  rcases exists_Icc_bounds_of_compact_tsupport_subset_Ici
      (g := g.f) hδ_supp g.compact with
    ⟨R, hδR, hR⟩
  exact ⟨δ, R, hδ_pos, hδR, hR⟩

theorem section43OneSidedLaplaceRawDerivCandidate_hasDerivAt
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ₀ : ℝ) :
    HasDerivAt
      (section43OneSidedLaplaceRawDerivCandidate g r)
      (section43OneSidedLaplaceRawDerivCandidate g (r + 1) σ₀)
      σ₀ := by
  classical
  rcases exists_positive_Icc_bounds_of_compactPositiveTimeSource g with
    ⟨δ, R, hδ_pos, hδR, hsupp⟩
  let B : ℝ :=
    (max |δ| |R|) ^ (r + 1) * Real.exp (R * (|σ₀| + 1))
  let bound : ℝ → ℝ := fun t => B * ‖g.f t‖
  have hR_pos : 0 < R := lt_of_lt_of_le hδ_pos hδR
  have hs : Metric.closedBall σ₀ (1 : ℝ) ∈ 𝓝 σ₀ :=
    Metric.closedBall_mem_nhds σ₀ zero_lt_one
  have hF_meas :
      ∀ᶠ σ : ℝ in 𝓝 σ₀,
        AEStronglyMeasurable
          (fun t : ℝ =>
            ((-t : ℂ) ^ r *
              Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t)
          (volume : Measure ℝ) := by
    filter_upwards with σ
    exact (section43OneSidedLaplaceRawDerivCandidate_integrable g r σ).aestronglyMeasurable
  have hF_int :
      Integrable
        (fun t : ℝ =>
          ((-t : ℂ) ^ r *
            Complex.exp (-(t : ℂ) * (σ₀ : ℂ))) * g.f t) :=
    section43OneSidedLaplaceRawDerivCandidate_integrable g r σ₀
  have hF'_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          ((-t : ℂ) ^ (r + 1) *
            Complex.exp (-(t : ℂ) * (σ₀ : ℂ))) * g.f t)
        (volume : Measure ℝ) :=
    (section43OneSidedLaplaceRawDerivCandidate_integrable g (r + 1) σ₀).aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    dsimp [bound]
    exact g.f.integrable.norm.const_mul B
  have h_bound :
      ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∀ σ ∈ Metric.closedBall σ₀ (1 : ℝ),
        ‖((-t : ℂ) ^ (r + 1) *
            Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t‖ ≤ bound t := by
    filter_upwards with t σ hσ
    by_cases htzero : g.f t = 0
    · simp [bound, htzero]
    · have ht_supp : t ∈ tsupport (g.f : ℝ → ℂ) :=
        subset_tsupport _ htzero
      have htIcc : t ∈ Set.Icc δ R := hsupp ht_supp
      have htδ : δ ≤ t := htIcc.1
      have htR : t ≤ R := htIcc.2
      have ht_nonneg : 0 ≤ t := le_trans (le_of_lt hδ_pos) htδ
      have hσ_dist : dist σ σ₀ ≤ (1 : ℝ) := by
        simpa [Metric.mem_closedBall] using hσ
      have hσ_abs : |σ| ≤ |σ₀| + 1 := by
        have hsub : |σ - σ₀| ≤ (1 : ℝ) := by
          simpa [Real.dist_eq] using hσ_dist
        calc
          |σ| = |(σ - σ₀) + σ₀| := by ring_nf
          _ ≤ |σ - σ₀| + |σ₀| := abs_add_le _ _
          _ ≤ |σ₀| + 1 := by linarith
      have ht_abs_le : |t| ≤ max |δ| |R| := by
        rw [abs_of_nonneg ht_nonneg]
        exact htR.trans ((le_abs_self R).trans (le_max_right |δ| |R|))
      have hexp_re :
          (-(t : ℂ) * (σ : ℂ)).re ≤ R * (|σ₀| + 1) := by
        have hre : (-(t : ℂ) * (σ : ℂ)).re = -(t * σ) := by
          simp [Complex.mul_re]
        rw [hre]
        have h_abs_mul : |t * σ| ≤ R * (|σ₀| + 1) := by
          calc
            |t * σ| = |t| * |σ| := abs_mul t σ
            _ ≤ R * (|σ₀| + 1) := by
              rw [abs_of_nonneg ht_nonneg]
              exact mul_le_mul htR hσ_abs (abs_nonneg σ) (le_of_lt hR_pos)
        exact (neg_le_abs (t * σ)).trans h_abs_mul
      calc
        ‖((-t : ℂ) ^ (r + 1) *
            Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t‖
            = ‖(-t : ℂ) ^ (r + 1)‖ *
                ‖Complex.exp (-(t : ℂ) * (σ : ℂ))‖ * ‖g.f t‖ := by
              rw [norm_mul, norm_mul]
        _ = |t| ^ (r + 1) *
                Real.exp ((-(t : ℂ) * (σ : ℂ)).re) * ‖g.f t‖ := by
              rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
                Complex.norm_exp]
        _ ≤ (max |δ| |R|) ^ (r + 1) *
                Real.exp (R * (|σ₀| + 1)) * ‖g.f t‖ := by
              gcongr
        _ = bound t := by
              rfl
  have h_diff :
      ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∀ σ ∈ Metric.closedBall σ₀ (1 : ℝ),
        HasDerivAt
          (fun σ : ℝ =>
            ((-t : ℂ) ^ r *
              Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t)
          (((-t : ℂ) ^ (r + 1) *
            Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t)
          σ := by
    filter_upwards with t σ _hσ
    exact section43OneSidedLaplaceRawDerivKernel_hasDerivAt g r t σ
  have hmain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℝ) (μ := volume)
      (F := fun (σ : ℝ) (t : ℝ) =>
        ((-t : ℂ) ^ r *
          Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t)
      (F' := fun (σ : ℝ) (t : ℝ) =>
        ((-t : ℂ) ^ (r + 1) *
          Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t)
      (x₀ := σ₀) (s := Metric.closedBall σ₀ (1 : ℝ))
      (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  change HasDerivAt
    (fun σ : ℝ =>
      ∫ t : ℝ,
        ((-t : ℂ) ^ r *
          Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t)
    (∫ t : ℝ,
      ((-t : ℂ) ^ (r + 1) *
        Complex.exp (-(t : ℂ) * (σ₀ : ℂ))) * g.f t)
    σ₀
  simpa [neg_mul, mul_assoc] using hmain

theorem section43OneSidedLaplaceRaw_iteratedDeriv_formula
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ : ℝ) :
    iteratedDeriv r (section43OneSidedLaplaceRaw g) σ =
      section43OneSidedLaplaceRawDerivCandidate g r σ := by
  revert σ
  induction r with
  | zero =>
      intro σ
      simp
  | succ r ih =>
      intro σ
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv r (section43OneSidedLaplaceRaw g) =
            section43OneSidedLaplaceRawDerivCandidate g r := by
        ext u
        exact ih u
      rw [hfun]
      exact (section43OneSidedLaplaceRawDerivCandidate_hasDerivAt g r σ).deriv

theorem section43OneSidedLaplaceRaw_contDiff
    (g : Section43CompactPositiveTimeSource1D) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (section43OneSidedLaplaceRaw g) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro r _hr
  have hfun :
      iteratedDeriv r (section43OneSidedLaplaceRaw g) =
        section43OneSidedLaplaceRawDerivCandidate g r := by
    ext σ
    exact section43OneSidedLaplaceRaw_iteratedDeriv_formula g r σ
  rw [hfun]
  exact fun σ =>
    (section43OneSidedLaplaceRawDerivCandidate_hasDerivAt g r σ).differentiableAt

theorem section43OneSidedLaplaceRaw_iteratedFDeriv_formula
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ : ℝ) :
    iteratedFDeriv ℝ r (section43OneSidedLaplaceRaw g) σ =
      (ContinuousMultilinearMap.mkPiAlgebraFin ℝ r ℝ).smulRight
        (section43OneSidedLaplaceRawDerivCandidate g r σ) := by
  apply ContinuousMultilinearMap.ext
  intro m
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    section43OneSidedLaplaceRaw_iteratedDeriv_formula]
  change (∏ i, m i) • section43OneSidedLaplaceRawDerivCandidate g r σ =
    ((ContinuousMultilinearMap.mkPiAlgebraFin ℝ r ℝ) m) •
      section43OneSidedLaplaceRawDerivCandidate g r σ
  rw [ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  rw [List.prod_ofFn]

/-- If the exponential kernel has a real-part bound on the compact source
support, then the derivative-candidate integral has the corresponding scalar
norm bound. -/
theorem section43OneSidedLaplaceRawDerivCandidate_norm_le_of_re_bound
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ)
    {δ R σ E : ℝ}
    (hδ_pos : 0 < δ)
    (hsupp : tsupport (g.f : ℝ → ℂ) ⊆ Set.Icc δ R)
    (hRe : ∀ t : ℝ, g.f t ≠ 0 →
      (-(t : ℂ) * (σ : ℂ)).re ≤ E) :
    ‖section43OneSidedLaplaceRawDerivCandidate g r σ‖ ≤
      ((max |δ| |R|) ^ r * Real.exp E) * ∫ t : ℝ, ‖g.f t‖ := by
  let M : ℝ := max |δ| |R|
  let K : ℝ := M ^ r * Real.exp E
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact (abs_nonneg δ).trans (le_max_left |δ| |R|)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (pow_nonneg hM_nonneg r) (Real.exp_pos E).le
  have hpoint :
      ∀ t : ℝ,
        ‖((-t : ℂ) ^ r *
            Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t‖ ≤
          K * ‖g.f t‖ := by
    intro t
    by_cases htzero : g.f t = 0
    · simp [K, htzero]
    · have ht_supp : t ∈ tsupport (g.f : ℝ → ℂ) :=
        subset_tsupport _ htzero
      have htIcc : t ∈ Set.Icc δ R := hsupp ht_supp
      have htδ : δ ≤ t := htIcc.1
      have htR : t ≤ R := htIcc.2
      have ht_nonneg : 0 ≤ t := le_trans (le_of_lt hδ_pos) htδ
      have ht_abs_le : |t| ≤ M := by
        rw [abs_of_nonneg ht_nonneg]
        exact htR.trans ((le_abs_self R).trans (le_max_right |δ| |R|))
      have hpow_le : ‖(-t : ℂ) ^ r‖ ≤ M ^ r := by
        calc
          ‖(-t : ℂ) ^ r‖ = |t| ^ r := by
            rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ M ^ r := pow_le_pow_left₀ (abs_nonneg t) ht_abs_le r
      have hexp_le :
          ‖Complex.exp (-(t : ℂ) * (σ : ℂ))‖ ≤ Real.exp E := by
        rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (hRe t htzero)
      calc
        ‖((-t : ℂ) ^ r *
            Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t‖
            = ‖(-t : ℂ) ^ r‖ *
                ‖Complex.exp (-(t : ℂ) * (σ : ℂ))‖ * ‖g.f t‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ (M ^ r * Real.exp E) * ‖g.f t‖ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul hpow_le hexp_le (norm_nonneg _)
                  (pow_nonneg hM_nonneg r))
                (norm_nonneg (g.f t))
        _ = K * ‖g.f t‖ := by
              rfl
  have hleft_int :
      Integrable
        (fun t : ℝ =>
          ‖((-t : ℂ) ^ r *
            Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t‖) :=
    (section43OneSidedLaplaceRawDerivCandidate_integrable g r σ).norm
  have hright_int : Integrable (fun t : ℝ => K * ‖g.f t‖) :=
    g.f.integrable.norm.const_mul K
  calc
    ‖section43OneSidedLaplaceRawDerivCandidate g r σ‖
        ≤ ∫ t : ℝ,
            ‖((-t : ℂ) ^ r *
              Complex.exp (-(t : ℂ) * (σ : ℂ))) * g.f t‖ := by
          exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, K * ‖g.f t‖ := by
          exact integral_mono hleft_int hright_int hpoint
    _ = K * ∫ t : ℝ, ‖g.f t‖ := by
          rw [integral_const_mul]
    _ = ((max |δ| |R|) ^ r * Real.exp E) * ∫ t : ℝ, ‖g.f t‖ := by
          rfl

/-- Uniform bound for derivative candidates in the cutoff transition strip
`-1 ≤ σ ≤ 0`. -/
theorem section43OneSidedLaplaceRawDerivCandidate_norm_le_strip
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ)
    {δ R σ : ℝ}
    (hδ_pos : 0 < δ) (hδR : δ ≤ R)
    (hsupp : tsupport (g.f : ℝ → ℂ) ⊆ Set.Icc δ R)
    (hσ_lower : -1 ≤ σ) (hσ_nonpos : σ ≤ 0) :
    ‖section43OneSidedLaplaceRawDerivCandidate g r σ‖ ≤
      ((max |δ| |R|) ^ r * Real.exp R) * ∫ t : ℝ, ‖g.f t‖ := by
  refine section43OneSidedLaplaceRawDerivCandidate_norm_le_of_re_bound
    (g := g) (r := r) (δ := δ) (R := R) (σ := σ) (E := R)
    hδ_pos hsupp ?_
  intro t htzero
  have ht_supp : t ∈ tsupport (g.f : ℝ → ℂ) :=
    subset_tsupport _ htzero
  have htIcc : t ∈ Set.Icc δ R := hsupp ht_supp
  have htδ : δ ≤ t := htIcc.1
  have htR : t ≤ R := htIcc.2
  have ht_nonneg : 0 ≤ t := le_trans (le_of_lt hδ_pos) htδ
  have hR_pos : 0 < R := lt_of_lt_of_le hδ_pos hδR
  have hneg_nonneg : 0 ≤ -σ := by linarith
  have hneg_le_one : -σ ≤ 1 := by linarith
  have hre : (-(t : ℂ) * (σ : ℂ)).re = -(t * σ) := by
    simp [Complex.mul_re]
  rw [hre]
  calc
    -(t * σ) = t * (-σ) := by ring
    _ ≤ R * 1 := by
          exact mul_le_mul htR hneg_le_one hneg_nonneg (le_of_lt hR_pos)
    _ = R := by ring

/-- Exponential-decay bound for derivative candidates on the positive half-line. -/
theorem section43OneSidedLaplaceRawDerivCandidate_norm_le_nonneg
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ)
    {δ R σ : ℝ}
    (hδ_pos : 0 < δ)
    (hsupp : tsupport (g.f : ℝ → ℂ) ⊆ Set.Icc δ R)
    (hσ_nonneg : 0 ≤ σ) :
    ‖section43OneSidedLaplaceRawDerivCandidate g r σ‖ ≤
      ((max |δ| |R|) ^ r * Real.exp (-(δ * σ))) *
        ∫ t : ℝ, ‖g.f t‖ := by
  refine section43OneSidedLaplaceRawDerivCandidate_norm_le_of_re_bound
    (g := g) (r := r) (δ := δ) (R := R) (σ := σ) (E := -(δ * σ))
    hδ_pos hsupp ?_
  intro t htzero
  have ht_supp : t ∈ tsupport (g.f : ℝ → ℂ) :=
    subset_tsupport _ htzero
  have htIcc : t ∈ Set.Icc δ R := hsupp ht_supp
  have htδ : δ ≤ t := htIcc.1
  have hre : (-(t : ℂ) * (σ : ℂ)).re = -(t * σ) := by
    simp [Complex.mul_re]
  rw [hre]
  have hmul : δ * σ ≤ t * σ :=
    mul_le_mul_of_nonneg_right htδ hσ_nonneg
  linarith

/-- The raw compact one-sided Laplace transform has rapid decay on the support
of the cutoff derivatives, namely on `Set.Ici (-1)`. -/
theorem section43OneSidedLaplaceRaw_rapid_on_Ici_neg_one
    (g : Section43CompactPositiveTimeSource1D) :
    ∀ r s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ ∈ Set.Ici (-1 : ℝ),
        (1 + ‖σ‖) ^ s *
          ‖iteratedFDeriv ℝ r (section43OneSidedLaplaceRaw g) σ‖ ≤ C := by
  intro r s
  rcases exists_positive_Icc_bounds_of_compactPositiveTimeSource g with
    ⟨δ, R, hδ_pos, hδR, hsupp⟩
  rcases SCV.pow_mul_exp_neg_le_const hδ_pos s with
    ⟨C0, hC0_pos, hC0_bound⟩
  let M : ℝ := max |δ| |R|
  let I : ℝ := ∫ t : ℝ, ‖g.f t‖
  let Cstrip : ℝ := (2 : ℝ) ^ s * ((M ^ r * Real.exp R) * I)
  let Cpos : ℝ := (M ^ r * I) * (Real.exp δ * C0)
  let C : ℝ := Cstrip + Cpos
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact (abs_nonneg δ).trans (le_max_left |δ| |R|)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun t => norm_nonneg (g.f t)
  have hstripBase_nonneg : 0 ≤ (M ^ r * Real.exp R) * I := by
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hM_nonneg r) (Real.exp_pos R).le)
      hI_nonneg
  have hCstrip_nonneg : 0 ≤ Cstrip := by
    dsimp [Cstrip]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s)
      hstripBase_nonneg
  have hA_nonneg : 0 ≤ M ^ r * I := by
    exact mul_nonneg (pow_nonneg hM_nonneg r) hI_nonneg
  have hC0_nonneg : 0 ≤ C0 := le_of_lt hC0_pos
  have hCpos_nonneg : 0 ≤ Cpos := by
    dsimp [Cpos]
    exact mul_nonneg hA_nonneg
      (mul_nonneg (Real.exp_pos δ).le hC0_nonneg)
  refine ⟨C, add_nonneg hCstrip_nonneg hCpos_nonneg, ?_⟩
  intro σ hσ_mem
  have hσ_lower : -1 ≤ σ := by
    simpa [Set.mem_Ici] using hσ_mem
  have hF_norm :
      ‖iteratedFDeriv ℝ r (section43OneSidedLaplaceRaw g) σ‖ =
        ‖section43OneSidedLaplaceRawDerivCandidate g r σ‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      section43OneSidedLaplaceRaw_iteratedDeriv_formula]
  by_cases hσ_nonpos : σ ≤ 0
  · have hraw_bound :
        ‖section43OneSidedLaplaceRawDerivCandidate g r σ‖ ≤
          (M ^ r * Real.exp R) * I := by
      simpa [M, I] using
        section43OneSidedLaplaceRawDerivCandidate_norm_le_strip
          (g := g) (r := r) (δ := δ) (R := R) (σ := σ)
          hδ_pos hδR hsupp hσ_lower hσ_nonpos
    have hnorm_le_one : ‖σ‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨hσ_lower, by linarith⟩
    have hpoly_le : (1 + ‖σ‖) ^ s ≤ (2 : ℝ) ^ s := by
      exact pow_le_pow_left₀ (by positivity) (by linarith) s
    calc
      (1 + ‖σ‖) ^ s *
          ‖iteratedFDeriv ℝ r (section43OneSidedLaplaceRaw g) σ‖
          = (1 + ‖σ‖) ^ s *
              ‖section43OneSidedLaplaceRawDerivCandidate g r σ‖ := by
            rw [hF_norm]
      _ ≤ (1 + ‖σ‖) ^ s * ((M ^ r * Real.exp R) * I) := by
            exact mul_le_mul_of_nonneg_left hraw_bound (by positivity)
      _ ≤ (2 : ℝ) ^ s * ((M ^ r * Real.exp R) * I) := by
            exact mul_le_mul_of_nonneg_right hpoly_le hstripBase_nonneg
      _ = Cstrip := by
            rfl
      _ ≤ C := by
            dsimp [C]
            exact le_add_of_nonneg_right hCpos_nonneg
  · have hσ_nonneg : 0 ≤ σ := le_of_not_ge hσ_nonpos
    have hraw_bound :
        ‖section43OneSidedLaplaceRawDerivCandidate g r σ‖ ≤
          (M ^ r * Real.exp (-(δ * σ))) * I := by
      simpa [M, I] using
        section43OneSidedLaplaceRawDerivCandidate_norm_le_nonneg
          (g := g) (r := r) (δ := δ) (R := R) (σ := σ)
          hδ_pos hsupp hσ_nonneg
    have hposBase_nonneg :
        0 ≤ (M ^ r * Real.exp (-(δ * σ))) * I := by
      exact mul_nonneg
        (mul_nonneg (pow_nonneg hM_nonneg r)
          (Real.exp_pos (-(δ * σ))).le)
        hI_nonneg
    have htail :
        (1 + ‖σ‖) ^ s * Real.exp (-(δ * σ)) ≤
          Real.exp δ * C0 := by
      have hx_nonneg : 0 ≤ 1 + σ := by linarith
      have htail0 := hC0_bound (1 + σ) hx_nonneg
      have hexp_eq :
          Real.exp (-(δ * σ)) =
            Real.exp δ * Real.exp (-(δ * (1 + σ))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [Real.norm_eq_abs, abs_of_nonneg hσ_nonneg]
      calc
        (1 + σ) ^ s * Real.exp (-(δ * σ))
            = Real.exp δ *
                ((1 + σ) ^ s * Real.exp (-(δ * (1 + σ)))) := by
              rw [hexp_eq]
              ring
        _ ≤ Real.exp δ * C0 := by
              exact mul_le_mul_of_nonneg_left htail0 (Real.exp_pos δ).le
    calc
      (1 + ‖σ‖) ^ s *
          ‖iteratedFDeriv ℝ r (section43OneSidedLaplaceRaw g) σ‖
          = (1 + ‖σ‖) ^ s *
              ‖section43OneSidedLaplaceRawDerivCandidate g r σ‖ := by
            rw [hF_norm]
      _ ≤ (1 + ‖σ‖) ^ s *
            ((M ^ r * Real.exp (-(δ * σ))) * I) := by
            exact mul_le_mul_of_nonneg_left hraw_bound (by positivity)
      _ = (M ^ r * I) *
            ((1 + ‖σ‖) ^ s * Real.exp (-(δ * σ))) := by
            ring
      _ ≤ (M ^ r * I) * (Real.exp δ * C0) := by
            exact mul_le_mul_of_nonneg_left htail hA_nonneg
      _ = Cpos := by
            rfl
      _ ≤ C := by
            dsimp [C]
            exact le_add_of_nonneg_left hCstrip_nonneg

/-- The cutoff product is the ambient Schwartz representative of the compact
one-sided Laplace transform. -/
noncomputable def section43OneSidedLaplaceSchwartzRepresentative1D
    (g : Section43CompactPositiveTimeSource1D) : SchwartzMap ℝ ℂ :=
  schwartzMap_of_temperate_mul_rapid_on_derivSupport
    (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ))
    (section43OneSidedLaplaceRaw g)
    (Set.Ici (-1 : ℝ))
    SCV.smoothCutoff_complex_hasTemperateGrowth
    section43SmoothCutoff_complex_iteratedFDeriv_support_subset_Ici_neg_one
    (section43OneSidedLaplaceRaw_contDiff g)
    (section43OneSidedLaplaceRaw_rapid_on_Ici_neg_one g)

@[simp] theorem section43OneSidedLaplaceSchwartzRepresentative1D_apply
    (g : Section43CompactPositiveTimeSource1D) (σ : ℝ) :
    section43OneSidedLaplaceSchwartzRepresentative1D g σ =
      section43OneSidedLaplaceCutoffFun g σ := rfl

theorem exists_section43OneSidedLaplaceRepresentative1D
    (g : Section43CompactPositiveTimeSource1D) :
    ∃ Φ : SchwartzMap ℝ ℂ,
      section43OneSidedLaplaceRepresentative1D g Φ := by
  refine ⟨section43OneSidedLaplaceSchwartzRepresentative1D g, ?_⟩
  intro σ hσ
  rw [section43OneSidedLaplaceSchwartzRepresentative1D_apply,
    section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg g hσ]
  rfl

/-- Compact strict-positive one-sided Laplace sources as elements of the
one-dimensional positive-energy quotient. -/
noncomputable def section43OneSidedLaplaceCompactTransform1D :
    Section43CompactPositiveTimeSource1D → Section43PositiveEnergy1D :=
  fun g =>
    section43PositiveEnergyQuotientMap1D
      (Classical.choose (exists_section43OneSidedLaplaceRepresentative1D g))

theorem section43OneSidedLaplaceCompactTransform1D_choose_spec
    (g : Section43CompactPositiveTimeSource1D) :
    section43OneSidedLaplaceRepresentative1D g
      (Classical.choose (exists_section43OneSidedLaplaceRepresentative1D g)) :=
  Classical.choose_spec (exists_section43OneSidedLaplaceRepresentative1D g)

/-- The abstractly chosen compact transform is represented by the explicit
cutoff-Schwartz representative. -/
theorem section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient
    (g : Section43CompactPositiveTimeSource1D) :
    section43OneSidedLaplaceCompactTransform1D g =
      section43PositiveEnergyQuotientMap1D
        (section43OneSidedLaplaceSchwartzRepresentative1D g) := by
  dsimp [section43OneSidedLaplaceCompactTransform1D]
  apply section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
  intro σ hσ
  calc
    Classical.choose (exists_section43OneSidedLaplaceRepresentative1D g) σ
        = ∫ t : ℝ,
            Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t :=
          section43OneSidedLaplaceCompactTransform1D_choose_spec g σ hσ
    _ = section43OneSidedLaplaceSchwartzRepresentative1D g σ := by
          rw [section43OneSidedLaplaceSchwartzRepresentative1D_apply,
            section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg g hσ]
          rfl

/-- Local name for Mathlib's inverse Fourier continuous linear map on
one-dimensional Schwartz space. -/
noncomputable def section43FourierInvCLM1D :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)

@[simp] theorem section43FourierInvCLM1D_apply
    (φ : SchwartzMap ℝ ℂ) :
    section43FourierInvCLM1D φ = FourierTransform.fourierInv φ := rfl

/-- Turn a continuous functional on the half-line quotient into a tempered
functional with one-sided Fourier support by precomposing with inverse Fourier
transform. -/
noncomputable def section43PositiveEnergy1D_to_oneSidedFourierFunctional
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  (A.comp section43PositiveEnergyQuotientMap1D).comp
    section43FourierInvCLM1D

/-- The inverse-Fourier pullback of a half-line quotient functional has
one-sided Fourier support. -/
theorem section43PositiveEnergy1D_to_oneSidedFourierFunctional_support
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    SCV.HasOneSidedFourierSupport
      (section43PositiveEnergy1D_to_oneSidedFourierFunctional A) := by
  intro φ hφ
  dsimp [section43PositiveEnergy1D_to_oneSidedFourierFunctional,
    section43FourierInvCLM1D]
  rw [FourierTransform.fourierInv_fourier_eq]
  have hEqOn : Set.EqOn (φ : ℝ → ℂ) (0 : ℝ → ℂ) (Set.Ici (0 : ℝ)) := by
    intro x hx
    by_contra hne
    have hx_supp : x ∈ Function.support (φ : ℝ → ℂ) := by
      simpa [Function.mem_support] using hne
    have hx_neg := hφ x hx_supp
    exact (not_lt_of_ge hx) hx_neg
  have hqzero : section43PositiveEnergyQuotientMap1D φ = 0 := by
    have hsub :=
      section43PositiveEnergyQuotientMap1D_sub_eq_zero_of_eqOn_nonneg
        (f := φ) (g := 0) hEqOn
    simpa using hsub
  rw [hqzero]
  simp

/-- Descending the inverse-Fourier pullback functional recovers the original
half-line quotient functional. -/
theorem fourierPairingDescendsToSection43PositiveEnergy1D_to_oneSided
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    fourierPairingDescendsToSection43PositiveEnergy1D
        (section43PositiveEnergy1D_to_oneSidedFourierFunctional A)
        (section43PositiveEnergy1D_to_oneSidedFourierFunctional_support A)
      = A := by
  ext u
  obtain ⟨φ, hφ⟩ := surjective_section43PositiveEnergyQuotientMap1D u
  rw [← hφ]
  rw [fourierPairingDescendsToSection43PositiveEnergy1D_apply]
  dsimp [section43PositiveEnergy1D_to_oneSidedFourierFunctional,
    section43FourierInvCLM1D]
  rw [FourierTransform.fourierInv_fourier_eq]

/-- Fourier-Laplace transform of a half-line quotient functional, expressed via
the existing `SCV.schwartzPsiZ` kernel. -/
noncomputable def section43OneSidedAnnihilatorFL
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (z : ℂ) (hz : 0 < z.im) : ℂ :=
  A (section43PositiveEnergyQuotientMap1D (SCV.schwartzPsiZ z hz))

theorem section43OneSidedAnnihilatorFL_eq_fourierLaplaceExt_to_oneSided
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (z : ℂ) (hz : 0 < z.im) :
    section43OneSidedAnnihilatorFL A z hz =
      SCV.fourierLaplaceExt
        (section43PositiveEnergy1D_to_oneSidedFourierFunctional A) z hz := by
  rw [SCV.fourierLaplaceExt_eq]
  dsimp [section43OneSidedAnnihilatorFL,
    section43PositiveEnergy1D_to_oneSidedFourierFunctional,
    section43FourierInvCLM1D]
  rw [FourierTransform.fourierInv_fourier_eq]

/-- Imaginary-axis version of `section43OneSidedAnnihilatorFL`, with an
off-half-line zero branch to avoid dependent positivity proofs inside
integrals. -/
noncomputable def section43OneSidedAnnihilatorFLOnImag
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (t : ℝ) : ℂ :=
  if ht : 0 < t then
    section43OneSidedAnnihilatorFL A ((t : ℂ) * Complex.I)
      (by simpa using ht)
  else
    0

/-- Imaginary-axis Paley-Wiener kernel, with a zero branch off the strict
positive half-line. -/
noncomputable def section43ImagAxisPsiKernel (t : ℝ) : SchwartzMap ℝ ℂ :=
  if ht : 0 < t then
    SCV.schwartzPsiZ ((t : ℂ) * Complex.I)
      (by simpa [Complex.mul_im] using ht)
  else
    0

@[simp] theorem section43ImagAxisPsiKernel_of_pos
    {t : ℝ} (ht : 0 < t) :
    section43ImagAxisPsiKernel t =
      SCV.schwartzPsiZ ((t : ℂ) * Complex.I)
        (by simpa [Complex.mul_im] using ht) := by
  simp [section43ImagAxisPsiKernel, ht]

theorem section43ImagAxisPsiKernel_of_not_pos
    {t : ℝ} (ht : ¬ 0 < t) :
    section43ImagAxisPsiKernel t = 0 := by
  simp [section43ImagAxisPsiKernel, ht]

@[simp] theorem section43ImagAxisPsiKernel_apply_of_not_pos
    {t σ : ℝ} (ht : ¬ 0 < t) :
    section43ImagAxisPsiKernel t σ = 0 := by
  rw [section43ImagAxisPsiKernel_of_not_pos ht]
  rfl

theorem section43ImagAxisPsiKernel_apply_of_pos_of_nonneg
    {t σ : ℝ} (ht : 0 < t) (hσ : 0 ≤ σ) :
    section43ImagAxisPsiKernel t σ =
      Complex.exp (-(t : ℂ) * (σ : ℂ)) := by
  rw [section43ImagAxisPsiKernel_of_pos ht, SCV.schwartzPsiZ_apply,
    SCV.psiZ_eq_exp_of_nonneg hσ]
  congr 1
  calc
    Complex.I * ((t : ℂ) * Complex.I) * (σ : ℂ)
        = (Complex.I * Complex.I) * (t : ℂ) * (σ : ℂ) := by ring
    _ = -(t : ℂ) * (σ : ℂ) := by
          rw [Complex.I_mul_I]
          ring

theorem section43ImagAxisPsiKernel_apply_mul_source_of_nonneg
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    section43ImagAxisPsiKernel t σ * g.f t =
      Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t := by
  by_cases ht : 0 < t
  · rw [section43ImagAxisPsiKernel_apply_of_pos_of_nonneg ht hσ]
  · rw [section43ImagAxisPsiKernel_apply_of_not_pos ht,
      g.eq_zero_of_not_pos ht]
    simp

theorem section43ImagAxisPsiKernel_apply_mul_source
    (g : Section43CompactPositiveTimeSource1D)
    (σ t : ℝ) :
    section43ImagAxisPsiKernel t σ * g.f t =
      (SCV.smoothCutoff σ : ℂ) *
        (Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t) := by
  by_cases ht : 0 < t
  · rw [section43ImagAxisPsiKernel_of_pos ht, SCV.schwartzPsiZ_apply]
    simp only [SCV.psiZ_eq]
    have harg :
        Complex.I * ((t : ℂ) * Complex.I) * (σ : ℂ) =
          -(t : ℂ) * (σ : ℂ) := by
      calc
        Complex.I * ((t : ℂ) * Complex.I) * (σ : ℂ)
            = (Complex.I * Complex.I) * (t : ℂ) * (σ : ℂ) := by ring
        _ = -(t : ℂ) * (σ : ℂ) := by
              rw [Complex.I_mul_I]
              ring
    rw [harg]
    ring
  · rw [section43ImagAxisPsiKernel_apply_of_not_pos ht,
      g.eq_zero_of_not_pos ht]
    simp

theorem section43OneSidedLaplaceCutoffFun_eq_integral_imagAxisPsiKernel
    (g : Section43CompactPositiveTimeSource1D)
    (σ : ℝ) :
    section43OneSidedLaplaceCutoffFun g σ =
      ∫ t : ℝ, section43ImagAxisPsiKernel t σ * g.f t := by
  unfold section43OneSidedLaplaceCutoffFun section43OneSidedLaplaceRaw
  calc
    (SCV.smoothCutoff σ : ℂ) *
        ∫ t : ℝ, Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t
        = ∫ t : ℝ,
            (SCV.smoothCutoff σ : ℂ) *
              (Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t) := by
            simpa using
              (MeasureTheory.integral_const_mul
                (SCV.smoothCutoff σ : ℂ)
                (fun t : ℝ =>
                  Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t)).symm
    _ = ∫ t : ℝ, section43ImagAxisPsiKernel t σ * g.f t := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with t
          exact (section43ImagAxisPsiKernel_apply_mul_source g σ t).symm

theorem section43OneSidedLaplaceRaw_eq_integral_imagAxisPsiKernel_of_nonneg
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    section43OneSidedLaplaceRaw g σ =
      ∫ t : ℝ, section43ImagAxisPsiKernel t σ * g.f t := by
  unfold section43OneSidedLaplaceRaw
  refine (MeasureTheory.integral_congr_ae ?_).symm
  filter_upwards with t
  exact section43ImagAxisPsiKernel_apply_mul_source_of_nonneg g hσ t

theorem section43OneSidedLaplaceSchwartzRepresentative1D_eq_integral_imagAxisPsiKernel_of_nonneg
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    section43OneSidedLaplaceSchwartzRepresentative1D g σ =
      ∫ t : ℝ, section43ImagAxisPsiKernel t σ * g.f t := by
  rw [section43OneSidedLaplaceSchwartzRepresentative1D_apply,
    section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg g hσ,
    section43OneSidedLaplaceRaw_eq_integral_imagAxisPsiKernel_of_nonneg g hσ]

theorem section43OneSidedLaplaceSchwartzRepresentative1D_eq_integral_imagAxisPsiKernel
    (g : Section43CompactPositiveTimeSource1D)
    (σ : ℝ) :
    section43OneSidedLaplaceSchwartzRepresentative1D g σ =
      ∫ t : ℝ, section43ImagAxisPsiKernel t σ * g.f t := by
  rw [section43OneSidedLaplaceSchwartzRepresentative1D_apply,
    section43OneSidedLaplaceCutoffFun_eq_integral_imagAxisPsiKernel]

theorem section43OneSidedLaplaceSchwartzRepresentative1D_iteratedDeriv_formula
    (g : Section43CompactPositiveTimeSource1D) (n : ℕ) (σ : ℝ) :
    iteratedDeriv n (section43OneSidedLaplaceSchwartzRepresentative1D g) σ =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i *
          iteratedDeriv i (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ *
            section43OneSidedLaplaceRawDerivCandidate g (n - i) σ := by
  have hχ :
      ContDiffAt ℝ n (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ := by
    have hχ_smooth :
        ContDiff ℝ (↑(⊤ : ℕ∞)) (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) := by
      simpa using (Complex.ofRealCLM.contDiff.comp SCV.smoothCutoff_contDiff)
    exact (hχ_smooth.contDiffAt.of_le
      (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
        exact mod_cast le_top))
  have hraw :
      ContDiffAt ℝ n (section43OneSidedLaplaceRaw g) σ := by
    exact ((section43OneSidedLaplaceRaw_contDiff g).contDiffAt.of_le
      (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
        exact mod_cast le_top))
  change iteratedDeriv n
      (fun σ : ℝ =>
        (SCV.smoothCutoff σ : ℂ) * section43OneSidedLaplaceRaw g σ) σ = _
  have hmul :=
    iteratedDeriv_mul (x := σ) hχ hraw
  have hmul' :
      iteratedDeriv n
          (fun σ : ℝ =>
            (SCV.smoothCutoff σ : ℂ) * section43OneSidedLaplaceRaw g σ) σ =
        ∑ i ∈ Finset.range (n + 1),
          n.choose i *
            iteratedDeriv i (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ *
              iteratedDeriv (n - i) (section43OneSidedLaplaceRaw g) σ := by
    simpa only [Pi.mul_apply] using hmul
  rw [hmul']
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [section43OneSidedLaplaceRaw_iteratedDeriv_formula]

theorem section43ImagAxisPsiKernel_iteratedDeriv_mul_source
    (g : Section43CompactPositiveTimeSource1D)
    (n : ℕ) (σ t : ℝ) :
    iteratedDeriv n (fun σ : ℝ => section43ImagAxisPsiKernel t σ) σ *
        g.f t =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i *
          iteratedDeriv i (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ *
            ((-(t : ℂ)) ^ (n - i) *
              Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t) := by
  by_cases ht : 0 < t
  · have hχ :
        ContDiffAt ℝ n (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ := by
      have hχ_smooth :
          ContDiff ℝ (↑(⊤ : ℕ∞)) (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) := by
        simpa using (Complex.ofRealCLM.contDiff.comp SCV.smoothCutoff_contDiff)
      exact (hχ_smooth.contDiffAt.of_le
        (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
          exact mod_cast le_top))
    have he :
        ContDiffAt ℝ n
          (fun σ : ℝ => Complex.exp (-(t : ℂ) * (σ : ℂ))) σ := by
      have he_smooth :
          ContDiff ℝ (↑(⊤ : ℕ∞))
            (fun σ : ℝ => Complex.exp (-(t : ℂ) * (σ : ℂ))) := by
        have hcoef :
            ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : ℝ => -(t : ℂ)) :=
          contDiff_const
        have hofReal :
            ContDiff ℝ (↑(⊤ : ℕ∞)) (fun σ : ℝ => (σ : ℂ)) :=
          Complex.ofRealCLM.contDiff
        exact Complex.contDiff_exp.comp (hcoef.mul hofReal)
      exact (he_smooth.contDiffAt.of_le
        (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
          exact mod_cast le_top))
    have hkernel :
        (fun σ : ℝ => section43ImagAxisPsiKernel t σ) =
          fun σ : ℝ =>
            (SCV.smoothCutoff σ : ℂ) *
              Complex.exp (-(t : ℂ) * (σ : ℂ)) := by
      funext σ'
      rw [section43ImagAxisPsiKernel_of_pos ht, SCV.schwartzPsiZ_apply,
        SCV.psiZ_eq]
      have harg :
          Complex.I * ((t : ℂ) * Complex.I) * (σ' : ℂ) =
            -(t : ℂ) * (σ' : ℂ) := by
        calc
          Complex.I * ((t : ℂ) * Complex.I) * (σ' : ℂ)
              = (Complex.I * Complex.I) * (t : ℂ) * (σ' : ℂ) := by ring
          _ = -(t : ℂ) * (σ' : ℂ) := by
                rw [Complex.I_mul_I]
                ring
      rw [harg]
    rw [hkernel]
    have hmul :=
      iteratedDeriv_mul (x := σ) hχ he
    have hmul' :
        iteratedDeriv n
            (fun σ : ℝ =>
              (SCV.smoothCutoff σ : ℂ) *
                Complex.exp (-(t : ℂ) * (σ : ℂ))) σ =
          ∑ i ∈ Finset.range (n + 1),
            n.choose i *
              iteratedDeriv i (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ *
                iteratedDeriv (n - i)
                  (fun σ : ℝ => Complex.exp (-(t : ℂ) * (σ : ℂ))) σ := by
      simpa only [Pi.mul_apply] using hmul
    rw [hmul']
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hexp :
        iteratedDeriv (n - i)
            (fun σ : ℝ => Complex.exp (-(t : ℂ) * (σ : ℂ))) σ =
          (-(t : ℂ)) ^ (n - i) *
            Complex.exp (-(t : ℂ) * (σ : ℂ)) := by
      simpa using
        congrFun (SCV.iteratedDeriv_cexp_const_mul_real (n - i) (-(t : ℂ))) σ
    rw [hexp]
    ring
  · rw [section43ImagAxisPsiKernel_of_not_pos ht,
      g.eq_zero_of_not_pos ht]
    simp

theorem section43OneSidedLaplaceSchwartzRepresentative1D_iteratedDeriv_eq_integral_kernel_iteratedDeriv
    (g : Section43CompactPositiveTimeSource1D) (n : ℕ) (σ : ℝ) :
    iteratedDeriv n (section43OneSidedLaplaceSchwartzRepresentative1D g) σ =
      ∫ t : ℝ,
        iteratedDeriv n (fun σ : ℝ => section43ImagAxisPsiKernel t σ) σ *
          g.f t := by
  classical
  let χ : ℕ → ℂ := fun i =>
    n.choose i *
      iteratedDeriv i (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ
  let K : ℕ → ℝ → ℂ := fun i t =>
    (-(t : ℂ)) ^ (n - i) *
      Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t
  have hterm_int :
      ∀ i ∈ Finset.range (n + 1),
        Integrable (fun t : ℝ => χ i * K i t) := by
    intro i hi
    have hbase := section43OneSidedLaplaceRawDerivCandidate_integrable
      (g := g) (r := n - i) (σ := σ)
    simpa [K, mul_assoc] using hbase.const_mul (χ i)
  have hkernel_integral :
      (∫ t : ℝ,
        iteratedDeriv n (fun σ : ℝ => section43ImagAxisPsiKernel t σ) σ *
          g.f t) =
        ∫ t : ℝ, ∑ i ∈ Finset.range (n + 1), χ i * K i t := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    have hpoint :=
      section43ImagAxisPsiKernel_iteratedDeriv_mul_source
        (g := g) (n := n) (σ := σ) (t := t)
    simpa [χ, K, mul_assoc] using hpoint
  rw [section43OneSidedLaplaceSchwartzRepresentative1D_iteratedDeriv_formula]
  rw [hkernel_integral]
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    unfold section43OneSidedLaplaceRawDerivCandidate
    calc
      n.choose i *
          iteratedDeriv i (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ *
            ∫ t : ℝ,
              (-(t : ℂ)) ^ (n - i) *
                Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t
          = χ i * ∫ t : ℝ, K i t := by
            rfl
      _ = ∫ t : ℝ, χ i * K i t := by
            simpa using
              (MeasureTheory.integral_const_mul
                (χ i) (fun t : ℝ => K i t)).symm
  · intro i hi
    exact hterm_int i hi

/-- Polynomial weight used in the finite-probe reduction of Schwartz
functionals. -/
def section43PolyWeight (k : ℕ) (σ : ℝ) : ℂ := ((1 + σ ^ 2) ^ k : ℝ)

theorem section43PolyWeight_hasTemperateGrowth (k : ℕ) :
    (section43PolyWeight k).HasTemperateGrowth := by
  unfold section43PolyWeight
  fun_prop

/-- Continuous linear map sending a Schwartz function to its `n`th derivative,
as a Schwartz function. -/
noncomputable def section43IteratedDerivCLM :
    ℕ → SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ
  | 0 => ContinuousLinearMap.id ℂ _
  | n + 1 => (SchwartzMap.derivCLM ℂ ℂ).comp (section43IteratedDerivCLM n)

theorem section43IteratedDerivCLM_apply
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (σ : ℝ) :
    section43IteratedDerivCLM n f σ = iteratedDeriv n f σ := by
  induction n generalizing f σ with
  | zero => simp [section43IteratedDerivCLM]
  | succ n ih =>
      have hf : ⇑(section43IteratedDerivCLM n f) =
          fun y : ℝ => iteratedDeriv n f y := by
        ext y
        exact ih f y
      rw [section43IteratedDerivCLM, ContinuousLinearMap.comp_apply,
        SchwartzMap.derivCLM_apply]
      rw [hf, ← iteratedDeriv_succ]

/-- Weighted derivative probe into bounded continuous functions. -/
noncomputable def section43WeightedDerivToBCFCLM
    (k n : ℕ) : SchwartzMap ℝ ℂ →L[ℂ] ℝ →ᵇ ℂ :=
  (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).comp <|
    (SchwartzMap.smulLeftCLM ℂ (section43PolyWeight k)).comp <|
      section43IteratedDerivCLM n

theorem section43WeightedDerivToBCFCLM_apply
    (k n : ℕ) (f : SchwartzMap ℝ ℂ) (σ : ℝ) :
    section43WeightedDerivToBCFCLM k n f σ =
      section43PolyWeight k σ * iteratedDeriv n f σ := by
  rw [section43WeightedDerivToBCFCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (section43PolyWeight_hasTemperateGrowth k),
    section43IteratedDerivCLM_apply]
  simp [section43PolyWeight]

theorem section43_abs_pow_le_polyWeight (k : ℕ) (σ : ℝ) :
    |σ| ^ k ≤ ‖section43PolyWeight k σ‖ := by
  rw [section43PolyWeight, Complex.norm_real]
  have h1 : |σ| ≤ 1 + σ ^ 2 := by
    have hσ2_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
    nlinarith [sq_abs σ]
  calc
    |σ| ^ k ≤ (1 + σ ^ 2) ^ k := by
      exact pow_le_pow_left₀ (abs_nonneg σ) h1 k
    _ = ‖((1 + σ ^ 2) ^ k : ℝ)‖ := by
      rw [Real.norm_of_nonneg]
      positivity

/-- Finite product of weighted derivative probes.  This is the Banach-valued
target where the later parameter integral is legal. -/
noncomputable def section43ProbeCLM (s : Finset (ℕ × ℕ)) :
    SchwartzMap ℝ ℂ →L[ℂ] ((p : ↑s.attach) → (ℝ →ᵇ ℂ)) :=
  ContinuousLinearMap.pi fun p : ↑s.attach =>
    section43WeightedDerivToBCFCLM p.1.1.1 p.1.1.2

set_option backward.isDefEq.respectTransparency false in
theorem section43SchwartzSeminorm_le_probe_component_norm
    (k n : ℕ) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.seminorm ℝ k n f ≤
      ‖section43WeightedDerivToBCFCLM k n f‖ := by
  refine SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) k n f (norm_nonneg _) ?_
  intro σ
  have h1 :
      |σ| ^ k * ‖iteratedDeriv n f σ‖ ≤
        ‖section43PolyWeight k σ‖ * ‖iteratedDeriv n f σ‖ := by
    exact mul_le_mul_of_nonneg_right
      (section43_abs_pow_le_polyWeight k σ) (norm_nonneg _)
  calc
    |σ| ^ k * ‖iteratedDeriv n f σ‖
        ≤ ‖section43PolyWeight k σ‖ * ‖iteratedDeriv n f σ‖ := h1
    _ = ‖section43PolyWeight k σ * iteratedDeriv n f σ‖ := by
          rw [norm_mul]
    _ = ‖section43WeightedDerivToBCFCLM k n f σ‖ := by
          rw [section43WeightedDerivToBCFCLM_apply]
    _ ≤ ‖section43WeightedDerivToBCFCLM k n f‖ := by
          simpa using
            (BoundedContinuousFunction.norm_coe_le_norm
              (section43WeightedDerivToBCFCLM k n f) σ)

set_option backward.isDefEq.respectTransparency false in
theorem section43SchwartzSeminorm_le_probe_norm
    (s : Finset (ℕ × ℕ)) (p : ↑s.attach) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.seminorm ℝ p.1.1.1 p.1.1.2 f ≤
      ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
  calc
    SchwartzMap.seminorm ℝ p.1.1.1 p.1.1.2 f
        ≤ ‖section43WeightedDerivToBCFCLM p.1.1.1 p.1.1.2 f‖ :=
          section43SchwartzSeminorm_le_probe_component_norm
            p.1.1.1 p.1.1.2 f
    _ ≤ ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
          simpa [section43ProbeCLM] using
            (norm_le_pi_norm
              (section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ))) p)

set_option backward.isDefEq.respectTransparency false in
theorem section43SchwartzFunctional_bound_by_probeNorm
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      ∀ f : SchwartzMap ℝ ℂ,
        ‖T f‖ ≤
          (C : ℝ) *
            ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
  classical
  obtain ⟨s, C0, hC0, hbound⟩ := SCV.schwartz_functional_bound T
  refine ⟨s, C0 * (s.card + 1), by
    refine mul_ne_zero hC0 ?_
    exact_mod_cast Nat.succ_ne_zero s.card, ?_⟩
  intro f
  have hsup_sum :
      (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤
        (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) f := by
    exact Seminorm.le_def.mp
      (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℂ ℝ ℂ) s) f
  have hsum_apply_all :
      ∀ s' : Finset (ℕ × ℕ),
        (∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p) f =
          ∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p f := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        simp
    | insert a s' ha ih =>
        simp [Finset.sum_insert, ha, ih]
  have hsum_apply :
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) f =
        ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p f := hsum_apply_all s
  have hsum_probe :
      ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p f ≤
        s.card *
          ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
    calc
      ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p f
          ≤ ∑ _p ∈ s,
              ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
              refine Finset.sum_le_sum ?_
              intro a ha
              let p : ↑s.attach := ⟨⟨a, ha⟩, by simp⟩
              simpa [schwartzSeminormFamily, p] using
                section43SchwartzSeminorm_le_probe_norm s p f
      _ = s.card *
            ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
            simp
  calc
    ‖T f‖ ≤ (C0 • s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := hbound f
    _ = (C0 : ℝ) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by rfl
    _ ≤ (C0 : ℝ) *
          ((∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) f) := by
        exact mul_le_mul_of_nonneg_left hsup_sum C0.coe_nonneg
    _ = (C0 : ℝ) *
          (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p f) := by
        rw [hsum_apply]
    _ ≤ (C0 : ℝ) *
          (s.card *
            ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖) := by
        exact mul_le_mul_of_nonneg_left hsum_probe C0.coe_nonneg
    _ ≤ (C0 : ℝ) *
          ((s.card + 1 : ℝ) *
            ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖) := by
        have hcard : (s.card : ℝ) ≤ s.card + 1 := by
          exact_mod_cast Nat.le_succ s.card
        have hnorm :=
          norm_nonneg (section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))
        have hcardnorm :
            (s.card : ℝ) *
                ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ ≤
              (s.card + 1 : ℝ) *
                ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
          exact mul_le_mul_of_nonneg_right hcard hnorm
        exact mul_le_mul_of_nonneg_left hcardnorm C0.coe_nonneg
    _ = ((C0 * (s.card + 1) : NNReal) : ℝ) *
          ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
        rw [NNReal.coe_mul]
        norm_num
        ring

private noncomputable def section43RangeLiftLinear
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ))
    (hker :
      LinearMap.ker (section43ProbeCLM s).toLinearMap ≤
        LinearMap.ker T.toLinearMap) :
    LinearMap.range (section43ProbeCLM s).toLinearMap →ₗ[ℂ] ℂ :=
  ((LinearMap.ker (section43ProbeCLM s).toLinearMap).liftQ
      T.toLinearMap hker).comp
    ((section43ProbeCLM s).toLinearMap.quotKerEquivRange.symm.toLinearMap)

private theorem section43RangeLiftLinear_apply
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ))
    (hker :
      LinearMap.ker (section43ProbeCLM s).toLinearMap ≤
        LinearMap.ker T.toLinearMap)
    (f : SchwartzMap ℝ ℂ) :
    section43RangeLiftLinear T s hker
        ⟨section43ProbeCLM s f, LinearMap.mem_range_self _ f⟩ = T f := by
  change
    ((LinearMap.ker (section43ProbeCLM s).toLinearMap).liftQ
        T.toLinearMap hker)
      (((section43ProbeCLM s).toLinearMap.quotKerEquivRange.symm)
        ⟨section43ProbeCLM s f, LinearMap.mem_range_self _ f⟩) = T f
  have hsymm :
      ((section43ProbeCLM s).toLinearMap.quotKerEquivRange.symm)
          ⟨section43ProbeCLM s f, LinearMap.mem_range_self _ f⟩ =
        (LinearMap.ker (section43ProbeCLM s).toLinearMap).mkQ f := by
    simpa using
      (LinearMap.quotKerEquivRange_symm_apply_image
        ((section43ProbeCLM s).toLinearMap) f
        (LinearMap.mem_range_self _ f))
  rw [hsymm]
  simp

private theorem section43RangeLiftLinear_bound
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ))
    (C : NNReal)
    (hbound : ∀ f : SchwartzMap ℝ ℂ,
      ‖T f‖ ≤
        (C : ℝ) *
          ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖)
    (hker :
      LinearMap.ker (section43ProbeCLM s).toLinearMap ≤
        LinearMap.ker T.toLinearMap) :
    ∀ y, ‖section43RangeLiftLinear T s hker y‖ ≤ (C : ℝ) * ‖y‖ := by
  intro y
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨f, rfl⟩
  simpa [section43RangeLiftLinear_apply] using hbound f

/-- Any continuous Schwartz functional factors through finitely many weighted
derivative probes landing in a Banach finite product.  This is the finite
normed replacement for the unavailable `SchwartzMap`-valued Bochner integral. -/
theorem section43_exists_probe_factorization
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ),
    ∃ G : ((p : ↑s.attach) → (ℝ →ᵇ ℂ)) →L[ℂ] ℂ,
      T = G.comp (section43ProbeCLM s) := by
  classical
  obtain ⟨s, C, _hC, hbound⟩ :=
    section43SchwartzFunctional_bound_by_probeNorm T
  have hker :
      LinearMap.ker (section43ProbeCLM s).toLinearMap ≤
        LinearMap.ker T.toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply norm_eq_zero.mp
    apply le_antisymm
    · calc
        ‖T f‖ ≤
            (C : ℝ) *
              ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ :=
              hbound f
        _ = 0 := by
          have hfnorm :
              ‖(section43ProbeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ = 0 := by
            simpa using congrArg norm hf
          rw [hfnorm, mul_zero]
    · exact norm_nonneg _
  let FrangeLin :
      LinearMap.range (section43ProbeCLM s).toLinearMap →ₗ[ℂ] ℂ :=
    section43RangeLiftLinear T s hker
  let Frange :
      StrongDual ℂ (LinearMap.range (section43ProbeCLM s).toLinearMap) :=
    FrangeLin.mkContinuous (C : ℝ)
      (section43RangeLiftLinear_bound T s C hbound hker)
  obtain ⟨G, hGext, _⟩ :=
    exists_extension_norm_eq
      (LinearMap.range (section43ProbeCLM s).toLinearMap) Frange
  refine ⟨s, G, ?_⟩
  ext f
  have hmem : section43ProbeCLM s f ∈
      LinearMap.range (section43ProbeCLM s).toLinearMap :=
    LinearMap.mem_range_self _ f
  change T f = G (section43ProbeCLM s f)
  calc
    T f = FrangeLin ⟨section43ProbeCLM s f, hmem⟩ := by
      exact (section43RangeLiftLinear_apply T s hker f).symm
    _ = Frange ⟨section43ProbeCLM s f, hmem⟩ := by
      rfl
    _ = G (section43ProbeCLM s f) := by
      symm
      exact hGext ⟨section43ProbeCLM s f, hmem⟩

theorem section43WeightedDerivToBCFCLM_representative_eq_integral_kernel_apply
    (g : Section43CompactPositiveTimeSource1D)
    (k n : ℕ) (σ : ℝ) :
    section43WeightedDerivToBCFCLM k n
        (section43OneSidedLaplaceSchwartzRepresentative1D g) σ =
      ∫ t : ℝ,
        g.f t *
          section43WeightedDerivToBCFCLM k n
            (section43ImagAxisPsiKernel t) σ := by
  rw [section43WeightedDerivToBCFCLM_apply]
  rw [section43OneSidedLaplaceSchwartzRepresentative1D_iteratedDeriv_eq_integral_kernel_iteratedDeriv]
  calc
    section43PolyWeight k σ *
        ∫ t : ℝ,
          iteratedDeriv n
              (fun σ : ℝ => section43ImagAxisPsiKernel t σ) σ *
            g.f t
        =
          ∫ t : ℝ,
            section43PolyWeight k σ *
              (iteratedDeriv n
                  (fun σ : ℝ => section43ImagAxisPsiKernel t σ) σ *
                g.f t) := by
          simpa using
            (MeasureTheory.integral_const_mul
              (section43PolyWeight k σ)
              (fun t : ℝ =>
                iteratedDeriv n
                    (fun σ : ℝ => section43ImagAxisPsiKernel t σ) σ *
                  g.f t)).symm
    _ =
        ∫ t : ℝ,
          g.f t *
            section43WeightedDerivToBCFCLM k n
              (section43ImagAxisPsiKernel t) σ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with t
          rw [section43WeightedDerivToBCFCLM_apply]
          ring

@[simp] theorem section43OneSidedAnnihilatorFLOnImag_of_pos
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    {t : ℝ} (ht : 0 < t) :
    section43OneSidedAnnihilatorFLOnImag A t =
      section43OneSidedAnnihilatorFL A ((t : ℂ) * Complex.I)
        (by simpa using ht) := by
  simp [section43OneSidedAnnihilatorFLOnImag, ht]

theorem section43OneSidedAnnihilatorFLOnImag_of_not_pos
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    {t : ℝ} (ht : ¬ 0 < t) :
    section43OneSidedAnnihilatorFLOnImag A t = 0 := by
  simp [section43OneSidedAnnihilatorFLOnImag, ht]

theorem section43OneSidedAnnihilatorFLOnImag_eq_apply_kernel
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) (t : ℝ) :
    section43OneSidedAnnihilatorFLOnImag A t =
      A (section43PositiveEnergyQuotientMap1D
        (section43ImagAxisPsiKernel t)) := by
  by_cases ht : 0 < t
  · simp [section43OneSidedAnnihilatorFLOnImag, section43ImagAxisPsiKernel,
      section43OneSidedAnnihilatorFL, ht]
  · simp [section43OneSidedAnnihilatorFLOnImag, section43ImagAxisPsiKernel,
      ht]

theorem continuousOn_section43OneSidedAnnihilatorFLOnImag_Ioi
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    ContinuousOn (section43OneSidedAnnihilatorFLOnImag A) (Set.Ioi (0 : ℝ)) := by
  let T := section43PositiveEnergy1D_to_oneSidedFourierFunctional A
  let F : ℂ → ℂ := fun w =>
    if hw : 0 < w.im then
      SCV.fourierLaplaceExt T w hw
    else
      0
  have hF_cont : ContinuousOn F SCV.upperHalfPlane := by
    simpa [F] using (SCV.fourierLaplaceExt_differentiableOn T).continuousOn
  have hpath_cont :
      ContinuousOn (fun t : ℝ => (t : ℂ) * Complex.I) (Set.Ioi (0 : ℝ)) := by
    exact ((Complex.continuous_ofReal.comp continuous_id).mul
      (continuous_const : Continuous (fun _ : ℝ => Complex.I))).continuousOn
  have hmap :
      Set.MapsTo (fun t : ℝ => (t : ℂ) * Complex.I)
        (Set.Ioi (0 : ℝ)) SCV.upperHalfPlane := by
    intro t ht
    simpa [SCV.upperHalfPlane, Complex.mul_im] using ht
  refine (hF_cont.comp hpath_cont hmap).congr ?_
  intro t ht
  have htpos : 0 < t := by simpa using ht
  have hw : 0 < (((t : ℂ) * Complex.I).im) := by
    simpa [Complex.mul_im] using htpos
  change section43OneSidedAnnihilatorFLOnImag A t = F (((t : ℂ) * Complex.I))
  rw [section43OneSidedAnnihilatorFLOnImag_of_pos A htpos]
  dsimp [F]
  rw [dif_pos (by simpa [Complex.mul_im] using htpos)]
  exact section43OneSidedAnnihilatorFL_eq_fourierLaplaceExt_to_oneSided
    (A := A) (((t : ℂ) * Complex.I)) hw

theorem section43PositiveEnergy1D_ext_of_FL_zero
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hFL :
      ∀ (z : ℂ) (hz : 0 < z.im),
        section43OneSidedAnnihilatorFL A z hz = 0) :
    A = 0 := by
  let T := section43PositiveEnergy1D_to_oneSidedFourierFunctional A
  have hT_supp : SCV.HasOneSidedFourierSupport T := by
    simpa [T] using section43PositiveEnergy1D_to_oneSidedFourierFunctional_support A
  have hT_zero : T = 0 := by
    ext φ
    have hpw := (SCV.paley_wiener_half_line_explicit T hT_supp).2.2 φ
    have hEventually_zero :
        (fun η : ℝ =>
          ∫ x : ℝ,
            (if hw : 0 < (↑x + ↑η * Complex.I).im then
              SCV.fourierLaplaceExt T
                ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I)))
                (by
                  have hscaled : 0 < (2 * Real.pi) *
                      (↑x + ↑η * Complex.I).im :=
                    mul_pos Real.two_pi_pos hw
                  simpa [Complex.mul_im] using hscaled)
            else 0) * φ x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun _ : ℝ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      have hη_pos : 0 < η := by simpa using hη
      apply integral_eq_zero_of_ae
      filter_upwards with x
      have hw : 0 < (↑x + ↑η * Complex.I).im := by
        simpa using hη_pos
      have hscaled :
          0 < ((((2 * Real.pi : ℝ) : ℂ) *
            (↑x + ↑η * Complex.I)).im) := by
        simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hw
      have hz0 :
          SCV.fourierLaplaceExt T
              ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I))) hscaled =
            0 := by
        have hEq :=
          section43OneSidedAnnihilatorFL_eq_fourierLaplaceExt_to_oneSided
            (A := A)
            ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I))) hscaled
        simpa [T] using (hEq.symm.trans (hFL _ hscaled))
      rw [dif_pos hw]
      rw [show
          SCV.fourierLaplaceExt T
              ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I))) _ =
            0 by
          convert hz0 using 1]
      simp
    have hlim_zero :
        Tendsto
          (fun η : ℝ =>
            ∫ x : ℝ,
              (if hw : 0 < (↑x + ↑η * Complex.I).im then
                SCV.fourierLaplaceExt T
                  ((((2 * Real.pi : ℝ) : ℂ) * (↑x + ↑η * Complex.I)))
                  (by
                    have hscaled : 0 < (2 * Real.pi) *
                        (↑x + ↑η * Complex.I).im :=
                      mul_pos Real.two_pi_pos hw
                    simpa [Complex.mul_im] using hscaled)
              else 0) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      (tendsto_congr' hEventually_zero).2 tendsto_const_nhds
    exact tendsto_nhds_unique hpw hlim_zero
  have hdesc := fourierPairingDescendsToSection43PositiveEnergy1D_to_oneSided A
  rw [← hdesc]
  ext u
  obtain ⟨φ, hφ⟩ := surjective_section43PositiveEnergyQuotientMap1D u
  rw [← hφ]
  rw [fourierPairingDescendsToSection43PositiveEnergy1D_apply]
  have hTφ : T ((SchwartzMap.fourierTransformCLM ℂ) φ) = 0 := by
    rw [hT_zero]
    rfl
  simpa [T] using hTφ

end OSReconstruction
