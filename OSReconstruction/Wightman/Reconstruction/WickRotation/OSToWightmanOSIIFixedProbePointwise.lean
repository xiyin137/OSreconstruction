import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIDeltaSmearing
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Support
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.OrbitBridge

/-!
# OS-II Fixed-Probe Pointwise Recovery

This companion specializes the neutral OS-II delta-smearing bridge to the
fixed-probe Laplace-Fourier/Product-shell comparison.  The translated-delta
integrability and product-shell continuity obligations are discharged from the
existing Bochner/Fubini and VI.1 orbit support lemmas; the remaining analytic
input is continuity of the Laplace-Fourier kernel at the positive-time center.
-/

noncomputable section

open Complex Topology MeasureTheory Filter
open scoped Classical NNReal BigOperators

namespace OSReconstruction

theorem integrable_weighted_shift_of_integrable_mul_translated
    {d : ℕ}
    (F : SpacetimeDim d → ℂ)
    (φ : SchwartzSpacetime d)
    (x0 : SpacetimeDim d)
    (h : Integrable (fun ξ : SpacetimeDim d =>
      F ξ * (SCV.translateSchwartz (-x0) φ) ξ)) :
    Integrable (fun y : SpacetimeDim d => φ y * F (x0 + y)) := by
  have hcomp : Integrable (fun y : SpacetimeDim d =>
      F (y + x0) * (SCV.translateSchwartz (-x0) φ) (y + x0)) := by
    simpa [Function.comp_def] using
      (MeasureTheory.measurePreserving_add_right
        (volume : Measure (SpacetimeDim d)) x0).integrable_comp_of_integrable h
  simpa [SCV.translateSchwartz_apply, add_assoc, add_comm, add_left_comm, mul_comm]
    using hcomp

/-- The Laplace-Fourier kernel of a finite nonnegative-energy measure is
continuous at every positive-time point.  This is the OS-II dominated
convergence input used by the delta-smearing pointwise recovery. -/
theorem continuousAt_laplaceFourierKernel_of_nonnegEnergy_local
    {d : ℕ}
    (μ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (x0 : SpacetimeDim d)
    (hx0 : 0 < x0 0) :
    ContinuousAt (laplaceFourierKernel (d := d) μ) x0 := by
  have h_nonneg_p : ∀ᵐ p : ℝ × (Fin d → ℝ) ∂μ, 0 ≤ p.1 := by
    rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
    suffices
        {p : ℝ × (Fin d → ℝ) | ¬ 0 ≤ p.1} ⊆ Set.prod (Set.Iio 0) Set.univ by
      exact le_antisymm (le_trans (μ.mono this) (le_of_eq hsupp)) (zero_le _)
    intro p hp
    rcases p with ⟨E, q⟩
    simp only [Set.mem_setOf_eq, not_le] at hp
    exact Set.mk_mem_prod hp (Set.mem_univ q)
  let F : SpacetimeDim d → (ℝ × (Fin d → ℝ)) → ℂ := fun ξ p =>
    Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
      Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i)))
  change Tendsto (fun ξ : SpacetimeDim d => ∫ p, F ξ p ∂μ)
    (𝓝 x0) (𝓝 (∫ p, F x0 p ∂μ))
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ))
  · exact Filter.Eventually.of_forall fun ξ => by
      have hcont : Continuous (fun p : ℝ × (Fin d → ℝ) => F ξ p) := by
        dsimp [F]
        fun_prop
      exact hcont.aestronglyMeasurable
  · have hpos_nhds :
        {ξ : SpacetimeDim d | 0 < ξ 0} ∈ 𝓝 x0 := by
      exact (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx0
    apply Filter.eventually_of_mem hpos_nhds
    intro ξ hξ
    have hξ0 : 0 < ξ 0 := hξ
    filter_upwards [h_nonneg_p] with p hp_nonneg
    have hphase :
        (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))).re = 0 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hexp_le_one :
        Real.exp (-(ξ 0 * p.1)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [hξ0, hp_nonneg]
    calc
      ‖F ξ p‖
          = Real.exp (-(ξ 0 * p.1)) := by
              rw [show F ξ p =
                Complex.exp (-(↑(ξ 0 * p.1) : ℂ)) *
                  Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * ξ (Fin.succ i))) by rfl]
              rw [norm_mul, Complex.norm_exp, Complex.norm_exp, hphase, Real.exp_zero, mul_one]
              simp
      _ ≤ 1 := hexp_le_one
  · exact integrable_const (1 : ℝ)
  · exact Filter.Eventually.of_forall fun p => by
      have hcont : Continuous (fun ξ : SpacetimeDim d => F ξ p) := by
        dsimp [F]
        fun_prop
      exact hcont.continuousAt

/-- Fixed-probe pointwise OS-II real-edge recovery, with the public
integrability/continuity support lemmas filling all translated-delta
obligations except continuity of the Laplace-Fourier kernel itself. -/
theorem fixed_probe_laplaceFourier_eq_translatedProductShell_of_delta_bridge_public
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
    (hLF_cont : ContinuousAt (laplaceFourierKernel (d := d) μ) x0) :
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
  have hTPS_cont : ContinuousAt TPS x0 := by
    have hcontOn :
        ContinuousOn TPS {ξ : SpacetimeDim d | 0 < ξ 0} := by
      simpa [TPS] using
        continuousOn_translatedProductShell_boundary_positiveTime_vi1Bridge_local
          (d := d) OS lgc φ hφ_real hφ_compact hφ_neg
    have hopen : IsOpen {ξ : SpacetimeDim d | 0 < ξ 0} :=
      isOpen_lt continuous_const (continuous_apply 0)
    exact hcontOn.continuousAt (hopen.mem_nhds hx0)
  have hLF_int :
      ∀ n, Integrable (fun y : SpacetimeDim d =>
        ψδ n y * laplaceFourierKernel (d := d) μ (x0 + y)) := by
    intro n
    let hδ : positiveTimeCompactSupportSubmodule d :=
      ⟨SCV.translateSchwartz (-x0) (ψδ n),
        translate_positiveTime_schwartz_mem_positiveTimeCompactSupport
          (d := d) (ψδ n) (hψδ_pos n) (hψδ_compact n) x0 hx0⟩
    have hbase :
        Integrable (fun ξ : SpacetimeDim d =>
          laplaceFourierKernel (d := d) μ ξ * (hδ : SchwartzSpacetime d) ξ) :=
      integrable_laplaceFourierKernel_mul_of_nonnegEnergy_local
        (d := d) μ hsupp hδ
    exact
      integrable_weighted_shift_of_integrable_mul_translated
        (d := d) (laplaceFourierKernel (d := d) μ) (ψδ n) x0
        (by simpa [hδ] using hbase)
  have hTPS_int :
      ∀ n, Integrable (fun y : SpacetimeDim d =>
        ψδ n y * TPS (x0 + y)) := by
    intro n
    let hδ : positiveTimeCompactSupportSubmodule d :=
      ⟨SCV.translateSchwartz (-x0) (ψδ n),
        translate_positiveTime_schwartz_mem_positiveTimeCompactSupport
          (d := d) (ψδ n) (hψδ_pos n) (hψδ_compact n) x0 hx0⟩
    have hbase :
        Integrable (fun ξ : SpacetimeDim d =>
          TPS ξ * (hδ : SchwartzSpacetime d) ξ) := by
      simpa [TPS, hδ] using
        integrable_translatedProductShell_boundary_weight_vi1Bridge_local
          (d := d) OS lgc φ hφ_real hφ_compact hφ_neg hδ
    exact
      integrable_weighted_shift_of_integrable_mul_translated
        (d := d) TPS (ψδ n) x0 (by simpa [hδ] using hbase)
  exact
    fixed_probe_laplaceFourier_eq_translatedProductShell_of_delta_bridge
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμ_repr
      ψδ r x0 hx0 hψδ_nonneg hψδ_real hψδ_int hψδ_compact hψδ_pos
      hψδ_support hr hLF_cont hTPS_cont hLF_int hTPS_int

/-- Fully discharged fixed-probe OS-II pointwise recovery from a finite
nonnegative-energy Bochner measure.  The only remaining hypotheses are the
spectral representation, the positive-time translated delta family, and the
standard support/normalization data for that family. -/
theorem fixed_probe_laplaceFourier_eq_translatedProductShell_of_delta_bridge_of_nonnegEnergy
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
    (hr : Tendsto r atTop (𝓝 0)) :
    laplaceFourierKernel (d := d) μ x0 =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          (SCV.translateSchwartz (-x0) (reflectedSchwartzSpacetime φ)))) := by
  exact
    fixed_probe_laplaceFourier_eq_translatedProductShell_of_delta_bridge_public
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμ_repr
      ψδ r x0 hx0 hψδ_nonneg hψδ_real hψδ_int hψδ_compact hψδ_pos
      hψδ_support hr
      (continuousAt_laplaceFourierKernel_of_nonnegEnergy_local
        (d := d) μ hsupp x0 hx0)

/-- Closed fixed-probe OS-II pointwise recovery.  The positive-time
delta family is supplied by the repository's checked approximate-identity
construction, so callers only provide the OS data, Bochner representation, and
the positive-time point. -/
theorem fixed_probe_laplaceFourier_eq_translatedProductShell_of_nonnegEnergy
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
    (x0 : SpacetimeDim d) (hx0 : 0 < x0 0) :
    laplaceFourierKernel (d := d) μ x0 =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          (SCV.translateSchwartz (-x0) (reflectedSchwartzSpacetime φ)))) := by
  obtain ⟨ψδ, r, hψδ_nonneg, hψδ_real, hψδ_int, hψδ_compact, hψδ_pos,
    hψδ_support, hr⟩ :=
    exists_positiveTime_shrinking_schwartz_approx_identity_for_delta_bridge
      (d := d)
  exact
    fixed_probe_laplaceFourier_eq_translatedProductShell_of_delta_bridge_of_nonnegEnergy
      (d := d) OS lgc φ hφ_real hφ_compact hφ_neg μ hsupp hμ_repr
      ψδ r x0 hx0 hψδ_nonneg hψδ_real hψδ_int hψδ_compact hψδ_pos
      hψδ_support hr

end OSReconstruction
