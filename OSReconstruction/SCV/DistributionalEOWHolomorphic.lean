/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWCutoff
import OSReconstruction.SCV.EuclideanWeylOpen

/-!
# Holomorphic Regularity for Distributional EOW

This downstream file starts the final regularity assembly for the local
distributional edge-of-the-wedge route.  The Euclidean Weyl theorem is already
checked in `EuclideanWeylOpen`; the theorem below transports it through the
complex-chart Euclidean flattening from `DistributionalEOWRegularity`.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter
open scoped LineDeriv BigOperators

namespace SCV

variable {m : ℕ}

/-- Local fundamental lemma for continuous functions tested against all
Schwartz functions compactly supported in an open set. -/
theorem eq_zero_on_open_of_supportsInOpen_schwartz_integral_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsLocallyFiniteMeasure (volume : Measure E)]
    [Measure.IsOpenPosMeasure (volume : Measure E)]
    {g : E → ℂ} {U : Set E}
    (hU_open : IsOpen U)
    (hg : ContinuousOn g U)
    (hint : ∀ φ : SchwartzMap E ℂ,
      SupportsInOpen (φ : E → ℂ) U →
        (∫ x : E, g x * φ x) = 0) :
    ∀ x ∈ U, g x = 0 := by
  intro x hx
  classical
  obtain ⟨χ, hχ_tsupport, hχ_compact, hχ_smooth, _hχ_range, hχx⟩ :=
    exists_contDiff_tsupport_subset
      (s := U) (x := x) (n := (⊤ : ℕ∞)) (hU_open.mem_nhds hx)
  let χC : E → ℂ := fun y => (χ y : ℂ)
  have hχC_smooth : ContDiff ℝ (⊤ : ℕ∞) χC := by
    exact Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hχC_compact : HasCompactSupport χC :=
    hχ_compact.comp_left Complex.ofReal_zero
  let χS : SchwartzMap E ℂ := hχC_compact.toSchwartzMap hχC_smooth
  have hχS_apply : ∀ y, χS y = χC y :=
    HasCompactSupport.toSchwartzMap_toFun hχC_compact hχC_smooth
  have hχC_temp : χC.HasTemperateGrowth := by
    simpa [χS, hχS_apply] using χS.hasTemperateGrowth
  have hχC_support : Function.support χC = Function.support χ := by
    ext y
    simp [χC, Function.mem_support]
  have hχC_tsupport : tsupport χC = tsupport χ := by
    simp [tsupport, hχC_support]
  let χg : E → ℂ := fun y => if hy : y ∈ U then χC y * g y else 0
  have hχg_eq_mul : ∀ y, χg y = χC y * g y := by
    intro y
    by_cases hy : y ∈ U
    · simp [χg, hy]
    · have hy_not_tsupport : y ∉ tsupport χ := by
        intro hyχ
        exact hy (hχ_tsupport hyχ)
      have hy_not_support : y ∉ Function.support χ := by
        intro hys
        exact hy_not_tsupport (subset_tsupport χ hys)
      have hχy : χ y = 0 := by
        simpa [Function.mem_support] using hy_not_support
      simp [χg, hy, χC, hχy]
  have hχg_cont : Continuous χg := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ U
    · have hUy : U ∈ 𝓝 y := hU_open.mem_nhds hy
      have hχC_at : ContinuousAt χC y :=
        (Complex.ofRealCLM.continuous.comp hχ_smooth.continuous).continuousAt
      have hg_at : ContinuousAt g y := hg.continuousAt hUy
      have hχg_eventually :
          χg =ᶠ[𝓝 y] fun z => χC z * g z := by
        filter_upwards [hUy] with z hz
        simp [χg, hz]
      exact (hχC_at.mul hg_at).congr_of_eventuallyEq hχg_eventually
    · have hy_not_tsupport : y ∉ tsupport χ := by
        intro hyχ
        exact hy (hχ_tsupport hyχ)
      have hχ_eventually_zero : χ =ᶠ[𝓝 y] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at hy_not_tsupport
      have hχg_eventually_zero : χg =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hχ_eventually_zero] with z hz
        by_cases hzU : z ∈ U <;> simp [χg, hzU, χC, hz]
      exact continuousAt_const.congr_of_eventuallyEq hχg_eventually_zero
  have hχg_integral_zero :
      ∀ φ : SchwartzMap E ℂ, (∫ y : E, χg y * φ y) = 0 := by
    intro φ
    let φχ : SchwartzMap E ℂ := SchwartzMap.smulLeftCLM ℂ χC φ
    have hφχ_tsupport_subset :
        tsupport (φχ : E → ℂ) ⊆ tsupport χC := by
      intro z hz
      exact
        (SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ) (g := χC) (f := φ) hz).2
    have hφχ_compact : HasCompactSupport (φχ : E → ℂ) := by
      exact IsCompact.of_isClosed_subset hχC_compact (isClosed_tsupport _)
        hφχ_tsupport_subset
    have hφχ_support_U : tsupport (φχ : E → ℂ) ⊆ U := by
      exact hφχ_tsupport_subset.trans (by simpa [hχC_tsupport] using hχ_tsupport)
    have hzero := hint φχ ⟨hφχ_compact, hφχ_support_U⟩
    calc
      (∫ y : E, χg y * φ y) =
          ∫ y : E, g y * φχ y := by
        congr 1
        ext y
        rw [hχg_eq_mul y]
        simp [φχ, SchwartzMap.smulLeftCLM_apply_apply hχC_temp]
        ring
      _ = 0 := hzero
  have hχg_zero_univ :
      ∀ y ∈ (Set.univ : Set E), χg y = 0 :=
    eq_zero_on_open_of_compactSupport_schwartz_integral_zero
      (g := χg) hχg_cont (U := Set.univ) isOpen_univ
      (by
        intro φ _hφ_compact _hφ_support
        exact hχg_integral_zero φ)
  have hxχg : χg x = 0 := hχg_zero_univ x (by simp)
  have hχgx : χg x = g x := by
    simp [χg, hx, χC, hχx]
  simpa [hχgx] using hxχg

/-- Weyl regularity for the real coordinate Laplacian on the complex chart.

This is the honest transport of
`euclidean_weyl_laplacian_distribution_regular_on_open` through
`complexChartEuclideanCLE`.  The explicit `0 < m` hypothesis supplies the
positive Euclidean dimension currently required by the checked bump primitive;
the theorem-2 OS45 chart callers are positive-dimensional. -/
theorem weyl_laplacian_distribution_regular_on_open
    (T : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    {U0 : Set (ComplexChartSpace m)}
    (hm : 0 < m)
    (hU0_open : IsOpen U0)
    (hΔ :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 →
          T (complexChartLaplacianSchwartzCLM φ) = 0) :
    ∃ H : ComplexChartSpace m → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) H U0 ∧
      RepresentsDistributionOnComplexDomain T H U0 := by
  classical
  let E := EuclideanSpace ℝ (Fin (m * 2))
  let e := complexChartEuclideanCLE m
  let V : Set E := e '' U0
  let TE : SchwartzMap E ℂ →L[ℂ] ℂ := transportedDistributionToEuclidean T
  haveI : Nonempty (Fin (m * 2)) := by
    exact ⟨⟨0, Nat.mul_pos hm (by norm_num)⟩⟩
  have hV_open : IsOpen V := by
    simpa [V, e] using e.toHomeomorph.isOpenMap U0 hU0_open
  have hΔE :
      ∀ ψ : SchwartzMap E ℂ,
        SupportsInOpen (ψ : E → ℂ) V →
          TE
            (LineDeriv.laplacianCLM ℝ E (SchwartzMap E ℂ) ψ) = 0 := by
    intro ψ hψ
    let ψc : SchwartzMap (ComplexChartSpace m) ℂ :=
      (complexChartEuclideanSchwartzCLE m).symm ψ
    have hψc : SupportsInOpen (ψc : ComplexChartSpace m → ℂ) U0 := by
      simpa [ψc, V, E, e] using
        (supportsInOpen_transport_to_euclidean (m := m) (φ := ψ) (U0 := U0) hψ)
    have hzero : T (complexChartLaplacianSchwartzCLM ψc) = 0 :=
      hΔ ψc hψc
    have htransport :
        (complexChartEuclideanSchwartzCLE m).symm
            (LineDeriv.laplacianCLM ℝ E (SchwartzMap E ℂ) ψ) =
          complexChartLaplacianSchwartzCLM ψc := by
      apply (complexChartEuclideanSchwartzCLE m).injective
      simpa [ψc, E] using
        (complexChartLaplacianSchwartzCLM_transport (m := m) ψc).symm
    change
      T ((complexChartEuclideanSchwartzCLE m).symm
          (LineDeriv.laplacianCLM ℝ E (SchwartzMap E ℂ) ψ)) = 0
    rw [htransport]
    exact hzero
  obtain ⟨HE, hHE_smooth, hHE_rep⟩ :=
    euclidean_weyl_laplacian_distribution_regular_on_open
      (T := TE) hV_open hΔE
  refine ⟨fun z => HE (e z), ?_, ?_⟩
  · exact
      hHE_smooth.comp
        (e.contDiff.contDiffOn)
        (fun z hz => by exact Set.mem_image_of_mem e hz)
  · simpa [TE, V, E, e] using
      (representsDistributionOnComplexDomain_of_euclidean
        (m := m) T (U0 := U0) HE hHE_rep)

/-- The pointwise `∂bar` expression of a real-smooth representative is
continuous on the open chart domain. -/
theorem continuousOn_pointwiseDbar_of_contDiffOn
    {H : ComplexChartSpace m → ℂ} {U0 : Set (ComplexChartSpace m)}
    (hU0_open : IsOpen U0)
    (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
    (j : Fin m) :
    ContinuousOn (pointwiseDbar j H) U0 := by
  have hfd : ContinuousOn (fun z => fderiv ℝ H z) U0 :=
    hH_smooth.continuousOn_fderiv_of_isOpen hU0_open (by simp)
  have hreal :
      ContinuousOn
        (fun z => fderiv ℝ H z (complexRealDir j)) U0 :=
    hfd.clm_apply continuousOn_const
  have himag :
      ContinuousOn
        (fun z => fderiv ℝ H z (complexImagDir j)) U0 :=
    hfd.clm_apply continuousOn_const
  change ContinuousOn
    (fun z => (1 / 2 : ℂ) *
      (fderiv ℝ H z (complexRealDir j) +
        Complex.I * fderiv ℝ H z (complexImagDir j))) U0
  simpa [mul_assoc] using
    (hreal.add (himag.const_mul Complex.I)).const_mul (1 / 2 : ℂ)

/-- A real-smooth local representative can be cut off to a global Schwartz
representative whose `∂bar` agrees with the pointwise `∂bar` of the local
representative on the test support. -/
theorem exists_local_schwartz_representative_with_dbar_eq
    {H : ComplexChartSpace m → ℂ} {U0 : Set (ComplexChartSpace m)}
    (hU0_open : IsOpen U0)
    (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0)
    (j : Fin m) :
    ∃ G : SchwartzMap (ComplexChartSpace m) ℂ,
      (∀ z ∈ tsupport
          ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
            ComplexChartSpace m → ℂ),
          H z = G z) ∧
      (∀ z ∈ tsupport (φ : ComplexChartSpace m → ℂ),
          (dbarSchwartzCLM j G) z = pointwiseDbar j H z) := by
  obtain ⟨χ, hχ_contDiff, hχ_compact, hχ_tsupport_U, _hχrange,
      V, hV_open, hK_sub_V, _hV_U, hχ_eq_one_V⟩ :=
    exists_smooth_cutoff_eq_one_near_tsupport_of_supportsInOpen
      U0 hU0_open φ hφ
  let Hcut : ComplexChartSpace m → ℂ := fun z => (χ z : ℂ) * H z
  have hχC_contDiff :
      ContDiff ℝ (⊤ : ℕ∞) (fun z : ComplexChartSpace m => (χ z : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hχ_contDiff
  have hHcut_smooth : ContDiff ℝ (⊤ : ℕ∞) Hcut := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hzU : z ∈ U0
    · have hH_at : ContDiffAt ℝ (⊤ : ℕ∞) H z :=
        (hH_smooth z hzU).contDiffAt (hU0_open.mem_nhds hzU)
      exact hχC_contDiff.contDiffAt.mul hH_at
    · have hz_not_tsupport : z ∉ tsupport χ := by
        intro hzχ
        exact hzU (hχ_tsupport_U hzχ)
      have hχ0 : χ =ᶠ[nhds z] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at hz_not_tsupport
      have hHcut0 : Hcut =ᶠ[nhds z] fun _ => 0 := by
        filter_upwards [hχ0] with y hy
        simp [Hcut, hy]
      exact (contDiff_const.contDiffAt (x := z)).congr_of_eventuallyEq hHcut0
  have hHcut_tsupport_subset : tsupport Hcut ⊆ tsupport χ := by
    rw [tsupport]
    exact closure_mono (by
      intro z hz
      by_contra hzχ
      have hχz : χ z = 0 := by
        simpa [Function.mem_support] using hzχ
      exact hz (by simp [Hcut, hχz]))
  have hHcut_compact : HasCompactSupport Hcut := by
    exact IsCompact.of_isClosed_subset hχ_compact (isClosed_tsupport Hcut)
      hHcut_tsupport_subset
  let G : SchwartzMap (ComplexChartSpace m) ℂ :=
    hHcut_compact.toSchwartzMap hHcut_smooth
  have hG_apply : ∀ z, G z = Hcut z :=
    HasCompactSupport.toSchwartzMap_toFun hHcut_compact hHcut_smooth
  refine ⟨G, ?_, ?_⟩
  · intro z hz
    have hzK : z ∈ tsupport (φ : ComplexChartSpace m → ℂ) :=
      dbarSchwartzCLM_tsupport_subset j φ hz
    have hχz : χ z = 1 := hχ_eq_one_V (hK_sub_V hzK)
    rw [hG_apply z]
    simp [Hcut, hχz]
  · intro z hz
    have hzV : z ∈ V := hK_sub_V hz
    have hGH_eventually : (G : ComplexChartSpace m → ℂ) =ᶠ[nhds z] H := by
      filter_upwards [hV_open.mem_nhds hzV] with y hy
      have hχy : χ y = 1 := hχ_eq_one_V hy
      rw [hG_apply y]
      simp [Hcut, hχy]
    have hfderiv_eq :
        fderiv ℝ (G : ComplexChartSpace m → ℂ) z = fderiv ℝ H z :=
      hGH_eventually.fderiv_eq
    rw [dbarSchwartzCLM_apply_eq_pointwiseDbar]
    simp [pointwiseDbar, hfderiv_eq]

/-- Distributional `∂bar`-holomorphy of a distribution represented by a
real-smooth function forces the pointwise `∂bar` expression to pair trivially
with every test supported in the domain. -/
theorem integral_pointwiseDbar_mul_eq_zero_of_distributionalHolomorphic
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    {U0 : Set (ComplexChartSpace m)}
    (hU0_open : IsOpen U0)
    (hCR : IsDistributionalHolomorphicOn Hdist U0)
    (H : ComplexChartSpace m → ℂ)
    (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
    (hRep : RepresentsDistributionOnComplexDomain Hdist H U0)
    (j : Fin m)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0) :
    (∫ z : ComplexChartSpace m, pointwiseDbar j H z * φ z) = 0 := by
  have hH_dbar_zero :
      (∫ z : ComplexChartSpace m, H z * (dbarSchwartzCLM j φ) z) = 0 := by
    calc
      (∫ z : ComplexChartSpace m, H z * (dbarSchwartzCLM j φ) z) =
          Hdist (dbarSchwartzCLM j φ) := by
        exact (hRep (dbarSchwartzCLM j φ) (hφ.dbar j)).symm
      _ = 0 := hCR j φ hφ
  obtain ⟨G, hHG_dbar, hG_dbar_eq⟩ :=
    exists_local_schwartz_representative_with_dbar_eq
      hU0_open hH_smooth φ hφ j
  have hG_dbar_zero :
      (∫ z : ComplexChartSpace m, G z * (dbarSchwartzCLM j φ) z) = 0 := by
    calc
      (∫ z : ComplexChartSpace m, G z * (dbarSchwartzCLM j φ) z) =
          ∫ z : ComplexChartSpace m, H z * (dbarSchwartzCLM j φ) z := by
        congr 1
        ext z
        by_cases hz : z ∈ tsupport
            ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
              ComplexChartSpace m → ℂ)
        · rw [hHG_dbar z hz]
        · have hzero :
              (dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) z = 0 :=
            image_eq_zero_of_notMem_tsupport hz
          simp [hzero]
      _ = 0 := hH_dbar_zero
  have hIBP :=
    integral_mul_dbarSchwartzCLM_right_eq_neg_left G φ j
  have h_dbarG_integral_zero :
      (∫ z : ComplexChartSpace m, (dbarSchwartzCLM j G) z * φ z) = 0 := by
    have hneg :
        - (∫ z : ComplexChartSpace m, (dbarSchwartzCLM j G) z * φ z) = 0 := by
      rw [← hIBP]
      exact hG_dbar_zero
    exact neg_eq_zero.mp hneg
  calc
    (∫ z : ComplexChartSpace m, pointwiseDbar j H z * φ z) =
        ∫ z : ComplexChartSpace m, (dbarSchwartzCLM j G) z * φ z := by
      congr 1
      ext z
      by_cases hz : z ∈ tsupport (φ : ComplexChartSpace m → ℂ)
      · rw [hG_dbar_eq z hz]
      · have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [hzero]
    _ = 0 := h_dbarG_integral_zero

/-- A real-smooth representative of a distributionally holomorphic
distribution satisfies the pointwise Cauchy-Riemann equations on the open
domain. -/
theorem pointwiseDbar_eq_zero_of_distributionalHolomorphic
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    {U0 : Set (ComplexChartSpace m)}
    (hU0_open : IsOpen U0)
    (hCR : IsDistributionalHolomorphicOn Hdist U0)
    (H : ComplexChartSpace m → ℂ)
    (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
    (hRep : RepresentsDistributionOnComplexDomain Hdist H U0) :
    ∀ j : Fin m, ∀ z ∈ U0, pointwiseDbar j H z = 0 := by
  intro j
  exact
    eq_zero_on_open_of_supportsInOpen_schwartz_integral_zero
      hU0_open
      (continuousOn_pointwiseDbar_of_contDiffOn hU0_open hH_smooth j)
      (fun φ hφ =>
        integral_pointwiseDbar_mul_eq_zero_of_distributionalHolomorphic
          Hdist hU0_open hCR H hH_smooth hRep j φ hφ)

/-- Decompose a complex-chart vector into real and imaginary coordinate
directions. -/
theorem complexChart_vector_decomposition (v : ComplexChartSpace m) :
    v =
      ∑ j : Fin m,
        ((v j).re • complexRealDir j + (v j).im • complexImagDir j) := by
  ext k
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single k]
  · simp [complexRealDir, complexImagDir]
  · intro j _hj hjk
    simp [complexRealDir, complexImagDir, hjk.symm]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- Multiplication by `I` sends the real coordinate direction to the imaginary
coordinate direction. -/
theorem complexChart_I_smul_realDir (j : Fin m) :
    Complex.I • complexRealDir j = complexImagDir j := by
  ext k
  by_cases hkj : k = j <;> simp [complexRealDir, complexImagDir, hkj]

/-- Multiplication by `I` sends the imaginary coordinate direction to minus the
real coordinate direction. -/
theorem complexChart_I_smul_imagDir (j : Fin m) :
    Complex.I • complexImagDir j = -complexRealDir j := by
  ext k
  by_cases hkj : k = j <;> simp [complexRealDir, complexImagDir, hkj]

/-- A vanishing pointwise `∂bar_j` equation says that the real derivative in
the imaginary coordinate direction is `I` times the derivative in the real
coordinate direction. -/
theorem fderiv_imagDir_eq_I_mul_realDir_of_pointwiseDbar_zero
    {H : ComplexChartSpace m → ℂ} {z : ComplexChartSpace m} {j : Fin m}
    (h : pointwiseDbar j H z = 0) :
    fderiv ℝ H z (complexImagDir j) =
      Complex.I * fderiv ℝ H z (complexRealDir j) := by
  let a := fderiv ℝ H z (complexRealDir j)
  let b := fderiv ℝ H z (complexImagDir j)
  have hsum : a + Complex.I * b = 0 := by
    have hnon : (1 / 2 : ℂ) ≠ 0 := by norm_num
    exact
      (mul_eq_zero.mp (by simpa [pointwiseDbar, a, b] using h)).resolve_left
        hnon
  have hsum' : Complex.I * b + a = 0 := by
    simpa [add_comm] using hsum
  have hIb : Complex.I * b = -a :=
    eq_neg_of_add_eq_zero_left hsum'
  calc
    b = (1 : ℂ) * b := by ring
    _ = (-(Complex.I * Complex.I)) * b := by
      rw [Complex.I_mul_I]
      simp
    _ = (-Complex.I) * (Complex.I * b) := by ring
    _ = (-Complex.I) * (-a) := by rw [hIb]
    _ = Complex.I * a := by ring_nf

/-- Coordinate Cauchy-Riemann equations force a real continuous linear map on
the complex chart to commute with multiplication by `I`. -/
theorem realCLM_commutes_I_of_coordinate_CR
    (L : ComplexChartSpace m →L[ℝ] ℂ)
    (hcoord : ∀ j : Fin m,
      L (complexImagDir j) = Complex.I * L (complexRealDir j)) :
    ∀ v : ComplexChartSpace m, L (Complex.I • v) = Complex.I * L v := by
  intro v
  have hIv_decomp :
      Complex.I • v =
        ∑ j : Fin m,
          ((-((v j).im)) • complexRealDir j +
            (v j).re • complexImagDir j) := by
    ext k
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single k]
    · simp [complexRealDir, complexImagDir, smul_eq_mul]
      calc
        Complex.I * v k =
            Complex.I * ((v k).re + (v k).im * Complex.I) := by
          rw [Complex.re_add_im (v k)]
        _ = -((v k).im : ℂ) + (v k).re * Complex.I := by
          ring_nf
          rw [Complex.I_sq]
          ring
    · intro j _hj hjk
      simp [complexRealDir, complexImagDir, hjk.symm]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  calc
    L (Complex.I • v) =
        L (∑ j : Fin m,
          ((-((v j).im)) • complexRealDir j +
            (v j).re • complexImagDir j)) := by
      rw [hIv_decomp]
    _ = ∑ j : Fin m,
          ((-((v j).im)) • L (complexRealDir j) +
            (v j).re • L (complexImagDir j)) := by
      simp only [map_sum, map_add, map_smul]
    _ = ∑ j : Fin m,
          ((-((v j).im)) • L (complexRealDir j) +
            (v j).re • (Complex.I * L (complexRealDir j))) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hcoord j]
    _ = Complex.I * L v := by
      conv_rhs =>
        rw [complexChart_vector_decomposition v]
      simp only [map_sum, map_add, map_smul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hcoord j]
      simp
      ring_nf
      rw [Complex.I_sq]
      ring

/-- If a real continuous linear map on the complex chart commutes with
multiplication by `I`, then it is complex-linear. -/
theorem realCLM_map_complex_smul_of_commutes_I
    (L : ComplexChartSpace m →L[ℝ] ℂ)
    (hI : ∀ v : ComplexChartSpace m, L (Complex.I • v) = Complex.I * L v)
    (c : ℂ) (v : ComplexChartSpace m) :
    L (c • v) = c • L v := by
  have hdecomp :
      c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
    ext k
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      c * v k = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * v k := by
        rw [Complex.re_add_im c]
      _ = (c.re : ℂ) * v k + (c.im : ℂ) * (Complex.I * v k) := by
        ring_nf
  calc
    L (c • v) =
        L ((c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v)) := by
      rw [hdecomp]
    _ = (c.re : ℝ) • L v + (c.im : ℝ) • L (Complex.I • v) := by
      simp
    _ = (c.re : ℝ) • L v + (c.im : ℝ) • (Complex.I * L v) := by
      rw [hI v]
    _ = c • L v := by
      simp [smul_eq_mul]
      calc
        (c.re : ℂ) * L v + (c.im : ℂ) * (Complex.I * L v) =
            ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * L v := by
          ring_nf
        _ = c * L v := by
          rw [Complex.re_add_im c]

/-- Package a real continuous linear map commuting with the complex structure
as a complex continuous linear map. -/
noncomputable def complexChartCLMOfRealCLMCommutingI
    (L : ComplexChartSpace m →L[ℝ] ℂ)
    (hI : ∀ v : ComplexChartSpace m, L (Complex.I • v) = Complex.I * L v) :
    ComplexChartSpace m →L[ℂ] ℂ where
  toLinearMap :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := realCLM_map_complex_smul_of_commutes_I L hI }
  cont := L.continuous

/-- A real-smooth complex-chart function whose pointwise `∂bar_j` equations
vanish is holomorphic on the open domain. -/
theorem differentiableOn_complex_of_contDiffOn_real_and_pointwiseDbar_zero
    {H : ComplexChartSpace m → ℂ} {U0 : Set (ComplexChartSpace m)}
    (hU0_open : IsOpen U0)
    (hH_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H U0)
    (hDbar : ∀ j : Fin m, ∀ z ∈ U0, pointwiseDbar j H z = 0) :
    DifferentiableOn ℂ H U0 := by
  intro z hz
  have hH_real_on : DifferentiableOn ℝ H U0 :=
    hH_smooth.differentiableOn (by simp)
  have hreal_at : DifferentiableAt ℝ H z :=
    (hH_real_on z hz).differentiableAt (hU0_open.mem_nhds hz)
  have hcoord : ∀ j : Fin m,
      fderiv ℝ H z (complexImagDir j) =
        Complex.I * fderiv ℝ H z (complexRealDir j) := by
    intro j
    exact fderiv_imagDir_eq_I_mul_realDir_of_pointwiseDbar_zero
      (hDbar j z hz)
  have hI : ∀ v : ComplexChartSpace m,
      fderiv ℝ H z (Complex.I • v) = Complex.I * fderiv ℝ H z v :=
    realCLM_commutes_I_of_coordinate_CR (fderiv ℝ H z) hcoord
  have hcomplex_at : DifferentiableAt ℂ H z := by
    rw [differentiableAt_iff_restrictScalars ℝ hreal_at]
    refine ⟨complexChartCLMOfRealCLMCommutingI (fderiv ℝ H z) hI, ?_⟩
    ext v
    rfl
  exact hcomplex_at.differentiableWithinAt

/-- Distributional holomorphy on an open complex chart admits a genuine
holomorphic function representative on that chart. -/
theorem distributionalHolomorphic_regular
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    {U0 : Set (ComplexChartSpace m)}
    (hm : 0 < m)
    (hU0_open : IsOpen U0)
    (hCR : IsDistributionalHolomorphicOn Hdist U0) :
    ∃ H : ComplexChartSpace m → ℂ,
      DifferentiableOn ℂ H U0 ∧
      RepresentsDistributionOnComplexDomain Hdist H U0 := by
  have hΔ :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 →
          Hdist (complexChartLaplacianSchwartzCLM φ) = 0 := by
    intro φ hφ
    exact local_laplacian_zero_of_distributionalHolomorphic Hdist hCR φ hφ
  obtain ⟨H, hH_smooth, hRep⟩ :=
    weyl_laplacian_distribution_regular_on_open Hdist hm hU0_open hΔ
  have hDbar : ∀ j : Fin m, ∀ z ∈ U0, pointwiseDbar j H z = 0 :=
    pointwiseDbar_eq_zero_of_distributionalHolomorphic
      Hdist hU0_open hCR H hH_smooth hRep
  exact ⟨H,
    differentiableOn_complex_of_contDiffOn_real_and_pointwiseDbar_zero
      hU0_open hH_smooth hDbar,
    hRep⟩

end SCV
