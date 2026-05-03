/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernel

/-!
# Support Lemmas for Local Distributional Edge-of-the-Wedge

This file records the support hygiene used by the
Streater-Wightman/Jost regularization route.  The lemmas are QFT-free and
consume only the checked SCV kernel substrate.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

variable {m : ℕ}

/-- A kernel whose topological support is contained in a closed ball is
compactly supported in the finite-dimensional real chart. -/
theorem KernelSupportWithin_hasCompactSupport
    {ψ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r) :
    HasCompactSupport (ψ : (Fin m → ℝ) → ℂ) := by
  exact IsCompact.of_isClosed_subset
    (isCompact_closedBall 0 r) (isClosed_tsupport _) hψ

/-- The fixed-radius kernel support class is closed under addition. -/
theorem KernelSupportWithin.add
    {ψ η : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r)
    (hη : KernelSupportWithin η r) :
    KernelSupportWithin (ψ + η) r := by
  intro x hx
  have hx' :
      x ∈ tsupport (ψ : (Fin m → ℝ) → ℂ) ∪
          tsupport (η : (Fin m → ℝ) → ℂ) := by
    simpa using
      tsupport_add (ψ : (Fin m → ℝ) → ℂ) (η : (Fin m → ℝ) → ℂ) hx
  rcases hx' with hxψ | hxη
  · exact hψ hxψ
  · exact hη hxη

/-- The fixed-radius kernel support class is closed under scalar
multiplication. -/
theorem KernelSupportWithin.smul
    (c : ℂ) {ψ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r) :
    KernelSupportWithin (c • ψ) r := by
  intro x hx
  exact hψ ((tsupport_smul_subset_right (fun _ : Fin m → ℝ => c)
    (ψ : (Fin m → ℝ) → ℂ)) hx)

/-- Translating a fixed-radius kernel enlarges the radius by at most the
translation length.  This is the support bookkeeping needed when a local EOW
window uses a larger radius for translated chart kernels. -/
theorem KernelSupportWithin.translateSchwartz
    (a : Fin m → ℝ) {ψ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r) :
    KernelSupportWithin (translateSchwartz a ψ) (r + ‖a‖) := by
  intro x hx
  have hsub :
      tsupport ((ψ : (Fin m → ℝ) → ℂ) ∘ fun x : Fin m → ℝ => x + a) ⊆
        (fun x : Fin m → ℝ => x + a) ⁻¹'
          tsupport (ψ : (Fin m → ℝ) → ℂ) := by
    exact tsupport_comp_subset_preimage (ψ : (Fin m → ℝ) → ℂ)
      (continuous_id.add continuous_const)
  have hx' : x ∈
      tsupport ((ψ : (Fin m → ℝ) → ℂ) ∘ fun x : Fin m → ℝ => x + a) := by
    simpa [translateSchwartz_apply] using hx
  have hxa_supp : x + a ∈ tsupport (ψ : (Fin m → ℝ) → ℂ) := hsub hx'
  have hxa_ball := hψ hxa_supp
  rw [Metric.mem_closedBall, dist_zero_right] at hxa_ball ⊢
  have hnorm : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
    calc
      ‖x‖ = ‖(x + a) - a‖ := by
        congr 1
        ext i
        simp
      _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
  linarith

/-- Multiplying a supported kernel by a Schwartz-side cutoff cannot enlarge
the kernel support radius. -/
theorem KernelSupportWithin.smulLeftCLM
    (χ : (Fin m → ℝ) → ℂ)
    {ψ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r) :
    KernelSupportWithin (SchwartzMap.smulLeftCLM ℂ χ ψ) r := by
  intro x hx
  exact hψ ((SchwartzMap.tsupport_smulLeftCLM_subset (F := ℂ) (g := χ)
    (f := ψ) hx).1)

/-- If the cutoff factor is supported in a radius, then multiplying any
Schwartz kernel by that cutoff produces a kernel supported in that radius. -/
theorem KernelSupportWithin.smulLeftCLM_of_leftSupport
    {χ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hχ : tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ Metric.closedBall 0 r)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    KernelSupportWithin (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) r := by
  intro x hx
  exact hχ ((SchwartzMap.tsupport_smulLeftCLM_subset (F := ℂ)
    (g := (χ : (Fin m → ℝ) → ℂ)) (f := ψ) hx).2)

/-- A Schwartz cutoff that is identically one on the closed support ball acts
as the identity on kernels supported in that ball. -/
theorem KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    {ψ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hχ_one :
      ∀ x : Fin m → ℝ, x ∈ Metric.closedBall (0 : Fin m → ℝ) r → χ x = 1)
    (hψ : KernelSupportWithin ψ r) :
    SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ = ψ := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
  by_cases hx : x ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
  · exact by simp [hχ_one x (hψ hx)]
  · have hψx : ψ x = 0 := by
      have hxsupp : x ∉ Function.support (ψ : (Fin m → ℝ) → ℂ) := by
        intro hs
        exact hx (subset_closure hs)
      simpa [Function.mem_support] using hxsupp
    simp [hψx]

/-- A compact Schwartz cutoff that is one on a prescribed closed ball and
supported in a larger closed ball. -/
theorem exists_schwartz_cutoff_eq_one_on_closedBall
    {r rLarge : ℝ} (hr : 0 < r) (hrLarge : r < rLarge) :
    ∃ χ : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) r, χ t = 1) ∧
      tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ Metric.closedBall 0 rLarge := by
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨r, rLarge, hr, hrLarge⟩
  let f : (Fin m → ℝ) → ℂ := fun t => (b t : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let χ : SchwartzMap (Fin m → ℝ) ℂ :=
    hf_compact.toSchwartzMap hf_smooth
  have hχ_apply : ∀ t, χ t = f t :=
    HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth
  refine ⟨χ, ?_, ?_⟩
  · intro t ht
    rw [hχ_apply t]
    simp [f, b.one_of_mem_closedBall ht]
  · intro t ht
    have htf : t ∈ tsupport f := by
      simpa [χ, hχ_apply] using ht
    have htb : t ∈ tsupport b := by
      simpa [tsupport, f, Function.support] using htf
    rw [b.tsupport_eq] at htb
    exact htb

/-- A compact Schwartz cutoff on the complex chart that is one on a prescribed
closed ball and supported in a larger closed ball. -/
theorem exists_complexChart_schwartz_cutoff_eq_one_on_closedBall
    {R Rlarge : ℝ} (hR : 0 < R) (hRlarge : R < Rlarge) :
    ∃ χ : SchwartzMap (ComplexChartSpace m) ℂ,
      (∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) R, χ z = 1) ∧
      tsupport (χ : ComplexChartSpace m → ℂ) ⊆ Metric.closedBall 0 Rlarge := by
  let b : ContDiffBump (0 : ComplexChartSpace m) := ⟨R, Rlarge, hR, hRlarge⟩
  let f : ComplexChartSpace m → ℂ := fun z => (b z : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let χ : SchwartzMap (ComplexChartSpace m) ℂ :=
    hf_compact.toSchwartzMap hf_smooth
  have hχ_apply : ∀ z, χ z = f z :=
    HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth
  refine ⟨χ, ?_, ?_⟩
  · intro z hz
    rw [hχ_apply z]
    simp [f, b.one_of_mem_closedBall hz]
  · intro z hz
    have hzf : z ∈ tsupport f := by
      simpa [χ, hχ_apply] using hz
    have hzb : z ∈ tsupport b := by
      simpa [tsupport, f, Function.support] using hzf
    rw [b.tsupport_eq] at hzb
    exact hzb

/-- A complex-chart cutoff that is identically one on the declared support
window acts as the identity on Schwartz tests supported in that window. -/
theorem SupportsInOpen.smulLeftCLM_eq_of_eq_one_on
    {U : Set (ComplexChartSpace m)}
    (χ : SchwartzMap (ComplexChartSpace m) ℂ)
    {φ : SchwartzMap (ComplexChartSpace m) ℂ}
    (hχ_one : ∀ z, z ∈ U → χ z = 1)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U) :
    SchwartzMap.smulLeftCLM ℂ (χ : ComplexChartSpace m → ℂ) φ = φ := by
  ext z
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
  by_cases hz : z ∈ tsupport (φ : ComplexChartSpace m → ℂ)
  · exact by simp [hχ_one z (hφ.2 hz)]
  · have hφz : φ z = 0 := by
      have hz_support : z ∉ Function.support (φ : ComplexChartSpace m → ℂ) := by
        intro hs
        exact hz (subset_closure hs)
      simpa [Function.mem_support] using hz_support
    simp [hφz]

/-- A locally continuous coefficient times a Schwartz test supported in the
local domain is globally continuous.  Outside the declared domain the test is
eventually zero, so no regularity of the coefficient is used there. -/
theorem continuous_mul_of_continuousOn_supportsInOpen
    {U : Set (ComplexChartSpace m)}
    (hU_open : IsOpen U)
    (G : ComplexChartSpace m → ℂ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hG : ContinuousOn G U)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U) :
    Continuous (fun z : ComplexChartSpace m => G z * φ z) := by
  let f : ComplexChartSpace m → ℂ := fun z => G z * φ z
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hzU : z ∈ U
  · have hGz : ContinuousAt G z :=
      hG.continuousAt (hU_open.mem_nhds hzU)
    simpa [f] using hGz.mul φ.continuous.continuousAt
  · have hz_tsupport : z ∉ tsupport (φ : ComplexChartSpace m → ℂ) := by
      intro hzφ
      exact hzU (hφ.2 hzφ)
    have hφ_zero :
        (φ : ComplexChartSpace m → ℂ) =ᶠ[nhds z] fun _ => 0 := by
      rwa [notMem_tsupport_iff_eventuallyEq] at hz_tsupport
    have hf_zero : f =ᶠ[nhds z] fun _ => 0 := by
      filter_upwards [hφ_zero] with y hy
      simp [f, hy]
    exact hf_zero.continuousAt

/-- A locally continuous coefficient can be paired over all space with a
Schwartz test whose topological support is compactly contained in the local
domain. -/
theorem integrable_mul_of_continuousOn_supportsInOpen
    {U : Set (ComplexChartSpace m)}
    (hU_open : IsOpen U)
    (G : ComplexChartSpace m → ℂ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hG : ContinuousOn G U)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U) :
    Integrable (fun z : ComplexChartSpace m => G z * φ z) := by
  let f : ComplexChartSpace m → ℂ := fun z => G z * φ z
  have hf_cont : Continuous f := by
    simpa [f] using
      continuous_mul_of_continuousOn_supportsInOpen hU_open G φ hG hφ
  have hf_support_subset :
      Function.support f ⊆ Function.support (φ : ComplexChartSpace m → ℂ) := by
    intro z hz
    by_contra hzφ
    have hφz : φ z = 0 := by
      simpa [Function.mem_support] using hzφ
    have hfz : f z = 0 := by
      simp [f, hφz]
    exact hz (by simp [hfz])
  have hf_compact : HasCompactSupport f := by
    rw [HasCompactSupport]
    refine hφ.1.of_isClosed_subset isClosed_closure ?_
    exact
      closure_minimal
        (fun z hz => subset_tsupport _ (hf_support_subset hz))
        (isClosed_tsupport _)
  exact hf_cont.integrable_of_hasCompactSupport hf_compact

/-- If the support window for a locally continuous coefficient/test product is
inside a closed ball, the closed-ball integral is the all-space integral. -/
theorem closedBall_setIntegral_mul_eq_integral_of_supportsInOpen
    {U : Set (ComplexChartSpace m)} {Rcut : ℝ}
    (hU_open : IsOpen U)
    (hU_closedBall :
      U ⊆ Metric.closedBall (0 : ComplexChartSpace m) Rcut)
    (G : ComplexChartSpace m → ℂ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (hG : ContinuousOn G U)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U) :
    (∫ z in Metric.closedBall (0 : ComplexChartSpace m) Rcut, G z * φ z) =
      ∫ z : ComplexChartSpace m, G z * φ z := by
  have _ : Integrable (fun z : ComplexChartSpace m => G z * φ z) :=
    integrable_mul_of_continuousOn_supportsInOpen hU_open G φ hG hφ
  let s : Set (ComplexChartSpace m) :=
    Metric.closedBall (0 : ComplexChartSpace m) Rcut
  have hzero :
      ∀ z : ComplexChartSpace m, z ∉ s → G z * φ z = 0 := by
    intro z hz
    have hz_tsupport : z ∉ tsupport (φ : ComplexChartSpace m → ℂ) := by
      intro hzφ
      exact hz (hU_closedBall (hφ.2 hzφ))
    have hφz : φ z = 0 := by
      have hz_support : z ∉ Function.support (φ : ComplexChartSpace m → ℂ) := by
        intro hsupp
        exact hz_tsupport (subset_closure hsupp)
      simpa [Function.mem_support] using hz_support
    simp [hφz]
  exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero

/-- Integration over a real closed ball against a continuous-on-the-ball
coefficient is a continuous linear functional on Schwartz kernels. -/
theorem exists_closedBall_integral_clm_of_continuousOn
    {R : ℝ} {g : (Fin m → ℝ) → ℂ}
    (hg_cont : ContinuousOn g (Metric.closedBall (0 : Fin m → ℝ) R)) :
    ∃ T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ,
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        T ψ = ∫ x in Metric.closedBall (0 : Fin m → ℝ) R, g x * ψ x := by
  let s : Set (Fin m → ℝ) := Metric.closedBall (0 : Fin m → ℝ) R
  have hs_compact : IsCompact s := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hs_compact.exists_bound_of_continuousOn hg_cont
  let C' : ℝ := max C 0
  have hC'_nonneg : 0 ≤ C' := by
    simp [C']
  have hs_fin : volume s < ⊤ := measure_closedBall_lt_top
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ)
      (fun ψ : SchwartzMap (Fin m → ℝ) ℂ => ∫ x in s, g x * ψ x) ?_ ?_ ?_, ?_⟩
  · intro ψ φ
    have hψint :
        Integrable (fun x : Fin m → ℝ => g x * ψ x) (volume.restrict s) := by
      exact ContinuousOn.integrableOn_compact hs_compact
        (hg_cont.mul ψ.continuous.continuousOn)
    have hφint :
        Integrable (fun x : Fin m → ℝ => g x * φ x) (volume.restrict s) := by
      exact ContinuousOn.integrableOn_compact hs_compact
        (hg_cont.mul φ.continuous.continuousOn)
    simpa [mul_add] using
      (MeasureTheory.integral_add
        (μ := volume.restrict s)
        (f := fun x : Fin m → ℝ => g x * ψ x)
        (g := fun x : Fin m → ℝ => g x * φ x)
        hψint hφint)
  · intro a ψ
    have hmul :
        (fun x : Fin m → ℝ => g x * (a * ψ x)) =
          fun x => a * (g x * ψ x) := by
      funext x
      ring
    change ∫ x in s, g x * (a * ψ x) = a * ∫ x in s, g x * ψ x
    rw [hmul]
    simpa using
      (MeasureTheory.integral_const_mul a (fun x : Fin m → ℝ => g x * ψ x) : _)
  · refine ⟨{(0, 0)}, C' * (volume s).toReal, ?_, ?_⟩
    · exact mul_nonneg hC'_nonneg ENNReal.toReal_nonneg
    · intro ψ
      calc
        ‖∫ x in s, g x * ψ x‖
            ≤ (C' * SchwartzMap.seminorm ℂ 0 0 ψ) * (volume s).toReal := by
              refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hs_fin ?_
              intro x hx
              have hgx : ‖g x‖ ≤ C' := le_trans (hC x hx) (le_max_left _ _)
              calc
                ‖g x * ψ x‖ = ‖g x‖ * ‖ψ x‖ := norm_mul _ _
                _ ≤ C' * SchwartzMap.seminorm ℂ 0 0 ψ := by
                  gcongr
                  simpa using (SchwartzMap.le_seminorm ℂ 0 0 ψ x)
        _ = (C' * (volume s).toReal) * SchwartzMap.seminorm ℂ 0 0 ψ := by
              ring
        _ = (C' * (volume s).toReal) *
              ({(0, 0)} : Finset (ℕ × ℕ)).sup
                (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ := by
              simp [mul_left_comm, mul_comm]
  · intro ψ
    rfl

/-- Real directional derivatives of Schwartz tests do not enlarge topological
support. -/
theorem directionalDerivSchwartzCLM_tsupport_subset
    (v : ComplexChartSpace m)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    tsupport
      ((directionalDerivSchwartzCLM v φ :
        SchwartzMap (ComplexChartSpace m) ℂ) :
          ComplexChartSpace m → ℂ) ⊆
    tsupport (φ : ComplexChartSpace m → ℂ) := by
  simpa [directionalDerivSchwartzCLM] using
    (SchwartzMap.tsupport_lineDerivOp_subset (m := v) (f := φ))

/-- Real directional derivatives preserve the predicate of being compactly
supported inside an open chart set. -/
theorem directionalDerivSchwartzCLM_supportsInOpen
    {U : Set (ComplexChartSpace m)}
    {φ : SchwartzMap (ComplexChartSpace m) ℂ}
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U)
    (v : ComplexChartSpace m) :
    SupportsInOpen
      ((directionalDerivSchwartzCLM v φ :
        SchwartzMap (ComplexChartSpace m) ℂ) :
          ComplexChartSpace m → ℂ) U := by
  constructor
  · exact hφ.1.mono'
      ((subset_tsupport _).trans
        (directionalDerivSchwartzCLM_tsupport_subset v φ))
  · exact (directionalDerivSchwartzCLM_tsupport_subset v φ).trans hφ.2

/-- The test-function `∂/∂bar z_j` operator does not enlarge topological
support. -/
theorem dbarSchwartzCLM_tsupport_subset
    (j : Fin m)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    tsupport
      ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
        ComplexChartSpace m → ℂ) ⊆
    tsupport (φ : ComplexChartSpace m → ℂ) := by
  let X := ComplexChartSpace m
  let dre : SchwartzMap X ℂ := directionalDerivSchwartzCLM (complexRealDir j) φ
  let dim : SchwartzMap X ℂ := directionalDerivSchwartzCLM (complexImagDir j) φ
  have hdre : tsupport (dre : X → ℂ) ⊆ tsupport (φ : X → ℂ) := by
    simpa [X, dre] using directionalDerivSchwartzCLM_tsupport_subset
      (m := m) (v := complexRealDir j) φ
  have hdim : tsupport (dim : X → ℂ) ⊆ tsupport (φ : X → ℂ) := by
    simpa [X, dim] using directionalDerivSchwartzCLM_tsupport_subset
      (m := m) (v := complexImagDir j) φ
  have hleft :
      tsupport (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ) ⊆
        tsupport (φ : X → ℂ) := by
    exact
      (tsupport_smul_subset_right (fun _ : X => (1 / 2 : ℂ))
        (dre : X → ℂ)).trans hdre
  have hI :
      tsupport ((Complex.I • dim : SchwartzMap X ℂ) : X → ℂ) ⊆
        tsupport (dim : X → ℂ) := by
    simpa using
      tsupport_smul_subset_right (fun _ : X => Complex.I) (dim : X → ℂ)
  have hright :
      tsupport
          (((1 / 2 : ℂ) • (Complex.I • dim) : SchwartzMap X ℂ) :
            X → ℂ) ⊆
        tsupport (φ : X → ℂ) := by
    exact
      (tsupport_smul_subset_right (fun _ : X => (1 / 2 : ℂ))
        ((Complex.I • dim : SchwartzMap X ℂ) : X → ℂ)).trans
          (hI.trans hdim)
  have hadd :
      tsupport
          ((((1 / 2 : ℂ) • dre +
            (1 / 2 : ℂ) • (Complex.I • dim)) : SchwartzMap X ℂ) :
              X → ℂ) ⊆
        tsupport (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ) ∪
          tsupport
            (((1 / 2 : ℂ) • (Complex.I • dim) : SchwartzMap X ℂ) :
              X → ℂ) := by
    simpa using
      tsupport_add (((1 / 2 : ℂ) • dre : SchwartzMap X ℂ) : X → ℂ)
        (((1 / 2 : ℂ) • (Complex.I • dim) : SchwartzMap X ℂ) : X → ℂ)
  intro x hx
  have hx' :
      x ∈
        tsupport
          ((((1 / 2 : ℂ) • dre +
            (1 / 2 : ℂ) • (Complex.I • dim)) : SchwartzMap X ℂ) :
              X → ℂ) := by
    simpa [dbarSchwartzCLM, X, dre, dim, smul_add] using hx
  rcases hadd hx' with hxleft | hxright
  · exact hleft hxleft
  · exact hright hxright

/-- The Cauchy-Riemann test operator preserves compact support inside the same
open chart set. -/
theorem SupportsInOpen.dbar
    {U : Set (ComplexChartSpace m)}
    {φ : SchwartzMap (ComplexChartSpace m) ℂ}
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U)
    (j : Fin m) :
    SupportsInOpen
      ((dbarSchwartzCLM j φ : SchwartzMap (ComplexChartSpace m) ℂ) :
        ComplexChartSpace m → ℂ) U := by
  constructor
  · exact hφ.1.mono'
      ((subset_tsupport _).trans (dbarSchwartzCLM_tsupport_subset j φ))
  · exact (dbarSchwartzCLM_tsupport_subset j φ).trans hφ.2

/-- Complex-chart translation transports compact support through the inverse
translation and maps the translated topological support into the declared
target set. -/
theorem SupportsInOpen.complexTranslateSchwartz_of_image_subset
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (U V : Set (ComplexChartSpace m)) (a : Fin m → ℝ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U)
    (himage :
      ∀ y : ComplexChartSpace m, y + realEmbed a ∈ U → y ∈ V) :
    SupportsInOpen
      (complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ) V := by
  have hsub :
      tsupport ((φ : ComplexChartSpace m → ℂ) ∘
          fun y : ComplexChartSpace m => y + realEmbed a) ⊆
        (fun y : ComplexChartSpace m => y + realEmbed a) ⁻¹'
          tsupport (φ : ComplexChartSpace m → ℂ) := by
    exact tsupport_comp_subset_preimage (φ : ComplexChartSpace m → ℂ)
      (continuous_id.add continuous_const)
  constructor
  · have hK : IsCompact
        ((fun u : ComplexChartSpace m => u - realEmbed a) ''
          tsupport (φ : ComplexChartSpace m → ℂ)) :=
      hφ.1.image (continuous_id.sub continuous_const)
    refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_
    intro y hy
    have hy' :
        y ∈ tsupport ((φ : ComplexChartSpace m → ℂ) ∘
          fun y : ComplexChartSpace m => y + realEmbed a) := by
      simpa [Function.comp_def, complexTranslateSchwartz_apply] using hy
    refine ⟨y + realEmbed a, hsub hy', ?_⟩
    ext i
    simp
  · intro y hy
    have hy' :
        y ∈ tsupport ((φ : ComplexChartSpace m → ℂ) ∘
          fun y : ComplexChartSpace m => y + realEmbed a) := by
      simpa [Function.comp_def, complexTranslateSchwartz_apply] using hy
    exact himage y (hφ.2 (hsub hy'))

end SCV
