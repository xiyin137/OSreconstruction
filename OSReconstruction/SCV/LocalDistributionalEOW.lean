/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernelRecovery
import OSReconstruction.SCV.LocalEOWChartLinear
import OSReconstruction.SCV.LocalContinuousEOWSideAgreement

/-!
# Local Distributional Edge-of-the-Wedge Support Lemmas

This file starts the upstream Streater-Wightman local EOW package: regularized
local wedge-side functions, common continuous boundary values, and the
product-kernel family that feeds the checked chart-envelope recovery theorem.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

variable {m : ℕ}

/-- The real-mollifier integrand is Bochner integrable when the side function is
holomorphic on an open set containing all real translates used by the compact
kernel support. -/
theorem integrable_realMollifyLocal_integrand_of_translate_margin
    (F : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (Ω : Set (ComplexChartSpace m))
    (z : ComplexChartSpace m)
    (hΩ_open : IsOpen Ω)
    (hF_holo : DifferentiableOn ℂ F Ω)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (hmargin :
      ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ω) :
    Integrable (fun t : Fin m → ℝ => F (z + realEmbed t) * ψ t) := by
  let I : (Fin m → ℝ) → ℂ := fun t => F (z + realEmbed t) * ψ t
  have hrealEmbed_cont : Continuous (fun t : Fin m → ℝ => realEmbed t) :=
    continuous_realEmbed (m := m)
  have hI_cont : Continuous I := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
    · have hshift : z + realEmbed t ∈ Ω := hmargin t ht
      have hF_at : ContinuousAt F (z + realEmbed t) :=
        ((hF_holo (z + realEmbed t) hshift).differentiableAt
          (hΩ_open.mem_nhds hshift)).continuousAt
      have hshift_at :
          ContinuousAt (fun u : Fin m → ℝ => z + realEmbed u) t :=
        (continuous_const.add hrealEmbed_cont).continuousAt
      have hleft : ContinuousAt (fun u : Fin m → ℝ => F (z + realEmbed u)) t :=
        ContinuousAt.comp_of_eq hF_at hshift_at rfl
      simpa [I] using hleft.mul ψ.continuous.continuousAt
    · have hψ_zero :
        (ψ : (Fin m → ℝ) → ℂ) =ᶠ[nhds t] fun _ => 0 := by
          rwa [notMem_tsupport_iff_eventuallyEq] at ht
      have hI_zero : I =ᶠ[nhds t] fun _ => 0 := by
        filter_upwards [hψ_zero] with u hu
        simp [I, hu]
      exact hI_zero.continuousAt
  have hI_support_subset :
      Function.support I ⊆ Function.support (ψ : (Fin m → ℝ) → ℂ) := by
    intro t ht
    by_contra hnot
    have hψt : ψ t = 0 := by
      simpa [Function.mem_support] using hnot
    have hIt : I t = 0 := by
      simp [I, hψt]
    exact ht (by simp [hIt])
  have hI_compact : HasCompactSupport I := by
    rw [HasCompactSupport]
    refine hψ_compact.of_isClosed_subset isClosed_closure ?_
    exact
      closure_minimal
        (fun t ht => subset_tsupport _ (hI_support_subset ht))
        (isClosed_tsupport _)
  simpa [I] using hI_cont.integrable_of_hasCompactSupport hI_compact

/-- For a fixed chart point, real mollification is represented on
fixed-radius supported kernels by a continuous linear functional of the kernel.

The coefficient only needs to be continuous on the closed support ball after
translation into the side domain. -/
theorem exists_realMollifyLocal_valueCLM_of_closedBall
    (F : ComplexChartSpace m → ℂ)
    (Ω : Set (ComplexChartSpace m))
    (z : ComplexChartSpace m)
    (r : ℝ)
    (hF_cont : ContinuousOn F Ω)
    (hmargin :
      ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) r, z + realEmbed t ∈ Ω) :
    ∃ L : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ,
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        KernelSupportWithin ψ r → L ψ = realMollifyLocal F ψ z := by
  let s : Set (Fin m → ℝ) := Metric.closedBall (0 : Fin m → ℝ) r
  let g : (Fin m → ℝ) → ℂ := fun t => F (z + realEmbed t)
  have hshift_cont : Continuous (fun t : Fin m → ℝ => z + realEmbed t) :=
    continuous_const.add (continuous_realEmbed (m := m))
  have hg_cont : ContinuousOn g s := by
    exact hF_cont.comp hshift_cont.continuousOn hmargin
  obtain ⟨L, hL⟩ :=
    exists_closedBall_integral_clm_of_continuousOn (m := m) hg_cont
  refine ⟨L, ?_⟩
  intro ψ hψ
  have hzero : ∀ t : Fin m → ℝ, t ∉ s → g t * ψ t = 0 := by
    intro t ht
    have ht_not_tsupport : t ∉ tsupport (ψ : (Fin m → ℝ) → ℂ) := by
      intro htψ
      exact ht (hψ htψ)
    have hψt : ψ t = 0 := by
      have ht_not_support : t ∉ Function.support (ψ : (Fin m → ℝ) → ℂ) := by
        intro hsupp
        exact ht_not_tsupport (subset_closure hsupp)
      simpa [Function.mem_support] using ht_not_support
    simp [hψt]
  have hset : (∫ t in s, g t * ψ t) = ∫ t : Fin m → ℝ, g t * ψ t := by
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  rw [hL ψ, hset]
  rfl

/-- A cutoff-supported real mollifier value is bounded by the zeroth Schwartz
seminorm of the unconstrained kernel. -/
theorem exists_bound_realMollifyLocal_smulLeftCLM
    (F : ComplexChartSpace m → ℂ)
    (Ω : Set (ComplexChartSpace m))
    (z : ComplexChartSpace m)
    (r : ℝ)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (hF_cont : ContinuousOn F Ω)
    (hmargin :
      ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) r, z + realEmbed t ∈ Ω)
    (hχ_support :
      tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ Metric.closedBall 0 r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        ‖realMollifyLocal F
            (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z‖ ≤
          C * SchwartzMap.seminorm ℂ 0 0 ψ := by
  let s : Set (Fin m → ℝ) := Metric.closedBall (0 : Fin m → ℝ) r
  let gχ : (Fin m → ℝ) → ℂ := fun t => F (z + realEmbed t) * χ t
  have hs_compact : IsCompact s := isCompact_closedBall _ _
  have hshift_cont : Continuous (fun t : Fin m → ℝ => z + realEmbed t) :=
    continuous_const.add (continuous_realEmbed (m := m))
  have hgχ_cont : ContinuousOn gχ s := by
    exact (hF_cont.comp hshift_cont.continuousOn hmargin).mul
      χ.continuous.continuousOn
  obtain ⟨C0, hC0⟩ := hs_compact.exists_bound_of_continuousOn hgχ_cont
  let C : ℝ := max C0 0 * (volume s).toReal
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg (le_max_right C0 0) ENNReal.toReal_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  intro ψ
  let η : SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ
  have hzero :
      ∀ t : Fin m → ℝ, t ∉ s → F (z + realEmbed t) * η t = 0 := by
    intro t ht
    have ht_not_tsupport : t ∉ tsupport (η : (Fin m → ℝ) → ℂ) := by
      intro htη
      have htχ : t ∈ tsupport (χ : (Fin m → ℝ) → ℂ) :=
        (SchwartzMap.tsupport_smulLeftCLM_subset (F := ℂ)
          (g := (χ : (Fin m → ℝ) → ℂ)) (f := ψ) htη).2
      exact ht (hχ_support htχ)
    have hηt : η t = 0 := by
      have ht_not_support : t ∉ Function.support (η : (Fin m → ℝ) → ℂ) := by
        intro hsupp
        exact ht_not_tsupport (subset_closure hsupp)
      simpa [Function.mem_support] using ht_not_support
    simp [hηt]
  have hset :
      (∫ t in s, F (z + realEmbed t) * η t) =
        ∫ t : Fin m → ℝ, F (z + realEmbed t) * η t := by
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  rw [realMollifyLocal]
  rw [← hset]
  have hs_fin : volume s < ⊤ := measure_closedBall_lt_top
  calc
    ‖∫ t in s, F (z + realEmbed t) * η t‖
        ≤ (max C0 0 * SchwartzMap.seminorm ℂ 0 0 ψ) *
            (volume s).toReal := by
          refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hs_fin ?_
          intro t ht
          have hgχt : ‖gχ t‖ ≤ max C0 0 :=
            le_trans (hC0 t ht) (le_max_left _ _)
          have hη_apply : η t = χ t * ψ t := by
            simpa [η, smul_eq_mul] using
              (SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth ψ t)
          calc
            ‖F (z + realEmbed t) * η t‖ = ‖gχ t * ψ t‖ := by
              rw [hη_apply]
              simp [gχ]
              ring_nf
            _ = ‖gχ t‖ * ‖ψ t‖ := norm_mul _ _
            _ ≤ max C0 0 * SchwartzMap.seminorm ℂ 0 0 ψ := by
              gcongr
              simpa using (SchwartzMap.le_seminorm ℂ 0 0 ψ t)
    _ = C * SchwartzMap.seminorm ℂ 0 0 ψ := by
      simp [C]
      ring

/-- If the two side values along the Rudin circle are uniformly bounded by the
zeroth Schwartz seminorm after applying a fixed cutoff, then the normalized
local Rudin envelope value has the same kind of seminorm bound.

This is the quantitative integration step needed for the value-CLM
construction; the uniform side bounds are supplied by separate compactness and
margin estimates. -/
theorem exists_bound_localRudinEnvelope_smulLeftCLM_of_side_bounds
    (δ : ℝ)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (w : ComplexChartSpace m)
    (Cplus Cminus : ℝ)
    (hplus_bound :
      ∀ θ : ℝ, 0 < Real.sin θ →
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          ‖realMollifyLocal Fplus
              (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ)
              (localEOWChart x0 ys
                (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))‖ ≤
            Cplus * SchwartzMap.seminorm ℂ 0 0 ψ)
    (hminus_bound :
      ∀ θ : ℝ, Real.sin θ < 0 →
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          ‖realMollifyLocal Fminus
              (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ)
              (localEOWChart x0 ys
                (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I))))‖ ≤
            Cminus * SchwartzMap.seminorm ℂ 0 0 ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        ‖localRudinEnvelope δ x0 ys
            (fun z =>
              realMollifyLocal Fplus
                (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z)
            (fun z =>
              realMollifyLocal Fminus
                (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z)
            w‖ ≤
          C * SchwartzMap.seminorm ℂ 0 0 ψ := by
  let B : ℝ := max (max Cplus Cminus) 0
  have hB_nonneg : 0 ≤ B := le_max_right (max Cplus Cminus) 0
  let C : ℝ := ‖((2 * Real.pi)⁻¹ : ℝ)‖ * (B * |Real.pi - (-Real.pi)|)
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg (norm_nonneg _) (mul_nonneg hB_nonneg (abs_nonneg _))
  refine ⟨C, hC_nonneg, ?_⟩
  intro ψ
  let η : SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ
  have hseminorm_nonneg : 0 ≤ SchwartzMap.seminorm ℂ 0 0 ψ := by
    positivity
  have h_integrand_bound :
      ∀ θ ∈ Set.uIoc (-Real.pi) Real.pi,
        ‖localRudinIntegrand δ x0 ys
            (fun z => realMollifyLocal Fplus η z)
            (fun z => realMollifyLocal Fminus η z) w θ‖ ≤
          B * SchwartzMap.seminorm ℂ 0 0 ψ := by
    intro θ _hθ
    by_cases hpos : 0 < Real.sin θ
    · have hplus := hplus_bound θ hpos ψ
      have hle :
          Cplus * SchwartzMap.seminorm ℂ 0 0 ψ ≤
            B * SchwartzMap.seminorm ℂ 0 0 ψ := by
        exact mul_le_mul_of_nonneg_right
          ((le_max_left Cplus Cminus).trans
            (le_max_left (max Cplus Cminus) 0))
          hseminorm_nonneg
      exact le_trans (by
        simpa [localRudinIntegrand, η, hpos] using hplus) hle
    · by_cases hneg : Real.sin θ < 0
      · have hminus := hminus_bound θ hneg ψ
        have hle :
            Cminus * SchwartzMap.seminorm ℂ 0 0 ψ ≤
              B * SchwartzMap.seminorm ℂ 0 0 ψ := by
          exact mul_le_mul_of_nonneg_right
            ((le_max_right Cplus Cminus).trans
              (le_max_left (max Cplus Cminus) 0))
            hseminorm_nonneg
        exact le_trans (by
          simpa [localRudinIntegrand, η, hpos, hneg] using hminus) hle
      · simp [localRudinIntegrand, hpos, hneg,
          mul_nonneg hB_nonneg hseminorm_nonneg]
  have h_interval_bound :
      ‖∫ θ in (-Real.pi)..Real.pi,
          localRudinIntegrand δ x0 ys
            (fun z => realMollifyLocal Fplus η z)
            (fun z => realMollifyLocal Fminus η z) w θ‖ ≤
        (B * SchwartzMap.seminorm ℂ 0 0 ψ) * |Real.pi - (-Real.pi)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const h_integrand_bound
  calc
    ‖localRudinEnvelope δ x0 ys
        (fun z => realMollifyLocal Fplus η z)
        (fun z => realMollifyLocal Fminus η z) w‖
        = ‖((2 * Real.pi)⁻¹ : ℝ)‖ *
            ‖∫ θ in (-Real.pi)..Real.pi,
              localRudinIntegrand δ x0 ys
                (fun z => realMollifyLocal Fplus η z)
                (fun z => realMollifyLocal Fminus η z) w θ‖ := by
          simp [localRudinEnvelope, localRudinIntegral]
    _ ≤ ‖((2 * Real.pi)⁻¹ : ℝ)‖ *
          ((B * SchwartzMap.seminorm ℂ 0 0 ψ) * |Real.pi - (-Real.pi)|) := by
        exact mul_le_mul_of_nonneg_left h_interval_bound (norm_nonneg _)
    _ = C * SchwartzMap.seminorm ℂ 0 0 ψ := by
        simp [C]
        ring

/-- Banach-Steinhaus plus interval integration for the Rudin-circle parameter.

If an interval-indexed family of real-linear Schwartz functionals is
pointwise bounded on every Schwartz test function, then the normalized
interval integral is controlled by one finite Schwartz seminorm.  This is the
functional-analytic estimate needed at the real-edge endpoints, where a
zeroth-seminorm compact coefficient bound is too strong for a general
distributional boundary value. -/
theorem exists_schwartz_bound_normalized_intervalIntegral_clm_family
    (T : ℝ → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (hT_bound :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        ∃ C : ℝ, ∀ θ ∈ Set.uIoc (-Real.pi) Real.pi, ‖T θ ψ‖ ≤ C) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        ‖((2 * Real.pi)⁻¹ : ℝ) •
            ∫ θ in (-Real.pi)..Real.pi, T θ ψ‖ ≤
          C * s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ := by
  let I : Set ℝ := Set.uIoc (-Real.pi) Real.pi
  let Tsub : I → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ :=
    fun θ => T θ
  have hTsub_bound :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        ∃ C : ℝ, ∀ θ : I, ‖Tsub θ ψ‖ ≤ C := by
    intro ψ
    obtain ⟨C, hC⟩ := hT_bound ψ
    exact ⟨C, fun θ => hC θ θ.property⟩
  obtain ⟨s, Cnn, _hCnn_ne, hbound⟩ :=
    SchwartzMap.tempered_uniform_schwartz_bound
      (E := Fin m → ℝ) (F := ℂ) (G := ℂ) hTsub_bound
  have sup_apply_real_eq_complex :
      ∀ (s' : Finset (ℕ × ℕ)) (ψ' : SchwartzMap (Fin m → ℝ) ℂ),
        (s'.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ' =
          (s'.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ' := by
    intro s' ψ'
    induction s' using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        have ha_eq :
            (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ a) ψ' =
              (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ a) ψ' := by
          cases a
          rfl
        simp [Finset.sup_insert, ih, ha_eq]
  let C : ℝ :=
    ‖((2 * Real.pi)⁻¹ : ℝ)‖ * ((Cnn : ℝ) * |Real.pi - (-Real.pi)|)
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg (norm_nonneg _)
      (mul_nonneg (NNReal.coe_nonneg Cnn) (abs_nonneg _))
  refine ⟨s, C, hC_nonneg, ?_⟩
  intro ψ
  let pℂ : Seminorm ℂ (SchwartzMap (Fin m → ℝ) ℂ) :=
    s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)
  have hp_eq :
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ = pℂ ψ := by
    dsimp [pℂ]
    exact sup_apply_real_eq_complex s ψ
  have hp_nonneg : 0 ≤ pℂ ψ := by
    positivity
  have h_interval_bound :
      ‖∫ θ in (-Real.pi)..Real.pi, T θ ψ‖ ≤
        ((Cnn : ℝ) * pℂ ψ) * |Real.pi - (-Real.pi)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro θ hθ
    have hθ' : θ ∈ I := hθ
    have h := hbound ⟨θ, hθ'⟩ ψ
    rw [← hp_eq]
    simpa [Tsub] using h
  calc
    ‖((2 * Real.pi)⁻¹ : ℝ) •
        ∫ θ in (-Real.pi)..Real.pi, T θ ψ‖
        = ‖((2 * Real.pi)⁻¹ : ℝ)‖ *
            ‖∫ θ in (-Real.pi)..Real.pi, T θ ψ‖ := by
          simp
    _ ≤ ‖((2 * Real.pi)⁻¹ : ℝ)‖ *
          (((Cnn : ℝ) * pℂ ψ) * |Real.pi - (-Real.pi)|) := by
        exact mul_le_mul_of_nonneg_left h_interval_bound (norm_nonneg _)
    _ = C * pℂ ψ := by
        simp [C, pℂ]
        ring

/-- Local real-direction mollification of a holomorphic function is
holomorphic on the shrunken local domain when all real translates used by the
kernel support stay inside the original holomorphy domain. -/
theorem localRealMollifySide_holomorphicOn_of_translate_margin
    (F : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (Ω D : Set (ComplexChartSpace m))
    (hΩ_open : IsOpen Ω)
    (hD_open : IsOpen D)
    (hF_holo : DifferentiableOn ℂ F Ω)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (hmargin :
      ∀ z ∈ D, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ω) :
    DifferentiableOn ℂ (realMollifyLocal F ψ) D := by
  intro z hz
  obtain ⟨R, hRpos, hRsub⟩ := Metric.isOpen_iff.mp hD_open z hz
  let r : ℝ := R / 2
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  let s : Set (ComplexChartSpace m) := Metric.ball z r
  have hs : s ∈ 𝓝 z := Metric.ball_mem_nhds z hrpos
  have hs_sub : s ⊆ D := by
    intro w hw
    exact hRsub <| by
      have hwR : dist w z < R := by
        calc
          dist w z < r := hw
          _ < R := by
            dsimp [r]
            linarith
      simpa [Metric.mem_ball] using hwR
  have hclosed_sub : Metric.closedBall z r ⊆ D := by
    intro w hw
    exact hRsub <| by
      have hwR : dist w z < R := by
        calc
          dist w z ≤ r := by simpa [Metric.mem_closedBall] using hw
          _ < R := by
            dsimp [r]
            linarith
      simpa [Metric.mem_ball] using hwR
  let I : ComplexChartSpace m → (Fin m → ℝ) → ℂ :=
    fun w t => F (w + realEmbed t) * ψ t
  let I' : ComplexChartSpace m → (Fin m → ℝ) → (ComplexChartSpace m →L[ℂ] ℂ) :=
    fun w t => (ψ t) • fderiv ℂ F (w + realEmbed t)
  have hψ_tsupport_compact :
      IsCompact (tsupport (ψ : (Fin m → ℝ) → ℂ)) := by
    simpa [HasCompactSupport] using hψ_compact
  have hrealEmbed_cont : Continuous (fun t : Fin m → ℝ => realEmbed t) :=
    continuous_realEmbed (m := m)
  have hI_cont_at :
      ∀ w ∈ D, Continuous fun t : Fin m → ℝ => I w t := by
    intro w hw
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
    · have hshift : w + realEmbed t ∈ Ω := hmargin w hw t ht
      have hF_at : ContinuousAt F (w + realEmbed t) :=
        ((hF_holo (w + realEmbed t) hshift).differentiableAt
          (hΩ_open.mem_nhds hshift)).continuousAt
      have hshift_at :
          ContinuousAt (fun u : Fin m → ℝ => w + realEmbed u) t :=
        (continuous_const.add hrealEmbed_cont).continuousAt
      have hleft : ContinuousAt (fun u : Fin m → ℝ => F (w + realEmbed u)) t :=
        ContinuousAt.comp_of_eq hF_at hshift_at rfl
      simpa [I] using hleft.mul ψ.continuous.continuousAt
    · have hψ_zero :
        (ψ : (Fin m → ℝ) → ℂ) =ᶠ[nhds t] fun _ => 0 := by
          rwa [notMem_tsupport_iff_eventuallyEq] at ht
      have hI_zero : (fun u : Fin m → ℝ => I w u) =ᶠ[nhds t] fun _ => 0 := by
        filter_upwards [hψ_zero] with u hu
        simp [I, hu]
      exact hI_zero.continuousAt
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (I w) volume := by
    filter_upwards [hs] with w hw
    exact (hI_cont_at w (hs_sub hw)).aestronglyMeasurable
  have hI_support_subset :
      ∀ w, Function.support (I w) ⊆
        Function.support (ψ : (Fin m → ℝ) → ℂ) := by
    intro w t ht
    by_contra hnot
    have hψt : ψ t = 0 := by
      simpa [Function.mem_support] using hnot
    have hIt : I w t = 0 := by
      simp [I, hψt]
    exact ht (by simp [hIt])
  have hI_compact : ∀ w, HasCompactSupport (I w) := by
    intro w
    rw [HasCompactSupport]
    refine hψ_compact.of_isClosed_subset isClosed_closure ?_
    exact
      closure_minimal
        (fun t ht => subset_tsupport _ (hI_support_subset w ht))
        (isClosed_tsupport _)
  have hF_int : Integrable (I z) volume :=
    (hI_cont_at z hz).integrable_of_hasCompactSupport (hI_compact z)
  have hF_contDiff : ContDiffOn ℂ 1 F Ω := by
    exact
      (hF_holo.analyticOnNhd_of_finiteDimensional hΩ_open).contDiffOn_of_completeSpace
  have hF_fderiv_cont : ContinuousOn (fderiv ℂ F) Ω :=
    hF_contDiff.continuousOn_fderiv_of_isOpen hΩ_open le_rfl
  let K : Set (ComplexChartSpace m) :=
    (Metric.closedBall z r ×ˢ tsupport (ψ : (Fin m → ℝ) → ℂ)).image
      (fun p : ComplexChartSpace m × (Fin m → ℝ) => p.1 + realEmbed p.2)
  have hK_compact : IsCompact K := by
    exact
      ((isCompact_closedBall z r).prod hψ_tsupport_compact).image <|
        (continuous_fst.add (hrealEmbed_cont.comp continuous_snd))
  have hK_sub : K ⊆ Ω := by
    intro w hw
    rcases hw with ⟨⟨x, t⟩, hx, rfl⟩
    exact hmargin x (hclosed_sub hx.1) t hx.2
  obtain ⟨Cbound, hCbound⟩ :=
    hK_compact.exists_bound_of_continuousOn (hF_fderiv_cont.mono hK_sub)
  let bound : (Fin m → ℝ) → ℝ := fun t => Cbound * ‖ψ t‖
  have hF'_meas : AEStronglyMeasurable (I' z) volume := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine Continuous.aemeasurable ?_
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
    · have hz_shift : z + realEmbed t ∈ Ω := hmargin z hz t ht
      have hderiv_at : ContinuousAt (fderiv ℂ F) (z + realEmbed t) :=
        (hF_fderiv_cont (z + realEmbed t) hz_shift).continuousAt
          (hΩ_open.mem_nhds hz_shift)
      have hshift_at :
          ContinuousAt (fun u : Fin m → ℝ => z + realEmbed u) t :=
        (continuous_const.add hrealEmbed_cont).continuousAt
      have hfderiv_shift :
          ContinuousAt (fun u : Fin m → ℝ => fderiv ℂ F (z + realEmbed u)) t :=
        ContinuousAt.comp_of_eq hderiv_at hshift_at rfl
      simpa [I'] using ψ.continuous.continuousAt.smul hfderiv_shift
    · have hψ_zero :
        (ψ : (Fin m → ℝ) → ℂ) =ᶠ[nhds t] fun _ => 0 := by
          rwa [notMem_tsupport_iff_eventuallyEq] at ht
      have hI'_zero : (fun u : Fin m → ℝ => I' z u) =ᶠ[nhds t] fun _ => 0 := by
        filter_upwards [hψ_zero] with u hu
        ext v
        simp [I', hu]
      exact hI'_zero.continuousAt
  have h_bound : ∀ᵐ t ∂volume, ∀ w ∈ s, ‖I' w t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall ?_
    intro t w hw
    by_cases hψt : ψ t = 0
    · have hzeroI' : I' w t = 0 := by
        ext v
        simp [I', hψt]
      have hzeroBound : bound t = 0 := by simp [bound, hψt]
      rw [hzeroI', norm_zero, hzeroBound]
    · have ht_support :
          t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ) :=
        subset_tsupport _ (by simpa [Function.mem_support] using hψt)
      have hwK : w + realEmbed t ∈ K := by
        refine ⟨⟨w, t⟩, ?_, rfl⟩
        refine ⟨?_, ht_support⟩
        simpa [s, Metric.mem_ball, Metric.mem_closedBall] using le_of_lt hw
      have hfderiv_bound : ‖fderiv ℂ F (w + realEmbed t)‖ ≤ Cbound :=
        hCbound _ hwK
      calc
        ‖I' w t‖ = ‖ψ t‖ * ‖fderiv ℂ F (w + realEmbed t)‖ := by
          simpa [I'] using norm_smul (ψ t) (fderiv ℂ F (w + realEmbed t))
        _ ≤ ‖ψ t‖ * Cbound := by
          exact mul_le_mul_of_nonneg_left hfderiv_bound (norm_nonneg _)
        _ = bound t := by ring
  have hbound_cont : Continuous bound := continuous_const.mul ψ.continuous.norm
  have hbound_support_subset :
      Function.support bound ⊆ Function.support (ψ : (Fin m → ℝ) → ℂ) := by
    intro t ht
    by_contra hnot
    have hψt : ψ t = 0 := by
      simpa [Function.mem_support] using hnot
    have hbt : bound t = 0 := by simp [bound, hψt]
    exact ht (by simp [hbt])
  have hbound_compact : HasCompactSupport bound := by
    rw [HasCompactSupport]
    refine hψ_compact.of_isClosed_subset isClosed_closure ?_
    exact
      closure_minimal
        (fun t ht => subset_tsupport _ (hbound_support_subset ht))
        (isClosed_tsupport _)
  have hbound_int : Integrable bound volume :=
    hbound_cont.integrable_of_hasCompactSupport hbound_compact
  have h_diff : ∀ᵐ t ∂volume, ∀ w ∈ s, HasFDerivAt (I · t) (I' w t) w := by
    refine Filter.Eventually.of_forall ?_
    intro t w hw
    by_cases hψt : ψ t = 0
    · have hI_zero : (fun u : ComplexChartSpace m => I u t) = fun _ => 0 := by
        funext u
        simp [I, hψt]
      have hI'_zero : I' w t = 0 := by
        ext v
        simp [I', hψt]
      rw [hI_zero, hI'_zero]
      exact hasFDerivAt_const (0 : ℂ) w
    · have ht_support :
          t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ) :=
        subset_tsupport _ (by simpa [Function.mem_support] using hψt)
      have hwD : w ∈ D := hs_sub hw
      have hshift : w + realEmbed t ∈ Ω := hmargin w hwD t ht_support
      have hderiv_F :
          HasFDerivAt F (fderiv ℂ F (w + realEmbed t)) (w + realEmbed t) :=
        ((hF_holo (w + realEmbed t) hshift).differentiableAt
          (hΩ_open.mem_nhds hshift)).hasFDerivAt
      have htrans :
          HasFDerivAt (fun u : ComplexChartSpace m => u + realEmbed t)
            (ContinuousLinearMap.id ℂ (ComplexChartSpace m)) w := by
        simpa using
          ((ContinuousLinearMap.id ℂ (ComplexChartSpace m)).hasFDerivAt).add_const
            (realEmbed t)
      have hcomp :
          HasFDerivAt (fun u : ComplexChartSpace m => F (u + realEmbed t))
            (fderiv ℂ F (w + realEmbed t)) w := by
        simpa using hderiv_F.comp w htrans
      simpa [I, I'] using hcomp.mul_const (ψ t)
  have hderiv :
      HasFDerivAt
        (fun w : ComplexChartSpace m => ∫ t : Fin m → ℝ, I w t)
        (∫ t : Fin m → ℝ, I' z t)
        z := by
    exact
      hasFDerivAt_integral_of_dominated_of_fderiv_le
        hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa [realMollifyLocal, I] using hderiv.differentiableAt.differentiableWithinAt

/-- The regularized boundary value
`x ↦ T (translateSchwartz (-x) ψ)` is continuous on any real edge set when the
regularizing kernel has compact support. -/
theorem regularizedBoundaryValue_continuousOn
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (E : Set (Fin m → ℝ))
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ)) :
    ContinuousOn (fun x : Fin m → ℝ => T (translateSchwartz (-x) ψ)) E := by
  have hcont :
      Continuous (fun t : Fin m → ℝ => T (translateSchwartz t ψ)) :=
    continuous_apply_translateSchwartz_of_isCompactSupport T ψ hψ_compact
  simpa [Function.comp_def] using (hcont.comp continuous_neg).continuousOn

/-- A real-direction mollified value is the boundary slice at the imaginary
part, paired with the translated real kernel centered at the real part. -/
theorem realMollifyLocal_eq_sliceIntegral_translate
    (F : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (w : ComplexChartSpace m) :
    realMollifyLocal F ψ w =
      ∫ x : Fin m → ℝ,
        F (fun i => (x i : ℂ) + ((w i).im : ℂ) * Complex.I) *
          translateSchwartz (fun i => - (w i).re) ψ x := by
  let a : Fin m → ℝ := fun i => (w i).re
  let f : (Fin m → ℝ) → ℂ := fun x =>
    F (fun i => (x i : ℂ) + ((w i).im : ℂ) * Complex.I) *
      translateSchwartz (fun i => - (w i).re) ψ x
  calc
    realMollifyLocal F ψ w =
        ∫ t : Fin m → ℝ,
          F (fun i => ((t i + a i : ℝ) : ℂ) + ((w i).im : ℂ) * Complex.I) *
            ψ t := by
          apply integral_congr_ae
          filter_upwards with t
          congr 2
          ext i
          simp [realEmbed, a]
          conv_lhs => rw [← Complex.re_add_im (w i)]
          abel
    _ = ∫ t : Fin m → ℝ, f (t + a) := by
          apply integral_congr_ae
          filter_upwards with t
          dsimp [f]
          have hshift : t + a + (fun i => - (w i).re) = t := by
            ext i
            simp [a]
          rw [hshift]
    _ = ∫ x : Fin m → ℝ, f x := by
          exact MeasureTheory.integral_add_right_eq_self (μ := volume) f a
    _ =
        ∫ x : Fin m → ℝ,
          F (fun i => (x i : ℂ) + ((w i).im : ℂ) * Complex.I) *
            translateSchwartz (fun i => - (w i).re) ψ x := rfl

/-- Translating the real smoothing kernel is the same as translating the
complex argument in the opposite real direction. -/
theorem realMollifyLocal_translateSchwartz
    (F : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (a : Fin m → ℝ)
    (z : ComplexChartSpace m) :
    realMollifyLocal F (translateSchwartz a ψ) z =
      realMollifyLocal F ψ (z - realEmbed a) := by
  let f : (Fin m → ℝ) → ℂ :=
    fun x => F (z + realEmbed (x - a)) * ψ x
  calc
    realMollifyLocal F (translateSchwartz a ψ) z =
        ∫ t : Fin m → ℝ, f (t + a) := by
          apply integral_congr_ae
          filter_upwards with t
          dsimp [f, realMollifyLocal]
          have hsub : t + a - a = t := by
            ext i
            simp
          rw [hsub]
    _ = ∫ x : Fin m → ℝ, f x := by
          exact MeasureTheory.integral_add_right_eq_self (μ := volume) f a
    _ = realMollifyLocal F ψ (z - realEmbed a) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [f, realMollifyLocal]
          congr 2
          ext i
          simp [realEmbed]
          ring

/-- Change variables in the real mollifier through the local EOW chart's
linear part.  The pushed kernel is the Jacobian-normalized chart-to-original
kernel, so the original real-edge mollifier equals the chart-coordinate
integral. -/
theorem realMollifyLocal_localEOWRealLinearKernelPushforwardCLM
    (F : ComplexChartSpace m → ℂ)
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (z : ComplexChartSpace m) :
    realMollifyLocal F (localEOWRealLinearKernelPushforwardCLM ys hli φ) z =
      ∫ u : Fin m → ℝ,
        F (z + realEmbed (localEOWRealLinearPart ys u)) * φ u := by
  let e := localEOWRealLinearCLE ys hli
  let A : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := e.toContinuousLinearMap
  have hlin :
      (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) =
        Matrix.toLin' (localEOWRealLinearMatrix ys) := by
    apply LinearMap.ext
    intro u
    ext a
    change (localEOWRealLinearCLE ys hli u) a =
      (Matrix.toLin' (localEOWRealLinearMatrix ys) u) a
    rw [localEOWRealLinearCLE_apply]
    simpa [Matrix.toLin'_apply] using
      (congrFun (localEOWRealLinearMatrix_mulVec ys u).symm a)
  have hjac : localEOWRealJacobianAbs ys = |A.det| := by
    rw [localEOWRealJacobianAbs]
    change |(localEOWRealLinearMatrix ys).det| =
      |LinearMap.det (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))|
    rw [hlin, LinearMap.det_toLin']
  have hdet_ne : A.det ≠ 0 := by
    exact (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hdet_abs_ne : |A.det| ≠ 0 := abs_ne_zero.mpr hdet_ne
  have he_symm (u : Fin m → ℝ) :
      e.symm (localEOWRealLinearPart ys u) = u := by
    rw [← localEOWRealLinearCLE_apply ys hli u]
    exact e.symm_apply_apply u
  let g : (Fin m → ℝ) → ℂ := fun y =>
    F (z + realEmbed y) *
      (((localEOWRealJacobianAbs ys)⁻¹ : ℂ) * φ (e.symm y))
  have hfderiv :
      ∀ x ∈ (Set.univ : Set (Fin m → ℝ)),
        HasFDerivWithinAt (fun u : Fin m → ℝ => e u) A Set.univ x := by
    intro x _hx
    exact e.hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn (fun u : Fin m → ℝ => e u) Set.univ := by
    intro x _hx y _hy hxy
    exact e.injective hxy
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) (s := (Set.univ : Set (Fin m → ℝ)))
      (f := fun u : Fin m → ℝ => e u) (f' := fun _ => A)
      MeasurableSet.univ hfderiv hinj g
  have himage : (fun u : Fin m → ℝ => e u) '' Set.univ = Set.univ := by
    ext y
    constructor
    · intro _hy
      trivial
    · intro _hy
      exact ⟨e.symm y, trivial, by simp [e]⟩
  rw [himage] at hchange
  have hrhs :
      ∀ u : Fin m → ℝ,
        |A.det| • g (e u) =
          F (z + realEmbed (localEOWRealLinearPart ys u)) * φ u := by
    intro u
    dsimp [g]
    rw [localEOWRealLinearCLE_apply, he_symm, hjac]
    field_simp [hdet_abs_ne]
  calc
    realMollifyLocal F (localEOWRealLinearKernelPushforwardCLM ys hli φ) z =
        ∫ y : Fin m → ℝ, g y := by
          simp [realMollifyLocal, g, e,
            localEOWRealLinearKernelPushforwardCLM_apply]
    _ = ∫ u : Fin m → ℝ, |A.det| • g (e u) := by
          simpa using hchange
    _ = ∫ u : Fin m → ℝ,
        F (z + realEmbed (localEOWRealLinearPart ys u)) * φ u := by
          apply integral_congr_ae
          filter_upwards with u
          exact hrhs u

/-- The overlap of one local Rudin window with its real translate by `a`.

This is the honest domain for local fixed-window covariance: both `w` and
`w - realEmbed a` must remain in the same chart ball. -/
def localEOWShiftedWindow (δ : ℝ) (a : Fin m → ℝ) :
    Set (ComplexChartSpace m) :=
  Metric.ball (0 : ComplexChartSpace m) (δ / 2) ∩
    {w | w - realEmbed a ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2)}

theorem localEOWShiftedWindow_mem_left {δ : ℝ} {a : Fin m → ℝ}
    {w : ComplexChartSpace m}
    (hw : w ∈ localEOWShiftedWindow (m := m) δ a) :
    w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2) :=
  hw.1

theorem localEOWShiftedWindow_mem_shift {δ : ℝ} {a : Fin m → ℝ}
    {w : ComplexChartSpace m}
    (hw : w ∈ localEOWShiftedWindow (m := m) δ a) :
    w - realEmbed a ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2) :=
  hw.2

/-- The shifted local EOW window is open. -/
theorem isOpen_localEOWShiftedWindow (δ : ℝ) (a : Fin m → ℝ) :
    IsOpen (localEOWShiftedWindow (m := m) δ a) := by
  exact Metric.isOpen_ball.inter
    (Metric.isOpen_ball.preimage (continuous_id.sub continuous_const))

/-- The shifted local EOW window is convex as the intersection of two balls:
the original chart ball and the ball centered at `realEmbed a`. -/
theorem convex_localEOWShiftedWindow (δ : ℝ) (a : Fin m → ℝ) :
    Convex ℝ (localEOWShiftedWindow (m := m) δ a) := by
  rw [localEOWShiftedWindow]
  refine (convex_ball (0 : ComplexChartSpace m) (δ / 2)).inter ?_
  have hset : {w : ComplexChartSpace m |
        w - realEmbed a ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2)} =
      Metric.ball (realEmbed a : ComplexChartSpace m) (δ / 2) := by
    ext w
    simp [Metric.mem_ball, dist_eq_norm]
  rw [hset]
  exact convex_ball (realEmbed a : ComplexChartSpace m) (δ / 2)

/-- The shifted local EOW window is preconnected, so the identity theorem can
propagate equality from any nonempty open seed inside the overlap. -/
theorem isPreconnected_localEOWShiftedWindow (δ : ℝ) (a : Fin m → ℝ) :
    IsPreconnected (localEOWShiftedWindow (m := m) δ a) :=
  (convex_localEOWShiftedWindow (m := m) δ a).isPreconnected

/-- A small real shift has a positive-imaginary seed inside the shifted local
EOW window.  This discharges the nonempty seed hypothesis in local covariance
applications where both translated complex test supports stay in a sufficiently
small chart ball. -/
theorem exists_positive_imag_mem_localEOWShiftedWindow_of_norm_lt
    (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ)
    {a : Fin m → ℝ} (ha : ‖a‖ < δ / 4) :
    ∃ z0 : ComplexChartSpace m,
      z0 ∈ localEOWShiftedWindow (m := m) δ a ∧
      (∀ j, 0 < (z0 j).im) := by
  let c : ℂ := ((δ / 8 : ℝ) : ℂ) * Complex.I
  let z0 : ComplexChartSpace m := fun _ => c
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hδnonneg : 0 ≤ δ := le_of_lt hδ
  have hc_norm : ‖c‖ = δ / 8 := by
    simp [c, Real.norm_eq_abs, hδnonneg]
  have hz0_norm : ‖z0‖ = δ / 8 := by
    simp [z0, hc_norm]
  refine ⟨z0, ?_, ?_⟩
  · rw [localEOWShiftedWindow]
    constructor
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero, hz0_norm]
      linarith
    · change z0 - realEmbed a ∈
        Metric.ball (0 : ComplexChartSpace m) (δ / 2)
      rw [Metric.mem_ball, dist_eq_norm]
      have hshift_le : ‖z0 - realEmbed a - 0‖ ≤ δ / 8 + ‖a‖ := by
        calc
          ‖z0 - realEmbed a - 0‖ = ‖z0 - realEmbed a‖ := by simp
          _ ≤ ‖z0‖ + ‖realEmbed a‖ := norm_sub_le _ _
          _ ≤ δ / 8 + ‖a‖ := by
            exact add_le_add (le_of_eq hz0_norm) (norm_realEmbed_le (m := m) a)
      linarith
  · intro j
    have hδ8pos : 0 < δ / 8 := by linarith
    simpa [z0, c] using hδ8pos

/-- Chart-coordinate form of the Jacobian-normalized kernel pushforward
identity.  After transporting the kernel to the original real edge, the
original mollifier at `localEOWChart x0 ys w` is exactly the chart-coordinate
mollifier in the Rudin variable. -/
theorem realMollifyLocal_localEOWChart_kernelPushforwardCLM
    (F : ComplexChartSpace m → ℂ)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (w : ComplexChartSpace m) :
    realMollifyLocal F (localEOWRealLinearKernelPushforwardCLM ys hli φ)
        (localEOWChart x0 ys w) =
      ∫ u : Fin m → ℝ,
        F (localEOWChart x0 ys (w + realEmbed u)) * φ u := by
  rw [realMollifyLocal_localEOWRealLinearKernelPushforwardCLM]
  apply integral_congr_ae
  filter_upwards with u
  rw [localEOWChart_add_realEmbed]

/-- Direct pulled-back side-function form of the chart-kernel pushforward
identity.  This is the form consumed by the local product-kernel recovery,
where the side functions live in Rudin chart coordinates. -/
theorem realMollifyLocal_localEOWChart_kernelPushforwardCLM_pullback
    (F : ComplexChartSpace m → ℂ)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (w : ComplexChartSpace m) :
    realMollifyLocal F (localEOWRealLinearKernelPushforwardCLM ys hli φ)
        (localEOWChart x0 ys w) =
      realMollifyLocal (fun ζ => F (localEOWChart x0 ys ζ)) φ w := by
  rw [realMollifyLocal_localEOWChart_kernelPushforwardCLM]
  rfl

/-- Translating a chart-coordinate smoothing kernel before
Jacobian-normalized pushforward is the same as translating the Rudin chart
point in the opposite direction.  This is the side-branch identity used by
fixed-window uniqueness to prove regularized-family covariance. -/
theorem realMollifyLocal_localEOWChart_translate_kernelPushforwardCLM
    (F : ComplexChartSpace m → ℂ)
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (a : Fin m → ℝ)
    (w : ComplexChartSpace m) :
    realMollifyLocal F
        (localEOWRealLinearKernelPushforwardCLM ys hli (translateSchwartz a φ))
        (localEOWChart x0 ys w) =
      realMollifyLocal F (localEOWRealLinearKernelPushforwardCLM ys hli φ)
        (localEOWChart x0 ys (w - realEmbed a)) := by
  rw [realMollifyLocal_localEOWChart_kernelPushforwardCLM]
  rw [realMollifyLocal_localEOWChart_kernelPushforwardCLM]
  let f : (Fin m → ℝ) → ℂ := fun u =>
    F (localEOWChart x0 ys (w + realEmbed (u - a))) * φ u
  calc
    ∫ u : Fin m → ℝ,
        F (localEOWChart x0 ys (w + realEmbed u)) * translateSchwartz a φ u =
        ∫ u : Fin m → ℝ, f (u + a) := by
          apply integral_congr_ae
          filter_upwards with u
          dsimp [f]
          have hsub : u + a - a = u := by
            ext i
            simp
          rw [hsub]
    _ = ∫ u : Fin m → ℝ, f u := by
          exact MeasureTheory.integral_add_right_eq_self (μ := volume) f a
    _ = ∫ u : Fin m → ℝ,
        F (localEOWChart x0 ys (w - realEmbed a + realEmbed u)) * φ u := by
          apply integral_congr_ae
          filter_upwards with u
          dsimp [f]
          have harg : w + realEmbed (u - a) =
              w - realEmbed a + realEmbed u := by
            ext i
            simp [realEmbed]
            ring
          rw [harg]

/-- Additivity of real-direction mollification in the smoothing kernel, with
the required Bochner-integrability hypotheses explicit. -/
theorem realMollifyLocal_add_of_integrable
    (F : ComplexChartSpace m → ℂ)
    (ψ η : SchwartzMap (Fin m → ℝ) ℂ)
    (z : ComplexChartSpace m)
    (hψ : Integrable fun t : Fin m → ℝ => F (z + realEmbed t) * ψ t)
    (hη : Integrable fun t : Fin m → ℝ => F (z + realEmbed t) * η t) :
    realMollifyLocal F (ψ + η) z =
      realMollifyLocal F ψ z + realMollifyLocal F η z := by
  rw [realMollifyLocal, realMollifyLocal, realMollifyLocal]
  trans ∫ t : Fin m → ℝ,
      (F (z + realEmbed t) * ψ t) + (F (z + realEmbed t) * η t)
  · apply integral_congr_ae
    filter_upwards with t
    simp [mul_add]
  · exact integral_add hψ hη

/-- Complex homogeneity of real-direction mollification in the smoothing
kernel. -/
theorem realMollifyLocal_smul
    (F : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (c : ℂ)
    (z : ComplexChartSpace m) :
    realMollifyLocal F (c • ψ) z =
      c * realMollifyLocal F ψ z := by
  rw [realMollifyLocal, realMollifyLocal]
  trans ∫ t : Fin m → ℝ, c • (F (z + realEmbed t) * ψ t)
  · apply integral_congr_ae
    filter_upwards with t
    simp
    ring
  · rw [integral_smul]
    rfl

/-- Additivity of real-direction mollification on a side domain, with
integrability discharged from compact supports and the translate-margin
hypotheses. -/
theorem realMollifyLocal_add_of_translate_margin
    (F : ComplexChartSpace m → ℂ)
    (ψ η : SchwartzMap (Fin m → ℝ) ℂ)
    (Ω : Set (ComplexChartSpace m))
    (z : ComplexChartSpace m)
    (hΩ_open : IsOpen Ω)
    (hF_holo : DifferentiableOn ℂ F Ω)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (hη_compact : HasCompactSupport (η : (Fin m → ℝ) → ℂ))
    (hψ_margin :
      ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ω)
    (hη_margin :
      ∀ t ∈ tsupport (η : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ω) :
    realMollifyLocal F (ψ + η) z =
      realMollifyLocal F ψ z + realMollifyLocal F η z :=
  realMollifyLocal_add_of_integrable F ψ η z
    (integrable_realMollifyLocal_integrand_of_translate_margin
      F ψ Ω z hΩ_open hF_holo hψ_compact hψ_margin)
    (integrable_realMollifyLocal_integrand_of_translate_margin
      F η Ω z hΩ_open hF_holo hη_compact hη_margin)

/-- If the slice functional at imaginary part `y` is represented by integrating
`F(x + i y)` against the test function, then local real mollification at `w`
is exactly that slice functional evaluated on the kernel translated by
`-re w`. -/
theorem realMollifyLocal_eq_sliceFunctional
    (F : ComplexChartSpace m → ℂ)
    (Tseq : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (w : ComplexChartSpace m)
    (hTseq_eval :
      ∀ (y : Fin m → ℝ) (φ : SchwartzMap (Fin m → ℝ) ℂ),
        Tseq y φ =
          ∫ x : Fin m → ℝ,
            F (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) * φ x) :
    realMollifyLocal F ψ w =
      Tseq (fun i => (w i).im)
        (translateSchwartz (fun i => - (w i).re) ψ) := by
  rw [realMollifyLocal_eq_sliceIntegral_translate]
  rw [hTseq_eval]

/-- A compactly supported cutoff times a continuous boundary slice defines a
tempered slice functional.  This is the local Streater-Wightman construction of
the `F(x + i y)` slice after extending compactly supported edge tests by a fixed
cutoff. -/
theorem exists_cutoffSliceIntegral_clm_of_continuousOn
    (F : ComplexChartSpace m → ℂ)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (Ω : Set (ComplexChartSpace m))
    (y : Fin m → ℝ)
    (hΩ_open : IsOpen Ω)
    (hF_cont : ContinuousOn F Ω)
    (hχ_compact : HasCompactSupport (χ : (Fin m → ℝ) → ℂ))
    (hmargin :
      ∀ x ∈ tsupport (χ : (Fin m → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ω) :
    ∃ T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ,
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        T φ = ∫ x : Fin m → ℝ,
          (χ x * F (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I)) *
            φ x := by
  let slice : (Fin m → ℝ) → ComplexChartSpace m :=
    fun x i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I
  let g : (Fin m → ℝ) → ℂ := fun x => χ x * F (slice x)
  have hslice_cont : Continuous slice := by
    refine continuous_pi ?_
    intro i
    exact (Complex.continuous_ofReal.comp (continuous_apply i)).add continuous_const
  have hg_cont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport (χ : (Fin m → ℝ) → ℂ)
    · have hFx : slice x ∈ Ω := hmargin x hx
      have hF_at : ContinuousAt F (slice x) :=
        (hF_cont (slice x) hFx).continuousAt (hΩ_open.mem_nhds hFx)
      have hF_slice : ContinuousAt (fun u : Fin m → ℝ => F (slice u)) x :=
        hF_at.comp hslice_cont.continuousAt
      simpa [g] using χ.continuous.continuousAt.mul hF_slice
    · have hχ_zero : (χ : (Fin m → ℝ) → ℂ) =ᶠ[nhds x] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at hx
      have hg_zero : g =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [hχ_zero] with u hu
        simp [g, hu]
      exact hg_zero.continuousAt
  have hg_support_subset :
      Function.support g ⊆ Function.support (χ : (Fin m → ℝ) → ℂ) := by
    intro x hx
    by_contra hnot
    have hχx : χ x = 0 := by
      simpa [Function.mem_support] using hnot
    have hgx : g x = 0 := by simp [g, hχx]
    exact hx (by simp [hgx])
  have hg_compact : HasCompactSupport g := by
    rw [HasCompactSupport]
    refine hχ_compact.of_isClosed_subset isClosed_closure ?_
    exact
      closure_minimal
        (fun x hx => subset_tsupport _ (hg_support_subset hx))
        (isClosed_tsupport _)
  have hg_int : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      Integrable (fun x : Fin m → ℝ => g x * φ x) := by
    intro φ
    have hprod_support_subset :
        Function.support (fun x : Fin m → ℝ => g x * φ x) ⊆
          Function.support g := by
      intro x hx
      by_contra hnot
      have hgx : g x = 0 := by
        simpa [Function.mem_support] using hnot
      have hprod : g x * φ x = 0 := by simp [hgx]
      exact hx (by simp [hprod])
    have hprod_compact :
        HasCompactSupport (fun x : Fin m → ℝ => g x * φ x) := by
      rw [HasCompactSupport]
      refine hg_compact.of_isClosed_subset isClosed_closure ?_
      exact
        closure_minimal
          (fun x hx => subset_tsupport _ (hprod_support_subset hx))
          (isClosed_tsupport _)
    exact (hg_cont.mul φ.continuous).integrable_of_hasCompactSupport hprod_compact
  obtain ⟨T, hT⟩ := exists_integral_clm_of_continuous hg_cont hg_int
  refine ⟨T, ?_⟩
  intro φ
  simpa [g, slice, mul_assoc] using hT φ

/-- If the cutoff is identically one on the translated regularizing kernel
support, then the cutoff slice functional evaluates to the real mollifier. -/
theorem realMollifyLocal_eq_cutoffSliceCLM
    (F : ComplexChartSpace m → ℂ)
    (χ ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (w : ComplexChartSpace m)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (hχ_one :
      ∀ x ∈ tsupport
          ((translateSchwartz (fun i => - (w i).re) ψ :
            SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ),
        χ x = 1)
    (hT :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        T φ = ∫ x : Fin m → ℝ,
          (χ x * F (fun i => (x i : ℂ) + ((w i).im : ℂ) * Complex.I)) *
            φ x) :
    realMollifyLocal F ψ w =
      T (translateSchwartz (fun i => - (w i).re) ψ) := by
  rw [realMollifyLocal_eq_sliceIntegral_translate, hT]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Function.support
      ((translateSchwartz (fun i => - (w i).re) ψ :
        SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ)
  · have hxt : x ∈ tsupport
        ((translateSchwartz (fun i => - (w i).re) ψ :
          SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ) :=
      subset_tsupport _ hx
    have hχx : χ x = 1 := hχ_one x hxt
    simp [hχx]
  · have hψx : translateSchwartz (fun i => - (w i).re) ψ x = 0 := by
      simpa [Function.mem_support] using hx
    simp [hψx]

/-- A raw distributional boundary value for the uncut slice implies convergence
of the cutoff slice CLMs to the cutoff-pulled boundary distribution. -/
theorem tendsto_cutoffSliceCLM_of_boundaryValue
    {C : Set (Fin m → ℝ)}
    (F : ComplexChartSpace m → ℂ)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (Traw : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tseq : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (hTseq :
      ∀ (y : Fin m → ℝ) (φ : SchwartzMap (Fin m → ℝ) ℂ),
        Tseq y φ = ∫ x : Fin m → ℝ,
          (χ x * F (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I)) *
            φ x)
    (hbv :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto
          (fun y : Fin m → ℝ => ∫ x : Fin m → ℝ,
            F (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 C)
          (nhds (Traw φ))) :
    ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      Tendsto (fun y : Fin m → ℝ => Tseq y φ) (nhdsWithin 0 C)
        (nhds (Traw ((SchwartzMap.smulLeftCLM ℂ
          (χ : (Fin m → ℝ) → ℂ)) φ))) := by
  intro φ
  let φχ : SchwartzMap (Fin m → ℝ) ℂ :=
    (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ)) φ
  have h := hbv φχ
  refine Tendsto.congr' ?_ h
  filter_upwards with y
  rw [hTseq y φ]
  apply integral_congr_ae
  filter_upwards with x
  simp [φχ, SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
  ring

/-- Cone-local family version of the cutoff slice construction.  The slice CLM
is constructed only where the cone-side margin places the cutoff support inside
the holomorphy domain; outside the cone it is set to zero, which is irrelevant
for the `nhdsWithin 0 C` boundary limit. -/
theorem exists_cutoffSliceCLM_family_of_boundaryValue
    {C : Set (Fin m → ℝ)}
    (F : ComplexChartSpace m → ℂ)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (Ω : Set (ComplexChartSpace m))
    (Traw : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (hΩ_open : IsOpen Ω)
    (hF_cont : ContinuousOn F Ω)
    (hχ_compact : HasCompactSupport (χ : (Fin m → ℝ) → ℂ))
    (hmargin :
      ∀ y ∈ C, ∀ x ∈ tsupport (χ : (Fin m → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ω)
    (hbv :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto
          (fun y : Fin m → ℝ => ∫ x : Fin m → ℝ,
            F (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 C)
          (nhds (Traw φ))) :
    ∃ Tseq : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ,
      (∀ y ∈ C, ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        Tseq y φ = ∫ x : Fin m → ℝ,
          (χ x * F (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I)) *
            φ x) ∧
      (∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y : Fin m → ℝ => Tseq y φ) (nhdsWithin 0 C)
          (nhds (Traw ((SchwartzMap.smulLeftCLM ℂ
            (χ : (Fin m → ℝ) → ℂ)) φ)))) := by
  classical
  let Tseq : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ := fun y =>
    if hy : y ∈ C then
      (exists_cutoffSliceIntegral_clm_of_continuousOn
        F χ Ω y hΩ_open hF_cont hχ_compact (hmargin y hy)).choose
    else 0
  have hTseq_repr : ∀ y ∈ C, ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      Tseq y φ = ∫ x : Fin m → ℝ,
        (χ x * F (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I)) *
          φ x := by
    intro y hy φ
    dsimp [Tseq]
    simp [hy, (exists_cutoffSliceIntegral_clm_of_continuousOn
      F χ Ω y hΩ_open hF_cont hχ_compact (hmargin y hy)).choose_spec φ]
  refine ⟨Tseq, hTseq_repr, ?_⟩
  intro φ
  let φχ : SchwartzMap (Fin m → ℝ) ℂ :=
    (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ)) φ
  have hraw := hbv φχ
  refine Tendsto.congr' ?_ hraw
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [hTseq_repr y hy φ]
  apply integral_congr_ae
  filter_upwards with x
  simp [φχ, SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
  ring

/-- Nonzero-limit version of the mollified boundary-trace theorem for a family
of slice functionals.  If the slice functionals converge pointwise to `T` as
the imaginary part tends to the cone edge, then their evaluations on translated
compactly supported kernels converge to the regularized boundary value. -/
theorem tendsto_mollified_boundary_of_clm
    {C : Set (Fin m → ℝ)}
    {Tseq : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    {T : SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ}
    (hT :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tseq y f) (nhdsWithin 0 C) (nhds (T f)))
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (x₀ : Fin m → ℝ) :
    Tendsto
      (fun w : ComplexChartSpace m =>
        Tseq (fun i => (w i).im)
          (translateSchwartz (fun i => - (w i).re) ψ))
      (nhdsWithin (realEmbed x₀) (TubeDomain C))
      (nhds (T (translateSchwartz (fun i => - x₀ i) ψ))) := by
  let l := nhdsWithin (realEmbed x₀) (TubeDomain C)
  have him :
      Tendsto (fun w : ComplexChartSpace m => fun i => (w i).im) l
        (nhdsWithin 0 C) := by
    let imMap : ComplexChartSpace m → (Fin m → ℝ) := fun w i => (w i).im
    have him_cont : Continuous imMap := by
      refine continuous_pi ?_
      intro i
      exact Complex.continuous_im.comp (continuous_apply i)
    have him_maps : MapsTo imMap (TubeDomain C) C := by
      intro w hw
      simpa [imMap] using hw
    simpa [l, imMap, realEmbed] using
      him_cont.continuousAt.continuousWithinAt.tendsto_nhdsWithin him_maps
  have hre :
      Tendsto (fun w : ComplexChartSpace m => fun i => - (w i).re) l
        (nhds (fun i => - x₀ i)) := by
    let reMap : ComplexChartSpace m → (Fin m → ℝ) := fun w i => - (w i).re
    have hre_cont : Continuous reMap := by
      refine continuous_pi ?_
      intro i
      exact (Complex.continuous_re.comp (continuous_apply i)).neg
    simpa [l, reMap, realEmbed] using
      hre_cont.continuousAt.tendsto.comp
        (tendsto_id'.2 (show l ≤ nhds (realEmbed x₀) by
          exact nhdsWithin_le_nhds))
  have hu :
      Tendsto
        (fun w : ComplexChartSpace m =>
          translateSchwartz (fun i => - (w i).re) ψ)
        l
        (nhds (translateSchwartz (fun i => - x₀ i) ψ)) :=
    (tendsto_translateSchwartz_nhds_of_isCompactSupport
      ψ hψ_compact (fun i => - x₀ i)).comp hre
  have hT_comp :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto
          (fun w : ComplexChartSpace m => Tseq (fun i => (w i).im) f)
          l
          (nhds (T f)) := by
    intro f
    exact (hT f).comp him
  exact SchwartzMap.tempered_apply_tendsto_of_tendsto_filter hT_comp hu

/-- Slice-functional convergence gives a common continuous boundary value for
the plus and minus real-direction mollifications.  The only analytic input is
the pointwise convergence of the slice CLMs to the same distributional boundary
functional together with the exact evaluation of those CLMs on the translated
kernels appearing in the real mollifier. -/
theorem localRealMollify_commonContinuousBoundary_of_clm
    {Cplus Cminus : Set (Fin m → ℝ)}
    (Ωplus Ωminus : Set (ComplexChartSpace m))
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (B : Set (Fin m → ℝ))
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (hΩplus_sub : Ωplus ⊆ TubeDomain Cplus)
    (hΩminus_sub : Ωminus ⊆ TubeDomain Cminus)
    (hplus_eval :
      ∀ w ∈ Ωplus,
        realMollifyLocal Fplus ψ w =
          Tplus (fun i => (w i).im)
            (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ w ∈ Ωminus,
        realMollifyLocal Fminus ψ w =
          Tminus (fun i => (w i).im)
            (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f))) :
    ContinuousOn (fun x : Fin m → ℝ => Tchart (translateSchwartz (-x) ψ)) B ∧
    (∀ x ∈ B,
      Tendsto (realMollifyLocal Fplus ψ)
        (nhdsWithin (realEmbed x) Ωplus)
        (nhds (Tchart (translateSchwartz (-x) ψ)))) ∧
    (∀ x ∈ B,
      Tendsto (realMollifyLocal Fminus ψ)
        (nhdsWithin (realEmbed x) Ωminus)
        (nhds (Tchart (translateSchwartz (-x) ψ)))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact regularizedBoundaryValue_continuousOn Tchart ψ B hψ_compact
  · intro x _hx
    have h := tendsto_mollified_boundary_of_clm
      (C := Cplus) (Tseq := Tplus) (T := Tchart.restrictScalars ℝ)
      hplus_limit ψ hψ_compact x
    have hΩ := h.mono_left (nhdsWithin_mono _ hΩplus_sub)
    refine Tendsto.congr' ?_ hΩ
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hplus_eval w hw).symm
  · intro x _hx
    have h := tendsto_mollified_boundary_of_clm
      (C := Cminus) (Tseq := Tminus) (T := Tchart.restrictScalars ℝ)
      hminus_limit ψ hψ_compact x
    have hΩ := h.mono_left (nhdsWithin_mono _ hΩminus_sub)
    refine Tendsto.congr' ?_ hΩ
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hminus_eval w hw).symm

/-- Construct the real-linear CLM family represented by the local Rudin
integrand after a fixed cutoff.

For positive circle angles the family is the plus side value functional
precomposed with the cutoff multiplication CLM; for negative angles it is the
minus side functional; at the two boundary angles it is zero.  The second
output is the pointwise boundedness needed by Banach-Steinhaus, obtained from
the checked compact bound for the continuous local EOW integrand applied to
each fixed cutoff kernel. -/
theorem exists_localRudinIntegrand_smulLeftCLM_clmFamily
    {Cplus Cminus : Set (Fin m → ℝ)} {rLarge ρ r δ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin_closed :
      ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rLarge,
        z + realEmbed t ∈ Ωplus)
    (hminus_margin_closed :
      ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rLarge,
        z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rLarge →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rLarge →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (hχ_support :
      tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ Metric.closedBall 0 rLarge)
    (w : ComplexChartSpace m)
    (hw : w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2)) :
    ∃ T : ℝ → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ,
      (∀ θ ∈ Set.uIoc (-Real.pi) Real.pi,
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          T θ ψ =
            localRudinIntegrand δ x0 ys
              (fun z =>
                realMollifyLocal Fplus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z)
              (fun z =>
                realMollifyLocal Fminus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z)
              w θ) ∧
      (∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        ∃ C : ℝ, ∀ θ ∈ Set.uIoc (-Real.pi) Real.pi, ‖T θ ψ‖ ≤ C) := by
  let sample : ℝ → ComplexChartSpace m := fun θ =>
    localEOWChart x0 ys
      (localEOWSmp δ w (Complex.exp ((θ : ℂ) * Complex.I)))
  have hw_closed : w ∈ Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) :=
    Metric.ball_subset_closedBall hw
  have hsample_plus : ∀ θ : ℝ, 0 < Real.sin θ → sample θ ∈ Dplus := by
    intro θ hθ
    exact localEOWChart_smp_upper_mem_of_delta_on_sphere hm Dplus x0 ys
      hδ hδρ hδsum hplus hw_closed
      (Complex.norm_exp_ofReal_mul_I θ)
      (by simpa [sample, Complex.exp_ofReal_mul_I_im] using hθ)
  have hsample_minus : ∀ θ : ℝ, Real.sin θ < 0 → sample θ ∈ Dminus := by
    intro θ hθ
    exact localEOWChart_smp_lower_mem_of_delta_on_sphere hm Dminus x0 ys
      hδ hδρ hδsum hminus hw_closed
      (Complex.norm_exp_ofReal_mul_I θ)
      (by simpa [sample, Complex.exp_ofReal_mul_I_im] using hθ)
  let cutoffCLMℝ :
      SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] SchwartzMap (Fin m → ℝ) ℂ :=
    (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ)).restrictScalars ℝ
  let plusL : (θ : ℝ) → 0 < Real.sin θ →
      SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    fun θ hθ =>
      (exists_realMollifyLocal_valueCLM_of_closedBall
        Fplus Ωplus (sample θ) rLarge hFplus_diff.continuousOn
        (hplus_margin_closed (sample θ) (hsample_plus θ hθ))).choose
  have plusL_spec :
      ∀ (θ : ℝ) (hθ : 0 < Real.sin θ)
        (φ : SchwartzMap (Fin m → ℝ) ℂ),
        KernelSupportWithin φ rLarge →
          plusL θ hθ φ = realMollifyLocal Fplus φ (sample θ) := by
    intro θ hθ φ hφ
    exact
      (exists_realMollifyLocal_valueCLM_of_closedBall
        Fplus Ωplus (sample θ) rLarge hFplus_diff.continuousOn
        (hplus_margin_closed (sample θ) (hsample_plus θ hθ))).choose_spec φ hφ
  let minusL : (θ : ℝ) → Real.sin θ < 0 →
      SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    fun θ hθ =>
      (exists_realMollifyLocal_valueCLM_of_closedBall
        Fminus Ωminus (sample θ) rLarge hFminus_diff.continuousOn
        (hminus_margin_closed (sample θ) (hsample_minus θ hθ))).choose
  have minusL_spec :
      ∀ (θ : ℝ) (hθ : Real.sin θ < 0)
        (φ : SchwartzMap (Fin m → ℝ) ℂ),
        KernelSupportWithin φ rLarge →
          minusL θ hθ φ = realMollifyLocal Fminus φ (sample θ) := by
    intro θ hθ φ hφ
    exact
      (exists_realMollifyLocal_valueCLM_of_closedBall
        Fminus Ωminus (sample θ) rLarge hFminus_diff.continuousOn
        (hminus_margin_closed (sample θ) (hsample_minus θ hθ))).choose_spec φ hφ
  let T : ℝ → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ := fun θ =>
    if hθpos : 0 < Real.sin θ then
      (plusL θ hθpos).restrictScalars ℝ |>.comp cutoffCLMℝ
    else if hθneg : Real.sin θ < 0 then
      (minusL θ hθneg).restrictScalars ℝ |>.comp cutoffCLMℝ
    else 0
  have hT_eval :
      ∀ θ ∈ Set.uIoc (-Real.pi) Real.pi,
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          T θ ψ =
            localRudinIntegrand δ x0 ys
              (fun z =>
                realMollifyLocal Fplus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z)
              (fun z =>
                realMollifyLocal Fminus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z)
              w θ := by
    intro θ _hθ ψ
    let η : SchwartzMap (Fin m → ℝ) ℂ :=
      SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ
    have hη_support : KernelSupportWithin η rLarge :=
      KernelSupportWithin.smulLeftCLM_of_leftSupport hχ_support ψ
    by_cases hpos : 0 < Real.sin θ
    · have hL := plusL_spec θ hpos η hη_support
      simpa [T, η, cutoffCLMℝ, sample, localRudinIntegrand, hpos] using hL
    · by_cases hneg : Real.sin θ < 0
      · have hL := minusL_spec θ hneg η hη_support
        simpa [T, η, cutoffCLMℝ, sample, localRudinIntegrand, hpos, hneg] using hL
      · simp [T, localRudinIntegrand, hpos, hneg]
  refine ⟨T, hT_eval, ?_⟩
  intro ψ
  let η : SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ
  have hη_support : KernelSupportWithin η rLarge :=
    KernelSupportWithin.smulLeftCLM_of_leftSupport hχ_support ψ
  have hη_compact : HasCompactSupport (η : (Fin m → ℝ) → ℂ) :=
    KernelSupportWithin_hasCompactSupport hη_support
  have hplus_margin_η :
      ∀ z ∈ Dplus, ∀ t ∈ tsupport (η : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ωplus := by
    intro z hz t ht
    exact hplus_margin_closed z hz t (hη_support ht)
  have hminus_margin_η :
      ∀ z ∈ Dminus, ∀ t ∈ tsupport (η : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ωminus := by
    intro z hz t ht
    exact hminus_margin_closed z hz t (hη_support ht)
  have hFplus_moll_holo :
      DifferentiableOn ℂ (realMollifyLocal Fplus η) Dplus :=
    localRealMollifySide_holomorphicOn_of_translate_margin
      Fplus η Ωplus Dplus hΩplus_open hDplus_open hFplus_diff
      hη_compact hplus_margin_η
  have hFminus_moll_holo :
      DifferentiableOn ℂ (realMollifyLocal Fminus η) Dminus :=
    localRealMollifySide_holomorphicOn_of_translate_margin
      Fminus η Ωminus Dminus hΩminus_open hDminus_open hFminus_diff
      hη_compact hminus_margin_η
  have hcommon :=
    localRealMollify_commonContinuousBoundary_of_clm
      Dplus Dminus Fplus Fminus Tplus Tminus Tchart η E hη_compact
      hDplus_sub hDminus_sub (hplus_eval η hη_support)
      (hminus_eval η hη_support) hplus_limit hminus_limit
  let bv : (Fin m → ℝ) → ℂ := fun x => Tchart (translateSchwartz (-x) η)
  obtain ⟨M, hM⟩ :=
    exists_bound_localRudinIntegrand hm Dplus Dminus E
      hDplus_open hDminus_open
      (realMollifyLocal Fplus η) (realMollifyLocal Fminus η)
      hFplus_moll_holo hFminus_moll_holo bv hcommon.1 hcommon.2.1
      hcommon.2.2 x0 ys hδ hδρ hδsum hE_mem hplus hminus
  refine ⟨M, ?_⟩
  intro θ hθ
  calc
    ‖T θ ψ‖ =
        ‖localRudinIntegrand δ x0 ys
          (fun z => realMollifyLocal Fplus η z)
          (fun z => realMollifyLocal Fminus η z) w θ‖ := by
          rw [hT_eval θ hθ ψ]
    _ ≤ M := hM w hw θ

/-- Finite Schwartz-seminorm bound for the actual cutoff local Rudin envelope
value.

This is the quantitative endpoint estimate needed to turn
`ψ ↦ G (χ • ψ) w` into a continuous linear functional.  The finite seminorm is
produced by Banach-Steinhaus from pointwise boundedness of the interval CLM
family; no zeroth-seminorm bound is assumed at the real-edge endpoints. -/
theorem exists_schwartz_bound_localRudinEnvelope_smulLeftCLM_value
    {Cplus Cminus : Set (Fin m → ℝ)} {rLarge ρ r δ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin_closed :
      ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rLarge,
        z + realEmbed t ∈ Ωplus)
    (hminus_margin_closed :
      ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rLarge,
        z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rLarge →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rLarge →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (hχ_support :
      tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ Metric.closedBall 0 rLarge) :
    ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          ‖localRudinEnvelope δ x0 ys
              (fun z =>
                realMollifyLocal Fplus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z)
              (fun z =>
                realMollifyLocal Fminus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z)
              w‖ ≤
            C * s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ := by
  intro w hw
  obtain ⟨T, hT_eval, hT_bound⟩ :=
    exists_localRudinIntegrand_smulLeftCLM_clmFamily hm
      Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
      hDplus_open hDminus_open Fplus Fminus hFplus_diff hFminus_diff
      hplus_margin_closed hminus_margin_closed hDplus_sub hDminus_sub
      Tplus Tminus Tchart hplus_eval hminus_eval hplus_limit hminus_limit
      x0 ys hδ hδρ hδsum hE_mem hplus hminus χ hχ_support w hw
  obtain ⟨s, C, hC_nonneg, hbound⟩ :=
    exists_schwartz_bound_normalized_intervalIntegral_clm_family T hT_bound
  refine ⟨s, C, hC_nonneg, ?_⟩
  intro ψ
  let η : SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ
  have hintegral :
      (∫ θ in (-Real.pi)..Real.pi, T θ ψ) =
        ∫ θ in (-Real.pi)..Real.pi,
          localRudinIntegrand δ x0 ys
            (fun z => realMollifyLocal Fplus η z)
            (fun z => realMollifyLocal Fminus η z) w θ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with θ hθ
    exact hT_eval θ hθ ψ
  calc
    ‖localRudinEnvelope δ x0 ys
        (fun z => realMollifyLocal Fplus η z)
        (fun z => realMollifyLocal Fminus η z) w‖
        = ‖((2 * Real.pi)⁻¹ : ℝ) •
            ∫ θ in (-Real.pi)..Real.pi, T θ ψ‖ := by
          simp [localRudinEnvelope, localRudinIntegral, hintegral]
    _ ≤ C * s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ :=
        hbound ψ

/-- Fixed-window local regularized EOW envelope from distributional boundary
slice data.

Unlike `regularizedLocalEOW_fixedKernelEnvelope_from_clm`, this theorem does
not choose the local Rudin chart window.  The data `ys, ρ, r, δ` are supplied
once, so the output is the explicit envelope
`localRudinEnvelope δ x0 ys (realMollifyLocal Fplus ψ)
  (realMollifyLocal Fminus ψ)`.  This is the form needed before building a
coherent family in the smoothing kernel. -/
theorem regularizedLocalEOW_fixedWindowEnvelope_from_clm
    {Cplus Cminus : Set (Fin m → ℝ)} {rψ ρ r δ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_support : KernelSupportWithin ψ rψ)
    (hplus_margin :
      ∀ z ∈ Dplus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ωplus)
    (hminus_margin :
      ∀ z ∈ Dminus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ w ∈ Dplus,
        realMollifyLocal Fplus ψ w =
          Tplus (fun i => (w i).im)
            (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ w ∈ Dminus,
        realMollifyLocal Fminus ψ w =
          Tminus (fun i => (w i).im)
            (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus) :
    DifferentiableOn ℂ
      (localRudinEnvelope δ x0 ys
        (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ))
      (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) ∧
    (∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
      (∀ j, 0 < (w j).im) →
        localEOWChart x0 ys w ∈ Dplus ∧
        localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ) w =
          realMollifyLocal Fplus ψ (localEOWChart x0 ys w)) ∧
    (∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
      (∀ j, (w j).im < 0) →
        localEOWChart x0 ys w ∈ Dminus ∧
        localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ) w =
          realMollifyLocal Fminus ψ (localEOWChart x0 ys w)) ∧
    (∀ u : Fin m → ℝ,
      (fun j => (u j : ℂ)) ∈
        Metric.ball (0 : ComplexChartSpace m) (δ / 2) →
        localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
          (fun j => (u j : ℂ)) =
          Tchart (translateSchwartz (-(localEOWRealChart x0 ys u)) ψ)) ∧
    (∀ G : ComplexChartSpace m → ℂ,
      DifferentiableOn ℂ G (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) →
      (∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
        (∀ j, 0 < (w j).im) →
          G w = realMollifyLocal Fplus ψ (localEOWChart x0 ys w)) →
      ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
        G w =
          localRudinEnvelope δ x0 ys
            (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ) w) := by
  have hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ) :=
    KernelSupportWithin_hasCompactSupport hψ_support
  have hFplus_moll_holo :
      DifferentiableOn ℂ (realMollifyLocal Fplus ψ) Dplus :=
    localRealMollifySide_holomorphicOn_of_translate_margin
      Fplus ψ Ωplus Dplus hΩplus_open hDplus_open hFplus_diff
      hψ_compact hplus_margin
  have hFminus_moll_holo :
      DifferentiableOn ℂ (realMollifyLocal Fminus ψ) Dminus :=
    localRealMollifySide_holomorphicOn_of_translate_margin
      Fminus ψ Ωminus Dminus hΩminus_open hDminus_open hFminus_diff
      hψ_compact hminus_margin
  have hcommon :=
    localRealMollify_commonContinuousBoundary_of_clm
      Dplus Dminus Fplus Fminus Tplus Tminus Tchart ψ E hψ_compact
      hDplus_sub hDminus_sub hplus_eval hminus_eval hplus_limit hminus_limit
  let bv : (Fin m → ℝ) → ℂ := fun x => Tchart (translateSchwartz (-x) ψ)
  have hF0_diff : DifferentiableOn ℂ
      (localRudinEnvelope δ x0 ys
        (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ))
      (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) := by
    exact differentiableOn_localRudinEnvelope hm Dplus Dminus E
      hDplus_open hDminus_open (realMollifyLocal Fplus ψ)
      (realMollifyLocal Fminus ψ) hFplus_moll_holo hFminus_moll_holo
      bv hcommon.1 hcommon.2.1 hcommon.2.2 x0 ys hδ hδρ
      hδsum hE_mem hplus hminus
  refine ⟨hF0_diff, ?_, ?_, ?_, ?_⟩
  · intro w hw hw_pos
    constructor
    · exact localEOWChart_ball_positive_mem_of_delta hm Dplus x0 ys
        hδ hδρ hδsum hplus hw hw_pos
    · simpa [bv] using
        localRudinEnvelope_eq_plus_on_positive_ball hm Dplus Dminus E
          hDplus_open hDminus_open (realMollifyLocal Fplus ψ)
          (realMollifyLocal Fminus ψ) hFplus_moll_holo hFminus_moll_holo
          hE_open bv hcommon.1 hcommon.2.1 hcommon.2.2 x0 ys hδ hδρ
          hδsum hE_mem hplus hminus hw hw_pos
  · intro w hw hw_neg
    constructor
    · exact localEOWChart_ball_negative_mem_of_delta hm Dminus x0 ys
        hδ hδρ hδsum hminus hw hw_neg
    · simpa [bv] using
        localRudinEnvelope_eq_minus_on_negative_ball hm Dplus Dminus E
          hDplus_open hDminus_open (realMollifyLocal Fplus ψ)
          (realMollifyLocal Fminus ψ) hFplus_moll_holo hFminus_moll_holo
          hE_open bv hcommon.1 hcommon.2.1 hcommon.2.2 x0 ys hδ hδρ
          hδsum hE_mem hplus hminus hw hw_neg
  · intro u hu
    have hu_closed :
        (fun j => (u j : ℂ)) ∈ Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) :=
      Metric.ball_subset_closedBall hu
    have hu_real : ∀ j, ((fun j => (u j : ℂ)) j).im = 0 := by
      intro j
      simp
    have hE_smp : ∀ s : ℝ, |s| < 2 →
        localEOWRealChart x0 ys
          (fun j => (localEOWSmp δ (fun j => (u j : ℂ)) (s : ℂ) j).re) ∈ E := by
      intro s hs
      apply hE_mem
      have hs_norm : ‖(s : ℂ)‖ ≤ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact le_of_lt hs
      exact localEOWSmp_re_mem_closedBall hδ hδρ hu_closed hs_norm
    simpa [bv] using
      localRudinEnvelope_eq_boundary_of_real hm Dplus Dminus
        hDplus_open hDminus_open (realMollifyLocal Fplus ψ)
        (realMollifyLocal Fminus ψ) hFplus_moll_holo hFminus_moll_holo
        hE_open bv hcommon.1 hcommon.2.1 hcommon.2.2 x0 ys hδ hδρ
        hδsum hplus hminus hu_closed hu_real hE_smp
  · intro G hG_diff hG_plus w hw
    let F0 : ComplexChartSpace m → ℂ :=
      localRudinEnvelope δ x0 ys
        (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
    let z0 : ComplexChartSpace m := fun _ => ((δ / 4 : ℝ) : ℂ) * Complex.I
    have hz0_im : ∀ j, (z0 j).im = δ / 4 := by
      intro j
      simp [z0, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have hz0_pos : ∀ j, 0 < (z0 j).im := by
      intro j
      rw [hz0_im j]
      linarith
    have hz0_ball : z0 ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2) := by
      rw [Metric.mem_ball, dist_zero_right]
      calc
        ‖z0‖ = ‖((δ / 4 : ℝ) : ℂ) * Complex.I‖ := by
          apply le_antisymm
          · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
            intro j
            rfl
          · exact norm_le_pi_norm z0 ⟨0, hm⟩
        _ = δ / 4 := by
          rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
            abs_of_pos (by linarith : 0 < δ / 4)]
        _ < δ / 2 := by linarith
    have hPos_open : IsOpen {w : ComplexChartSpace m | ∀ j, 0 < (w j).im} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply j))
    have hball_open : IsOpen (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) :=
      Metric.isOpen_ball
    have hF0_anal :
        AnalyticOnNhd ℂ F0 (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) := fun z hz =>
      SCV.differentiableOn_analyticAt hball_open hF0_diff hz
    have hG_anal :
        AnalyticOnNhd ℂ G (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) := fun z hz =>
      SCV.differentiableOn_analyticAt hball_open hG_diff hz
    have hpreconn : IsPreconnected (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) :=
      (convex_ball (0 : ComplexChartSpace m) (δ / 2)).isPreconnected
    have hF0_plus : ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
        (∀ j, 0 < (w j).im) →
          F0 w = realMollifyLocal Fplus ψ (localEOWChart x0 ys w) := by
      intro w hw hw_pos
      simpa [F0, bv] using
        localRudinEnvelope_eq_plus_on_positive_ball hm Dplus Dminus E
          hDplus_open hDminus_open (realMollifyLocal Fplus ψ)
          (realMollifyLocal Fminus ψ) hFplus_moll_holo hFminus_moll_holo
          hE_open bv hcommon.1 hcommon.2.1 hcommon.2.2 x0 ys hδ hδρ
          hδsum hE_mem hplus hminus hw hw_pos
    have h_eq_near : G =ᶠ[nhds z0] F0 := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Metric.ball (0 : ComplexChartSpace m) (δ / 2) ∩
          {w : ComplexChartSpace m | ∀ j, 0 < (w j).im}, ?_, ?_⟩
      · exact Filter.inter_mem (Metric.isOpen_ball.mem_nhds hz0_ball)
          (hPos_open.mem_nhds hz0_pos)
      · intro z hz
        exact (hG_plus z hz.1 hz.2).trans (hF0_plus z hz.1 hz.2).symm
    have hEqOn : Set.EqOn G F0 (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) :=
      hG_anal.eqOn_of_preconnected_of_eventuallyEq hF0_anal hpreconn hz0_ball h_eq_near
    exact hEqOn hw

/-- Uniform fixed-window regularized EOW family.

This exposes the honest family
`ψ ↦ localRudinEnvelope δ x0 ys (realMollifyLocal Fplus ψ)
  (realMollifyLocal Fminus ψ)` on one fixed Rudin chart window.  It packages
the holomorphy, side-agreement, real-edge, and uniqueness facts obtained by
the fixed-window theorem for every supported smoothing kernel. -/
theorem regularizedLocalEOW_family_from_fixedWindow
    {Cplus Cminus : Set (Fin m → ℝ)} {rψ ρ r δ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dplus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωplus)
    (hminus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dminus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus) :
    let G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
      fun ψ =>
        localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
    (∀ ψ, KernelSupportWithin ψ rψ →
      DifferentiableOn ℂ (G ψ) (Metric.ball (0 : ComplexChartSpace m) (δ / 2))) ∧
    (∀ ψ, KernelSupportWithin ψ rψ →
      ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
        (∀ j, 0 < (w j).im) →
          localEOWChart x0 ys w ∈ Dplus ∧
          G ψ w = realMollifyLocal Fplus ψ (localEOWChart x0 ys w)) ∧
    (∀ ψ, KernelSupportWithin ψ rψ →
      ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
        (∀ j, (w j).im < 0) →
          localEOWChart x0 ys w ∈ Dminus ∧
          G ψ w = realMollifyLocal Fminus ψ (localEOWChart x0 ys w)) ∧
    (∀ ψ, KernelSupportWithin ψ rψ →
      ∀ u : Fin m → ℝ,
        (fun j => (u j : ℂ)) ∈
          Metric.ball (0 : ComplexChartSpace m) (δ / 2) →
          G ψ (fun j => (u j : ℂ)) =
            Tchart (translateSchwartz (-(localEOWRealChart x0 ys u)) ψ)) ∧
    (∀ ψ, KernelSupportWithin ψ rψ →
      ∀ H : ComplexChartSpace m → ℂ,
        DifferentiableOn ℂ H (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) →
        (∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
          (∀ j, 0 < (w j).im) →
            H w = realMollifyLocal Fplus ψ (localEOWChart x0 ys w)) →
        ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
          H w = G ψ w) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    exact
      (regularizedLocalEOW_fixedWindowEnvelope_from_clm hm
        Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
        hDplus_open hDminus_open hE_open Fplus Fminus hFplus_diff
        hFminus_diff ψ hψ (hplus_margin ψ hψ) (hminus_margin ψ hψ)
        hDplus_sub hDminus_sub Tplus Tminus Tchart (hplus_eval ψ hψ)
        (hminus_eval ψ hψ) hplus_limit hminus_limit x0 ys hδ hδρ
        hδsum hE_mem hplus hminus).1
  · intro ψ hψ w hw hw_pos
    exact
      (regularizedLocalEOW_fixedWindowEnvelope_from_clm hm
        Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
        hDplus_open hDminus_open hE_open Fplus Fminus hFplus_diff
        hFminus_diff ψ hψ (hplus_margin ψ hψ) (hminus_margin ψ hψ)
        hDplus_sub hDminus_sub Tplus Tminus Tchart (hplus_eval ψ hψ)
        (hminus_eval ψ hψ) hplus_limit hminus_limit x0 ys hδ hδρ
        hδsum hE_mem hplus hminus).2.1 w hw hw_pos
  · intro ψ hψ w hw hw_neg
    exact
      (regularizedLocalEOW_fixedWindowEnvelope_from_clm hm
        Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
        hDplus_open hDminus_open hE_open Fplus Fminus hFplus_diff
        hFminus_diff ψ hψ (hplus_margin ψ hψ) (hminus_margin ψ hψ)
        hDplus_sub hDminus_sub Tplus Tminus Tchart (hplus_eval ψ hψ)
        (hminus_eval ψ hψ) hplus_limit hminus_limit x0 ys hδ hδρ
        hδsum hE_mem hplus hminus).2.2.1 w hw hw_neg
  · intro ψ hψ u hu
    exact
      (regularizedLocalEOW_fixedWindowEnvelope_from_clm hm
        Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
        hDplus_open hDminus_open hE_open Fplus Fminus hFplus_diff
        hFminus_diff ψ hψ (hplus_margin ψ hψ) (hminus_margin ψ hψ)
        hDplus_sub hDminus_sub Tplus Tminus Tchart (hplus_eval ψ hψ)
        (hminus_eval ψ hψ) hplus_limit hminus_limit x0 ys hδ hδρ
        hδsum hE_mem hplus hminus).2.2.2.1 u hu
  · intro ψ hψ H hH_diff hH_plus w hw
    exact
      (regularizedLocalEOW_fixedWindowEnvelope_from_clm hm
        Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
        hDplus_open hDminus_open hE_open Fplus Fminus hFplus_diff
        hFminus_diff ψ hψ (hplus_margin ψ hψ) (hminus_margin ψ hψ)
        hDplus_sub hDminus_sub Tplus Tminus Tchart (hplus_eval ψ hψ)
        (hminus_eval ψ hψ) hplus_limit hminus_limit x0 ys hδ hδρ
        hδsum hE_mem hplus hminus).2.2.2.2 H hH_diff hH_plus w hw

/-- Local real-translation covariance of the fixed-window regularized EOW
family on the honest shifted overlap.

The kernels are first pushed through the local real chart linear part.  The two
support hypotheses are intentionally explicit: translating the chart kernel
does not preserve a fixed support radius without a separate radius-enlargement
argument. -/
theorem regularizedLocalEOW_family_chartKernel_covariance_on_shiftedOverlap
    {Cplus Cminus : Set (Fin m → ℝ)} {rψ ρ r δ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dplus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωplus)
    (hminus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dminus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (hli : LinearIndependent ℝ ys)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (a : Fin m → ℝ)
    (hφ :
      KernelSupportWithin (localEOWRealLinearKernelPushforwardCLM ys hli φ) rψ)
    (hφa :
      KernelSupportWithin
        (localEOWRealLinearKernelPushforwardCLM ys hli (translateSchwartz a φ)) rψ)
    (hpos_overlap :
      ∃ z0, z0 ∈ localEOWShiftedWindow (m := m) δ a ∧
        (∀ j, 0 < (z0 j).im)) :
    let G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
      fun ψ =>
        localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
    ∀ w ∈ localEOWShiftedWindow (m := m) δ a,
      G (localEOWRealLinearKernelPushforwardCLM ys hli (translateSchwartz a φ)) w =
        G (localEOWRealLinearKernelPushforwardCLM ys hli φ) (w - realEmbed a) := by
  dsimp only
  have hfamily :=
    regularizedLocalEOW_family_from_fixedWindow hm
      Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open hDplus_open
      hDminus_open hE_open Fplus Fminus hFplus_diff hFminus_diff
      hplus_margin hminus_margin hDplus_sub hDminus_sub Tplus Tminus
      Tchart hplus_eval hminus_eval hplus_limit hminus_limit x0 ys hδ
      hδρ hδsum hE_mem hplus hminus
  dsimp only at hfamily
  let ψ0 : SchwartzMap (Fin m → ℝ) ℂ :=
    localEOWRealLinearKernelPushforwardCLM ys hli φ
  let ψa : SchwartzMap (Fin m → ℝ) ℂ :=
    localEOWRealLinearKernelPushforwardCLM ys hli (translateSchwartz a φ)
  let G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
    fun ψ =>
      localRudinEnvelope δ x0 ys
        (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
  have hV_open : IsOpen (localEOWShiftedWindow (m := m) δ a) :=
    isOpen_localEOWShiftedWindow (m := m) δ a
  have hV_preconn : IsPreconnected (localEOWShiftedWindow (m := m) δ a) :=
    isPreconnected_localEOWShiftedWindow (m := m) δ a
  have hleft_diff : DifferentiableOn ℂ (fun w => G ψa w)
      (localEOWShiftedWindow (m := m) δ a) := by
    exact (hfamily.1 ψa hφa).mono fun w hw =>
      localEOWShiftedWindow_mem_left (m := m) hw
  have hshift_diff : DifferentiableOn ℂ
      (fun w : ComplexChartSpace m => w - realEmbed a)
      (localEOWShiftedWindow (m := m) δ a) :=
    (differentiable_id.sub (differentiable_const _)).differentiableOn
  have hright_diff : DifferentiableOn ℂ (fun w => G ψ0 (w - realEmbed a))
      (localEOWShiftedWindow (m := m) δ a) := by
    have hGψ0_diff :
        DifferentiableOn ℂ (G ψ0) (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) := by
      simpa [G] using hfamily.1 ψ0 hφ
    change DifferentiableOn ℂ
      ((G ψ0) ∘ (fun w : ComplexChartSpace m => w - realEmbed a))
      (localEOWShiftedWindow (m := m) δ a)
    exact hGψ0_diff.comp hshift_diff fun w hw =>
      localEOWShiftedWindow_mem_shift (m := m) hw
  have hleft_anal : AnalyticOnNhd ℂ (fun w => G ψa w)
      (localEOWShiftedWindow (m := m) δ a) := fun z hz =>
    SCV.differentiableOn_analyticAt hV_open hleft_diff hz
  have hright_anal : AnalyticOnNhd ℂ (fun w => G ψ0 (w - realEmbed a))
      (localEOWShiftedWindow (m := m) δ a) := fun z hz =>
    SCV.differentiableOn_analyticAt hV_open hright_diff hz
  rcases hpos_overlap with ⟨z0, hz0V, hz0_pos⟩
  have hPos_open : IsOpen {w : ComplexChartSpace m | ∀ j, 0 < (w j).im} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply j))
  have h_eq_near :
      (fun w => G ψa w) =ᶠ[nhds z0] (fun w => G ψ0 (w - realEmbed a)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨localEOWShiftedWindow (m := m) δ a ∩
        {w : ComplexChartSpace m | ∀ j, 0 < (w j).im}, ?_, ?_⟩
    · exact Filter.inter_mem (hV_open.mem_nhds hz0V)
        (hPos_open.mem_nhds hz0_pos)
    · intro z hz
      have hzV : z ∈ localEOWShiftedWindow (m := m) δ a := hz.1
      have hz_pos : ∀ j, 0 < (z j).im := hz.2
      have hz_left :
          z ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2) :=
        localEOWShiftedWindow_mem_left (m := m) hzV
      have hz_shift :
          z - realEmbed a ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2) :=
        localEOWShiftedWindow_mem_shift (m := m) hzV
      have hz_shift_pos : ∀ j, 0 < ((z - realEmbed a) j).im := by
        intro j
        simpa [realEmbed] using hz_pos j
      have hψa_plus := hfamily.2.1 ψa hφa z hz_left hz_pos
      have hψ0_plus := hfamily.2.1 ψ0 hφ (z - realEmbed a) hz_shift hz_shift_pos
      have hψa_eval :
          G ψa z = realMollifyLocal Fplus ψa (localEOWChart x0 ys z) := by
        simpa [G] using hψa_plus.2
      have hψ0_eval :
          G ψ0 (z - realEmbed a) =
            realMollifyLocal Fplus ψ0 (localEOWChart x0 ys (z - realEmbed a)) := by
        simpa [G] using hψ0_plus.2
      calc
        G ψa z = realMollifyLocal Fplus ψa (localEOWChart x0 ys z) := hψa_eval
        _ = realMollifyLocal Fplus ψ0 (localEOWChart x0 ys (z - realEmbed a)) := by
          simpa [ψ0, ψa] using
            realMollifyLocal_localEOWChart_translate_kernelPushforwardCLM
              (m := m) Fplus x0 ys hli φ a z
        _ = G ψ0 (z - realEmbed a) := hψ0_eval.symm
  have hEqOn : Set.EqOn (fun w => G ψa w) (fun w => G ψ0 (w - realEmbed a))
      (localEOWShiftedWindow (m := m) δ a) :=
    hleft_anal.eqOn_of_preconnected_of_eventuallyEq
      hright_anal hV_preconn hz0V h_eq_near
  intro w hw
  simpa [G, ψ0, ψa] using hEqOn hw

/-- Additivity of the explicit fixed-window regularized EOW family on the
supported-kernel class. -/
theorem regularizedLocalEOW_family_add
    {Cplus Cminus : Set (Fin m → ℝ)} {rψ ρ r δ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dplus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωplus)
    (hminus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dminus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (ψ η : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ : KernelSupportWithin ψ rψ)
    (hη : KernelSupportWithin η rψ) :
    let G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
      fun ψ =>
        localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
    ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
      G (ψ + η) w = G ψ w + G η w := by
  dsimp only
  have hfamily :=
    regularizedLocalEOW_family_from_fixedWindow hm
      Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open hDplus_open
      hDminus_open hE_open Fplus Fminus hFplus_diff hFminus_diff
      hplus_margin hminus_margin hDplus_sub hDminus_sub Tplus Tminus
      Tchart hplus_eval hminus_eval hplus_limit hminus_limit x0 ys hδ
      hδρ hδsum hE_mem hplus hminus
  dsimp only at hfamily
  have hsum : KernelSupportWithin (ψ + η) rψ := KernelSupportWithin.add hψ hη
  let G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
    fun ψ =>
      localRudinEnvelope δ x0 ys
        (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
  have hH_diff : DifferentiableOn ℂ (fun w => G ψ w + G η w)
      (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) :=
    (hfamily.1 ψ hψ).add (hfamily.1 η hη)
  have hH_plus :
      ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
        (∀ j, 0 < (w j).im) →
          G ψ w + G η w =
            realMollifyLocal Fplus (ψ + η) (localEOWChart x0 ys w) := by
    intro w hw hw_pos
    have hψ_plus := hfamily.2.1 ψ hψ w hw hw_pos
    have hη_plus := hfamily.2.1 η hη w hw hw_pos
    have hadd :
        realMollifyLocal Fplus (ψ + η) (localEOWChart x0 ys w) =
          realMollifyLocal Fplus ψ (localEOWChart x0 ys w) +
            realMollifyLocal Fplus η (localEOWChart x0 ys w) :=
      realMollifyLocal_add_of_translate_margin Fplus ψ η Ωplus
        (localEOWChart x0 ys w) hΩplus_open hFplus_diff
        (KernelSupportWithin_hasCompactSupport hψ)
        (KernelSupportWithin_hasCompactSupport hη)
        (hplus_margin ψ hψ (localEOWChart x0 ys w) hψ_plus.1)
        (hplus_margin η hη (localEOWChart x0 ys w) hη_plus.1)
    dsimp [G]
    rw [hψ_plus.2, hη_plus.2, hadd]
  intro w hw
  have huniq := hfamily.2.2.2.2 (ψ + η) hsum
  exact (huniq (fun w => G ψ w + G η w) hH_diff hH_plus w hw).symm

/-- Complex homogeneity of the explicit fixed-window regularized EOW family on
the supported-kernel class. -/
theorem regularizedLocalEOW_family_smul
    {Cplus Cminus : Set (Fin m → ℝ)} {rψ ρ r δ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dplus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωplus)
    (hminus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ z ∈ Dminus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rψ →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (c : ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ : KernelSupportWithin ψ rψ) :
    let G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
      fun ψ =>
        localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
    ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
      G (c • ψ) w = c * G ψ w := by
  dsimp only
  have hfamily :=
    regularizedLocalEOW_family_from_fixedWindow hm
      Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open hDplus_open
      hDminus_open hE_open Fplus Fminus hFplus_diff hFminus_diff
      hplus_margin hminus_margin hDplus_sub hDminus_sub Tplus Tminus
      Tchart hplus_eval hminus_eval hplus_limit hminus_limit x0 ys hδ
      hδρ hδsum hE_mem hplus hminus
  dsimp only at hfamily
  have hsmul : KernelSupportWithin (c • ψ) rψ :=
    KernelSupportWithin.smul c hψ
  let G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ :=
    fun ψ =>
      localRudinEnvelope δ x0 ys
        (realMollifyLocal Fplus ψ) (realMollifyLocal Fminus ψ)
  have hH_diff : DifferentiableOn ℂ (fun w => c * G ψ w)
      (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) := by
    simpa [smul_eq_mul] using (hfamily.1 ψ hψ).const_smul c
  have hH_plus :
      ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
        (∀ j, 0 < (w j).im) →
          c * G ψ w =
            realMollifyLocal Fplus (c • ψ) (localEOWChart x0 ys w) := by
    intro w hw hw_pos
    have hψ_plus := hfamily.2.1 ψ hψ w hw hw_pos
    have hsmul_eq :=
      realMollifyLocal_smul Fplus ψ c (localEOWChart x0 ys w)
    dsimp [G]
    rw [hψ_plus.2, hsmul_eq]
  intro w hw
  have huniq := hfamily.2.2.2.2 (c • ψ) hsmul
  exact (huniq (fun w => c * G ψ w) hH_diff hH_plus w hw).symm

/-- Pointwise continuous linear functional represented by the cutoff local
Rudin envelope value.

The fixed window hypotheses are instantiated at the larger cutoff support
radius `rLarge`.  The functional acts on all Schwartz kernels by first
multiplying by the cutoff `χ`, applying the regularized local EOW envelope,
and evaluating at `w`. -/
theorem regularizedEnvelope_valueCLM_of_cutoff
    {Cplus Cminus : Set (Fin m → ℝ)} {rLarge ρ r δ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin_closed :
      ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rLarge,
        z + realEmbed t ∈ Ωplus)
    (hminus_margin_closed :
      ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rLarge,
        z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rLarge →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rLarge →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (hχ_support :
      tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ Metric.closedBall 0 rLarge) :
    ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
      ∃ Lw : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ,
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          Lw ψ =
            localRudinEnvelope δ x0 ys
              (fun z =>
                realMollifyLocal Fplus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z)
              (fun z =>
                realMollifyLocal Fminus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) ψ) z)
              w := by
  intro w hw
  let cutoffCLM : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ)
  let A : SchwartzMap (Fin m → ℝ) ℂ → ℂ := fun ψ =>
    localRudinEnvelope δ x0 ys
      (fun z => realMollifyLocal Fplus (cutoffCLM ψ) z)
      (fun z => realMollifyLocal Fminus (cutoffCLM ψ) z) w
  have hplus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rLarge →
        ∀ z ∈ Dplus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωplus := by
    intro ψ hψ z hz t ht
    exact hplus_margin_closed z hz t (hψ ht)
  have hminus_margin :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rLarge →
        ∀ z ∈ Dminus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωminus := by
    intro ψ hψ z hz t ht
    exact hminus_margin_closed z hz t (hψ ht)
  have hbound_exists :
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
          ‖A ψ‖ ≤
            C * s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ := by
    obtain ⟨s, C, hC, hbound⟩ :=
      exists_schwartz_bound_localRudinEnvelope_smulLeftCLM_value hm
        Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
        hDplus_open hDminus_open Fplus Fminus hFplus_diff hFminus_diff
        hplus_margin_closed hminus_margin_closed hDplus_sub hDminus_sub
        Tplus Tminus Tchart hplus_eval hminus_eval hplus_limit hminus_limit
        x0 ys hδ hδρ hδsum hE_mem hplus hminus χ hχ_support w hw
    exact ⟨s, C, hC, by intro ψ; simpa [A, cutoffCLM] using hbound ψ⟩
  have hcut_support :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin (cutoffCLM ψ) rLarge := by
    intro ψ
    exact KernelSupportWithin.smulLeftCLM_of_leftSupport hχ_support ψ
  have hadd : ∀ ψ η : SchwartzMap (Fin m → ℝ) ℂ, A (ψ + η) = A ψ + A η := by
    intro ψ η
    have hcut_add : cutoffCLM (ψ + η) = cutoffCLM ψ + cutoffCLM η := by
      exact map_add cutoffCLM ψ η
    have hGadd :=
      regularizedLocalEOW_family_add hm
        Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
        hDplus_open hDminus_open hE_open Fplus Fminus hFplus_diff
        hFminus_diff hplus_margin hminus_margin hDplus_sub hDminus_sub
        Tplus Tminus Tchart hplus_eval hminus_eval hplus_limit hminus_limit
        x0 ys hδ hδρ hδsum hE_mem hplus hminus
        (cutoffCLM ψ) (cutoffCLM η) (hcut_support ψ) (hcut_support η) w hw
    simpa [A, cutoffCLM, hcut_add] using hGadd
  have hsmul :
      ∀ (c : ℂ) (ψ : SchwartzMap (Fin m → ℝ) ℂ), A (c • ψ) = c • A ψ := by
    intro c ψ
    have hcut_smul : cutoffCLM (c • ψ) = c • cutoffCLM ψ := by
      exact map_smul cutoffCLM c ψ
    have hGsmul :=
      regularizedLocalEOW_family_smul hm
        Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
        hDplus_open hDminus_open hE_open Fplus Fminus hFplus_diff
        hFminus_diff hplus_margin hminus_margin hDplus_sub hDminus_sub
        Tplus Tminus Tchart hplus_eval hminus_eval hplus_limit hminus_limit
        x0 ys hδ hδρ hδsum hE_mem hplus hminus
        c (cutoffCLM ψ) (hcut_support ψ) w hw
    simpa [A, cutoffCLM, hcut_smul, smul_eq_mul] using hGsmul
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) A hadd hsmul hbound_exists, ?_⟩
  intro ψ
  rfl

/-- Compact-window family of continuous linear functionals represented by the
cutoff local Rudin envelope values, with one finite Schwartz-seminorm bound
uniform in the chart point. -/
theorem regularizedLocalEOW_originalFamily_compactValueCLM
    {Cplus Cminus : Set (Fin m → ℝ)} {rLarge ρ r δ Rcut : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin_closed :
      ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rLarge,
        z + realEmbed t ∈ Ωplus)
    (hminus_margin_closed :
      ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : Fin m → ℝ) rLarge,
        z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rLarge →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ, KernelSupportWithin ψ rLarge →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (χ : SchwartzMap (Fin m → ℝ) ℂ)
    (hχ_support :
      tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ Metric.closedBall 0 rLarge)
    (hRcut_window :
      Metric.closedBall (0 : ComplexChartSpace m) Rcut ⊆
        Metric.ball (0 : ComplexChartSpace m) (δ / 2)) :
    ∃ L : ComplexChartSpace m → SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ,
      (∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
        ∀ η : SchwartzMap (Fin m → ℝ) ℂ,
          L z η =
            localRudinEnvelope δ x0 ys
              (fun w =>
                realMollifyLocal Fplus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) η) w)
              (fun w =>
                realMollifyLocal Fminus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) η) w)
              z) ∧
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
        ∀ η : SchwartzMap (Fin m → ℝ) ℂ,
          ‖L z η‖ ≤
            C * s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) η := by
  classical
  let valueCLM_at :
      ∀ z ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
        SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ := fun z hz =>
    (regularizedEnvelope_valueCLM_of_cutoff hm
      Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
      hDplus_open hDminus_open hE_open Fplus Fminus hFplus_diff
      hFminus_diff hplus_margin_closed hminus_margin_closed hDplus_sub hDminus_sub
      Tplus Tminus Tchart hplus_eval hminus_eval hplus_limit hminus_limit
      x0 ys hδ hδρ hδsum hE_mem hplus hminus χ hχ_support z hz).choose
  let L : ComplexChartSpace m → SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ := fun z =>
    if hz : z ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2) then
      valueCLM_at z hz
    else
      0
  have hL_spec :
      ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut,
        ∀ η : SchwartzMap (Fin m → ℝ) ℂ,
          L z η =
            localRudinEnvelope δ x0 ys
              (fun w =>
                realMollifyLocal Fplus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) η) w)
              (fun w =>
                realMollifyLocal Fminus
                  (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) η) w)
              z := by
    intro z hz η
    have hzball : z ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2) :=
      hRcut_window hz
    have hchoose :=
      (regularizedEnvelope_valueCLM_of_cutoff hm
        Ωplus Ωminus Dplus Dminus E hΩplus_open hΩminus_open
        hDplus_open hDminus_open hE_open Fplus Fminus hFplus_diff
        hFminus_diff hplus_margin_closed hminus_margin_closed hDplus_sub hDminus_sub
        Tplus Tminus Tchart hplus_eval hminus_eval hplus_limit hminus_limit
        x0 ys hδ hδρ hδsum hE_mem hplus hminus χ hχ_support z hzball).choose_spec η
    change (if hz' : z ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2) then
        valueCLM_at z hz' else 0) η =
      localRudinEnvelope δ x0 ys
        (fun w =>
          realMollifyLocal Fplus
            (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) η) w)
        (fun w =>
          realMollifyLocal Fminus
            (SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ) η) w)
        z
    rw [dif_pos hzball]
    simpa [valueCLM_at] using hchoose
  let Zcut := {z : ComplexChartSpace m // z ∈ Metric.closedBall (0 : ComplexChartSpace m) Rcut}
  let T : Zcut → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ :=
    fun z => (L z).restrictScalars ℝ
  have hT_bound :
      ∀ η : SchwartzMap (Fin m → ℝ) ℂ,
        ∃ C : ℝ, ∀ z : Zcut, ‖T z η‖ ≤ C := by
    intro η
    let cutoffCLM : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
      SchwartzMap.smulLeftCLM ℂ (χ : (Fin m → ℝ) → ℂ)
    let ηχ : SchwartzMap (Fin m → ℝ) ℂ := cutoffCLM η
    have hηχ_support : KernelSupportWithin ηχ rLarge :=
      KernelSupportWithin.smulLeftCLM_of_leftSupport hχ_support η
    have hηχ_compact : HasCompactSupport (ηχ : (Fin m → ℝ) → ℂ) :=
      KernelSupportWithin_hasCompactSupport hηχ_support
    have hplus_margin_ηχ :
        ∀ z ∈ Dplus, ∀ t ∈ tsupport (ηχ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωplus := by
      intro z hz t ht
      exact hplus_margin_closed z hz t (hηχ_support ht)
    have hminus_margin_ηχ :
        ∀ z ∈ Dminus, ∀ t ∈ tsupport (ηχ : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ Ωminus := by
      intro z hz t ht
      exact hminus_margin_closed z hz t (hηχ_support ht)
    have hFplus_moll_holo :
        DifferentiableOn ℂ (realMollifyLocal Fplus ηχ) Dplus :=
      localRealMollifySide_holomorphicOn_of_translate_margin
        Fplus ηχ Ωplus Dplus hΩplus_open hDplus_open hFplus_diff
        hηχ_compact hplus_margin_ηχ
    have hFminus_moll_holo :
        DifferentiableOn ℂ (realMollifyLocal Fminus ηχ) Dminus :=
      localRealMollifySide_holomorphicOn_of_translate_margin
        Fminus ηχ Ωminus Dminus hΩminus_open hDminus_open hFminus_diff
        hηχ_compact hminus_margin_ηχ
    have hcommon :=
      localRealMollify_commonContinuousBoundary_of_clm
        Dplus Dminus Fplus Fminus Tplus Tminus Tchart ηχ E hηχ_compact
        hDplus_sub hDminus_sub (hplus_eval ηχ hηχ_support)
        (hminus_eval ηχ hηχ_support) hplus_limit hminus_limit
    let bv : (Fin m → ℝ) → ℂ := fun x => Tchart (translateSchwartz (-x) ηχ)
    obtain ⟨M, hM⟩ :=
      exists_bound_localRudinIntegrand hm Dplus Dminus E
        hDplus_open hDminus_open
        (realMollifyLocal Fplus ηχ) (realMollifyLocal Fminus ηχ)
        hFplus_moll_holo hFminus_moll_holo bv hcommon.1 hcommon.2.1
        hcommon.2.2 x0 ys hδ hδρ hδsum hE_mem hplus hminus
    let B : ℝ :=
      ‖((2 * Real.pi)⁻¹ : ℝ)‖ * ((max M 0) * |Real.pi - (-Real.pi)|)
    refine ⟨B, ?_⟩
    intro z
    have hzball : (z : ComplexChartSpace m) ∈
        Metric.ball (0 : ComplexChartSpace m) (δ / 2) :=
      hRcut_window z.property
    have h_interval_bound :
        ‖∫ θ in (-Real.pi)..Real.pi,
          localRudinIntegrand δ x0 ys
            (fun w => realMollifyLocal Fplus ηχ w)
            (fun w => realMollifyLocal Fminus ηχ w) z θ‖ ≤
          (max M 0) * |Real.pi - (-Real.pi)| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro θ _hθ
      exact (hM z hzball θ).trans (le_max_left M 0)
    calc
      ‖T z η‖ = ‖L (z : ComplexChartSpace m) η‖ := rfl
      _ = ‖localRudinEnvelope δ x0 ys
          (fun w => realMollifyLocal Fplus ηχ w)
          (fun w => realMollifyLocal Fminus ηχ w) z‖ := by
        rw [hL_spec (z : ComplexChartSpace m) z.property η]
      _ = ‖((2 * Real.pi)⁻¹ : ℝ) •
            ∫ θ in (-Real.pi)..Real.pi,
              localRudinIntegrand δ x0 ys
                (fun w => realMollifyLocal Fplus ηχ w)
                (fun w => realMollifyLocal Fminus ηχ w) z θ‖ := by
        simp [localRudinEnvelope, localRudinIntegral]
      _ ≤ B := by
        calc
          ‖((2 * Real.pi)⁻¹ : ℝ) •
              ∫ θ in (-Real.pi)..Real.pi,
                localRudinIntegrand δ x0 ys
                  (fun w => realMollifyLocal Fplus ηχ w)
                  (fun w => realMollifyLocal Fminus ηχ w) z θ‖
              = ‖((2 * Real.pi)⁻¹ : ℝ)‖ *
                  ‖∫ θ in (-Real.pi)..Real.pi,
                    localRudinIntegrand δ x0 ys
                      (fun w => realMollifyLocal Fplus ηχ w)
                      (fun w => realMollifyLocal Fminus ηχ w) z θ‖ := by
                simp
          _ ≤ ‖((2 * Real.pi)⁻¹ : ℝ)‖ *
                ((max M 0) * |Real.pi - (-Real.pi)|) := by
              exact mul_le_mul_of_nonneg_left h_interval_bound (norm_nonneg _)
          _ = B := rfl
  obtain ⟨s, Cnn, _hCnn_ne, hboundℝ⟩ :=
    SchwartzMap.tempered_uniform_schwartz_bound
      (E := Fin m → ℝ) (F := ℂ) (G := ℂ) hT_bound
  have sup_apply_real_eq_complex :
      ∀ (s' : Finset (ℕ × ℕ)) (η : SchwartzMap (Fin m → ℝ) ℂ),
        (s'.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) η =
          (s'.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) η := by
    intro s' η
    induction s' using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        have ha_eq :
            (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ a) η =
              (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ a) η := by
          cases a
          rfl
        simp [Finset.sup_insert, ih, ha_eq]
  refine ⟨L, hL_spec, s, (Cnn : ℝ), NNReal.coe_nonneg Cnn, ?_⟩
  intro z hz η
  have h := hboundℝ (⟨z, hz⟩ : Zcut) η
  calc
    ‖L z η‖ = ‖T (⟨z, hz⟩ : Zcut) η‖ := rfl
    _ ≤ (Cnn • s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) η := h
    _ = (Cnn : ℝ) * s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) η := by
        rw [Seminorm.smul_apply, sup_apply_real_eq_complex s η]
        rfl

/-- Fixed-kernel local regularized EOW envelope from distributional boundary
slice data.

This is the first upstream bridge from the Streater-Wightman distributional
boundary hypotheses to the checked local continuous EOW theorem.  For one
compactly supported smoothing kernel, the real-direction mollified plus/minus
branches are holomorphic on shrunken wedge domains, have the common continuous
boundary value supplied by the slice CLMs, and therefore have the checked
local coordinate envelope. -/
theorem regularizedLocalEOW_fixedKernelEnvelope_from_clm
    {Cplus Cminus C : Set (Fin m → ℝ)} {rψ : ℝ}
    (hm : 0 < m)
    (Ωplus Ωminus Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E) (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C) (hC_ne : C.Nonempty)
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Dplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Dminus)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hψ_support : KernelSupportWithin ψ rψ)
    (hplus_margin :
      ∀ z ∈ Dplus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ωplus)
    (hminus_margin :
      ∀ z ∈ Dminus, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ w ∈ Dplus,
        realMollifyLocal Fplus ψ w =
          Tplus (fun i => (w i).im)
            (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ w ∈ Dminus,
        realMollifyLocal Fminus ψ w =
          Tminus (fun i => (w i).im)
            (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (hx0 : x0 ∈ E) :
    ∃ ys : Fin m → Fin m → ℝ,
      (∀ j, ys j ∈ C) ∧ LinearIndependent ℝ ys ∧
      ∃ ρ : ℝ, 0 < ρ ∧
      ∃ r : ℝ, 0 < r ∧
      ∃ δ : ℝ, 0 < δ ∧
        δ * 10 ≤ ρ ∧
        (Fintype.card (Fin m) : ℝ) * (δ * 10) < r ∧
        (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
          localEOWRealChart x0 ys u ∈ E) ∧
        (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
          (∀ j, 0 ≤ v j) →
          0 < ∑ j, v j →
          (∑ j, v j) < r →
            localEOWChart x0 ys
              (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus) ∧
        (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ, ∀ v : Fin m → ℝ,
          (∀ j, v j ≤ 0) →
          0 < ∑ j, -v j →
          (∑ j, -v j) < r →
            localEOWChart x0 ys
              (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus) ∧
        ∃ F0 : ComplexChartSpace m → ℂ,
          DifferentiableOn ℂ F0 (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) ∧
          (∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
            (∀ j, 0 < (w j).im) →
              localEOWChart x0 ys w ∈ Dplus ∧
              F0 w = realMollifyLocal Fplus ψ (localEOWChart x0 ys w)) ∧
          (∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
            (∀ j, (w j).im < 0) →
              localEOWChart x0 ys w ∈ Dminus ∧
              F0 w = realMollifyLocal Fminus ψ (localEOWChart x0 ys w)) ∧
          (∀ u : Fin m → ℝ,
            (fun j => (u j : ℂ)) ∈
              Metric.ball (0 : ComplexChartSpace m) (δ / 2) →
              F0 (fun j => (u j : ℂ)) =
                Tchart (translateSchwartz (-(localEOWRealChart x0 ys u)) ψ)) ∧
          (∀ G : ComplexChartSpace m → ℂ,
            DifferentiableOn ℂ G (Metric.ball (0 : ComplexChartSpace m) (δ / 2)) →
            (∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2),
              (∀ j, 0 < (w j).im) →
                G w = realMollifyLocal Fplus ψ (localEOWChart x0 ys w)) →
            ∀ w ∈ Metric.ball (0 : ComplexChartSpace m) (δ / 2), G w = F0 w) := by
  have hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ) :=
    KernelSupportWithin_hasCompactSupport hψ_support
  have hFplus_moll_holo :
      DifferentiableOn ℂ (realMollifyLocal Fplus ψ) Dplus :=
    localRealMollifySide_holomorphicOn_of_translate_margin
      Fplus ψ Ωplus Dplus hΩplus_open hDplus_open hFplus_diff
      hψ_compact hplus_margin
  have hFminus_moll_holo :
      DifferentiableOn ℂ (realMollifyLocal Fminus ψ) Dminus :=
    localRealMollifySide_holomorphicOn_of_translate_margin
      Fminus ψ Ωminus Dminus hΩminus_open hDminus_open hFminus_diff
      hψ_compact hminus_margin
  have hcommon :=
    localRealMollify_commonContinuousBoundary_of_clm
      Dplus Dminus Fplus Fminus Tplus Tminus Tchart ψ E hψ_compact
      hDplus_sub hDminus_sub hplus_eval hminus_eval hplus_limit hminus_limit
  exact
    local_continuous_edge_of_the_wedge_envelope hm
      Dplus Dminus E C hDplus_open hDminus_open hE_open hC_open hC_conv
      hC_ne hlocal_wedge (realMollifyLocal Fplus ψ)
      (realMollifyLocal Fminus ψ) hFplus_moll_holo hFminus_moll_holo
      (fun x : Fin m → ℝ => Tchart (translateSchwartz (-x) ψ))
      hcommon.1 hcommon.2.1 hcommon.2.2 x0 hx0

end SCV
