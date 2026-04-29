/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalDistributionalEOW

/-!
# Varying-Kernel Continuity for Local EOW

This file contains the small analytic continuity lemmas needed to integrate the
local EOW envelope while the real smoothing kernel varies with the chart point.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

variable {m : ℕ}

/-- Real translations of Schwartz functions are uniformly bounded on compact
sets of translation parameters, for each fixed Schwartz seminorm.  The output
`k,l` seminorm is controlled by the input `k,l` and `0,l` seminorms; the latter
is necessary because the polynomial weight vanishes at the origin. -/
theorem seminorm_translateSchwartz_uniformOn
    (E : Set (Fin m → ℝ)) (hE : IsCompact E)
    (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ E, ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        (SchwartzMap.seminorm ℝ k l) (translateSchwartz a ψ) ≤
          C * ((SchwartzMap.seminorm ℝ k l) ψ +
            (SchwartzMap.seminorm ℝ 0 l) ψ) := by
  obtain ⟨R0, hR0⟩ :=
    hE.exists_bound_of_continuousOn
      (f := fun a : Fin m → ℝ => ‖a‖)
      continuous_norm.continuousOn
  let R : ℝ := max R0 0
  have hR_nonneg : 0 ≤ R := le_max_right R0 0
  have hR : ∀ a ∈ E, ‖a‖ ≤ R := by
    intro a ha
    have hR0' : ‖a‖ ≤ R0 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)] using hR0 a ha
    exact hR0'.trans (le_max_left R0 0)
  let C : ℝ := 2 ^ (k - 1) * (1 + R) ^ k
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (pow_nonneg (by linarith) _)
  refine ⟨C, hC_nonneg, ?_⟩
  intro a ha ψ
  let Ck : ℝ := (SchwartzMap.seminorm ℝ k l) ψ
  let C0 : ℝ := (SchwartzMap.seminorm ℝ 0 l) ψ
  have hCk_nn : 0 ≤ Ck := by
    dsimp [Ck]
    exact apply_nonneg _ _
  have hC0_nn : 0 ≤ C0 := by
    dsimp [C0]
    exact apply_nonneg _ _
  have hCk : ∀ y : Fin m → ℝ,
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (⇑ψ) y‖ ≤ Ck := by
    intro y
    simpa [Ck] using (SchwartzMap.le_seminorm (𝕜 := ℝ) k l ψ y)
  have hC0' : ∀ y : Fin m → ℝ,
      ‖iteratedFDeriv ℝ l (⇑ψ) y‖ ≤ C0 := by
    intro y
    have h := SchwartzMap.le_seminorm (𝕜 := ℝ) 0 l ψ y
    simpa [C0] using h
  have h1a : 1 ≤ 1 + ‖a‖ := le_add_of_nonneg_right (norm_nonneg a)
  have hkey_a :
      Ck + ‖a‖ ^ k * C0 ≤ (1 + ‖a‖) ^ k * (Ck + C0) := by
    rw [mul_add]
    apply add_le_add
    · exact le_mul_of_one_le_left hCk_nn (one_le_pow₀ h1a)
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg a)
          (le_add_of_nonneg_left zero_le_one) k) hC0_nn
  have haR : 1 + ‖a‖ ≤ 1 + R := by
    linarith [hR a ha]
  have hkey : Ck + ‖a‖ ^ k * C0 ≤ (1 + R) ^ k * (Ck + C0) := by
    exact hkey_a.trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) haR k)
        (add_nonneg hCk_nn hC0_nn))
  refine SchwartzMap.seminorm_le_bound ℝ k l _ ?_ ?_
  · exact mul_nonneg hC_nonneg (add_nonneg hCk_nn hC0_nn)
  intro x
  have hcoe :
      (⇑(translateSchwartz a ψ) : (Fin m → ℝ) → ℂ) =
        fun z => ψ (z + a) :=
    funext fun _ => rfl
  rw [hcoe, iteratedFDeriv_comp_add_right]
  have hnorm_x : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
    calc
      ‖x‖ = ‖(x + a) - a‖ := by ring_nf
      _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑ψ) (x + a)‖
        ≤ (‖x + a‖ + ‖a‖) ^ k *
            ‖iteratedFDeriv ℝ l (⇑ψ) (x + a)‖ := by
          gcongr
    _ ≤ (2 ^ (k - 1) * (‖x + a‖ ^ k + ‖a‖ ^ k)) *
          ‖iteratedFDeriv ℝ l (⇑ψ) (x + a)‖ := by
          gcongr
          exact add_pow_le (norm_nonneg _) (norm_nonneg _) k
    _ = 2 ^ (k - 1) *
          (‖x + a‖ ^ k * ‖iteratedFDeriv ℝ l (⇑ψ) (x + a)‖ +
            ‖a‖ ^ k * ‖iteratedFDeriv ℝ l (⇑ψ) (x + a)‖) := by
          ring
    _ ≤ 2 ^ (k - 1) * (Ck + ‖a‖ ^ k * C0) := by
          gcongr
          · exact hCk (x + a)
          · exact hC0' (x + a)
    _ ≤ 2 ^ (k - 1) * ((1 + R) ^ k * (Ck + C0)) := by
          gcongr
    _ = C * (Ck + C0) := by
          simp only [C]
          ring
    _ = C * ((SchwartzMap.seminorm ℝ k l) ψ +
            (SchwartzMap.seminorm ℝ 0 l) ψ) := by
          rfl

private theorem hasCompactSupport_of_zero_off_compact
    (K : Set (Fin m → ℝ)) (hK : IsCompact K)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hzero : ∀ t ∉ K, ψ t = 0) :
    HasCompactSupport (ψ : (Fin m → ℝ) → ℂ) := by
  have hK_closed : IsClosed K := hK.isClosed
  have hsupport_subset : Function.support (ψ : (Fin m → ℝ) → ℂ) ⊆ K := by
    intro t ht
    by_contra htK
    exact ht (hzero t htK)
  have htsupport_subset : tsupport (ψ : (Fin m → ℝ) → ℂ) ⊆ K :=
    closure_minimal hsupport_subset hK_closed
  exact hK.of_isClosed_subset (isClosed_tsupport _) htsupport_subset

/-- If a Schwartz kernel depends continuously on a parameter and all kernels
vanish outside one fixed compact set, then translating by a compactly varying
center is jointly continuous in the Schwartz topology. -/
theorem continuousOn_translateSchwartz_varyingKernel_of_fixedSupport
    (Z : Set (ComplexChartSpace m)) (E : Set (Fin m → ℝ))
    (K : Set (Fin m → ℝ))
    (η : ComplexChartSpace m → SchwartzMap (Fin m → ℝ) ℂ)
    (hE_compact : IsCompact E) (hK_compact : IsCompact K)
    (hη_cont : ContinuousOn η Z)
    (hη_zero : ∀ z ∈ Z, ∀ t ∉ K, η z t = 0) :
    ContinuousOn
      (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
        translateSchwartz (-p.2) (η p.1))
      (Z ×ˢ E) := by
  intro p0 hp0
  rcases p0 with ⟨z0, a0⟩
  rcases hp0 with ⟨hz0, ha0⟩
  change Tendsto
    (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
      translateSchwartz (-p.2) (η p.1))
    (nhdsWithin (z0, a0) (Z ×ˢ E))
    (nhds (translateSchwartz (-a0) (η z0)))
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
  intro i ε hε
  rcases i with ⟨k, l⟩
  have hε2 : 0 < ε / 2 := by positivity
  let L : Filter (ComplexChartSpace m × (Fin m → ℝ)) :=
    nhdsWithin (z0, a0) (Z ×ˢ E)
  let Eneg : Set (Fin m → ℝ) := (fun a => -a) '' E
  have hEneg_compact : IsCompact Eneg := hE_compact.image continuous_neg
  obtain ⟨C, hC_nonneg, hCbound⟩ :=
    seminorm_translateSchwartz_uniformOn Eneg hEneg_compact k l
  have hfst :
      Tendsto (fun p : ComplexChartSpace m × (Fin m → ℝ) => p.1)
        L (nhdsWithin z0 Z) := by
    exact continuous_fst.continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (by intro p hp; exact hp.1)
  have hη_tend :
      Tendsto (fun p : ComplexChartSpace m × (Fin m → ℝ) => η p.1)
        L (nhds (η z0)) :=
    Filter.Tendsto.comp (hη_cont z0 hz0) hfst
  have hη_diff :
      Tendsto
        (fun p : ComplexChartSpace m × (Fin m → ℝ) => η p.1 - η z0)
        L (nhds 0) := by
    have hconst :
        Tendsto (fun _ : ComplexChartSpace m × (Fin m → ℝ) => η z0)
          L (nhds (η z0)) :=
      tendsto_const_nhds
    simpa using hη_tend.sub hconst
  have hsemi_kl :
      Tendsto
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          (SchwartzMap.seminorm ℝ k l) (η p.1 - η z0))
        L (nhds 0) := by
    simpa using
      (Filter.Tendsto.comp
        (((schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).continuous_seminorm
          (k, l)).continuousAt) hη_diff)
  have hsemi_0l :
      Tendsto
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          (SchwartzMap.seminorm ℝ 0 l) (η p.1 - η z0))
        L (nhds 0) := by
    simpa using
      (Filter.Tendsto.comp
        (((schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).continuous_seminorm
          (0, l)).continuousAt) hη_diff)
  have hsum :
      Tendsto
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          (SchwartzMap.seminorm ℝ k l) (η p.1 - η z0) +
            (SchwartzMap.seminorm ℝ 0 l) (η p.1 - η z0))
        L (nhds 0) := by
    simpa using hsemi_kl.add hsemi_0l
  have hprod :
      Tendsto
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          C * ((SchwartzMap.seminorm ℝ k l) (η p.1 - η z0) +
            (SchwartzMap.seminorm ℝ 0 l) (η p.1 - η z0)))
        L (nhds 0) := by
    simpa using tendsto_const_nhds.mul hsum
  have hsmall1 :
      ∀ᶠ p : ComplexChartSpace m × (Fin m → ℝ) in L,
        C * ((SchwartzMap.seminorm ℝ k l) (η p.1 - η z0) +
            (SchwartzMap.seminorm ℝ 0 l) (η p.1 - η z0)) < ε / 2 :=
    hprod.eventually (Iio_mem_nhds hε2)
  have hηz0_compact : HasCompactSupport (η z0 : (Fin m → ℝ) → ℂ) :=
    hasCompactSupport_of_zero_off_compact K hK_compact (η z0)
      (hη_zero z0 hz0)
  have hsnd_neg :
      Tendsto
        (fun p : ComplexChartSpace m × (Fin m → ℝ) => -p.2)
        L (nhds (-a0)) := by
    have hcont :
        Continuous (fun p : ComplexChartSpace m × (Fin m → ℝ) => -p.2) :=
      continuous_snd.neg
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have htrans0 :
      Tendsto
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          translateSchwartz (-p.2) (η z0))
        L (nhds (translateSchwartz (-a0) (η z0))) :=
    (tendsto_translateSchwartz_nhds_of_isCompactSupport
      (η z0) hηz0_compact (-a0)).comp hsnd_neg
  have htrans_diff :
      Tendsto
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          translateSchwartz (-p.2) (η z0) -
            translateSchwartz (-a0) (η z0))
        L (nhds 0) := by
    have hconst :
        Tendsto
          (fun _ : ComplexChartSpace m × (Fin m → ℝ) =>
            translateSchwartz (-a0) (η z0))
          L (nhds (translateSchwartz (-a0) (η z0))) :=
      tendsto_const_nhds
    simpa using htrans0.sub hconst
  have hsemi2 :
      Tendsto
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          (SchwartzMap.seminorm ℝ k l)
            (translateSchwartz (-p.2) (η z0) -
              translateSchwartz (-a0) (η z0)))
        L (nhds 0) := by
    simpa using
      (Filter.Tendsto.comp
        (((schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).continuous_seminorm
          (k, l)).continuousAt) htrans_diff)
  have hsmall2 :
      ∀ᶠ p : ComplexChartSpace m × (Fin m → ℝ) in L,
        (SchwartzMap.seminorm ℝ k l)
            (translateSchwartz (-p.2) (η z0) -
              translateSchwartz (-a0) (η z0)) < ε / 2 :=
    hsemi2.eventually (Iio_mem_nhds hε2)
  filter_upwards [self_mem_nhdsWithin, hsmall1, hsmall2] with p hp h1 h2
  change
    (SchwartzMap.seminorm ℝ k l)
      (translateSchwartz (-p.2) (η p.1) - translateSchwartz (-a0) (η z0)) <
        ε
  have hpEneg : -p.2 ∈ Eneg := ⟨p.2, hp.2, rfl⟩
  have hterm1 := hCbound (-p.2) hpEneg (η p.1 - η z0)
  have hsplit :
      translateSchwartz (-p.2) (η p.1) -
          translateSchwartz (-a0) (η z0) =
        translateSchwartz (-p.2) (η p.1 - η z0) +
          (translateSchwartz (-p.2) (η z0) -
            translateSchwartz (-a0) (η z0)) := by
    ext x
    simp [translateSchwartz_apply]
  calc
    (SchwartzMap.seminorm ℝ k l)
        (translateSchwartz (-p.2) (η p.1) -
          translateSchwartz (-a0) (η z0))
        = (SchwartzMap.seminorm ℝ k l)
          (translateSchwartz (-p.2) (η p.1 - η z0) +
            (translateSchwartz (-p.2) (η z0) -
              translateSchwartz (-a0) (η z0))) := by
          rw [hsplit]
    _ ≤ (SchwartzMap.seminorm ℝ k l)
          (translateSchwartz (-p.2) (η p.1 - η z0)) +
        (SchwartzMap.seminorm ℝ k l)
          (translateSchwartz (-p.2) (η z0) -
            translateSchwartz (-a0) (η z0)) := by
          exact map_add_le_add _ _ _
    _ ≤ C * ((SchwartzMap.seminorm ℝ k l) (η p.1 - η z0) +
          (SchwartzMap.seminorm ℝ 0 l) (η p.1 - η z0)) +
        (SchwartzMap.seminorm ℝ k l)
          (translateSchwartz (-p.2) (η z0) -
            translateSchwartz (-a0) (η z0)) := by
          gcongr
    _ < ε := by
          linarith

/-- A real-direction mollifier is continuous when both the base point and the
compactly supported smoothing kernel vary continuously, provided all translated
points used by the fixed compact support stay in the side domain. -/
theorem continuousOn_realMollifyLocal_varyingKernel_of_fixedSupport
    {X : Type*} [TopologicalSpace X]
    (S : Set X) (K : Set (Fin m → ℝ))
    (Fside : ComplexChartSpace m → ℂ)
    (Ω : Set (ComplexChartSpace m))
    (w : X → ComplexChartSpace m)
    (η : X → SchwartzMap (Fin m → ℝ) ℂ)
    (hK : IsCompact K)
    (hΩ_open : IsOpen Ω)
    (hFside_cont : ContinuousOn Fside Ω)
    (hw_cont : ContinuousOn w S)
    (hη_eval_cont :
      ContinuousOn
        (fun p : X × (Fin m → ℝ) => η p.1 p.2)
        (S ×ˢ Set.univ))
    (hη_zero : ∀ q ∈ S, ∀ t ∉ K, η q t = 0)
    (hmargin : ∀ q ∈ S, ∀ t ∈ K,
      w q + realEmbed t ∈ Ω) :
    ContinuousOn
      (fun q => realMollifyLocal Fside (η q) (w q)) S := by
  let f : X → (Fin m → ℝ) → ℂ :=
    fun q t => Fside (w q + realEmbed t) * η q t
  have hK_closed : IsClosed K := hK.isClosed
  have hf : ContinuousOn f.uncurry (S ×ˢ Set.univ) := by
    intro p hp
    rcases hp with ⟨hpS, -⟩
    by_cases ht : p.2 ∈ K
    · have hp_shift : w p.1 + realEmbed p.2 ∈ Ω :=
        hmargin p.1 hpS p.2 ht
      have hF_at : ContinuousAt Fside (w p.1 + realEmbed p.2) :=
        (hFside_cont (w p.1 + realEmbed p.2) hp_shift).continuousAt
          (hΩ_open.mem_nhds hp_shift)
      have hfst :
          Tendsto (fun q : X × (Fin m → ℝ) => q.1)
            (nhdsWithin p (S ×ˢ Set.univ)) (nhdsWithin p.1 S) := by
        exact continuous_fst.continuousAt.continuousWithinAt.tendsto_nhdsWithin
          (by intro q hq; exact hq.1)
      have hw_tend :
          Tendsto (fun q : X × (Fin m → ℝ) => w q.1)
            (nhdsWithin p (S ×ˢ Set.univ)) (nhds (w p.1)) :=
        Filter.Tendsto.comp (hw_cont p.1 hpS) hfst
      have hreal_tend :
          Tendsto (fun q : X × (Fin m → ℝ) => realEmbed q.2)
            (nhdsWithin p (S ×ˢ Set.univ)) (nhds (realEmbed p.2)) := by
        exact ((continuous_realEmbed (m := m)).comp
          continuous_snd).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hshift_cwa : ContinuousWithinAt
          (fun q : X × (Fin m → ℝ) => w q.1 + realEmbed q.2)
          (S ×ˢ Set.univ) p :=
        hw_tend.add hreal_tend
      have hleft : ContinuousWithinAt
          (fun q : X × (Fin m → ℝ) =>
            Fside (w q.1 + realEmbed q.2))
          (S ×ˢ Set.univ) p :=
        Filter.Tendsto.comp hF_at hshift_cwa
      have hright : ContinuousWithinAt
          (fun q : X × (Fin m → ℝ) => η q.1 q.2)
          (S ×ˢ Set.univ) p :=
        hη_eval_cont p ⟨hpS, trivial⟩
      simpa [f] using hleft.mul hright
    · have hnotK_nhds : {t : Fin m → ℝ | t ∉ K} ∈ 𝓝 p.2 :=
        hK_closed.isOpen_compl.mem_nhds ht
      have hnotK_pair :
          ∀ᶠ q : X × (Fin m → ℝ) in nhdsWithin p (S ×ˢ Set.univ),
            q.2 ∉ K := by
        exact (continuous_snd.continuousAt.eventually hnotK_nhds).filter_mono
          nhdsWithin_le_nhds
      have hprod_zero :
          f.uncurry =ᶠ[nhdsWithin p (S ×ˢ Set.univ)] fun _ => 0 := by
        filter_upwards [self_mem_nhdsWithin, hnotK_pair] with q hq hqK
        have hqS : q.1 ∈ S := hq.1
        change Fside (w q.1 + realEmbed q.2) * η q.1 q.2 = 0
        rw [hη_zero q.1 hqS q.2 hqK, mul_zero]
      exact (continuousWithinAt_const.congr_of_eventuallyEq hprod_zero) (by
        change Fside (w p.1 + realEmbed p.2) * η p.1 p.2 = 0
        rw [hη_zero p.1 hpS p.2 ht, mul_zero])
  have hfs : ∀ p, ∀ x, p ∈ S → x ∉ K → f p x = 0 := by
    intro p x hp hx
    simp [f, hη_zero p hp x hx]
  simpa [realMollifyLocal, f] using
    continuousOn_integral_of_compact_support
      (μ := volume) hK hf hfs

/-- The actual chart-kernel slice used by the mixed pairing integrand varies
continuously in the chart point. -/
theorem continuous_chartKernelCutoffSlice
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    (χr χψ : SchwartzMap (Fin m → ℝ) ℂ)
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ) :
    let P := localEOWRealLinearKernelPushforwardCLM ys hli
    Continuous fun z : ComplexChartSpace m =>
      SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m → ℝ) → ℂ)
        (P (SchwartzMap.smulLeftCLM ℂ
          (χr : (Fin m → ℝ) → ℂ)
          (schwartzPartialEval₁CLM z F))) := by
  let P := localEOWRealLinearKernelPushforwardCLM ys hli
  let A : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin m → ℝ) ℂ :=
    (SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m → ℝ) → ℂ)).comp
      (P.comp (SchwartzMap.smulLeftCLM ℂ (χr : (Fin m → ℝ) → ℂ)))
  have hA : Continuous fun z : ComplexChartSpace m =>
      A (schwartzPartialEval₁CLM z F) :=
    A.continuous.comp (continuous_schwartzPartialEval₁CLM F)
  simpa [A, P] using hA

/-- The actual chart-kernel slice has jointly continuous scalar evaluation in
the chart point and real-edge variable. -/
theorem continuous_chartKernelCutoffSlice_eval
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    (χr χψ : SchwartzMap (Fin m → ℝ) ℂ)
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ) :
    Continuous fun p : ComplexChartSpace m × (Fin m → ℝ) =>
      (SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m → ℝ) → ℂ)
        (localEOWRealLinearKernelPushforwardCLM ys hli
          (SchwartzMap.smulLeftCLM ℂ
          (χr : (Fin m → ℝ) → ℂ)
          (schwartzPartialEval₁CLM p.1 F)))) p.2 := by
  let e := localEOWRealLinearCLE ys hli
  have he_cont : Continuous fun p : ComplexChartSpace m × (Fin m → ℝ) =>
      e.symm p.2 :=
    e.symm.continuous.comp continuous_snd
  have hχψ : Continuous fun p : ComplexChartSpace m × (Fin m → ℝ) =>
      χψ p.2 :=
    χψ.continuous.comp continuous_snd
  have hχr : Continuous fun p : ComplexChartSpace m × (Fin m → ℝ) =>
      χr (e.symm p.2) :=
    χr.continuous.comp he_cont
  have hF : Continuous fun p : ComplexChartSpace m × (Fin m → ℝ) =>
      F (p.1, e.symm p.2) :=
    F.continuous.comp (continuous_fst.prodMk he_cont)
  have hmain : Continuous fun p : ComplexChartSpace m × (Fin m → ℝ) =>
      χψ p.2 *
        (((localEOWRealJacobianAbs ys)⁻¹ : ℂ) *
          (χr (e.symm p.2) * F (p.1, e.symm p.2))) :=
    hχψ.mul (continuous_const.mul (hχr.mul hF))
  simpa [e, localEOWRealLinearKernelPushforwardCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply χψ.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply χr.hasTemperateGrowth,
    schwartzPartialEval₁CLM_apply, mul_assoc] using hmain

/-- The actual chart-kernel cutoff slice is supported wherever the final
original-edge cutoff is supported. -/
theorem KernelSupportWithin.chartKernelCutoffSlice
    (ys : Fin m → Fin m → ℝ) (hli : LinearIndependent ℝ ys)
    (χr χψ : SchwartzMap (Fin m → ℝ) ℂ)
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    {rψLarge : ℝ}
    (hχψ_support :
      tsupport (χψ : (Fin m → ℝ) → ℂ) ⊆
        Metric.closedBall 0 rψLarge) :
    ∀ z : ComplexChartSpace m,
      KernelSupportWithin
        (SchwartzMap.smulLeftCLM ℂ (χψ : (Fin m → ℝ) → ℂ)
          (SCV.localEOWRealLinearKernelPushforwardCLM ys hli
            (SchwartzMap.smulLeftCLM ℂ
            (χr : (Fin m → ℝ) → ℂ)
            (schwartzPartialEval₁CLM z F))))
        rψLarge := by
  intro z
  exact KernelSupportWithin.smulLeftCLM_of_leftSupport hχψ_support _

/-- A kernel supported in a closed ball is pointwise zero outside that ball. -/
theorem KernelSupportWithin.eq_zero_of_not_mem_closedBall
    {ψ : SchwartzMap (Fin m → ℝ) ℂ} {r : ℝ}
    (hψ : KernelSupportWithin ψ r) {x : Fin m → ℝ}
    (hx : x ∉ Metric.closedBall (0 : Fin m → ℝ) r) :
    ψ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hx_supp => hx (hψ hx_supp))

/-- Continuity of the moving boundary-value CLM branch used at the real edge
of the parametric local Rudin circle. -/
theorem continuousOn_localRudinBoundaryCLM_varyingKernel_of_fixedSupport
    (Z : Set (ComplexChartSpace m)) (E : Set (Fin m → ℝ))
    (η : ComplexChartSpace m → SchwartzMap (Fin m → ℝ) ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    {rψLarge : ℝ}
    (hE_compact : IsCompact E)
    (hη_cont : ContinuousOn η Z)
    (hη_support : ∀ z ∈ Z, KernelSupportWithin (η z) rψLarge) :
    ContinuousOn
      (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
        Tchart (translateSchwartz (-p.2) (η p.1)))
      (Z ×ˢ E) := by
  have hη_zero :
      ∀ z ∈ Z, ∀ t ∉ Metric.closedBall (0 : Fin m → ℝ) rψLarge,
        η z t = 0 := by
    intro z hz t ht
    exact KernelSupportWithin.eq_zero_of_not_mem_closedBall
      (hη_support z hz) ht
  have htrans :
      ContinuousOn
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          translateSchwartz (-p.2) (η p.1))
        (Z ×ˢ E) :=
    continuousOn_translateSchwartz_varyingKernel_of_fixedSupport
      Z E (Metric.closedBall (0 : Fin m → ℝ) rψLarge) η
      hE_compact (isCompact_closedBall (0 : Fin m → ℝ) rψLarge)
      hη_cont hη_zero
  exact Tchart.continuous.comp_continuousOn htrans

/-- Positive-side moving-kernel boundary limit for the local Rudin circle,
with the translated smoothing kernels converging in the Schwartz topology. -/
theorem tendsto_localRudinPlusBoundary_varyingKernel_of_clm
    {Cplus : Set (Fin m → ℝ)} {δ ρ r rψLarge : ℝ}
    (hm : 0 < m)
    (Dplus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ)) (Z : Set (ComplexChartSpace m))
    (Fplus : ComplexChartSpace m → ℂ)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (Tplus :
      (Fin m → ℝ) →
        SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        KernelSupportWithin ψ rψLarge →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hplus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tplus y f) (nhdsWithin 0 Cplus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (η : ComplexChartSpace m → SchwartzMap (Fin m → ℝ) ℂ)
    (hZ_ball :
      Z ⊆ Metric.ball (0 : ComplexChartSpace m) (δ / 2))
    (hη_support : ∀ z ∈ Z, KernelSupportWithin (η z) rψLarge)
    (hkernel_cont :
      ContinuousOn
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          translateSchwartz (-p.2) (η p.1))
        (Z ×ˢ E))
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
      ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus) :
    ∀ z0 ∈ Z, ∀ l0 ∈ Metric.sphere (0 : ℂ) 1,
      l0.im = 0 →
        Filter.Tendsto
          (fun p : ComplexChartSpace m × ℂ =>
            realMollifyLocal Fplus (η p.1)
              (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)))
          (nhdsWithin (z0, l0)
            ((Z ×ˢ Metric.sphere (0 : ℂ) 1) ∩
              {p : ComplexChartSpace m × ℂ | 0 < p.2.im}))
          (nhds
            (Tchart
              (translateSchwartz
                (-(localEOWRealChart x0 ys
                  (fun j => (localEOWSmp δ z0 l0 j).re)))
                (η z0)))) := by
  intro z0 hz0 l0 hl0 hreal
  have hδ_cnorm : ‖(δ : ℂ)‖ = δ := by
    simp [Complex.norm_real, abs_of_pos hδ]
  have cball_comp_le_half :
      ∀ w ∈ Metric.closedBall (0 : ComplexChartSpace m) (δ / 2),
        ∀ j, ‖w j / (δ : ℂ)‖ ≤ 1 / 2 := by
    intro w hw j
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [norm_div, hδ_cnorm]
    calc
      ‖w j‖ / δ ≤ ‖w‖ / δ := by
        gcongr
        exact norm_le_pi_norm w j
      _ ≤ (δ / 2) / δ := by gcongr
      _ = 1 / 2 := by field_simp
  have cball_comp_lt :
      ∀ w ∈ Metric.closedBall (0 : ComplexChartSpace m) (δ / 2),
        ∀ j, ‖w j / (δ : ℂ)‖ < 1 := by
    intro w hw j
    linarith [cball_comp_le_half w hw j]
  have sphere_norm : ∀ l ∈ Metric.sphere (0 : ℂ) 1, ‖l‖ = 1 := by
    intro l hl
    rwa [← dist_zero_right]
  have sphere_normSq : ∀ l ∈ Metric.sphere (0 : ℂ) 1, Complex.normSq l = 1 := by
    intro l hl
    have h := sphere_norm l hl
    rw [Complex.normSq_eq_norm_sq, h]
    norm_num
  have smp_cont : ContinuousOn
      (fun p : ComplexChartSpace m × ℂ => localEOWSmp δ p.1 p.2)
      (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
        Metric.closedBall (0 : ℂ) 1) := by
    apply continuousOn_pi.mpr
    intro j
    show ContinuousOn
      (fun p : ComplexChartSpace m × ℂ =>
        (δ : ℂ) * moebiusProd (fun k => p.1 k / (δ : ℂ)) p.2 j)
      (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
        Metric.closedBall (0 : ℂ) 1)
    have h_proj : ContinuousOn
        (fun p : ComplexChartSpace m × ℂ => (p.1 j / (δ : ℂ), p.2))
        (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
          Metric.closedBall (0 : ℂ) 1) :=
      (((continuous_apply j).comp continuous_fst).div_const _ |>.prodMk
        continuous_snd).continuousOn
    have h_maps : Set.MapsTo
        (fun p : ComplexChartSpace m × ℂ => (p.1 j / (δ : ℂ), p.2))
        (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
          Metric.closedBall (0 : ℂ) 1)
        (Metric.ball (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ℂ) 1) := by
      intro ⟨w, l⟩ ⟨hw, hl⟩
      exact ⟨by
          rw [Metric.mem_ball, dist_zero_right]
          exact cball_comp_lt w hw j,
        by rwa [Metric.mem_closedBall, dist_zero_right] at hl ⊢⟩
    exact continuousOn_const.mul (moebiusRudin_continuousOn.comp h_proj h_maps)
  have chart_smp_cont : ContinuousOn
      (fun p : ComplexChartSpace m × ℂ =>
        localEOWChart x0 ys (localEOWSmp δ p.1 p.2))
      (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
        Metric.closedBall (0 : ℂ) 1) :=
    (continuous_localEOWChart x0 ys).comp_continuousOn smp_cont
  have real_chart_smp_cont : ContinuousOn
      (fun p : ComplexChartSpace m × ℂ =>
        localEOWRealChart x0 ys
          (fun j => (localEOWSmp δ p.1 p.2 j).re))
      (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
        Metric.closedBall (0 : ℂ) 1) := by
    apply (continuous_localEOWRealChart x0 ys).comp_continuousOn
    exact continuousOn_pi.mpr fun j =>
      Complex.continuous_re.comp_continuousOn
        ((continuous_apply j).comp_continuousOn smp_cont)
  let S : Set (ComplexChartSpace m × ℂ) :=
    Z ×ˢ Metric.sphere (0 : ℂ) 1
  let sample : ComplexChartSpace m × ℂ → ComplexChartSpace m := fun p =>
    localEOWChart x0 ys (localEOWSmp δ p.1 p.2)
  let realSample : ComplexChartSpace m × ℂ → Fin m → ℝ := fun p =>
    localEOWRealChart x0 ys (fun j => (localEOWSmp δ p.1 p.2 j).re)
  let imSample : ComplexChartSpace m × ℂ → Fin m → ℝ := fun p =>
    fun i => (sample p i).im
  let L : Filter (ComplexChartSpace m × ℂ) :=
    nhdsWithin (z0, l0) (S ∩ {p : ComplexChartSpace m × ℂ | 0 < p.2.im})
  have hS_sub :
      S ⊆ Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
        Metric.closedBall (0 : ℂ) 1 := by
    intro p hp
    exact ⟨Metric.ball_subset_closedBall (hZ_ball hp.1),
      Metric.sphere_subset_closedBall hp.2⟩
  have hbase : (z0, l0) ∈ S := ⟨hz0, hl0⟩
  have h_chart_cwa : ContinuousWithinAt sample S (z0, l0) := by
    simpa [sample] using
      (chart_smp_cont.mono hS_sub).continuousWithinAt hbase
  have h_real_cwa : ContinuousWithinAt realSample S (z0, l0) := by
    simpa [realSample] using
      (real_chart_smp_cont.mono hS_sub).continuousWithinAt hbase
  have hsample_pos_mem :
      ∀ p : ComplexChartSpace m × ℂ,
        p ∈ S ∩ {p : ComplexChartSpace m × ℂ | 0 < p.2.im} →
          sample p ∈ Dplus := by
    intro p hp
    rcases p with ⟨z, l⟩
    rcases hp with ⟨⟨hz, hl⟩, him⟩
    simpa [sample] using
      localEOWChart_smp_upper_mem_of_delta_on_sphere hm Dplus x0 ys
        hδ hδρ hδsum hplus
        (Metric.ball_subset_closedBall (hZ_ball hz)) (sphere_norm l hl) him
  have h_chart_real :
      sample (z0, l0) = realEmbed (realSample (z0, l0)) := by
    simpa [sample, realSample] using
      localEOWChart_smp_realEdge_eq_of_unit_real x0 ys
        (sphere_normSq l0 hl0) hreal
  have him0 : imSample (z0, l0) = 0 := by
    have hsample_im0 : (fun i => (sample (z0, l0) i).im) = 0 := by
      rw [h_chart_real]
      ext i
      simp [realEmbed]
    simpa [imSample] using hsample_im0
  have him_cwa :
      ContinuousWithinAt imSample
        (S ∩ {p : ComplexChartSpace m × ℂ | 0 < p.2.im}) (z0, l0) := by
    let imMap : ComplexChartSpace m → Fin m → ℝ := fun w i => (w i).im
    have himMap_cont : Continuous imMap := by
      refine continuous_pi ?_
      intro i
      exact Complex.continuous_im.comp (continuous_apply i)
    have hcomp : ContinuousWithinAt (fun p => imMap (sample p)) S (z0, l0) :=
      himMap_cont.continuousAt.comp_continuousWithinAt h_chart_cwa
    simpa [imMap, imSample] using hcomp.mono Set.inter_subset_left
  have him_maps :
      Set.MapsTo imSample
        (S ∩ {p : ComplexChartSpace m × ℂ | 0 < p.2.im}) Cplus := by
    intro p hp
    have hD : sample p ∈ Dplus := hsample_pos_mem p hp
    simpa [TubeDomain, imSample] using hDplus_sub hD
  have him_tendsto :
      Tendsto imSample L (nhdsWithin 0 Cplus) := by
    have ht := him_cwa.tendsto_nhdsWithin him_maps
    simpa [L, him0] using ht
  have hreal_endpoint_mem : realSample (z0, l0) ∈ E := by
    exact hE_mem _
      (localEOWSmp_re_mem_closedBall hδ hδρ
        (Metric.ball_subset_closedBall (hZ_ball hz0))
        ((sphere_norm l0 hl0).le.trans (by norm_num)))
  let realParam : ComplexChartSpace m × ℂ →
      ComplexChartSpace m × (Fin m → ℝ) := fun p => (p.1, realSample p)
  have hrealParam_cwa :
      ContinuousWithinAt realParam
        (S ∩ {p : ComplexChartSpace m × ℂ | 0 < p.2.im}) (z0, l0) := by
    have hfst : ContinuousWithinAt (fun p : ComplexChartSpace m × ℂ => p.1)
        (S ∩ {p : ComplexChartSpace m × ℂ | 0 < p.2.im}) (z0, l0) :=
      continuous_fst.continuousAt.continuousWithinAt
    have hreal_side : ContinuousWithinAt realSample
        (S ∩ {p : ComplexChartSpace m × ℂ | 0 < p.2.im}) (z0, l0) :=
      h_real_cwa.mono Set.inter_subset_left
    show Tendsto realParam
        (nhdsWithin (z0, l0)
          (S ∩ {p : ComplexChartSpace m × ℂ | 0 < p.2.im}))
        (nhds (realParam (z0, l0)))
    simpa [realParam] using Filter.Tendsto.prodMk_nhds hfst hreal_side
  have hrealParam_maps :
      Set.MapsTo realParam
        (S ∩ {p : ComplexChartSpace m × ℂ | 0 < p.2.im}) (Z ×ˢ E) := by
    intro p hp
    rcases p with ⟨z, l⟩
    rcases hp with ⟨⟨hz, hl⟩, _him⟩
    constructor
    · exact hz
    · exact hE_mem _
        (localEOWSmp_re_mem_closedBall hδ hδρ
          (Metric.ball_subset_closedBall (hZ_ball hz))
          ((sphere_norm l hl).le.trans (by norm_num)))
  have hrealParam_tendsto :
      Tendsto realParam L (nhdsWithin (realParam (z0, l0)) (Z ×ˢ E)) := by
    have ht := hrealParam_cwa.tendsto_nhdsWithin hrealParam_maps
    simpa [L] using ht
  have hkernel_tendsto :
      Tendsto
        (fun p : ComplexChartSpace m × ℂ =>
          translateSchwartz (-(realSample p)) (η p.1))
        L
        (nhds (translateSchwartz (-(realSample (z0, l0))) (η z0))) := by
    have hmem : realParam (z0, l0) ∈ Z ×ˢ E := by
      exact ⟨hz0, hreal_endpoint_mem⟩
    have ht := Filter.Tendsto.comp (hkernel_cont (realParam (z0, l0)) hmem)
      hrealParam_tendsto
    simpa [realParam] using ht
  have hT_comp :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto
          (fun p : ComplexChartSpace m × ℂ => Tplus (imSample p) f)
          L (nhds ((Tchart.restrictScalars ℝ) f)) := by
    intro f
    exact (hplus_limit f).comp him_tendsto
  have happly :
      Tendsto
        (fun p : ComplexChartSpace m × ℂ =>
          Tplus (imSample p)
            (translateSchwartz (-(realSample p)) (η p.1)))
        L
        (nhds
          (Tchart
            (translateSchwartz (-(realSample (z0, l0))) (η z0)))) := by
    simpa using
      (SchwartzMap.tempered_apply_tendsto_of_tendsto_filter hT_comp
        hkernel_tendsto)
  exact happly.congr' (eventually_nhdsWithin_of_forall fun p hp => by
    have hD : sample p ∈ Dplus := hsample_pos_mem p hp
    have hz : p.1 ∈ Z := hp.1.1
    have heval := hplus_eval (η p.1) (hη_support p.1 hz) (sample p) hD
    have hneg_re : (fun i => - (sample p i).re) = -(realSample p) := by
      ext i
      simp [sample, realSample, localEOWChart, localEOWRealChart]
    simpa [imSample, hneg_re] using heval.symm)

/-- Negative-side moving-kernel boundary limit for the local Rudin circle,
with the translated smoothing kernels converging in the Schwartz topology. -/
theorem tendsto_localRudinMinusBoundary_varyingKernel_of_clm
    {Cminus : Set (Fin m → ℝ)} {δ ρ r rψLarge : ℝ}
    (hm : 0 < m)
    (Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ)) (Z : Set (ComplexChartSpace m))
    (Fminus : ComplexChartSpace m → ℂ)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tminus :
      (Fin m → ℝ) →
        SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        KernelSupportWithin ψ rψLarge →
        ∀ w ∈ Dminus,
          realMollifyLocal Fminus ψ w =
            Tminus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_limit :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun y => Tminus y f) (nhdsWithin 0 Cminus)
          (nhds ((Tchart.restrictScalars ℝ) f)))
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (hδ : 0 < δ) (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin m) : ℝ) * (δ * 10) < r)
    (η : ComplexChartSpace m → SchwartzMap (Fin m → ℝ) ℂ)
    (hZ_ball :
      Z ⊆ Metric.ball (0 : ComplexChartSpace m) (δ / 2))
    (hη_support : ∀ z ∈ Z, KernelSupportWithin (η z) rψLarge)
    (hkernel_cont :
      ContinuousOn
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          translateSchwartz (-p.2) (η p.1))
        (Z ×ˢ E))
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
      ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus) :
    ∀ z0 ∈ Z, ∀ l0 ∈ Metric.sphere (0 : ℂ) 1,
      l0.im = 0 →
        Filter.Tendsto
          (fun p : ComplexChartSpace m × ℂ =>
            realMollifyLocal Fminus (η p.1)
              (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)))
          (nhdsWithin (z0, l0)
            ((Z ×ˢ Metric.sphere (0 : ℂ) 1) ∩
              {p : ComplexChartSpace m × ℂ | p.2.im < 0}))
          (nhds
            (Tchart
              (translateSchwartz
                (-(localEOWRealChart x0 ys
                  (fun j => (localEOWSmp δ z0 l0 j).re)))
                (η z0)))) := by
  intro z0 hz0 l0 hl0 hreal
  have hδ_cnorm : ‖(δ : ℂ)‖ = δ := by
    simp [Complex.norm_real, abs_of_pos hδ]
  have cball_comp_le_half :
      ∀ w ∈ Metric.closedBall (0 : ComplexChartSpace m) (δ / 2),
        ∀ j, ‖w j / (δ : ℂ)‖ ≤ 1 / 2 := by
    intro w hw j
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [norm_div, hδ_cnorm]
    calc
      ‖w j‖ / δ ≤ ‖w‖ / δ := by
        gcongr
        exact norm_le_pi_norm w j
      _ ≤ (δ / 2) / δ := by gcongr
      _ = 1 / 2 := by field_simp
  have cball_comp_lt :
      ∀ w ∈ Metric.closedBall (0 : ComplexChartSpace m) (δ / 2),
        ∀ j, ‖w j / (δ : ℂ)‖ < 1 := by
    intro w hw j
    linarith [cball_comp_le_half w hw j]
  have sphere_norm : ∀ l ∈ Metric.sphere (0 : ℂ) 1, ‖l‖ = 1 := by
    intro l hl
    rwa [← dist_zero_right]
  have sphere_normSq : ∀ l ∈ Metric.sphere (0 : ℂ) 1, Complex.normSq l = 1 := by
    intro l hl
    have h := sphere_norm l hl
    rw [Complex.normSq_eq_norm_sq, h]
    norm_num
  have smp_cont : ContinuousOn
      (fun p : ComplexChartSpace m × ℂ => localEOWSmp δ p.1 p.2)
      (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
        Metric.closedBall (0 : ℂ) 1) := by
    apply continuousOn_pi.mpr
    intro j
    show ContinuousOn
      (fun p : ComplexChartSpace m × ℂ =>
        (δ : ℂ) * moebiusProd (fun k => p.1 k / (δ : ℂ)) p.2 j)
      (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
        Metric.closedBall (0 : ℂ) 1)
    have h_proj : ContinuousOn
        (fun p : ComplexChartSpace m × ℂ => (p.1 j / (δ : ℂ), p.2))
        (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
          Metric.closedBall (0 : ℂ) 1) :=
      (((continuous_apply j).comp continuous_fst).div_const _ |>.prodMk
        continuous_snd).continuousOn
    have h_maps : Set.MapsTo
        (fun p : ComplexChartSpace m × ℂ => (p.1 j / (δ : ℂ), p.2))
        (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
          Metric.closedBall (0 : ℂ) 1)
        (Metric.ball (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ℂ) 1) := by
      intro ⟨w, l⟩ ⟨hw, hl⟩
      exact ⟨by
          rw [Metric.mem_ball, dist_zero_right]
          exact cball_comp_lt w hw j,
        by rwa [Metric.mem_closedBall, dist_zero_right] at hl ⊢⟩
    exact continuousOn_const.mul (moebiusRudin_continuousOn.comp h_proj h_maps)
  have chart_smp_cont : ContinuousOn
      (fun p : ComplexChartSpace m × ℂ =>
        localEOWChart x0 ys (localEOWSmp δ p.1 p.2))
      (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
        Metric.closedBall (0 : ℂ) 1) :=
    (continuous_localEOWChart x0 ys).comp_continuousOn smp_cont
  have real_chart_smp_cont : ContinuousOn
      (fun p : ComplexChartSpace m × ℂ =>
        localEOWRealChart x0 ys
          (fun j => (localEOWSmp δ p.1 p.2 j).re))
      (Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
        Metric.closedBall (0 : ℂ) 1) := by
    apply (continuous_localEOWRealChart x0 ys).comp_continuousOn
    exact continuousOn_pi.mpr fun j =>
      Complex.continuous_re.comp_continuousOn
        ((continuous_apply j).comp_continuousOn smp_cont)
  let S : Set (ComplexChartSpace m × ℂ) :=
    Z ×ˢ Metric.sphere (0 : ℂ) 1
  let sample : ComplexChartSpace m × ℂ → ComplexChartSpace m := fun p =>
    localEOWChart x0 ys (localEOWSmp δ p.1 p.2)
  let realSample : ComplexChartSpace m × ℂ → Fin m → ℝ := fun p =>
    localEOWRealChart x0 ys (fun j => (localEOWSmp δ p.1 p.2 j).re)
  let imSample : ComplexChartSpace m × ℂ → Fin m → ℝ := fun p =>
    fun i => (sample p i).im
  let L : Filter (ComplexChartSpace m × ℂ) :=
    nhdsWithin (z0, l0) (S ∩ {p : ComplexChartSpace m × ℂ | p.2.im < 0})
  have hS_sub :
      S ⊆ Metric.closedBall (0 : ComplexChartSpace m) (δ / 2) ×ˢ
        Metric.closedBall (0 : ℂ) 1 := by
    intro p hp
    exact ⟨Metric.ball_subset_closedBall (hZ_ball hp.1),
      Metric.sphere_subset_closedBall hp.2⟩
  have hbase : (z0, l0) ∈ S := ⟨hz0, hl0⟩
  have h_chart_cwa : ContinuousWithinAt sample S (z0, l0) := by
    simpa [sample] using
      (chart_smp_cont.mono hS_sub).continuousWithinAt hbase
  have h_real_cwa : ContinuousWithinAt realSample S (z0, l0) := by
    simpa [realSample] using
      (real_chart_smp_cont.mono hS_sub).continuousWithinAt hbase
  have hsample_neg_mem :
      ∀ p : ComplexChartSpace m × ℂ,
        p ∈ S ∩ {p : ComplexChartSpace m × ℂ | p.2.im < 0} →
          sample p ∈ Dminus := by
    intro p hp
    rcases p with ⟨z, l⟩
    rcases hp with ⟨⟨hz, hl⟩, him⟩
    simpa [sample] using
      localEOWChart_smp_lower_mem_of_delta_on_sphere hm Dminus x0 ys
        hδ hδρ hδsum hminus
        (Metric.ball_subset_closedBall (hZ_ball hz)) (sphere_norm l hl) him
  have h_chart_real :
      sample (z0, l0) = realEmbed (realSample (z0, l0)) := by
    simpa [sample, realSample] using
      localEOWChart_smp_realEdge_eq_of_unit_real x0 ys
        (sphere_normSq l0 hl0) hreal
  have him0 : imSample (z0, l0) = 0 := by
    have hsample_im0 : (fun i => (sample (z0, l0) i).im) = 0 := by
      rw [h_chart_real]
      ext i
      simp [realEmbed]
    simpa [imSample] using hsample_im0
  have him_cwa :
      ContinuousWithinAt imSample
        (S ∩ {p : ComplexChartSpace m × ℂ | p.2.im < 0}) (z0, l0) := by
    let imMap : ComplexChartSpace m → Fin m → ℝ := fun w i => (w i).im
    have himMap_cont : Continuous imMap := by
      refine continuous_pi ?_
      intro i
      exact Complex.continuous_im.comp (continuous_apply i)
    have hcomp : ContinuousWithinAt (fun p => imMap (sample p)) S (z0, l0) :=
      himMap_cont.continuousAt.comp_continuousWithinAt h_chart_cwa
    simpa [imMap, imSample] using hcomp.mono Set.inter_subset_left
  have him_maps :
      Set.MapsTo imSample
        (S ∩ {p : ComplexChartSpace m × ℂ | p.2.im < 0}) Cminus := by
    intro p hp
    have hD : sample p ∈ Dminus := hsample_neg_mem p hp
    simpa [TubeDomain, imSample] using hDminus_sub hD
  have him_tendsto :
      Tendsto imSample L (nhdsWithin 0 Cminus) := by
    have ht := him_cwa.tendsto_nhdsWithin him_maps
    simpa [L, him0] using ht
  have hreal_endpoint_mem : realSample (z0, l0) ∈ E := by
    exact hE_mem _
      (localEOWSmp_re_mem_closedBall hδ hδρ
        (Metric.ball_subset_closedBall (hZ_ball hz0))
        ((sphere_norm l0 hl0).le.trans (by norm_num)))
  let realParam : ComplexChartSpace m × ℂ →
      ComplexChartSpace m × (Fin m → ℝ) := fun p => (p.1, realSample p)
  have hrealParam_cwa :
      ContinuousWithinAt realParam
        (S ∩ {p : ComplexChartSpace m × ℂ | p.2.im < 0}) (z0, l0) := by
    have hfst : ContinuousWithinAt (fun p : ComplexChartSpace m × ℂ => p.1)
        (S ∩ {p : ComplexChartSpace m × ℂ | p.2.im < 0}) (z0, l0) :=
      continuous_fst.continuousAt.continuousWithinAt
    have hreal_side : ContinuousWithinAt realSample
        (S ∩ {p : ComplexChartSpace m × ℂ | p.2.im < 0}) (z0, l0) :=
      h_real_cwa.mono Set.inter_subset_left
    show Tendsto realParam
        (nhdsWithin (z0, l0)
          (S ∩ {p : ComplexChartSpace m × ℂ | p.2.im < 0}))
        (nhds (realParam (z0, l0)))
    simpa [realParam] using Filter.Tendsto.prodMk_nhds hfst hreal_side
  have hrealParam_maps :
      Set.MapsTo realParam
        (S ∩ {p : ComplexChartSpace m × ℂ | p.2.im < 0}) (Z ×ˢ E) := by
    intro p hp
    rcases p with ⟨z, l⟩
    rcases hp with ⟨⟨hz, hl⟩, _him⟩
    constructor
    · exact hz
    · exact hE_mem _
        (localEOWSmp_re_mem_closedBall hδ hδρ
          (Metric.ball_subset_closedBall (hZ_ball hz))
          ((sphere_norm l hl).le.trans (by norm_num)))
  have hrealParam_tendsto :
      Tendsto realParam L (nhdsWithin (realParam (z0, l0)) (Z ×ˢ E)) := by
    have ht := hrealParam_cwa.tendsto_nhdsWithin hrealParam_maps
    simpa [L] using ht
  have hkernel_tendsto :
      Tendsto
        (fun p : ComplexChartSpace m × ℂ =>
          translateSchwartz (-(realSample p)) (η p.1))
        L
        (nhds (translateSchwartz (-(realSample (z0, l0))) (η z0))) := by
    have hmem : realParam (z0, l0) ∈ Z ×ˢ E := by
      exact ⟨hz0, hreal_endpoint_mem⟩
    have ht := Filter.Tendsto.comp (hkernel_cont (realParam (z0, l0)) hmem)
      hrealParam_tendsto
    simpa [realParam] using ht
  have hT_comp :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto
          (fun p : ComplexChartSpace m × ℂ => Tminus (imSample p) f)
          L (nhds ((Tchart.restrictScalars ℝ) f)) := by
    intro f
    exact (hminus_limit f).comp him_tendsto
  have happly :
      Tendsto
        (fun p : ComplexChartSpace m × ℂ =>
          Tminus (imSample p)
            (translateSchwartz (-(realSample p)) (η p.1)))
        L
        (nhds
          (Tchart
            (translateSchwartz (-(realSample (z0, l0))) (η z0)))) := by
    simpa using
      (SchwartzMap.tempered_apply_tendsto_of_tendsto_filter hT_comp
        hkernel_tendsto)
  exact happly.congr' (eventually_nhdsWithin_of_forall fun p hp => by
    have hD : sample p ∈ Dminus := hsample_neg_mem p hp
    have hz : p.1 ∈ Z := hp.1.1
    have heval := hminus_eval (η p.1) (hη_support p.1 hz) (sample p) hD
    have hneg_re : (fun i => - (sample p i).re) = -(realSample p) := by
      ext i
      simp [sample, realSample, localEOWChart, localEOWRealChart]
    simpa [imSample, hneg_re] using heval.symm)

/-- Boundary-data package for the local Rudin circle with a varying smoothing
kernel.  The proof first obtains Schwartz-valued translated-kernel continuity,
then returns its scalar `Tchart` image together with the two side limits. -/
theorem localRudin_varyingKernel_boundaryData_of_clm
    {Cplus Cminus : Set (Fin m → ℝ)} {δ ρ r rψLarge : ℝ}
    (hm : 0 < m)
    (Dplus Dminus : Set (ComplexChartSpace m))
    (E : Set (Fin m → ℝ))
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hDplus_sub : Dplus ⊆ TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ TubeDomain Cminus)
    (Tplus Tminus :
      (Fin m → ℝ) →
        SchwartzMap (Fin m → ℝ) ℂ →L[ℝ] ℂ)
    (Tchart : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        KernelSupportWithin ψ rψLarge →
        ∀ w ∈ Dplus,
          realMollifyLocal Fplus ψ w =
            Tplus (fun i => (w i).im)
              (translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        KernelSupportWithin ψ rψLarge →
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
    (Z : Set (ComplexChartSpace m))
    (η : ComplexChartSpace m → SchwartzMap (Fin m → ℝ) ℂ)
    (hZ_ball :
      Z ⊆ Metric.ball (0 : ComplexChartSpace m) (δ / 2))
    (hE_compact : IsCompact E)
    (hη_cont : ContinuousOn η Z)
    (hη_support : ∀ z ∈ Z, KernelSupportWithin (η z) rψLarge)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
      ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
      ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus) :
    ContinuousOn
      (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
        Tchart (translateSchwartz (-p.2) (η p.1)))
      (Z ×ˢ E) ∧
    (∀ z0 ∈ Z, ∀ l0 ∈ Metric.sphere (0 : ℂ) 1,
      l0.im = 0 →
        Filter.Tendsto
          (fun p : ComplexChartSpace m × ℂ =>
            realMollifyLocal Fplus (η p.1)
              (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)))
          (nhdsWithin (z0, l0)
            ((Z ×ˢ Metric.sphere (0 : ℂ) 1) ∩
              {p : ComplexChartSpace m × ℂ | 0 < p.2.im}))
          (nhds
            (Tchart
              (translateSchwartz
                (-(localEOWRealChart x0 ys
                  (fun j => (localEOWSmp δ z0 l0 j).re)))
                (η z0))))) ∧
    (∀ z0 ∈ Z, ∀ l0 ∈ Metric.sphere (0 : ℂ) 1,
      l0.im = 0 →
        Filter.Tendsto
          (fun p : ComplexChartSpace m × ℂ =>
            realMollifyLocal Fminus (η p.1)
              (localEOWChart x0 ys (localEOWSmp δ p.1 p.2)))
          (nhdsWithin (z0, l0)
            ((Z ×ˢ Metric.sphere (0 : ℂ) 1) ∩
              {p : ComplexChartSpace m × ℂ | p.2.im < 0}))
          (nhds
            (Tchart
              (translateSchwartz
                (-(localEOWRealChart x0 ys
                  (fun j => (localEOWSmp δ z0 l0 j).re)))
                (η z0))))) := by
  have hη_zero :
      ∀ z ∈ Z, ∀ t ∉ Metric.closedBall (0 : Fin m → ℝ) rψLarge,
        η z t = 0 := by
    intro z hz t ht
    exact KernelSupportWithin.eq_zero_of_not_mem_closedBall
      (hη_support z hz) ht
  have hkernel_cont :
      ContinuousOn
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          translateSchwartz (-p.2) (η p.1))
        (Z ×ˢ E) :=
    continuousOn_translateSchwartz_varyingKernel_of_fixedSupport
      Z E (Metric.closedBall (0 : Fin m → ℝ) rψLarge) η
      hE_compact (isCompact_closedBall (0 : Fin m → ℝ) rψLarge)
      hη_cont hη_zero
  refine ⟨Tchart.continuous.comp_continuousOn hkernel_cont, ?_, ?_⟩
  · exact tendsto_localRudinPlusBoundary_varyingKernel_of_clm hm Dplus E Z
      Fplus hDplus_sub Tplus Tchart hplus_eval hplus_limit x0 ys
      hδ hδρ hδsum η hZ_ball hη_support hkernel_cont hE_mem hplus
  · exact tendsto_localRudinMinusBoundary_varyingKernel_of_clm hm Dminus E Z
      Fminus hDminus_sub Tminus Tchart hminus_eval hminus_limit x0 ys
      hδ hδρ hδsum η hZ_ball hη_support hkernel_cont hE_mem hminus

/-- Continuity of the normalized local Rudin envelope when the smoothing kernel
varies with the outer chart point, assuming a uniform bound on the circle
integrand. -/
theorem continuousOn_localRudinEnvelope_varyingKernel_of_bound
    {δ : ℝ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (Z : Set (ComplexChartSpace m))
    (η : ComplexChartSpace m → SchwartzMap (Fin m → ℝ) ℂ)
    (hside_plus :
      ∀ θ, 0 < Real.sin θ →
        ContinuousOn
          (fun z => realMollifyLocal Fplus (η z)
            (localEOWChart x0 ys
              (localEOWSmp δ z
                (Complex.exp ((θ : ℂ) * Complex.I))))) Z)
    (hside_minus :
      ∀ θ, Real.sin θ < 0 →
        ContinuousOn
          (fun z => realMollifyLocal Fminus (η z)
            (localEOWChart x0 ys
              (localEOWSmp δ z
                (Complex.exp ((θ : ℂ) * Complex.I))))) Z)
    (M : ℝ)
    (hmeas :
      ∀ z ∈ Z,
        AEStronglyMeasurable
          (localRudinIntegrand δ x0 ys
            (realMollifyLocal Fplus (η z))
            (realMollifyLocal Fminus (η z)) z)
          (MeasureTheory.volume.restrict
            (Set.uIoc (-Real.pi) Real.pi)))
    (hM : ∀ z ∈ Z, ∀ θ,
      ‖localRudinIntegrand δ x0 ys
        (realMollifyLocal Fplus (η z))
        (realMollifyLocal Fminus (η z)) z θ‖ ≤ M) :
    ContinuousOn
      (fun z =>
        localRudinEnvelope δ x0 ys
          (realMollifyLocal Fplus (η z))
          (realMollifyLocal Fminus (η z)) z) Z := by
  intro z0 hz0
  have hint : ContinuousWithinAt
      (fun z : ComplexChartSpace m => ∫ θ in (-Real.pi)..Real.pi,
        localRudinIntegrand δ x0 ys
          (realMollifyLocal Fplus (η z))
          (realMollifyLocal Fminus (η z)) z θ) Z z0 := by
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _ => M)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact hmeas z hz
    · filter_upwards [self_mem_nhdsWithin] with z hz
      filter_upwards with θ _hθ
      exact hM z hz θ
    · exact intervalIntegrable_const
    · filter_upwards with θ _hθ
      by_cases hpos : 0 < Real.sin θ
      · have h_eq :
            (fun z : ComplexChartSpace m =>
              localRudinIntegrand δ x0 ys
                (realMollifyLocal Fplus (η z))
                (realMollifyLocal Fminus (η z)) z θ) =
            fun z : ComplexChartSpace m =>
              realMollifyLocal Fplus (η z)
                (localEOWChart x0 ys
                  (localEOWSmp δ z
                    (Complex.exp ((θ : ℂ) * Complex.I)))) := by
          funext z
          simp [localRudinIntegrand, hpos]
        rw [h_eq]
        exact hside_plus θ hpos z0 hz0
      · by_cases hneg : Real.sin θ < 0
        · have h_eq :
              (fun z : ComplexChartSpace m =>
                localRudinIntegrand δ x0 ys
                  (realMollifyLocal Fplus (η z))
                  (realMollifyLocal Fminus (η z)) z θ) =
              fun z : ComplexChartSpace m =>
                realMollifyLocal Fminus (η z)
                  (localEOWChart x0 ys
                    (localEOWSmp δ z
                      (Complex.exp ((θ : ℂ) * Complex.I)))) := by
            funext z
            simp [localRudinIntegrand, hpos, hneg]
          rw [h_eq]
          exact hside_minus θ hneg z0 hz0
        · have h_eq :
              (fun z : ComplexChartSpace m =>
                localRudinIntegrand δ x0 ys
                  (realMollifyLocal Fplus (η z))
                  (realMollifyLocal Fminus (η z)) z θ) =
              fun _ : ComplexChartSpace m => 0 := by
            funext z
            simp [localRudinIntegrand, hpos, hneg]
          rw [h_eq]
          exact continuousWithinAt_const
  have hscaled : ContinuousWithinAt
      (fun z : ComplexChartSpace m =>
        ((2 * Real.pi)⁻¹ : ℝ) •
          (∫ θ in (-Real.pi)..Real.pi,
            localRudinIntegrand δ x0 ys
              (realMollifyLocal Fplus (η z))
              (realMollifyLocal Fminus (η z)) z θ)) Z z0 :=
    continuousWithinAt_const.smul hint
  simpa [localRudinEnvelope, localRudinIntegral] using hscaled

end SCV
