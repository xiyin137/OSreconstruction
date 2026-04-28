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
