/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWHolomorphic
import OSReconstruction.SCV.DistributionalEOWApproxIdentity
import OSReconstruction.SCV.ProductDensity

/-!
# Kernel Recovery Midpoint for Distributional EOW

This downstream file assembles the checked product-kernel descent,
approximate-identity, product-kernel `∂bar`, and distributional-holomorphic
regularity layers.  It also contains the checked delta-limit agreement step
and the final assembly consumer that keeps the remaining pointwise kernel
representation bridge explicit.
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter
open scoped BigOperators LineDeriv

namespace SCV

variable {m : ℕ}

/-- If compact real kernels shrink like `1/(n+1)`, then for each fixed chart
point in an open domain, all real translates in the kernel support eventually
stay inside the domain and have arbitrarily small embedded real displacement. -/
theorem eventually_translate_mem_open_of_shrinking_support
    (Ucore U0 : Set (ComplexChartSpace m))
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore, ∀ ρ > 0,
      ∀ᶠ n in atTop,
        ∀ t ∈ tsupport (ψn n : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ U0 ∧ ‖realEmbed t‖ < ρ := by
  intro z hz ρ hρ
  have hzU : z ∈ U0 := hcore_U0 hz
  obtain ⟨η, hη_pos, hη_sub⟩ := Metric.isOpen_iff.mp hU0_open z hzU
  have hmin_pos : 0 < min η ρ := lt_min hη_pos hρ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hmin_pos
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn t ht
  have hmono : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
    have hNle : (N + 1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ hn
    exact one_div_le_one_div_of_le (by positivity) hNle
  have hsmall : 1 / (n + 1 : ℝ) < min η ρ :=
    lt_of_le_of_lt hmono hN
  have ht_closed := hψ_support n ht
  have ht_norm : ‖t‖ ≤ 1 / (n + 1 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using ht_closed
  have hreal_small_min : ‖realEmbed t‖ < min η ρ :=
    lt_of_le_of_lt (norm_realEmbed_le t) (lt_of_le_of_lt ht_norm hsmall)
  have hreal_eta : ‖realEmbed t‖ < η :=
    lt_of_lt_of_le hreal_small_min (min_le_left η ρ)
  have hreal_rho : ‖realEmbed t‖ < ρ :=
    lt_of_lt_of_le hreal_small_min (min_le_right η ρ)
  have hdist : dist (z + realEmbed t) z = ‖realEmbed t‖ := by
    rw [dist_eq_norm]
    congr 1
    ext i
    simp
  refine ⟨?_, hreal_rho⟩
  exact hη_sub (by simpa [Metric.mem_ball, hdist] using hreal_eta)

/-- A local continuous chart representative is integrable against a compactly
supported real kernel, provided the real-translated topological support stays
inside the chart domain. -/
theorem integrable_continuousOn_realTranslate_mul_kernel
    (H : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (U0 : Set (ComplexChartSpace m))
    (z : ComplexChartSpace m)
    (hU0_open : IsOpen U0)
    (hH_cont : ContinuousOn H U0)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (htranslate :
      ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ), z + realEmbed t ∈ U0) :
    Integrable fun t : Fin m → ℝ => H (z + realEmbed t) * ψ t := by
  have hcont :
      Continuous fun t : Fin m → ℝ => H (z + realEmbed t) * ψ t := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
    · have hzU : z + realEmbed t ∈ U0 := htranslate t ht
      have hH_at : ContinuousAt H (z + realEmbed t) :=
        (hH_cont (z + realEmbed t) hzU).continuousAt
          (hU0_open.mem_nhds hzU)
      have hshift_at :
          ContinuousAt (fun s : Fin m → ℝ => z + realEmbed s) t :=
        (continuous_const.add (continuous_realEmbed (m := m))).continuousAt
      have hH_shift : ContinuousAt (fun s : Fin m → ℝ =>
          H (z + realEmbed s)) t :=
        ContinuousAt.comp_of_eq hH_at hshift_at rfl
      exact hH_shift.mul ψ.continuous.continuousAt
    · have hψ_zero :
          (ψ : (Fin m → ℝ) → ℂ) =ᶠ[nhds t] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at ht
      have hprod_zero :
          (fun y : Fin m → ℝ => H (z + realEmbed y) * ψ y)
            =ᶠ[nhds t] fun _ => 0 := by
        filter_upwards [hψ_zero] with y hy
        simp [hy]
      exact hprod_zero.continuousAt
  have hcompact :
      HasCompactSupport fun t : Fin m → ℝ => H (z + realEmbed t) * ψ t :=
    hψ_compact.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- Kernel-recovery representation algebra: once the translated kernel support
is eventually contained in the chart domain, the representation integral can be
rewritten as the difference integral used by the approximate-identity estimate. -/
theorem regularizedEnvelope_difference_integral_identity_eventually
    (Ucore U0 : Set (ComplexChartSpace m))
    (H : ComplexChartSpace m → ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hH_cont : ContinuousOn H U0)
    (hH_rep :
      ∀ n, ∀ z ∈ Ucore,
        G (ψn n) z =
          ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψn n t)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore,
      ∀ᶠ n in atTop,
        G (ψn n) z - H z =
          ∫ t : Fin m → ℝ,
            (H (z + realEmbed t) - H z) * ψn n t := by
  intro z hz
  have htranslate_eventually :
      ∀ᶠ n in atTop,
        ∀ t ∈ tsupport (ψn n : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ U0 ∧ ‖realEmbed t‖ < 1 :=
    eventually_translate_mem_open_of_shrinking_support
      Ucore U0 ψn hU0_open hcore_U0 hψ_support z hz 1 (by norm_num)
  filter_upwards [htranslate_eventually] with n htranslate_n
  have hHψ_int : Integrable fun t : Fin m → ℝ =>
      H (z + realEmbed t) * ψn n t :=
    integrable_continuousOn_realTranslate_mul_kernel
      H (ψn n) U0 z hU0_open hH_cont
      (KernelSupportWithin_hasCompactSupport (hψ_support n))
      (fun t ht => (htranslate_n t ht).1)
  have hconst_int : Integrable fun t : Fin m → ℝ => H z * ψn n t :=
    (SchwartzMap.integrable (ψn n)).const_mul (H z)
  have hconst_integral :
      (∫ t : Fin m → ℝ, H z * ψn n t) = H z := by
    calc
      (∫ t : Fin m → ℝ, H z * ψn n t) =
          H z * ∫ t : Fin m → ℝ, ψn n t := by
            exact MeasureTheory.integral_const_mul
              (H z) (fun t : Fin m → ℝ => ψn n t)
      _ = H z := by
            simp [hψ_norm n]
  calc
    G (ψn n) z - H z =
        (∫ t : Fin m → ℝ, H (z + realEmbed t) * ψn n t) - H z := by
          rw [hH_rep n z hz]
    _ =
        (∫ t : Fin m → ℝ, H (z + realEmbed t) * ψn n t) -
          (∫ t : Fin m → ℝ, H z * ψn n t) := by
          rw [hconst_integral]
    _ =
        ∫ t : Fin m → ℝ,
          H (z + realEmbed t) * ψn n t - H z * ψn n t := by
          rw [(MeasureTheory.integral_sub hHψ_int hconst_int).symm]
    _ =
        ∫ t : Fin m → ℝ,
          (H (z + realEmbed t) - H z) * ψn n t := by
          apply integral_congr_ae
          filter_upwards with t
          ring

/-- Approximate-identity recovery for the holomorphic representative, once the
kernel-recovery expression has already been rewritten as the difference
integral against the local representative.  The separate representation-to-
difference-integral identity carries the remaining compact-support
integrability bookkeeping. -/
theorem regularizedEnvelope_kernelLimit_from_difference_integral
    (Ucore U0 : Set (ComplexChartSpace m))
    (H : ComplexChartSpace m → ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hH_cont : ContinuousOn H U0)
    (hdiff :
      ∀ z ∈ Ucore,
        ∀ᶠ n in atTop,
          G (ψn n) z - H z =
            ∫ t : Fin m → ℝ,
              (H (z + realEmbed t) - H z) * ψn n t)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore,
      Tendsto (fun n => G (ψn n) z) atTop (nhds (H z)) := by
  intro z hz
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hzU : z ∈ U0 := hcore_U0 hz
  have hcont_at_z :=
    (Metric.continuousOn_iff.mp hH_cont) z hzU (ε / 2) hε2
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont_at_z
  have htranslate_eventually :
      ∀ᶠ n in atTop,
        ∀ t ∈ tsupport (ψn n : (Fin m → ℝ) → ℂ),
          z + realEmbed t ∈ U0 ∧ ‖realEmbed t‖ < δ :=
    eventually_translate_mem_open_of_shrinking_support
      Ucore U0 ψn hU0_open hcore_U0 hψ_support z hz δ hδ_pos
  have hdiff_eventually := hdiff z hz
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (htranslate_eventually.and hdiff_eventually)
  refine ⟨N, ?_⟩
  intro n hn
  have htranslate_n := (hN n hn).1
  have hdiff_n := (hN n hn).2
  have hnorm_int : ∫ t : Fin m → ℝ, ‖ψn n t‖ = 1 :=
    integral_norm_eq_one_of_real_nonneg_normalized
      (ψn n) (hψ_nonneg n) (hψ_real n) (hψ_norm n)
  have hbound : ∀ t : Fin m → ℝ,
      ‖(H (z + realEmbed t) - H z) * ψn n t‖ ≤
        (ε / 2) * ‖ψn n t‖ := by
    intro t
    by_cases ht : t ∈ tsupport (ψn n : (Fin m → ℝ) → ℂ)
    · have htrans := htranslate_n t ht
      have hdist : dist (z + realEmbed t) z = ‖realEmbed t‖ := by
        rw [dist_eq_norm]
        congr 1
        ext i
        simp
      have hH_small_dist :
          dist (H (z + realEmbed t)) (H z) < ε / 2 :=
        hδ (z + realEmbed t) htrans.1 (by simpa [hdist] using htrans.2)
      have hH_small : ‖H (z + realEmbed t) - H z‖ < ε / 2 := by
        simpa [dist_eq_norm] using hH_small_dist
      calc
        ‖(H (z + realEmbed t) - H z) * ψn n t‖ =
            ‖H (z + realEmbed t) - H z‖ * ‖ψn n t‖ := by
              exact norm_mul _ _
        _ ≤ (ε / 2) * ‖ψn n t‖ := by
              exact mul_le_mul_of_nonneg_right
                (le_of_lt hH_small) (norm_nonneg _)
    · have hzero : ψn n t = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [hzero]
  calc
    dist (G (ψn n) z) (H z) = ‖G (ψn n) z - H z‖ := by
      rw [dist_eq_norm]
    _ = ‖∫ t : Fin m → ℝ,
          (H (z + realEmbed t) - H z) * ψn n t‖ := by
      rw [hdiff_n]
    _ ≤ ∫ t : Fin m → ℝ,
          ‖(H (z + realEmbed t) - H z) * ψn n t‖ := by
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ t : Fin m → ℝ, (ε / 2) * ‖ψn n t‖ := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
      · exact (((SchwartzMap.integrable (ψn n)).norm).const_mul (ε / 2))
      · exact Filter.Eventually.of_forall hbound
    _ = (ε / 2) * ∫ t : Fin m → ℝ, ‖ψn n t‖ := by
      rw [MeasureTheory.integral_const_mul]
    _ = ε / 2 := by
      simp [hnorm_int]
    _ < ε := by
      linarith

/-- Approximate-identity recovery for the holomorphic representative directly
from the regularized kernel representation.  The proof is the composition of
the compact-support difference-integral identity with the kernel-limit
estimate. -/
theorem regularizedEnvelope_kernelLimit_from_representation
    (Ucore U0 : Set (ComplexChartSpace m))
    (H : ComplexChartSpace m → ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hH_cont : ContinuousOn H U0)
    (hH_rep :
      ∀ n, ∀ z ∈ Ucore,
        G (ψn n) z =
          ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψn n t)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ))) :
    ∀ z ∈ Ucore,
      Tendsto (fun n => G (ψn n) z) atTop (nhds (H z)) :=
  regularizedEnvelope_kernelLimit_from_difference_integral
    Ucore U0 H G ψn hU0_open hcore_U0 hH_cont
    (regularizedEnvelope_difference_integral_identity_eventually
      Ucore U0 H G ψn hU0_open hcore_U0 hH_cont
      hH_rep hψ_norm hψ_support)
    hψ_nonneg hψ_real hψ_norm hψ_support

/-- Real-direction mollification of a local holomorphic side function by a
compact real kernel. -/
noncomputable def realMollifyLocal
    (F : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    ComplexChartSpace m → ℂ :=
  fun z => ∫ t : Fin m → ℝ, F (z + realEmbed t) * ψ t

/-- The recovered real-direction mollifier is continuous on a core chart domain
whenever all real translates used by the compact kernel support stay inside the
domain where the recovered representative is continuous. -/
theorem continuousOn_realMollifyLocal_of_translate_margin
    (H : ComplexChartSpace m → ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (Ucore U0 : Set (ComplexChartSpace m))
    (hU0_open : IsOpen U0)
    (hH_cont : ContinuousOn H U0)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (hmargin :
      ∀ z ∈ Ucore, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ U0) :
    ContinuousOn (fun z : ComplexChartSpace m =>
      ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t) Ucore := by
  let k : Set (Fin m → ℝ) := tsupport (ψ : (Fin m → ℝ) → ℂ)
  let f : ComplexChartSpace m → (Fin m → ℝ) → ℂ :=
    fun z t => H (z + realEmbed t) * ψ t
  have hk : IsCompact k := by
    simpa [k] using hψ_compact
  have hf : ContinuousOn f.uncurry (Ucore ×ˢ univ) := by
    intro p hp
    rcases hp with ⟨hpU, -⟩
    by_cases ht : p.2 ∈ k
    · have hp_shift : p.1 + realEmbed p.2 ∈ U0 :=
        hmargin p.1 hpU p.2 ht
      have hH_at : ContinuousAt H (p.1 + realEmbed p.2) :=
        (hH_cont (p.1 + realEmbed p.2) hp_shift).continuousAt
          (hU0_open.mem_nhds hp_shift)
      have hshift_at :
          ContinuousAt
            (fun q : ComplexChartSpace m × (Fin m → ℝ) =>
              q.1 + realEmbed q.2) p :=
        (continuous_fst.add
          ((continuous_realEmbed (m := m)).comp continuous_snd)).continuousAt
      have hleft :
          ContinuousAt
            (fun q : ComplexChartSpace m × (Fin m → ℝ) =>
              H (q.1 + realEmbed q.2)) p :=
        ContinuousAt.comp_of_eq hH_at hshift_at rfl
      have hright :
          ContinuousAt
            (fun q : ComplexChartSpace m × (Fin m → ℝ) => ψ q.2) p :=
        ContinuousAt.comp ψ.continuous.continuousAt continuous_snd.continuousAt
      simpa [f] using (hleft.mul hright).continuousWithinAt
    · have hψ_zero :
          (ψ : (Fin m → ℝ) → ℂ) =ᶠ[nhds p.2] fun _ => 0 := by
        have ht' : p.2 ∉ tsupport (ψ : (Fin m → ℝ) → ℂ) := by
          simpa [k] using ht
        rwa [notMem_tsupport_iff_eventuallyEq] at ht'
      have hψ_zero_pair :
          (fun q : ComplexChartSpace m × (Fin m → ℝ) => ψ q.2)
            =ᶠ[nhds p] fun _ => 0 :=
        hψ_zero.comp_tendsto continuous_snd.continuousAt
      have hprod_zero : f.uncurry =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hψ_zero_pair] with q hq
        change H (q.1 + realEmbed q.2) * ψ q.2 = 0
        simp [hq]
      exact hprod_zero.continuousAt.continuousWithinAt
  have hfs : ∀ p, ∀ x, p ∈ Ucore → x ∉ k → f p x = 0 := by
    intro p x _ hx
    have hψ_zero : ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport (by simpa [k] using hx)
    simp [f, hψ_zero]
  simpa [f] using
    continuousOn_integral_of_compact_support
      (μ := volume) hk hf hfs

/-- The real-convolution test is supported in the larger chart domain whenever
the real translates of the support of the complex test by the support of the
real kernel stay in that domain. -/
theorem realConvolutionTest_supportsInOpen_of_translate_margin
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (Ucore U0 : Set (ComplexChartSpace m))
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (hmargin :
      ∀ z ∈ Ucore, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ U0) :
    SupportsInOpen
      (realConvolutionTest φ ψ : ComplexChartSpace m → ℂ) U0 := by
  let K : Set (ComplexChartSpace m) :=
    (fun p : ComplexChartSpace m × (Fin m → ℝ) => p.1 + realEmbed p.2) ''
      (tsupport (φ : ComplexChartSpace m → ℂ) ×ˢ
        tsupport (ψ : (Fin m → ℝ) → ℂ))
  have hshift_cont :
      Continuous
        (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
          p.1 + realEmbed p.2) :=
    continuous_fst.add ((continuous_realEmbed (m := m)).comp continuous_snd)
  have hK_compact : IsCompact K :=
    (hφ.1.prod hψ_compact).image hshift_cont
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hsupport_subset :
      Function.support (realConvolutionTest φ ψ : ComplexChartSpace m → ℂ)
        ⊆ K := by
    intro y hy
    by_contra hyK
    have hpoint_zero :
        ∀ t : Fin m → ℝ, φ (y - realEmbed t) * ψ t = 0 := by
      intro t
      by_cases ht : t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
      · have hz_not :
            y - realEmbed t ∉ tsupport (φ : ComplexChartSpace m → ℂ) := by
          intro hz
          have hy_mem : y ∈ K := by
            refine ⟨(y - realEmbed t, t), ⟨hz, ht⟩, ?_⟩
            ext i
            simp
          exact hyK hy_mem
        have hφ_zero : φ (y - realEmbed t) = 0 :=
          image_eq_zero_of_notMem_tsupport hz_not
        simp [hφ_zero]
      · have hψ_zero : ψ t = 0 := image_eq_zero_of_notMem_tsupport ht
        simp [hψ_zero]
    have hconv_zero : realConvolutionTest φ ψ y = 0 := by
      rw [realConvolutionTest_apply]
      calc
        (∫ t : Fin m → ℝ, φ (y - realEmbed t) * ψ t) =
            ∫ _t : Fin m → ℝ, 0 := by
              apply integral_congr_ae
              filter_upwards with t
              exact hpoint_zero t
        _ = 0 := by simp
    exact hy hconv_zero
  have htsubK :
      tsupport (realConvolutionTest φ ψ : ComplexChartSpace m → ℂ) ⊆ K :=
    closure_minimal hsupport_subset hK_closed
  refine ⟨?_, htsubK.trans ?_⟩
  · exact hK_compact.of_isClosed_subset (isClosed_tsupport _) htsubK
  · intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    exact hmargin p.1 (hφ.2 hp.1) p.2 hp.2

/-- Pairing the recovered representative with the real-convolution test is the
same as pairing the real-direction mollification of the representative with
the original complex-chart test.  This is the compact-support Fubini and
translation-invariance step in the pointwise kernel-representation bridge. -/
theorem realConvolutionTest_pairing_eq_mollifier_pairing
    (H : ComplexChartSpace m → ℂ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (Ucore U0 : Set (ComplexChartSpace m))
    (hU0_open : IsOpen U0)
    (hH_cont : ContinuousOn H U0)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore)
    (hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ))
    (hmargin :
      ∀ z ∈ Ucore, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ U0) :
    (∫ y : ComplexChartSpace m,
      H y * realConvolutionTest φ ψ y) =
      ∫ z : ComplexChartSpace m,
        (∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t) * φ z := by
  let J : ComplexChartSpace m → (Fin m → ℝ) → ℂ :=
    fun y t => H y * (φ (y - realEmbed t) * ψ t)
  have hJ_cont : Continuous J.uncurry := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases ht : p.2 ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
    · by_cases hz :
        p.1 - realEmbed p.2 ∈ tsupport (φ : ComplexChartSpace m → ℂ)
      · have hpU : p.1 ∈ U0 := by
          have htmp := hmargin (p.1 - realEmbed p.2) (hφ.2 hz) p.2 ht
          simpa using htmp
        have hH_at : ContinuousAt H p.1 :=
          (hH_cont p.1 hpU).continuousAt (hU0_open.mem_nhds hpU)
        have hH_comp :
            ContinuousAt
              (fun q : ComplexChartSpace m × (Fin m → ℝ) => H q.1) p :=
          ContinuousAt.comp hH_at continuous_fst.continuousAt
        have hshift_minus :
            ContinuousAt
              (fun q : ComplexChartSpace m × (Fin m → ℝ) =>
                q.1 - realEmbed q.2) p :=
          (continuous_fst.sub
            ((continuous_realEmbed (m := m)).comp continuous_snd)).continuousAt
        have hφ_comp :
            ContinuousAt
              (fun q : ComplexChartSpace m × (Fin m → ℝ) =>
                φ (q.1 - realEmbed q.2)) p :=
          ContinuousAt.comp φ.continuous.continuousAt hshift_minus
        have hψ_comp :
            ContinuousAt
              (fun q : ComplexChartSpace m × (Fin m → ℝ) => ψ q.2) p :=
          ContinuousAt.comp ψ.continuous.continuousAt
            continuous_snd.continuousAt
        simpa [J] using hH_comp.mul (hφ_comp.mul hψ_comp)
      · have hφ_zero :
            (φ : ComplexChartSpace m → ℂ)
              =ᶠ[nhds (p.1 - realEmbed p.2)] fun _ => 0 := by
          rwa [notMem_tsupport_iff_eventuallyEq] at hz
        have hshift_minus :
            ContinuousAt
              (fun q : ComplexChartSpace m × (Fin m → ℝ) =>
                q.1 - realEmbed q.2) p :=
          (continuous_fst.sub
            ((continuous_realEmbed (m := m)).comp continuous_snd)).continuousAt
        have hφ_zero_pair :
            (fun q : ComplexChartSpace m × (Fin m → ℝ) =>
              φ (q.1 - realEmbed q.2))
              =ᶠ[nhds p] fun _ => 0 :=
          hφ_zero.comp_tendsto hshift_minus
        have hJ_zero : J.uncurry =ᶠ[nhds p] fun _ => 0 := by
          filter_upwards [hφ_zero_pair] with q hq
          change H q.1 * (φ (q.1 - realEmbed q.2) * ψ q.2) = 0
          simp [hq]
        exact hJ_zero.continuousAt
    · have hψ_zero :
          (ψ : (Fin m → ℝ) → ℂ) =ᶠ[nhds p.2] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at ht
      have hψ_zero_pair :
          (fun q : ComplexChartSpace m × (Fin m → ℝ) => ψ q.2)
            =ᶠ[nhds p] fun _ => 0 :=
        hψ_zero.comp_tendsto continuous_snd.continuousAt
      have hJ_zero : J.uncurry =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hψ_zero_pair] with q hq
        change H q.1 * (φ (q.1 - realEmbed q.2) * ψ q.2) = 0
        simp [hq]
      exact hJ_zero.continuousAt
  have hJ_compact : HasCompactSupport J.uncurry := by
    let L : Set (ComplexChartSpace m × (Fin m → ℝ)) :=
      (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
        (p.1 + realEmbed p.2, p.2)) ''
        (tsupport (φ : ComplexChartSpace m → ℂ) ×ˢ
          tsupport (ψ : (Fin m → ℝ) → ℂ))
    have hmap_cont :
        Continuous
          (fun p : ComplexChartSpace m × (Fin m → ℝ) =>
            (p.1 + realEmbed p.2, p.2)) := by
      exact
        (continuous_fst.add
          ((continuous_realEmbed (m := m)).comp continuous_snd)).prodMk
            continuous_snd
    have hL_compact : IsCompact L :=
      (hφ.1.prod hψ_compact).image hmap_cont
    have hL_closed : IsClosed L := hL_compact.isClosed
    have hsupport_subset : Function.support J.uncurry ⊆ L := by
      intro p hp
      by_contra hpL
      have hpoint_zero : J.uncurry p = 0 := by
        by_cases ht : p.2 ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
        · have hz_not :
              p.1 - realEmbed p.2 ∉
                tsupport (φ : ComplexChartSpace m → ℂ) := by
            intro hz
            have hp_mem : p ∈ L := by
              refine ⟨(p.1 - realEmbed p.2, p.2), ⟨hz, ht⟩, ?_⟩
              ext i <;> simp
            exact hpL hp_mem
          have hφ_zero : φ (p.1 - realEmbed p.2) = 0 :=
            image_eq_zero_of_notMem_tsupport hz_not
          change H p.1 * (φ (p.1 - realEmbed p.2) * ψ p.2) = 0
          simp [hφ_zero]
        · have hψ_zero : ψ p.2 = 0 :=
            image_eq_zero_of_notMem_tsupport ht
          change H p.1 * (φ (p.1 - realEmbed p.2) * ψ p.2) = 0
          simp [hψ_zero]
      exact hp hpoint_zero
    have htsubL : tsupport J.uncurry ⊆ L :=
      closure_minimal hsupport_subset hL_closed
    exact hL_compact.of_isClosed_subset (isClosed_tsupport _) htsubL
  let M : ComplexChartSpace m → (Fin m → ℝ) → ℂ :=
    fun z t => H (z + realEmbed t) * (φ z * ψ t)
  have hM_cont : Continuous M.uncurry := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hz : p.1 ∈ tsupport (φ : ComplexChartSpace m → ℂ)
    · by_cases ht : p.2 ∈ tsupport (ψ : (Fin m → ℝ) → ℂ)
      · have hpU : p.1 + realEmbed p.2 ∈ U0 :=
          hmargin p.1 (hφ.2 hz) p.2 ht
        have hH_at : ContinuousAt H (p.1 + realEmbed p.2) :=
          (hH_cont (p.1 + realEmbed p.2) hpU).continuousAt
            (hU0_open.mem_nhds hpU)
        have hshift_at :
            ContinuousAt
              (fun q : ComplexChartSpace m × (Fin m → ℝ) =>
                q.1 + realEmbed q.2) p :=
          (continuous_fst.add
            ((continuous_realEmbed (m := m)).comp continuous_snd)).continuousAt
        have hH_comp :
            ContinuousAt
              (fun q : ComplexChartSpace m × (Fin m → ℝ) =>
                H (q.1 + realEmbed q.2)) p :=
          ContinuousAt.comp_of_eq hH_at hshift_at rfl
        have hφ_comp :
            ContinuousAt
              (fun q : ComplexChartSpace m × (Fin m → ℝ) => φ q.1) p :=
          ContinuousAt.comp φ.continuous.continuousAt
            continuous_fst.continuousAt
        have hψ_comp :
            ContinuousAt
              (fun q : ComplexChartSpace m × (Fin m → ℝ) => ψ q.2) p :=
          ContinuousAt.comp ψ.continuous.continuousAt
            continuous_snd.continuousAt
        simpa [M] using hH_comp.mul (hφ_comp.mul hψ_comp)
      · have hψ_zero :
            (ψ : (Fin m → ℝ) → ℂ) =ᶠ[nhds p.2] fun _ => 0 := by
          rwa [notMem_tsupport_iff_eventuallyEq] at ht
        have hψ_zero_pair :
            (fun q : ComplexChartSpace m × (Fin m → ℝ) => ψ q.2)
              =ᶠ[nhds p] fun _ => 0 :=
          hψ_zero.comp_tendsto continuous_snd.continuousAt
        have hM_zero : M.uncurry =ᶠ[nhds p] fun _ => 0 := by
          filter_upwards [hψ_zero_pair] with q hq
          change H (q.1 + realEmbed q.2) * (φ q.1 * ψ q.2) = 0
          simp [hq]
        exact hM_zero.continuousAt
    · have hφ_zero :
          (φ : ComplexChartSpace m → ℂ) =ᶠ[nhds p.1] fun _ => 0 := by
        rwa [notMem_tsupport_iff_eventuallyEq] at hz
      have hφ_zero_pair :
          (fun q : ComplexChartSpace m × (Fin m → ℝ) => φ q.1)
            =ᶠ[nhds p] fun _ => 0 :=
        hφ_zero.comp_tendsto continuous_fst.continuousAt
      have hM_zero : M.uncurry =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hφ_zero_pair] with q hq
        change H (q.1 + realEmbed q.2) * (φ q.1 * ψ q.2) = 0
        simp [hq]
      exact hM_zero.continuousAt
  have hM_compact : HasCompactSupport M.uncurry := by
    have hsupport_subset :
        Function.support M.uncurry ⊆
          tsupport (φ : ComplexChartSpace m → ℂ) ×ˢ
            tsupport (ψ : (Fin m → ℝ) → ℂ) := by
      intro p hp
      by_contra hp_prod
      have hzero : M.uncurry p = 0 := by
        by_cases hz : p.1 ∈ tsupport (φ : ComplexChartSpace m → ℂ)
        · have ht : p.2 ∉ tsupport (ψ : (Fin m → ℝ) → ℂ) := by
            intro ht
            exact hp_prod ⟨hz, ht⟩
          have hψ_zero : ψ p.2 = 0 :=
            image_eq_zero_of_notMem_tsupport ht
          change H (p.1 + realEmbed p.2) * (φ p.1 * ψ p.2) = 0
          simp [hψ_zero]
        · have hφ_zero : φ p.1 = 0 :=
            image_eq_zero_of_notMem_tsupport hz
          change H (p.1 + realEmbed p.2) * (φ p.1 * ψ p.2) = 0
          simp [hφ_zero]
      exact hp hzero
    have hprod_compact :
        IsCompact
          (tsupport (φ : ComplexChartSpace m → ℂ) ×ˢ
            tsupport (ψ : (Fin m → ℝ) → ℂ)) :=
      hφ.1.prod hψ_compact
    have htsub :
        tsupport M.uncurry ⊆
          tsupport (φ : ComplexChartSpace m → ℂ) ×ˢ
            tsupport (ψ : (Fin m → ℝ) → ℂ) :=
      closure_minimal hsupport_subset hprod_compact.isClosed
    exact hprod_compact.of_isClosed_subset (isClosed_tsupport _) htsub
  have hleft_expand :
      (∫ y : ComplexChartSpace m, H y * realConvolutionTest φ ψ y) =
        ∫ y : ComplexChartSpace m, ∫ t : Fin m → ℝ, J y t := by
    apply integral_congr_ae
    filter_upwards with y
    rw [realConvolutionTest_apply]
    exact
      (MeasureTheory.integral_const_mul (H y)
        (fun t : Fin m → ℝ => φ (y - realEmbed t) * ψ t)).symm
  have hswap_J :
      (∫ y : ComplexChartSpace m, ∫ t : Fin m → ℝ, J y t) =
        ∫ t : Fin m → ℝ, ∫ y : ComplexChartSpace m, J y t :=
    MeasureTheory.integral_integral_swap_of_hasCompactSupport hJ_cont hJ_compact
  have hchange :
      (∫ t : Fin m → ℝ, ∫ y : ComplexChartSpace m, J y t) =
        ∫ t : Fin m → ℝ, ∫ z : ComplexChartSpace m, M z t := by
    apply integral_congr_ae
    filter_upwards with t
    simpa [J, M] using
      (MeasureTheory.integral_add_right_eq_self
        (μ := (volume : Measure (ComplexChartSpace m)))
        (fun y : ComplexChartSpace m => J y t) (realEmbed t)).symm
  have hswap_M :
      (∫ t : Fin m → ℝ, ∫ z : ComplexChartSpace m, M z t) =
        ∫ z : ComplexChartSpace m, ∫ t : Fin m → ℝ, M z t :=
    (MeasureTheory.integral_integral_swap_of_hasCompactSupport hM_cont hM_compact).symm
  have hright_contract :
      (∫ z : ComplexChartSpace m, ∫ t : Fin m → ℝ, M z t) =
        ∫ z : ComplexChartSpace m,
          (∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t) * φ z := by
    apply integral_congr_ae
    filter_upwards with z
    calc
      (∫ t : Fin m → ℝ, M z t) =
          ∫ t : Fin m → ℝ, (H (z + realEmbed t) * ψ t) * φ z := by
            apply integral_congr_ae
            filter_upwards with t
            simp [M]
            ring
      _ =
          (∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t) * φ z := by
            exact
              MeasureTheory.integral_mul_const (φ z)
                (fun t : Fin m → ℝ => H (z + realEmbed t) * ψ t)
  calc
    (∫ y : ComplexChartSpace m, H y * realConvolutionTest φ ψ y)
        = ∫ y : ComplexChartSpace m, ∫ t : Fin m → ℝ, J y t :=
          hleft_expand
    _ = ∫ t : Fin m → ℝ, ∫ y : ComplexChartSpace m, J y t := hswap_J
    _ = ∫ t : Fin m → ℝ, ∫ z : ComplexChartSpace m, M z t := hchange
    _ = ∫ z : ComplexChartSpace m, ∫ t : Fin m → ℝ, M z t := hswap_M
    _ =
        ∫ z : ComplexChartSpace m,
          (∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t) * φ z :=
          hright_contract

/-- Fundamental-lemma endpoint for the pointwise kernel-representation bridge:
if two continuous local kernels have zero difference against every Schwartz
test supported in an open chart subdomain, then they agree pointwise there. -/
theorem regularizedEnvelope_pointwise_eq_of_test_integral_zero
    (Ucore : Set (ComplexChartSpace m))
    (Gψ Hψ : ComplexChartSpace m → ℂ)
    (hUcore_open : IsOpen Ucore)
    (hG_cont : ContinuousOn Gψ Ucore)
    (hH_cont : ContinuousOn Hψ Ucore)
    (htest_zero :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
          (∫ z : ComplexChartSpace m, (Gψ z - Hψ z) * φ z) = 0) :
    ∀ z ∈ Ucore, Gψ z = Hψ z := by
  have hdiff_zero :
      ∀ z ∈ Ucore, (Gψ z - Hψ z) = 0 :=
    eq_zero_on_open_of_supportsInOpen_schwartz_integral_zero
      hUcore_open (hG_cont.sub hH_cont) htest_zero
  intro z hz
  exact sub_eq_zero.mp (hdiff_zero z hz)

/-- Fundamental-lemma endpoint in equality-of-pairings form: if two continuous
local kernels have the same integral against every Schwartz test supported in
an open chart subdomain, then they agree pointwise there.  The explicit
integrability hypotheses keep the integral algebra honest. -/
theorem regularizedEnvelope_pointwise_eq_of_test_integral_eq
    (Ucore : Set (ComplexChartSpace m))
    (Gψ Hψ : ComplexChartSpace m → ℂ)
    (hUcore_open : IsOpen Ucore)
    (hG_cont : ContinuousOn Gψ Ucore)
    (hH_cont : ContinuousOn Hψ Ucore)
    (hG_int :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
          Integrable fun z : ComplexChartSpace m => Gψ z * φ z)
    (hH_int :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
          Integrable fun z : ComplexChartSpace m => Hψ z * φ z)
    (htest_eq :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
          (∫ z : ComplexChartSpace m, Gψ z * φ z) =
            ∫ z : ComplexChartSpace m, Hψ z * φ z) :
    ∀ z ∈ Ucore, Gψ z = Hψ z := by
  refine regularizedEnvelope_pointwise_eq_of_test_integral_zero
    Ucore Gψ Hψ hUcore_open hG_cont hH_cont ?_
  intro φ hφ
  calc
    (∫ z : ComplexChartSpace m, (Gψ z - Hψ z) * φ z) =
        ∫ z : ComplexChartSpace m, Gψ z * φ z - Hψ z * φ z := by
          apply integral_congr_ae
          filter_upwards with z
          ring
    _ =
        (∫ z : ComplexChartSpace m, Gψ z * φ z) -
          ∫ z : ComplexChartSpace m, Hψ z * φ z := by
          exact MeasureTheory.integral_sub (hG_int φ hφ) (hH_int φ hφ)
    _ = 0 := sub_eq_zero.mpr (htest_eq φ hφ)

/-- Pointwise representation of the regularized scalar kernel for the recovered
holomorphic representative.  This is the supplier needed by the final chart
assembly theorem, proved from product-kernel representation, descent to the
recovered distribution, support of the real-convolution test, Fubini, and the
local fundamental lemma. -/
theorem regularizedEnvelope_pointwiseRepresentation_of_productKernel
    {r : ℝ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (H : ComplexChartSpace m → ℂ)
    (Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    (Ucore U0 : Set (ComplexChartSpace m))
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hUcore_open : IsOpen Ucore)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hmargin_r :
      ∀ z ∈ Ucore, ∀ t : Fin m → ℝ, ‖t‖ ≤ r →
        z + realEmbed t ∈ U0)
    (hψ_support : KernelSupportWithin ψ r)
    (hG_holo : DifferentiableOn ℂ (G ψ) U0)
    (hH_holo : DifferentiableOn ℂ H U0)
    (hRep : RepresentsDistributionOnComplexDomain Hdist H U0)
    (hdesc :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (η : SchwartzMap (Fin m → ℝ) ℂ),
        K (schwartzTensorProduct₂ φ η) =
          Hdist (realConvolutionTest φ η))
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (η : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 →
        KernelSupportWithin η r →
          K (schwartzTensorProduct₂ φ η) =
            ∫ z : ComplexChartSpace m, G η z * φ z) :
    ∀ z ∈ Ucore,
      G ψ z = ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t := by
  let Hψ : ComplexChartSpace m → ℂ :=
    fun z => ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t
  have hψ_compact : HasCompactSupport (ψ : (Fin m → ℝ) → ℂ) :=
    KernelSupportWithin_hasCompactSupport hψ_support
  have hmargin :
      ∀ z ∈ Ucore, ∀ t ∈ tsupport (ψ : (Fin m → ℝ) → ℂ),
        z + realEmbed t ∈ U0 := by
    intro z hz t ht
    have ht_norm : ‖t‖ ≤ r := by
      simpa [KernelSupportWithin, Metric.mem_closedBall, dist_eq_norm]
        using hψ_support ht
    exact hmargin_r z hz t ht_norm
  have hG_cont_core : ContinuousOn (G ψ) Ucore :=
    hG_holo.continuousOn.mono hcore_U0
  have hHψ_cont : ContinuousOn Hψ Ucore := by
    simpa [Hψ] using
      continuousOn_realMollifyLocal_of_translate_margin
        H ψ Ucore U0 hU0_open hH_holo.continuousOn hψ_compact hmargin
  have hG_int :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
          Integrable fun z : ComplexChartSpace m => G ψ z * φ z := by
    intro φ hφ
    exact
      integrable_continuousOn_mul_schwartz_of_supportsInOpen
        hUcore_open hG_cont_core hφ
  have hH_int :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
          Integrable fun z : ComplexChartSpace m => Hψ z * φ z := by
    intro φ hφ
    exact
      integrable_continuousOn_mul_schwartz_of_supportsInOpen
        hUcore_open hHψ_cont hφ
  have htest_eq :
      ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
          (∫ z : ComplexChartSpace m, G ψ z * φ z) =
            ∫ z : ComplexChartSpace m, Hψ z * φ z := by
    intro φ hφ
    have hφ_U0 : SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 :=
      ⟨hφ.1, hφ.2.trans hcore_U0⟩
    have hconv_support :
        SupportsInOpen
          (realConvolutionTest φ ψ : ComplexChartSpace m → ℂ) U0 :=
      realConvolutionTest_supportsInOpen_of_translate_margin
        φ ψ Ucore U0 hφ hψ_compact hmargin
    calc
      (∫ z : ComplexChartSpace m, G ψ z * φ z) =
          K (schwartzTensorProduct₂ φ ψ) := by
            exact (hK_rep φ ψ hφ_U0 hψ_support).symm
      _ = Hdist (realConvolutionTest φ ψ) := hdesc φ ψ
      _ =
          ∫ y : ComplexChartSpace m,
            H y * realConvolutionTest φ ψ y :=
            hRep (realConvolutionTest φ ψ) hconv_support
      _ =
          ∫ z : ComplexChartSpace m,
            (∫ t : Fin m → ℝ, H (z + realEmbed t) * ψ t) * φ z :=
          realConvolutionTest_pairing_eq_mollifier_pairing
            H φ ψ Ucore U0 hU0_open hH_holo.continuousOn
            hφ hψ_compact hmargin
      _ = ∫ z : ComplexChartSpace m, Hψ z * φ z := by
          rfl
  exact
    regularizedEnvelope_pointwise_eq_of_test_integral_eq
      Ucore (G ψ) Hψ hUcore_open hG_cont_core hHψ_cont
      hG_int hH_int htest_eq

/-- Once the recovered holomorphic representative has the same kernel limit as
the regularized plus/minus side mollifications, uniqueness of limits identifies
it with the original side functions on the shrunken wedge pieces. -/
theorem regularizedEnvelope_deltaLimit_agreesOnWedges
    (Ucore : Set (ComplexChartSpace m))
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (Fplus Fminus H : ComplexChartSpace m → ℂ)
    (DplusSmall DminusSmall : Set (ComplexChartSpace m))
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hG_plus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DplusSmall,
        G (ψn n) z = realMollifyLocal Fplus (ψn n) z)
    (hG_minus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DminusSmall,
        G (ψn n) z = realMollifyLocal Fminus (ψn n) z)
    (happrox_plus :
      ∀ z ∈ Ucore ∩ DplusSmall,
        Tendsto (fun n => realMollifyLocal Fplus (ψn n) z)
          atTop (nhds (Fplus z)))
    (happrox_minus :
      ∀ z ∈ Ucore ∩ DminusSmall,
        Tendsto (fun n => realMollifyLocal Fminus (ψn n) z)
          atTop (nhds (Fminus z)))
    (hkernel_limit :
      ∀ z ∈ Ucore, Tendsto (fun n => G (ψn n) z) atTop (nhds (H z))) :
    (∀ z ∈ Ucore ∩ DplusSmall, H z = Fplus z) ∧
    (∀ z ∈ Ucore ∩ DminusSmall, H z = Fminus z) := by
  constructor
  · intro z hz
    have hG_to_plus : Tendsto (fun n => G (ψn n) z) atTop (nhds (Fplus z)) :=
      Tendsto.congr'
        (by
          filter_upwards [hG_plus] with n hn
          exact (hn z hz).symm)
        (happrox_plus z hz)
    exact tendsto_nhds_unique (hkernel_limit z hz.1) hG_to_plus
  · intro z hz
    have hG_to_minus : Tendsto (fun n => G (ψn n) z) atTop (nhds (Fminus z)) :=
      Tendsto.congr'
        (by
          filter_upwards [hG_minus] with n hn
          exact (hn z hz).symm)
        (happrox_minus z hz)
    exact tendsto_nhds_unique (hkernel_limit z hz.1) hG_to_minus

/-- A translation-covariant product kernel whose regularized scalar kernels are
holomorphic on a chart domain descends to a distributional-holomorphic chart
distribution, hence to a holomorphic representative on that chart.

This is the Streater-Wightman kernel-recovery midpoint. -/
theorem regularizedEnvelope_holomorphicDistribution_from_productKernel
    {r : ℝ}
    (hm : 0 < m)
    (hr : 0 < r)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (U0 : Set (ComplexChartSpace m))
    (hU0_open : IsOpen U0)
    (hcov : ProductKernelRealTranslationCovariantGlobal K)
    (hG_holo : ∀ ψ, KernelSupportWithin ψ r → DifferentiableOn ℂ (G ψ) U0)
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, G ψ z * φ z) :
    ∃ H : ComplexChartSpace m → ℂ,
      DifferentiableOn ℂ H U0 ∧
      ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ,
        RepresentsDistributionOnComplexDomain Hdist H U0 ∧
        ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m → ℝ) ℂ),
          K (schwartzTensorProduct₂ φ ψ) =
            Hdist (realConvolutionTest φ ψ) := by
  obtain ⟨ψn, hψ_norm, _hψ_small, hψ_support, hψ_approx⟩ :=
    exists_realConvolutionTest_approxIdentity (m := m) hr
  obtain ⟨Hdist, hdesc⟩ :=
    translationCovariantProductKernel_descends K hcov (ψn 0) (hψ_norm 0)
  have hK_dbar_zero :
      ∀ (j : Fin m) (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ) = 0 := by
    intro j φ ψ hφ hψ
    exact
      regularizedEnvelope_productKernel_dbar_eq_zero
        K G U0 hU0_open hG_holo hK_rep j φ hφ ψ hψ
  have hCR : IsDistributionalHolomorphicOn Hdist U0 :=
    translationCovariantKernel_distributionalHolomorphic
      (Hdist := Hdist) (K := K) (ψι := ψn)
      (hψ_support := Filter.Eventually.of_forall hψ_support)
      (hψ_approx := hψ_approx)
      (hdesc := hdesc)
      (hK_dbar_zero := hK_dbar_zero)
  obtain ⟨H, hH_holo, hRep⟩ :=
    distributionalHolomorphic_regular Hdist hm hU0_open hCR
  exact ⟨H, hH_holo, Hdist, hRep, hdesc⟩

/-- Final chart-envelope assembly from the checked product-kernel midpoint, the
proved pointwise-representation bridge for the recovered holomorphic function,
and the checked delta-limit wedge-agreement theorem. -/
theorem regularizedEnvelope_chartEnvelope_from_productKernel
    {r : ℝ}
    (hm : 0 < m)
    (hr : 0 < r)
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (G : SchwartzMap (Fin m → ℝ) ℂ → ComplexChartSpace m → ℂ)
    (Ucore U0 DplusSmall DminusSmall : Set (ComplexChartSpace m))
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (ψn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (hUcore_open : IsOpen Ucore)
    (hU0_open : IsOpen U0)
    (hcore_U0 : Ucore ⊆ U0)
    (hmargin_r :
      ∀ z ∈ Ucore, ∀ t : Fin m → ℝ, ‖t‖ ≤ r →
        z + realEmbed t ∈ U0)
    (hcov : ProductKernelRealTranslationCovariantGlobal K)
    (hG_holo : ∀ ψ, KernelSupportWithin ψ r → DifferentiableOn ℂ (G ψ) U0)
    (hK_rep :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) U0 →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ φ ψ) =
            ∫ z : ComplexChartSpace m, G ψ z * φ z)
    (hψ_nonneg : ∀ n t, 0 ≤ (ψn n t).re)
    (hψ_real : ∀ n t, (ψn n t).im = 0)
    (hψ_norm : ∀ n, ∫ t : Fin m → ℝ, ψn n t = 1)
    (hψ_support_shrink :
      ∀ n, KernelSupportWithin (ψn n) (1 / (n + 1 : ℝ)))
    (hψ_support_r : ∀ n, KernelSupportWithin (ψn n) r)
    (hG_plus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DplusSmall,
        G (ψn n) z = realMollifyLocal Fplus (ψn n) z)
    (hG_minus :
      ∀ᶠ n in atTop, ∀ z ∈ Ucore ∩ DminusSmall,
        G (ψn n) z = realMollifyLocal Fminus (ψn n) z)
    (happrox_plus :
      ∀ z ∈ Ucore ∩ DplusSmall,
        Tendsto (fun n => realMollifyLocal Fplus (ψn n) z)
          atTop (nhds (Fplus z)))
    (happrox_minus :
      ∀ z ∈ Ucore ∩ DminusSmall,
        Tendsto (fun n => realMollifyLocal Fminus (ψn n) z)
          atTop (nhds (Fminus z))) :
    ∃ H : ComplexChartSpace m → ℂ,
      DifferentiableOn ℂ H U0 ∧
      ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ,
        RepresentsDistributionOnComplexDomain Hdist H U0 ∧
        (∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
          (ψ : SchwartzMap (Fin m → ℝ) ℂ),
          K (schwartzTensorProduct₂ φ ψ) =
            Hdist (realConvolutionTest φ ψ)) ∧
        (∀ z ∈ Ucore ∩ DplusSmall, H z = Fplus z) ∧
        (∀ z ∈ Ucore ∩ DminusSmall, H z = Fminus z) := by
  obtain ⟨H, hH_holo, Hdist, hRep, hdesc⟩ :=
    regularizedEnvelope_holomorphicDistribution_from_productKernel
      hm hr K G U0 hU0_open hcov hG_holo hK_rep
  have hH_rep :
      ∀ n, ∀ z ∈ Ucore,
        G (ψn n) z =
          ∫ t : Fin m → ℝ, H (z + realEmbed t) * ψn n t := by
    intro n
    exact
      regularizedEnvelope_pointwiseRepresentation_of_productKernel
        K G H Hdist Ucore U0 (ψn n) hUcore_open hU0_open hcore_U0
        hmargin_r (hψ_support_r n) (hG_holo (ψn n) (hψ_support_r n))
        hH_holo hRep hdesc hK_rep
  have hkernel_limit :
      ∀ z ∈ Ucore, Tendsto (fun n => G (ψn n) z) atTop (nhds (H z)) :=
    regularizedEnvelope_kernelLimit_from_representation
      Ucore U0 H G ψn hU0_open hcore_U0 hH_holo.continuousOn
      hH_rep hψ_nonneg hψ_real hψ_norm hψ_support_shrink
  obtain ⟨hplus, hminus⟩ :=
    regularizedEnvelope_deltaLimit_agreesOnWedges
      Ucore G Fplus Fminus H DplusSmall DminusSmall ψn
      hG_plus hG_minus happrox_plus happrox_minus hkernel_limit
  exact ⟨H, hH_holo, Hdist, hRep, hdesc, hplus, hminus⟩

end SCV
