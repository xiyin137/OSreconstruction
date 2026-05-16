/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalEOWSideCone
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Side-height continuity for local EOW boundary values

This file contains the pure compact-support continuity step used after an
OS I §4.5 zero-height pairing has been identified.  It does not identify any
finite-height side value with a Euclidean Schwinger value; it only says that
continuous holomorphic-side representatives have uniform compact-direction
limits back to the real edge.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

variable {m : ℕ}

/-- If two side-height integral families converge uniformly on a nonempty compact
direction set and are eventually equal there, then their zero-height limits are
the same.

This is a neutral filter lemma used by the OS45 flat `(4.14)` subcase: the
OS-specific work is proving the eventual side-height equality, while this lemma
only takes the resulting equality to the zero-height boundary pairings. -/
theorem eq_zeroHeight_of_eventuallyEq_sideLimits
    {ι α : Type*} {l : Filter ι} [NeBot l]
    {K : Set α} (hK_nonempty : K.Nonempty)
    {F G : ι → α → ℂ} {cF cG : ℂ}
    (hF : TendstoUniformlyOn F (fun _ : α => cF) l K)
    (hG : TendstoUniformlyOn G (fun _ : α => cG) l K)
    (hEq : ∀ᶠ ε in l, ∀ η ∈ K, F ε η = G ε η) :
    cF = cG := by
  rcases hK_nonempty with ⟨η, hηK⟩
  have hFη : Tendsto (fun ε => F ε η) l (𝓝 cF) := by
    simpa using hF.tendsto_at hηK
  have hGη : Tendsto (fun ε => G ε η) l (𝓝 cG) := by
    simpa using hG.tendsto_at hηK
  have hEqη : (fun ε => F ε η) =ᶠ[l] fun ε => G ε η :=
    hEq.mono fun _ hε => hε η hηK
  exact tendsto_nhds_unique_of_eventuallyEq hFη hGη hEqη

/-- If two side-height integral families converge to their respective
zero-height pairings and also converge to the same comparison value on a
nonempty compact direction set, then the two zero-height pairings are equal.

This is the neutral filter form needed by the OS45 flat `(4.14)` transcript
after both signed side families have been rewritten to the same Schwinger
limit. -/
theorem eq_zeroHeight_of_common_sideLimit
    {ι α : Type*} {l : Filter ι} [NeBot l]
    {K : Set α} (hK_nonempty : K.Nonempty)
    {F G : ι → α → ℂ} {cF cG c : ℂ}
    (hF_zero : TendstoUniformlyOn F (fun _ : α => cF) l K)
    (hG_zero : TendstoUniformlyOn G (fun _ : α => cG) l K)
    (hF_common : TendstoUniformlyOn F (fun _ : α => c) l K)
    (hG_common : TendstoUniformlyOn G (fun _ : α => c) l K) :
    cF = cG := by
  rcases hK_nonempty with ⟨η, hηK⟩
  have hFη_zero : Tendsto (fun ε => F ε η) l (𝓝 cF) := by
    simpa using hF_zero.tendsto_at hηK
  have hFη_common : Tendsto (fun ε => F ε η) l (𝓝 c) := by
    simpa using hF_common.tendsto_at hηK
  have hGη_zero : Tendsto (fun ε => G ε η) l (𝓝 cG) := by
    simpa using hG_zero.tendsto_at hηK
  have hGη_common : Tendsto (fun ε => G ε η) l (𝓝 c) := by
    simpa using hG_common.tendsto_at hηK
  have hcF : cF = c := tendsto_nhds_unique hFη_zero hFη_common
  have hcG : cG = c := tendsto_nhds_unique hGη_zero hGη_common
  exact hcF.trans hcG.symm

/-- If a family is uniformly asymptotic to another family, and the second
family has a uniform limit, then the first family has the same uniform limit.

This is the neutral filter algebra used in the OS45 flat `(4.14)` transcript
after a branch-side side trace has been compared asymptotically with its
source-side test family. -/
theorem tendstoUniformlyOn_of_sub_tendstoUniformlyOn_zero
    {ι α : Type*} {l : Filter ι} {K : Set α}
    {F G : ι → α → ℂ} {c : ℂ}
    (hsub :
      TendstoUniformlyOn
        (fun eps eta => F eps eta - G eps eta)
        (fun _ : α => 0) l K)
    (hG : TendstoUniformlyOn G (fun _ : α => c) l K) :
    TendstoUniformlyOn F (fun _ : α => c) l K := by
  have hsum := hsub.add hG
  have hsumF :
      TendstoUniformlyOn F ((fun _ : α => 0) + fun _ : α => c) l K := by
    refine hsum.congr ?_
    filter_upwards with eps
    intro eta _heta
    simp
  exact hsumF.congr_right (by intro eta _heta; simp)

/-- A compact-support side integral converges uniformly, over compact direction
sets, to its zero-height pairing.

The domain hypothesis `hside` is deliberately local: for every compact real
support and compact direction set it supplies a positive side radius on which
all side translates stay inside the continuity domain `Ωc`.  The proof uses
continuity on a symmetric compact ball for the auxiliary height `max ε 0`, then
restricts the resulting uniform convergence to the positive-side filter. -/
theorem tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
    {E C : Set (Fin m → ℝ)}
    {Ωc : Set (ComplexChartSpace m)}
    (hΩc_open : IsOpen Ωc)
    (F : ComplexChartSpace m → ℂ)
    (hF_cont : ContinuousOn F Ωc)
    (hreal_mem : ∀ x ∈ E, (fun a => (x a : ℂ)) ∈ Ωc)
    (sgn : ℝ)
    (hside :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) +
                (sgn : ℂ) * (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωc)
    (Kη : Set (Fin m → ℝ)) (hKη : IsCompact Kη) (hKηC : Kη ⊆ C)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (hφ_compact : HasCompactSupport (φ : (Fin m → ℝ) → ℂ))
    (hφE : tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E)
    (Tφ : ℂ)
    (hzero :
      ∫ x : Fin m → ℝ,
        F (fun a => (x a : ℂ)) * φ x = Tφ) :
    TendstoUniformlyOn
      (fun (ε : ℝ) η =>
        ∫ x : Fin m → ℝ,
          F (fun a => (x a : ℂ) +
            (sgn : ℂ) * (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
      (fun _ : Fin m → ℝ => Tφ)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      Kη := by
  let K : Set (Fin m → ℝ) := tsupport (φ : (Fin m → ℝ) → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using hφ_compact
  have hK_closed : IsClosed K := isClosed_tsupport _
  have hK_subE : K ⊆ E := by
    simpa [K] using hφE
  obtain ⟨r, hrpos, hsideK⟩ := hside K hK_compact hK_subE Kη hKη hKηC
  let ρ : ℝ := r / 2
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hρlt : ρ < r := by
    dsimp [ρ]
    linarith
  let U : Set ℝ := Metric.closedBall (0 : ℝ) ρ
  let sideArg : (ℝ × (Fin m → ℝ)) × (Fin m → ℝ) → ComplexChartSpace m :=
    fun q a => (q.2 a : ℂ) +
      (sgn : ℂ) * ((max q.1.1 0 : ℝ) : ℂ) * (q.1.2 a : ℂ) * Complex.I
  let f : (ℝ × (Fin m → ℝ)) → (Fin m → ℝ) → ℂ :=
    fun p x => F (sideArg (p, x)) * φ x
  have hsideArg_cont : Continuous sideArg := by
    apply continuous_pi
    intro a
    dsimp [sideArg]
    have hx : Continuous fun q : (ℝ × (Fin m → ℝ)) × (Fin m → ℝ) =>
        (q.2 a : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_snd)
    have hε : Continuous fun q : (ℝ × (Fin m → ℝ)) × (Fin m → ℝ) =>
        ((max q.1.1 0 : ℝ) : ℂ) := by
      exact Complex.continuous_ofReal.comp
        ((continuous_fst.comp continuous_fst).max continuous_const)
    have hη : Continuous fun q : (ℝ × (Fin m → ℝ)) × (Fin m → ℝ) =>
        (q.1.2 a : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply a).comp (continuous_snd.comp continuous_fst))
    exact hx.add (((continuous_const.mul hε).mul hη).mul continuous_const)
  have harg_mem :
      ∀ q ∈ (U ×ˢ Kη) ×ˢ Set.univ, q.2 ∈ K → sideArg q ∈ Ωc := by
    intro q hq hqK
    have hεU : q.1.1 ∈ U := hq.1.1
    have hηK : q.1.2 ∈ Kη := hq.1.2
    let εpos : ℝ := max q.1.1 0
    have hεpos_nonneg : 0 ≤ εpos := by
      dsimp [εpos]
      exact le_max_right q.1.1 0
    by_cases hεpos_zero : εpos = 0
    · have hreal : (fun a => (q.2 a : ℂ)) ∈ Ωc :=
        hreal_mem q.2 (hK_subE hqK)
      convert hreal using 1
      ext a
      simp [sideArg, εpos, hεpos_zero]
    · have hεpos_pos : 0 < εpos :=
        lt_of_le_of_ne hεpos_nonneg (by simpa [eq_comm] using hεpos_zero)
      have hdist : dist q.1.1 (0 : ℝ) ≤ ρ := by
        simpa [U] using hεU
      have habs : |q.1.1| ≤ ρ := by
        simpa [Real.dist_eq] using hdist
      have hεpos_abs : εpos ≤ |q.1.1| := by
        dsimp [εpos]
        exact max_le (le_abs_self q.1.1) (abs_nonneg q.1.1)
      have hεpos_lt : εpos < r :=
        lt_of_le_of_lt (hεpos_abs.trans habs) hρlt
      exact hsideK q.2 hqK q.1.2 hηK εpos hεpos_pos hεpos_lt
  have hf_cont :
      ContinuousOn f.uncurry ((U ×ˢ Kη) ×ˢ Set.univ) := by
    intro q hq
    by_cases hqK : q.2 ∈ K
    · have hqΩ : sideArg q ∈ Ωc := harg_mem q hq hqK
      have hF_at : ContinuousAt F (sideArg q) :=
        (hF_cont (sideArg q) hqΩ).continuousAt
          (hΩc_open.mem_nhds hqΩ)
      have hleft : ContinuousAt (fun q => F (sideArg q)) q :=
        ContinuousAt.comp hF_at hsideArg_cont.continuousAt
      have hright : ContinuousAt (fun q : (ℝ × (Fin m → ℝ)) ×
          (Fin m → ℝ) => φ q.2) q :=
        ContinuousAt.comp φ.continuous.continuousAt continuous_snd.continuousAt
      simpa [f] using (hleft.mul hright).continuousWithinAt
    · have hnotK_nhds : {x : Fin m → ℝ | x ∉ K} ∈ 𝓝 q.2 :=
        hK_closed.isOpen_compl.mem_nhds hqK
      have hnotK_pair :
          ∀ᶠ q' : (ℝ × (Fin m → ℝ)) × (Fin m → ℝ)
            in nhdsWithin q ((U ×ˢ Kη) ×ˢ Set.univ), q'.2 ∉ K := by
        exact (continuous_snd.continuousAt.eventually hnotK_nhds).filter_mono
          nhdsWithin_le_nhds
      have hprod_zero :
          f.uncurry =ᶠ[nhdsWithin q ((U ×ˢ Kη) ×ˢ Set.univ)] fun _ => 0 := by
        filter_upwards [self_mem_nhdsWithin, hnotK_pair] with q' _ hq'K
        have hφ_zero : φ q'.2 = 0 := by
          simpa [K] using image_eq_zero_of_notMem_tsupport hq'K
        change F (sideArg (q'.1, q'.2)) * φ q'.2 = 0
        rw [hφ_zero, mul_zero]
      exact (continuousWithinAt_const.congr_of_eventuallyEq hprod_zero) (by
        have hφ_zero : φ q.2 = 0 := by
          simpa [K] using image_eq_zero_of_notMem_tsupport hqK
        change F (sideArg (q.1, q.2)) * φ q.2 = 0
        rw [hφ_zero, mul_zero])
  have hfs :
      ∀ p, ∀ x, p ∈ U ×ˢ Kη → x ∉ K → f p x = 0 := by
    intro p x _ hx
    have hφ_zero : φ x = 0 := by
      simpa [K] using image_eq_zero_of_notMem_tsupport hx
    simp [f, hφ_zero]
  have hInt_cont :
      ContinuousOn (fun p : ℝ × (Fin m → ℝ) => ∫ x, f p x)
        (U ×ˢ Kη) :=
    continuousOn_integral_of_compact_support (μ := volume) hK_compact hf_cont hfs
  let Faux : ℝ → (Fin m → ℝ) → ℂ := fun ε η => ∫ x, f (ε, η) x
  have hcompact_param : IsCompact (U ×ˢ Kη) := by
    exact (isCompact_closedBall (x := (0 : ℝ)) (r := ρ)).prod hKη
  have hunif :
      UniformContinuousOn (Function.uncurry Faux) (U ×ˢ Kη) := by
    simpa [Faux] using hcompact_param.uniformContinuousOn_of_continuous hInt_cont
  have h0U : (0 : ℝ) ∈ U := by
    simp [U, hρpos.le]
  have hTU :
      TendstoUniformlyOn Faux (Faux (0 : ℝ)) (𝓝[U] (0 : ℝ)) Kη :=
    hunif.tendstoUniformlyOn (x := (0 : ℝ)) h0U
  have hU_mem : U ∈ 𝓝[Set.Ioi 0] (0 : ℝ) := by
    exact nhdsWithin_le_nhds
      (Metric.closedBall_mem_nhds (0 : ℝ) hρpos)
  have hfilter : 𝓝[Set.Ioi 0] (0 : ℝ) ≤ 𝓝[U] (0 : ℝ) :=
    nhdsWithin_le_of_mem hU_mem
  have hTU_pos :
      TendstoUniformlyOn Faux (Faux (0 : ℝ)) (𝓝[Set.Ioi 0] (0 : ℝ)) Kη :=
    tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
      ((tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mp hTU).mono_left hfilter)
  let H : ℝ → (Fin m → ℝ) → ℂ := fun ε η =>
    ∫ x : Fin m → ℝ,
      F (fun a => (x a : ℂ) +
        (sgn : ℂ) * (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x
  have hFaux_H :
      ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), Set.EqOn (Faux ε) (H ε) Kη := by
    filter_upwards [self_mem_nhdsWithin] with ε hε η _
    have hmax : max ε 0 = ε := max_eq_left (le_of_lt hε)
    simp [Faux, H, f, sideArg, hmax]
  have hTU_H :
      TendstoUniformlyOn H (Faux (0 : ℝ)) (𝓝[Set.Ioi 0] (0 : ℝ)) Kη :=
    hTU_pos.congr hFaux_H
  have hFaux0 : Faux (0 : ℝ) = fun _ : Fin m → ℝ => Tφ := by
    funext η
    simpa [Faux, f, sideArg] using hzero
  simpa [H, hFaux0] using hTU_H

end SCV
