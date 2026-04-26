/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernel

/-!
# Euclidean Weyl Infrastructure

This file starts the pure Euclidean analysis package used by the localized
Weyl lemma in the distributional edge-of-the-wedge route.  The declarations
here contain no OS, Wightman, or EOW-specific data: they only record
translation and support bookkeeping for compactly supported Schwartz kernels
on finite-dimensional Euclidean spaces.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

/-- Translation on Euclidean Schwartz space as a continuous linear map:
`(euclideanTranslateSchwartzCLM a φ)(x) = φ (x + a)`. -/
noncomputable def euclideanTranslateSchwartzCLM
    {ι : Type*} [Fintype ι]
    (a : EuclideanSpace ℝ ι) :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ ι) ℂ := by
  let g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x => x + a
  have hg : g.HasTemperateGrowth := by
    fun_prop
  have hg_upper :
      ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k := by
    refine ⟨1, 1 + ‖a‖, ?_⟩
    intro x
    have htri : ‖x‖ ≤ ‖g x‖ + ‖a‖ := by
      calc
        ‖x‖ = ‖(x + a) - a‖ := by simp
        _ ≤ ‖g x‖ + ‖a‖ := by simpa [g] using norm_sub_le (x + a) a
    have hfac : ‖g x‖ + ‖a‖ ≤ (1 + ‖a‖) * (1 + ‖g x‖) := by
      nlinarith [norm_nonneg (g x), norm_nonneg a]
    have hpow : (1 + ‖g x‖) ^ (1 : ℕ) = 1 + ‖g x‖ := by simp
    rw [hpow]
    exact le_trans htri hfac
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

@[simp]
theorem euclideanTranslateSchwartz_apply
    {ι : Type*} [Fintype ι]
    (a : EuclideanSpace ℝ ι)
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    euclideanTranslateSchwartzCLM a φ x = φ (x + a) := rfl

/-- The reflected translate of a Euclidean Schwartz kernel:
`euclideanReflectedTranslate x ρ y = ρ (y - x)`. -/
noncomputable def euclideanReflectedTranslate
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
  euclideanTranslateSchwartzCLM (-x) ρ

@[simp]
theorem euclideanReflectedTranslate_apply
    {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℝ ι)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    euclideanReflectedTranslate x ρ y = ρ (y - x) := by
  simp [euclideanReflectedTranslate, sub_eq_add_neg]

/-- If a reflected Euclidean kernel of radius `r` is centered at a point whose
closed `r`-ball lies in `V`, then the reflected translate is compactly
supported in `V`. -/
theorem supportsInOpen_euclideanReflectedTranslate_of_kernelSupport
    {ι : Type*} [Fintype ι]
    {V : Set (EuclideanSpace ℝ ι)}
    {x : EuclideanSpace ℝ ι} {r : ℝ}
    {ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ}
    (hx : Metric.closedBall x r ⊆ V)
    (hρ : tsupport (ρ : EuclideanSpace ℝ ι → ℂ) ⊆
      Metric.closedBall 0 r) :
    SupportsInOpen
      (euclideanReflectedTranslate x ρ :
        EuclideanSpace ℝ ι → ℂ) V := by
  let e : EuclideanSpace ℝ ι ≃ₜ EuclideanSpace ℝ ι := Homeomorph.addRight (-x)
  have hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ) := by
    exact IsCompact.of_isClosed_subset
      (isCompact_closedBall 0 r) (isClosed_tsupport _) hρ
  constructor
  · change HasCompactSupport fun y : EuclideanSpace ℝ ι => ρ (e y)
    exact hρ_compact.comp_homeomorph e
  · have htsupport :
        tsupport
          (euclideanReflectedTranslate x ρ :
            EuclideanSpace ℝ ι → ℂ) =
          e ⁻¹' tsupport (ρ : EuclideanSpace ℝ ι → ℂ) := by
      simpa [e, euclideanReflectedTranslate, sub_eq_add_neg] using
        (tsupport_comp_eq_preimage
          (g := (ρ : EuclideanSpace ℝ ι → ℂ)) e)
    intro y hy
    have hyρ : y - x ∈ tsupport (ρ : EuclideanSpace ℝ ι → ℂ) := by
      simpa [htsupport, e, sub_eq_add_neg] using hy
    have hyball0 : y - x ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) r :=
      hρ hyρ
    have hyball : y ∈ Metric.closedBall x r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hyball0
    exact hx hyball

private theorem iteratedFDeriv_sub_euclidean_schwartz
    {ι : Type*} [Fintype ι]
    (f g : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (n : ℕ) (x : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ n (⇑(f - g)) x =
      iteratedFDeriv ℝ n (⇑f) x - iteratedFDeriv ℝ n (⇑g) x := by
  have hf : ContDiff ℝ n (⇑f) := f.smooth n
  have hg : ContDiff ℝ n (⇑g) := g.smooth n
  have hfg :
      (⇑(f - g) : EuclideanSpace ℝ ι → ℂ) =
        (⇑f) + fun x => -(⇑g x) := by
    ext y
    simp [sub_eq_add_neg]
  have hneg : (fun x => -(⇑g x)) = -⇑g := rfl
  rw [hfg, iteratedFDeriv_add_apply hf.contDiffAt hg.neg.contDiffAt,
    hneg, iteratedFDeriv_neg_apply]
  simp [sub_eq_add_neg]

/-- Compactly supported Euclidean translations are continuous in the Schwartz
topology. -/
theorem tendsto_euclideanTranslateSchwartz_nhds_of_isCompactSupport
    {ι : Type*} [Fintype ι]
    (ψ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hψ_compact : HasCompactSupport (ψ : EuclideanSpace ℝ ι → ℂ))
  (a0 : EuclideanSpace ℝ ι) :
    Tendsto (fun a : EuclideanSpace ℝ ι => euclideanTranslateSchwartzCLM a ψ)
      (𝓝 a0) (𝓝 (euclideanTranslateSchwartzCLM a0 ψ)) := by
  let K : Set (EuclideanSpace ℝ ι) :=
    tsupport (ψ : EuclideanSpace ℝ ι → ℂ)
  rw [(schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) ℂ).tendsto_nhds _ _]
  intro ⟨k, n⟩ ε hε
  let J : Set (EuclideanSpace ℝ ι) := Metric.closedBall a0 1
  have ha0J : a0 ∈ J := Metric.mem_closedBall_self (by positivity)
  have hJ_compact : IsCompact J := isCompact_closedBall _ _
  let Ktrans : Set (EuclideanSpace ℝ ι) :=
    (fun p : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) => p.1 - p.2) '' (K ×ˢ J)
  have hKtrans_compact : IsCompact Ktrans := by
    refine (hψ_compact.prod hJ_compact).image ?_
    exact continuous_fst.sub continuous_snd
  let q : EuclideanSpace ℝ ι → ℝ := fun x => ‖x‖ ^ k
  have hq_cont : Continuous q := continuous_norm.pow k
  obtain ⟨B, hB⟩ :=
    hKtrans_compact.exists_bound_of_continuousOn (f := q) hq_cont.continuousOn
  let M : ℝ := max 1 B
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let H : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ ι) ℂ :=
    fun p => iteratedFDeriv ℝ n (⇑ψ) (p.1 + p.2)
  have hH_cont : Continuous H := by
    let A : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) →
        EuclideanSpace ℝ ι := fun p => p.1 + p.2
    have hA : Continuous A := continuous_fst.add continuous_snd
    exact ((ψ.smooth n).continuous_iteratedFDeriv le_rfl).comp hA
  have hH_uc : UniformContinuousOn H (Ktrans ×ˢ J) :=
    (hKtrans_compact.prod hJ_compact).uniformContinuousOn_of_continuous hH_cont.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp hH_uc (ε / (2 * M)) (by positivity) with
    ⟨δ, hδ, hHδ⟩
  have hJ_nhds : J ∈ 𝓝 a0 := Metric.closedBall_mem_nhds _ (by positivity)
  have hball_nhds : Metric.ball a0 δ ∈ 𝓝 a0 := Metric.ball_mem_nhds _ hδ
  filter_upwards [inter_mem hJ_nhds hball_nhds] with a ha
  have haJ : a ∈ J := ha.1
  have hadist : dist a a0 < δ := ha.2
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ k n
      (euclideanTranslateSchwartzCLM a ψ - euclideanTranslateSchwartzCLM a0 ψ)
      (by positivity) ?_
  intro x
  by_cases hx : x ∈ Ktrans
  · have hpair_a : (x, a) ∈ Ktrans ×ˢ J := ⟨hx, haJ⟩
    have hpair_a0 : (x, a0) ∈ Ktrans ×ˢ J := ⟨hx, ha0J⟩
    have hpair_dist : dist (x, a) (x, a0) < δ := by
      simpa [Prod.dist_eq] using hadist
    have hderiv_close : ‖H (x, a) - H (x, a0)‖ < ε / (2 * M) := by
      simpa [H, dist_eq_norm] using hHδ _ hpair_a _ hpair_a0 hpair_dist
    have hnormx : ‖x‖ ^ k ≤ M := by
      have hBx : ‖q x‖ ≤ B := hB x hx
      have hqx : ‖q x‖ = ‖x‖ ^ k := by
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (pow_nonneg (norm_nonneg x) k)
      rw [hqx] at hBx
      exact le_trans hBx (le_max_right _ _)
    have hEq :
        iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM a ψ -
            euclideanTranslateSchwartzCLM a0 ψ)) x =
          H (x, a) - H (x, a0) := by
      have htrans_a :
          iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a ψ)) x =
            H (x, a) := by
        simpa [H] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a x)
      have htrans_a0 :
          iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a0 ψ)) x =
            H (x, a0) := by
        simpa [H] using
          (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a0 x)
      rw [iteratedFDeriv_sub_euclidean_schwartz, htrans_a, htrans_a0]
    rw [hEq]
    have hhalf : M * (ε / (2 * M)) = ε / 2 := by
      field_simp [hMpos.ne']
    calc
      ‖x‖ ^ k * ‖H (x, a) - H (x, a0)‖
          ≤ ‖x‖ ^ k * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_left (le_of_lt hderiv_close) (by positivity)
      _ ≤ M * (ε / (2 * M)) := by
            exact mul_le_mul_of_nonneg_right hnormx (by positivity)
      _ = ε / 2 := hhalf
  · have hsupport_deriv :
        Function.support (iteratedFDeriv ℝ n (⇑ψ)) ⊆ K := by
      intro y hy
      have hy' := support_iteratedFDeriv_subset (𝕜 := ℝ) (n := n) (f := ⇑ψ) hy
      simpa [K] using hy'
    have hx_not_a : x + a ∉ K := by
      intro hxa
      exact hx ⟨(x + a, a), ⟨hxa, haJ⟩, by simp⟩
    have hx_not_a0 : x + a0 ∉ K := by
      intro hxa0
      exact hx ⟨(x + a0, a0), ⟨hxa0, ha0J⟩, by simp⟩
    have hzero_a : iteratedFDeriv ℝ n (⇑ψ) (x + a) = 0 := by
      by_contra hne
      exact hx_not_a (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hzero_a0 : iteratedFDeriv ℝ n (⇑ψ) (x + a0) = 0 := by
      by_contra hne
      exact hx_not_a0 (hsupport_deriv (by simp [Function.mem_support, hne]))
    have hEq :
        iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM a ψ -
            euclideanTranslateSchwartzCLM a0 ψ)) x = 0 := by
      rw [iteratedFDeriv_sub_euclidean_schwartz]
      rw [show iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + a) by
              simpa using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a x)]
      rw [show iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a0 ψ)) x =
            iteratedFDeriv ℝ n (⇑ψ) (x + a0) by
              simpa using
                (iteratedFDeriv_comp_add_right (f := ⇑ψ) n a0 x)]
      simp [hzero_a, hzero_a0]
    rw [hEq]
    have : (0 : ℝ) ≤ ε / 2 := by positivity
    simpa using this

/-- Applying a continuous linear functional to compactly supported Euclidean
translates gives a continuous scalar function of the translation parameter. -/
theorem continuous_apply_euclideanTranslateSchwartz_of_isCompactSupport
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ψ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hψ_compact : HasCompactSupport (ψ : EuclideanSpace ℝ ι → ℂ)) :
    Continuous
      (fun a : EuclideanSpace ℝ ι => T (euclideanTranslateSchwartzCLM a ψ)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro a0
  exact T.continuous.continuousAt.tendsto.comp
    (tendsto_euclideanTranslateSchwartz_nhds_of_isCompactSupport ψ hψ_compact a0)

/-- The regularized distribution obtained by pairing a compactly supported
reflected Euclidean kernel with a continuous Schwartz functional is continuous
in the center. -/
theorem continuous_apply_euclideanReflectedTranslate_of_isCompactSupport
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ)) :
    Continuous
      (fun x : EuclideanSpace ℝ ι => T (euclideanReflectedTranslate x ρ)) := by
  have htranslate :=
    continuous_apply_euclideanTranslateSchwartz_of_isCompactSupport T ρ hρ_compact
  simpa [euclideanReflectedTranslate] using htranslate.comp continuous_neg

end SCV
